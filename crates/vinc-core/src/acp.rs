//! The access check: cache, gating, optimistic report and the READY hold.
//!
//! Every established session needs the application's answer to "may this peer connect". An answer is cached per peer
//! for 30 s of local time, measured from when it arrived and never from a deadline the application states, so a skewed
//! clock cannot stretch it. A session whose peer has a cached, unexpired answer resolves at once; otherwise one
//! [`Event::AcpCheck`] is raised per peer (further sessions of the peer wait for the same answer). A session with
//! 5 s or less of cached allow left asks again, once.
//!
//! - **Gate.** Application events of a session are held until the session is allowed; a deny closes it with code 3.
//! - **Optimistic.** A dial towards a peer with a cached allow that has more than 5 s left reports `Connected` at once,
//!   before the handshake; if the check then denies, the session closes and `Closed` follows. If the handshake is not
//!   done within 8 remembered round trips (2 s to 10 s), the peer is taken to have stopped: the session closes with
//!   `HandshakeTimeout` and `Closed` follows.
//! - **READY hold.** A client whose handshake round trip was under 20 ms reports `Connected` only after the server's
//!   READY, which the server sends once its own answer is in, so the first stream write is served one way later.
//!
//! Invariants: a session is allowed or denied exactly once per answer; no application event leaves a session before it
//! is allowed, nor after its peer's answer lapsed until a fresh allow comes; at most one check is pending per peer.

use vinc_crypto::NodeId;
use vinc_transport::conn::code;

use crate::api::{CommandError, Event};
use crate::endpoint::{AcpAnswer, env, ep_impl};
use crate::slot::State;
use crate::trace::trace;

/// A cached answer counts for this long (30 s).
pub const ACP_TTL: u64 = 30_000_000_000;
/// A cached allow with less than this left is asked again (5 s).
pub const ACP_RECHECK: u64 = 5_000_000_000;

/// The first instant at which less than [`ACP_RECHECK`] of a cached allow that ends at `until` remains.
const fn recheck_at(until: u64) -> u64 {
    until.saturating_sub(ACP_RECHECK).saturating_add(1)
}

ep_impl! {
    /// The cached answer for `peer`, if it has not expired.
    pub(crate) fn acp_cached(&self, peer: &NodeId, now: u64) -> Option<AcpAnswer> {
        self.acp.get(peer).copied().filter(|a| a.until > now)
    }

    /// Resolve the access check of an established session, or ask for it.
    pub(crate) fn start_acp(&mut self, i: usize, now: u64) {
        let Some(slot) = self.slots.get(i) else { return };
        let Some(peer) = slot.m.peer else { return };
        // A sub-session of an allowed session is allowed with it.
        let parent_allowed = slot
            .m
            .parent
            .and_then(|p| self.slot_of(p))
            .and_then(|p| self.slots.get(p))
            .is_some_and(|p| p.m.allowed);
        if parent_allowed {
            self.allow_session(i, now);
        } else if self.acp_cached(&peer, now).is_some() {
            self.acp_result(i, now);
        } else {
            self.ask_acp(i, now, false);
        }
    }

    /// Raise a check for the peer of session `i` unless one is pending. `again` marks a re-ask of a cached allow.
    pub(crate) fn ask_acp(&mut self, i: usize, now: u64, again: bool) {
        let Some(slot) = self.slots.get(i) else { return };
        let (Some(peer), Some(alpn)) = (slot.m.peer, slot.m.alpn) else { return };
        if again {
            match self.acp_cached(&peer, now) {
                Some(a) if a.allow && a.until.saturating_sub(now) < ACP_RECHECK => {}
                Some(a) if a.allow => {
                    if let Some(s) = self.slots.get_mut(i) {
                        s.m.acp_recheck = Some(recheck_at(a.until));
                    }
                    return;
                }
                Some(_) => return,
                // The answer expired before the re-ask came (the host did not run the endpoint for a while): ask.
                None => {}
            }
        }
        if self.check_of.contains(&peer) {
            return;
        }
        let check = self.next_check;
        self.next_check = self.next_check.wrapping_add(1).max(1);
        if let Some((_, old)) = self.checks.insert(check, peer) {
            self.check_of.remove(&old);
        }
        self.check_of.insert(peer, check);
        trace!(self, now, Acp { slot: i as u64, step: if again { 3 } else { 0 } });
        self.emit(Event::AcpCheck { check, node: peer, alpn });
    }

    /// Apply the cached answer to session `i`: allow, or deny and close.
    pub(crate) fn acp_result(&mut self, i: usize, now: u64) {
        let Some(peer) = self.slots.get(i).and_then(|s| s.m.peer) else { return };
        if self.acp_cached(&peer, now).is_some_and(|a| a.allow) {
            self.allow_session(i, now);
        } else {
            self.deny_session(i, now);
        }
    }

    fn deny_session(&mut self, i: usize, now: u64) {
        let Some(slot) = self.slots.get_mut(i) else { return };
        trace!(self, now, Acp { slot: i as u64, step: 2 });
        slot.m.denied = true;
        let announce_failure = slot.m.client && !slot.m.optimistic;
        let (peer, alpn) = (slot.m.peer, slot.m.alpn);
        if slot.m.client {
            // The dialer's Finish is still queued; it leaves first, so the peer knows whom it is closing on.
            slot.m.deferred_close = Some(code::FLOW_CONTROL);
        } else if let Some(conn) = slot.conn.as_mut() {
            let mut env = env!(self, now);
            conn.close(&mut env, code::FLOW_CONTROL);
        }
        if announce_failure && let (Some(node), Some(alpn)) = (peer, alpn) {
            self.emit(Event::ConnectFailed { node, alpn, reason: crate::api::ConnectFailure::Denied });
        }
        self.settle(i, now);
    }

    /// Close session `i` now if a close waited for its queue to drain. Returns whether it did.
    pub(crate) fn run_deferred_close(&mut self, i: usize, now: u64) -> bool {
        let Some(slot) = self.slots.get_mut(i) else { return false };
        let Some(error) = slot.m.deferred_close.take() else { return false };
        if let Some(conn) = slot.conn.as_mut() {
            let mut env = env!(self, now);
            conn.close(&mut env, error);
        }
        true
    }

    /// The access check allowed session `i`.
    pub(crate) fn allow_session(&mut self, i: usize, now: u64) {
        let Some(slot) = self.slots.get_mut(i) else { return };
        if slot.m.allowed || slot.m.state != State::Established {
            return;
        }
        slot.m.allowed = true;
        trace!(self, now, Acp { slot: i as u64, step: 1 });
        if let Some(peer) = slot.m.peer
            && let Some(a) = self.acp.get(&peer)
        {
            slot.m.acp_recheck = Some(recheck_at(a.until));
        }
        let (client, optimistic) = (slot.m.client, slot.m.optimistic);
        let has_sub = slot.m.has_sub;
        if !client && !slot.m.sub && let Some(conn) = slot.conn.as_mut() {
            conn.send_ready();
        }
        if client && slot.m.hold == 1 {
            slot.m.hold = 2;
            return;
        }
        if slot.m.hold == 3 {
            slot.m.hold = 0;
        }
        let session = self.session_id(i);
        if client && !optimistic {
            self.announce(i);
        } else if !client {
            let Some(slot) = self.slots.get_mut(i) else { return };
            if let (Some(node), Some(alpn)) = (slot.m.peer, slot.m.alpn) {
                slot.m.announced = true;
                self.emit(Event::Incoming { session, node, alpn });
            }
        }
        self.release_held(i, now);
        if has_sub {
            self.release_waiting(i, now);
        }
    }

    /// Apply the application's answer to check `check`.
    pub(crate) fn acp_answer(&mut self, check: u64, allow: bool, now: u64) -> Result<(), CommandError> {
        let peer = self.checks.remove(&check).ok_or(CommandError::NoCheck)?;
        self.check_of.remove(&peer);
        self.acp.insert(peer, AcpAnswer { allow, until: now.saturating_add(ACP_TTL) });
        // Sessions waiting for the answer resolve; sessions already allowed schedule their next re-ask.
        while let Some(s) = self.peer_find(&peer, |e, s| {
            e.slots
                .get(s)
                .is_some_and(|x| x.m.state == State::Established && !x.m.allowed && !x.m.denied)
        }) {
            self.acp_result(s, now);
        }
        let until = recheck_at(now.saturating_add(ACP_TTL));
        let mut i = self.by_peer.get(&peer).copied();
        while let Some(idx) = i {
            let Some(s) = self.slots.get_mut(idx as usize) else { break };
            let was_allowed = s.m.allowed;
            if was_allowed && allow {
                s.m.acp_recheck = Some(until);
            }
            let release = was_allowed && allow && s.m.hold != 2 && s.m.held.len() > 0;
            i = Some(s.m.peer_next).filter(|n| *n != crate::slot::NIL);
            // An allowed session whose answer lapsed held its events for this one: they go out, or the session closes.
            if release {
                self.release_held(idx as usize, now);
            } else if was_allowed && !allow {
                self.deny_session(idx as usize, now);
            }
            self.settle(idx as usize, now);
        }
        Ok(())
    }
}
