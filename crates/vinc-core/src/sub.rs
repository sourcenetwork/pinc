//! Sub-sessions: a second protocol to a connected peer at no cost in round trips.
//!
//! Dialing a peer that already has an established session with live keys opens a sub-session instead of a handshake.
//! The dialer picks two 4-byte connection ids `cc` and `cs`, derives the sub-session's keys from the parent's secrets
//! with those ids and the protocol name, reports `Connected` at once, and queues one sub-session open extension frame
//! (`alen alpn cc cs`) in the parent. The data it writes goes out in the next datagrams, so the peer sees the open and
//! the first bytes in the same flight. The peer derives the same keys from the frame, finds the protocol in its
//! registry and opens the matching session. The parent must have been heard from within [`PARENT_RX`]: one that went
//! silent may be a peer that restarted, so the dial makes its own handshake and reaches it.
//!
//! The extension frame is repeated by the transport until its packet is acknowledged, so the peer may see it twice;
//! the ids of the opens it accepted are remembered (1024 of them) and a repeat is ignored.
//!
//! Dialing a peer with a session for another protocol that is not yet allowed (its handshake still runs, or its access
//! check is open) opens a waiting sub-session instead: it reports `Connected` at once and takes writes, and gets its
//! keys, and its open goes out, when the parent is allowed. If the parent fails first, it closes as orphaned and the
//! application dials again.
//!
//! A sub-session that never heard its peer while its parent closes may never have been accepted (the parent died before
//! the frame arrived), so it is closed with its parent and the application dials again.
//!
//! Invariants: the keys of two sub-sessions differ whenever their ids or protocols differ; a sub-session is allowed
//! while its parent may release events (it is allowed and its peer's answer stands); an open whose ids are already used here, whose protocol is not in the registry or that finds no
//! free slot is dropped without effect.

use vinc_crypto::NodeId;
use vinc_security::{Alpn, ConnId, Failure};
use vinc_transport::conn::{Connection, PathId, PathInfo, SubOpen, SubWait};
use vinc_transport::frame::ext;

use crate::api::{CommandError, SessionId};
use crate::endpoint::{CID_LEN, env, ep_impl};
use crate::keepalive::Role;
use crate::slot::State;

/// The most sub-sessions that wait for one parent.
const MAX_WAITERS: usize = 8;
/// The most sessions that have waiters at one time.
const MAX_WAITING_PARENTS: usize = 256;
/// How recently a parent must have been heard from to carry a sub-session, in nanoseconds.
const PARENT_RX: u64 = 20_000_000_000;
use crate::trace::trace;

ep_impl! {
    /// The established session of `peer` a new session can be opened over, if any: an allowed, live one with a path,
    /// heard from within [`PARENT_RX`], a root one first.
    pub(crate) fn find_parent(&self, peer: &NodeId, now: u64) -> Option<usize> {
        let live = |i: &usize| {
            self.slots.get(*i).is_some_and(|s| {
                s.m.state == State::Established
                    && s.m.allowed
                    && now.saturating_sub(s.m.last_rx) < PARENT_RX
                    && s.conn.as_ref().is_some_and(|c| c.is_connected() && c.session().is_some() && c.active_path().is_some())
            })
        };
        self.peer_sessions(peer)
            .filter(live)
            .min_by_key(|i| self.slots.get(*i).map_or(1, |s| u8::from(s.m.parent.is_some())))
    }

    fn random_cid(&mut self) -> Result<ConnId, CommandError> {
        for _ in 0..8 {
            let mut b = [0u8; CID_LEN];
            self.drbg.fill(&mut b).map_err(|_| CommandError::Failure(Failure::Randomness))?;
            if let Some(c) = ConnId::new(&b)
                && !self.demux.contains(&c)
            {
                return Ok(c);
            }
        }
        Err(CommandError::Failure(Failure::Randomness))
    }

    /// Open a sub-session over session `parent` towards `peer` for `alpn` and return it.
    // Out of line, as `free_slot`: a whole connection moves here.
    #[inline(never)]
    pub(crate) fn open_sub(
        &mut self,
        parent: usize,
        peer: NodeId,
        alpn: &[u8],
        role: Role,
        now: u64,
    ) -> Result<SessionId, CommandError> {
        let alpn = Alpn::new(alpn).ok_or(CommandError::BadAlpn)?;
        let cc = self.random_cid()?;
        let cs = self.random_cid()?;
        let (est, path) = {
            let conn = self.slots.get(parent).and_then(|s| s.conn.as_ref()).ok_or(CommandError::NoSession)?;
            (conn.session().ok_or(CommandError::NoSession)?.clone(), conn.active_path().ok_or(CommandError::NoRoute)?)
        };
        let (child, mem) = self.alloc_slot(true, now).ok_or(CommandError::Full)?;
        let cfg = self.conn_config(Some(&peer));
        let open = SubOpen {
            client: true,
            parent: &est,
            alpn,
            cc,
            cs,
            identity: self.identity,
            path,
            path_info: PathInfo { interface_mtu: self.cfg.conn.interface_mtu, ..PathInfo::default() },
        };
        let mut env = env!(self, now);
        let conn = match Connection::sub_session(cfg, open, mem, &mut env) {
            Ok(c) => c,
            Err(e) => {
                self.retire_slot(child);
                return Err(CommandError::Failure(e));
            }
        };
        let pid = self.session_id(parent);
        if let Some(s) = self.slots.get_mut(child) {
            s.conn = Some(conn);
            s.m.peer = Some(peer);
            s.m.alpn = Some(alpn);
            s.m.parent = Some(pid);
            s.m.sub = true;
            s.m.role = role;
        }
        self.follow_parent_paths(parent, child, now);
        self.sync_cids(child, true);
        self.sync_ack_every(child);
        // The open leaves in the parent ahead of anything the child sends.
        let queued = self.queue_sub_open(parent, alpn, cc, cs);
        trace!(self, now, Sub { step: 0, parent: parent as u64, child: child as u64 });
        self.settle(parent, now);
        self.settle(child, now);
        if queued {
            return Ok(self.session_id(child));
        }
        // The open could not be queued: the child would never be accepted. Undo it.
        if let Some(s) = self.slots.get_mut(child) {
            s.m.orphaned = true;
        }
        self.redial(child, now);
        Err(CommandError::NoSession)
    }

    /// Sub-session `child` runs where session `parent` runs: it takes the parent's paths, with what the endpoint said
    /// of each and whether each is validated, its active path, its round-trip estimate, and when the endpoint last
    /// sent and heard on each (so a standby path the parent kept alive is not pinged again at once).
    fn follow_parent_paths(&mut self, parent: usize, child: usize, now: u64) {
        let Some(ps) = self.slots.get(parent) else { return };
        let stamps = ps.m.paths;
        let Some(pc) = ps.conn.as_ref() else { return };
        let Some(active) = pc.active_path() else { return };
        let mut list = [(PathId(0), PathInfo::default(), false); NP];
        let mut n = 0;
        for (d, p) in list.iter_mut().zip(pc.path_list()) {
            *d = p;
            n += 1;
        }
        let rtt = pc.rtt_estimate();
        let mut env = env!(self, now);
        if let Some(s) = self.slots.get_mut(child) {
            s.m.paths = stamps;
            if let Some(k) = s.conn.as_mut() {
                k.adopt_paths(&mut env, list.get(..n).unwrap_or_default(), active);
                k.adopt_rtt(rtt);
            }
        }
        self.refresh_rooms(child, true);
    }

    /// Queue the sub-session open extension in `parent`. Returns whether it was queued.
    fn queue_sub_open(&mut self, parent: usize, alpn: Alpn, cc: ConnId, cs: ConnId) -> bool {
        let mut body = [0u8; 1 + vinc_security::ids::MAX_ALPN_LEN + 2 * CID_LEN];
        let a = alpn.as_bytes();
        let used = 1 + a.len() + 2 * CID_LEN;
        if let Some(b) = body.get_mut(..used) {
            let (head, tail) = b.split_at_mut(1 + a.len());
            if let Some(l) = head.first_mut() {
                *l = u8::try_from(a.len()).unwrap_or(0);
            }
            if let Some(d) = head.get_mut(1..) {
                d.copy_from_slice(a);
            }
            let (c1, c2) = tail.split_at_mut(CID_LEN);
            c1.copy_from_slice(cc.as_bytes());
            c2.copy_from_slice(cs.as_bytes());
        }
        let queued = self.slots.get_mut(parent).and_then(|s| {
            s.m.has_sub = true;
            s.m.ctrl_pending = true;
            s.conn.as_mut().map(|c| c.send_extension(ext::SUB_SESSION_OPEN, body.get(..used).unwrap_or_default()))
        });
        matches!(queued, Some(Ok(())))
    }

    /// A session of `peer` that is not yet allowed, whatever its role and state, that a dial for another protocol can
    /// wait for: not itself a waiting sub-session, with room for another waiter, and while fewer than
    /// [`MAX_WAITING_PARENTS`] sessions have waiters.
    pub(crate) fn find_waiting_parent(&self, peer: &NodeId, alpn: &[u8]) -> Option<usize> {
        let parent = self.peer_find(peer, |e, i| {
            e.slots.get(i).is_some_and(|s| {
                s.m.state != State::Closing
                    && !s.m.allowed
                    && !s.m.denied
                    && !s.m.waiting
                    && s.m.alpn.is_some_and(|a| a.as_bytes() != alpn)
                    && e.waiters(i) < MAX_WAITERS
            })
        })?;
        (self.waiting_parents() < MAX_WAITING_PARENTS).then_some(parent)
    }

    /// How many sessions have a sub-session waiting for them.
    // vertexia: a scan of the table per waiting dial, a counter kept by the open and the release if dials get hot
    fn waiting_parents(&self) -> usize {
        let seen = self.slots.iter().enumerate().filter(|(_, s)| s.m.waiting);
        seen.clone()
            .filter(|(i, s)| !seen.clone().take_while(|(j, _)| j < i).any(|(_, o)| o.m.parent == s.m.parent))
            .count()
    }

    /// How many sub-sessions wait for session `parent`.
    fn waiters(&self, parent: usize) -> usize {
        let Some(peer) = self.slots.get(parent).and_then(|s| s.m.peer) else { return 0 };
        let pid = self.session_id(parent);
        self.peer_sessions(&peer)
            .filter(|c| self.slots.get(*c).is_some_and(|s| s.m.waiting && s.m.parent == Some(pid)))
            .count()
    }

    /// Open a sub-session towards `peer` for `alpn` over session `parent`, which is still in its handshake. The
    /// application is told `Connected` at once and may write; the keys come when the parent is allowed.
    // Out of line, as `free_slot`: a whole connection moves here.
    #[inline(never)]
    pub(crate) fn open_sub_wait(
        &mut self,
        parent: usize,
        peer: NodeId,
        alpn: &[u8],
        role: Role,
        now: u64,
    ) -> Result<SessionId, CommandError> {
        let alpn = Alpn::new(alpn).ok_or(CommandError::BadAlpn)?;
        let cc = self.random_cid()?;
        let cs = self.random_cid()?;
        let path = self
            .slots
            .get(parent)
            .and_then(|s| s.conn.as_ref())
            .and_then(Connection::active_path)
            .ok_or(CommandError::NoRoute)?;
        let (child, mem) = self.alloc_slot(true, now).ok_or(CommandError::Full)?;
        let cfg = self.conn_config(Some(&peer));
        let open = SubWait { alpn, cc, cs, identity: self.identity, path, path_info: PathInfo { interface_mtu: self.cfg.conn.interface_mtu, ..PathInfo::default() } };
        let mut env = env!(self, now);
        let conn = match Connection::sub_pending(cfg, open, mem, &mut env) {
            Ok(c) => c,
            Err(e) => {
                self.retire_slot(child);
                return Err(CommandError::Failure(e));
            }
        };
        let pid = self.session_id(parent);
        if let Some(s) = self.slots.get_mut(child) {
            s.conn = Some(conn);
            s.m.peer = Some(peer);
            s.m.alpn = Some(alpn);
            s.m.parent = Some(pid);
            s.m.sub = true;
            s.m.waiting = true;
            s.m.optimistic = true;
            s.m.sub_ids = Some((cc, cs));
            s.m.role = role;
        }
        if let Some(s) = self.slots.get_mut(parent) {
            s.m.has_sub = true;
        }
        self.link_peer(peer, u32::try_from(child).unwrap_or(0));
        self.sync_cids(child, true);
        self.sync_ack_every(child);
        trace!(self, now, Sub { step: 0, parent: parent as u64, child: child as u64 });
        self.announce(child);
        self.settle(child, now);
        Ok(self.session_id(child))
    }

    /// Session `parent` was allowed: the sub-sessions that waited for it get their keys and their open goes out.
    pub(crate) fn release_waiting(&mut self, parent: usize, now: u64) {
        let Some(peer) = self.slots.get(parent).and_then(|s| s.m.peer) else { return };
        let pid = self.session_id(parent);
        let Some(est) = self.slots.get(parent).and_then(|s| s.conn.as_ref()).and_then(|c| c.session().cloned()) else {
            return;
        };
        while let Some(c) = self.peer_find(&peer, |e, c| {
            e.slots.get(c).is_some_and(|s| s.m.waiting && s.m.parent == Some(pid))
        }) {
            let Some((alpn, ids)) = self.slots.get(c).and_then(|s| Some((s.m.alpn?, s.m.sub_ids?))) else { break };
            let mut env = env!(self, now);
            let activated = self
                .slots
                .get_mut(c)
                .and_then(|s| s.conn.as_mut())
                .is_some_and(|k| k.activate_sub(&mut env, &est, alpn).is_ok());
            if let Some(s) = self.slots.get_mut(c) {
                s.m.waiting = false;
            }
            if activated {
                self.follow_parent_paths(parent, c, now);
            }
            if activated && self.queue_sub_open(parent, alpn, ids.0, ids.1) {
                self.settle(parent, now);
            } else {
                // It cannot be opened: close it so the application dials again.
                if let Some(s) = self.slots.get_mut(c) {
                    s.m.orphaned = true;
                    if let Some(k) = s.conn.as_mut() {
                        k.close(&mut env!(self, now), vinc_transport::conn::code::NO_ERROR);
                    }
                }
            }
            self.settle(c, now);
        }
    }

    /// Accept a sub-session open that arrived in session `parent`.
    // Out of line, as `free_slot`: a whole connection moves here.
    #[inline(never)]
    pub(crate) fn sub_accept(&mut self, parent: usize, now: u64, body: &[u8]) {
        let Some(&alen) = body.first() else { return };
        let alen = usize::from(alen);
        if body.len() != 1 + alen + 2 * CID_LEN {
            return;
        }
        let (Some(a), Some(cc), Some(cs)) = (
            body.get(1..1 + alen),
            body.get(1 + alen..1 + alen + CID_LEN).and_then(ConnId::new),
            body.get(1 + alen + CID_LEN..).and_then(ConnId::new),
        ) else {
            return;
        };
        if alen == 0 || !self.accepts(a) || self.demux.contains(&cs) || self.subs_seen.contains(&cs) {
            return;
        }
        let Some(proto) = Alpn::new(a) else { return };
        let Some((est, path, peer)) = self
            .slots
            .get(parent)
            .and_then(|s| s.conn.as_ref().filter(|c| c.is_connected()))
            .and_then(|c| Some((c.session()?.clone(), c.active_path()?, c.session()?.peer)))
        else {
            return;
        };
        let Some((child, mem)) = self.alloc_slot(false, now) else { return };
        let cfg = self.conn_config(Some(&peer));
        let open = SubOpen {
            client: false,
            parent: &est,
            alpn: proto,
            cc,
            cs,
            identity: self.identity,
            path,
            path_info: PathInfo { interface_mtu: self.cfg.conn.interface_mtu, ..PathInfo::default() },
        };
        let mut env = env!(self, now);
        let Ok(conn) = Connection::sub_session(cfg, open, mem, &mut env) else {
            self.retire_slot(child);
            return;
        };
        self.subs_seen.insert(cs, ());
        let pid = self.session_id(parent);
        if let Some(s) = self.slots.get_mut(child) {
            s.conn = Some(conn);
            s.m.peer = Some(peer);
            s.m.alpn = Some(proto);
            s.m.parent = Some(pid);
            s.m.sub = true;
        }
        if let Some(s) = self.slots.get_mut(parent) {
            s.m.has_sub = true;
        }
        self.follow_parent_paths(parent, child, now);
        self.sync_cids(child, true);
        trace!(self, now, Sub { step: 1, parent: parent as u64, child: child as u64 });
        self.settle(child, now);
    }
}
