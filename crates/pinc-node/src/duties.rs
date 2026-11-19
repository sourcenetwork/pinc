//! The host-side duties of membership: dialing the hubs, repairing a session without a write stream (a member's to a
//! hub, a hub's to a member), and probing a member along another hub's relay.
//!
//! They run on the node's own cadence (half a second for a member, a second for a hub) and when a layer asks for a
//! dial by sending a frame to a peer with no session.
//!
//! Invariants: a peer is dialed once at a time and never inside its backoff window; a peer that refused us is
//! redialed only after the deny backoff; no duty closes a session for silence (membership does, on an unanswered HELLO).
//! Both dial promises hold below the tables' bound: a full failed-dial table keeps no window for a peer it has no
//! entry for, which is then redialed at every pass, and a full table of dials in progress does not record the dial.

use alloc::vec::Vec;

use pinc_core::{Command, Role};
use pinc_membership::NodeId;

use crate::config::{DUTY_HUB, DUTY_MEMBER, GONE_TTL, Nanos, STREAM_REPAIR, Store};
use crate::ep::Ep;
use crate::node::Node;
use crate::trace::{NodeTrace, tag};

/// The most members whose write stream a hub replaces in one duty pass; the rest wait for the next.
const REPAIRS_PER_PASS: usize = 256;

/// A failed dial's backoff entry is forgotten this long after it expired.
const FAILED_KEEP: Nanos = 3_600_000_000_000;

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: pinc_crypto::Provider + Clone,
    St: Store,
    A: crate::apps::Apps<P>,
    E::Src: crate::apps::ServeSource<A::Values>,
{
    /// Dial `peer` for the hub protocol, unless a session or a dial exists or the peer is backing off.
    pub(crate) fn dial_peer(&mut self, now: Nanos, peer: &NodeId) {
        let io = &self.io;
        if self.leaving
            || io.links.get(peer).is_some_and(|l| l.conn.is_some())
            || io.connecting.contains_key(peer)
            || io.revoked.contains(peer)
            || io.failed.get(peer).is_some_and(|(until, _)| now < *until)
        {
            return;
        }
        let id = io.full_id(peer);
        let hub = io.is_hub_id(peer);
        let udp = self
            .conn
            .relay_of(&id)
            .and_then(|i| self.conn.relay_cfg(i))
            .and_then(|c| c.udp);
        let hints = [udp];
        let hints: &[core::net::SocketAddr] = if let [Some(a)] = &hints {
            core::slice::from_ref(a)
        } else {
            &[]
        };
        let role = if hub { Role::Hub } else { Role::Other };
        let alpn = self.io.alpn;
        if self.conn.dial(now, &mut self.io.ep, id, alpn, role, hints).is_ok() {
            if self.io.connecting.len() < crate::config::TABLE_MAX {
                self.io.connecting.insert(*peer, now);
            }
            self.io.trace(NodeTrace::Dial { peer: tag(peer) });
        } else {
            self.io.backoff(peer);
            self.io.drop_queue(peer);
        }
    }

    /// Probe `member` on the path through `hub`'s relay: a path challenge on the member's session. The answer comes
    /// back as transport evidence.
    pub(crate) fn probe_via(&mut self, hub: &NodeId, member: &NodeId) {
        let Some(session) = self.io.links.get(member).and_then(|l| l.conn) else {
            return;
        };
        let Some(relay) = self.conn.relay_of(&self.io.full_id(hub)) else {
            return;
        };
        let addr = self.conn.path_addr(relay, &self.io.full_id(member));
        // A path the session cannot take is a probe that was not sent: nothing answers, and the lease decides.
        let _ = self.io.cmd(Command::Punch { session, addr });
    }

    /// The periodic duties.
    pub(crate) fn duties(&mut self, now: Nanos) {
        self.next_duty = now.saturating_add(if self.io.is_hub { DUTY_HUB } else { DUTY_MEMBER });
        if self.leaving {
            return;
        }
        self.io.note_rtts();
        for i in 0..self.io.hubs.len() {
            let Some(hub) = self.io.hubs.get(i).copied() else {
                continue;
            };
            if hub == self.io.me {
                continue;
            }
            self.dial_peer(now, &hub);
            self.repair_stream(now, &hub);
        }
        if self.io.is_hub {
            // A hub's write stream to a member that stopped it is replaced as a member's toward a hub is.
            let members: Vec<NodeId> = self
                .io
                .links
                .iter()
                .filter(|(p, l)| l.conn.is_some() && l.out.is_none() && !self.io.is_hub_id(p))
                .map(|(p, _)| *p)
                .take(REPAIRS_PER_PASS)
                .collect();
            for member in members {
                self.repair_stream(now, &member);
            }
        }
        self.prune(now);
    }

    /// A session without our write stream gets a fresh one; if none can be opened, the session is closed.
    fn repair_stream(&mut self, now: Nanos, hub: &NodeId) {
        let Some(l) = self.io.links.get(hub).copied() else {
            return;
        };
        let Some(session) = l.conn else { return };
        if l.out.is_some() || now.saturating_sub(l.opened) <= STREAM_REPAIR {
            return;
        }
        match self.io.try_open_stream_at(session, crate::config::HUB_URGENCY) {
            Ok(s) => {
                if let Some(x) = self.io.links.get_mut(hub) {
                    x.out = Some(s);
                }
                self.io.flush_queue(hub, session, s);
                self.io.trace(NodeTrace::StreamRepaired { peer: tag(hub) });
            }
            // No pool room for the window yet: the link is fine, so ask again on the next duty pass.
            Err(true) => {}
            Err(false) => {
                let _ = self.io.cmd(Command::Close { session, error: 0 });
                let (m, mut h) = self.mem_host();
                m.session_down(&mut h, now, hub, 0);
            }
        }
    }

    fn prune(&mut self, now: Nanos) {
        self.io
            .failed
            .retain(|_, (until, _)| until.saturating_add(FAILED_KEEP) > now);
        self.io.carriers.retain(|_, c| match c {
            pinc_membership::session::Carrier::Gone { since, .. } => now.saturating_sub(*since) < GONE_TTL,
            _ => true,
        });
    }
}
