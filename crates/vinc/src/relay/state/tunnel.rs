//! The relay's side of the tunnel: the members that hold a validated UDP session with the node's endpoint, and the
//! packets that pass between that endpoint and the members' carriers.
//!
//! The endpoint is not the relay's: the embedder owns it and lends it at each call (`vinc_node::Ep`), so the same
//! endpoint can be the application's. What the state machine wants of it is queued here while the machine runs (a
//! packet for the endpoint, a pulse for a member's session, a datagram for a member's UDP address) and applied when
//! the embedder calls [`Core::hub_pump`].
//!
//! Invariants: the queue and its byte arena never pass `WORK_BACKLOG` items, a packet past it is counted as dropped;
//! the table of slots that name members in relay path addresses never grows past `SLOTS` and reuses the oldest first;
//! a session is a member's only after the embedder reported it; the members never pass the limit `hub_sessions`; the
//! member a datagram came from is found through the endpoint's table of sessions by address, not by a walk.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::net::SocketAddr;

use vinc_core::{Command, Event as EpEvent, Role, SessionId, relay_addr, relay_parts};
use vinc_crypto::NodeId;
use vinc_keystore::KeyStore;
use vinc_node::Ep;

use super::Core;
use crate::relay::access::Access;

/// The relay path addresses name a member by a 16-bit slot; this many are kept.
const SLOTS: usize = 4096;
/// The most items waiting for the next pump.
const WORK_BACKLOG: usize = 1024;

#[derive(Debug, Clone, Copy)]
enum Work {
    /// A packet from a member's carrier for the endpoint (bytes `s..e` of the arena).
    Local(NodeId, usize, usize),
    /// The member's carrier showed life.
    Pulse(NodeId),
    /// A datagram for the member's UDP address.
    Udp(NodeId, usize, usize),
}

pub(super) struct Tunnel {
    local: SocketAddr,
    members: BTreeMap<SessionId, NodeId>,
    slots: Vec<NodeId>,
    next_slot: usize,
    work: Vec<Work>,
    arena: Vec<u8>,
}

impl Tunnel {
    pub(super) const fn new(local: SocketAddr) -> Self {
        Self {
            local,
            members: BTreeMap::new(),
            slots: Vec::new(),
            next_slot: 0,
            work: Vec::new(),
            arena: Vec::new(),
        }
    }

    pub(super) fn sessions(&self) -> usize {
        self.members.len()
    }

    fn slot_of(&mut self, node: &NodeId) -> u16 {
        let i = self.slots.iter().position(|x| x == node).unwrap_or_else(|| {
            if self.slots.len() < SLOTS {
                self.slots.push(*node);
                self.slots.len() - 1
            } else {
                let i = self.next_slot;
                self.next_slot = (i + 1) % SLOTS;
                if let Some(s) = self.slots.get_mut(i) {
                    *s = *node;
                }
                i
            }
        });
        u16::try_from(i).unwrap_or(0)
    }

    fn push(&mut self, w: impl FnOnce(usize, usize) -> Work, bytes: &[u8]) -> bool {
        if self.work.len() >= WORK_BACKLOG {
            return false;
        }
        let s = self.arena.len();
        self.arena.extend_from_slice(bytes);
        self.work.push(w(s, self.arena.len()));
        true
    }
}

fn session_remote<E: Ep>(ep: &E, sid: SessionId) -> Option<SocketAddr> {
    let st = ep.stats(sid)?;
    st.path_validated
        .then_some(st.route)
        .flatten()
        .map(|(_, r)| r)
        .filter(|r| !vinc_core::is_relay_addr(r))
}

/// The direct address of `node`'s validated session, any of its sessions: where a datagram for the member goes, and
/// whether the relay may tunnel to it.
fn node_remote<E: Ep>(ep: &E, members: &BTreeMap<SessionId, NodeId>, node: &NodeId) -> Option<SocketAddr> {
    members
        .iter()
        .filter(|(_, n)| *n == node)
        .find_map(|(sid, _)| session_remote(ep, *sid))
}

impl<S, K: KeyStore, A: Access> Core<S, K, A> {
    pub(super) fn queue_local(&mut self, from: &NodeId, packet: &[u8]) {
        let from = *from;
        let queued = self
            .hub
            .as_mut()
            .is_some_and(|t| t.push(|s, e| Work::Local(from, s, e), packet));
        if !queued {
            self.counters.hub_dropped += 1;
        }
    }

    pub(super) fn queue_pulse(&mut self, node: NodeId) {
        if let Some(t) = self.hub.as_mut()
            && t.work.len() < WORK_BACKLOG
        {
            t.work.push(Work::Pulse(node));
        }
    }

    pub(super) fn queue_member_udp(&mut self, node: &NodeId, bytes: &[u8]) {
        let node = *node;
        let queued = self
            .hub
            .as_mut()
            .is_some_and(|t| t.push(|s, e| Work::Udp(node, s, e), bytes));
        if !queued {
            self.counters.datagrams_dropped += 1;
        }
    }

    /// The member whose validated session talks from `src` (of several, the lowest session id), from the endpoint's
    /// table of sessions by address.
    pub(crate) fn member_at<E: Ep>(&self, ep: &E, src: &SocketAddr) -> Option<NodeId> {
        let t = self.hub.as_ref()?;
        let sid = ep.session_from(src, &|sid| t.members.contains_key(&sid))?;
        t.members.get(&sid).copied()
    }

    /// Apply what the machine queued for the endpoint. Whether anything was applied. The events the commands produced
    /// at once go to `out`: the endpoint's owner handles them like the ones it polls.
    #[allow(clippy::many_single_char_names, reason = "short-lived names of one command each")]
    pub(crate) fn hub_pump<E: Ep>(&mut self, ep: &mut E, now: u64, out: &mut Vec<EpEvent>) -> bool {
        let Some(mut t) = self.hub.take() else {
            return false;
        };
        let work = core::mem::take(&mut t.work);
        let did = !work.is_empty();
        for w in work {
            match w {
                Work::Local(from, s, e) => {
                    let slot = t.slot_of(&from);
                    if let Some(p) = t.arena.get_mut(s..e) {
                        ep.handle_datagram(now, t.local, relay_addr(false, 0, slot), p);
                    }
                }
                Work::Pulse(node) => {
                    if let Some((session, _)) = t.members.iter().find(|(_, n)| **n == node) {
                        let session = *session;
                        if let Ok(r) = ep.command(now, Command::Pulse { session, sent: true }) {
                            out.extend(r.events.iter().copied());
                        }
                    }
                }
                Work::Udp(node, s, e) => {
                    let addr = node_remote(ep, &t.members, &node);
                    if let (Some(a), Some(b)) = (addr, t.arena.get(s..e)) {
                        self.queue_udp(a, b);
                    } else {
                        // the route went since the relay chose it: later packets take the next rule
                        self.fx.set_direct(&node, false);
                        self.counters.datagrams_dropped += 1;
                    }
                }
            }
        }
        t.arena.clear();
        self.hub = Some(t);
        did
    }

    /// The endpoint reported `ev`; the relay takes what concerns its members.
    pub(crate) fn hub_event<E: Ep>(
        &mut self,
        ep: &mut E,
        now: u64,
        relay_now: u64,
        ev: &EpEvent,
        out: &mut Vec<EpEvent>,
    ) {
        let cap = self.limits.hub_sessions;
        let Some(t) = self.hub.as_mut() else { return };
        match *ev {
            EpEvent::Incoming { session, node, .. } => {
                if t.members.len() >= cap {
                    self.counters.hub_dropped += 1;
                    return;
                }
                t.members.insert(session, node);
                if let Ok(r) = ep.command(
                    now,
                    Command::SetRole {
                        session,
                        role: Role::Member,
                    },
                ) {
                    out.extend(r.events.iter().copied());
                }
            }
            EpEvent::Closed { session, .. } => {
                if let Some(node) = t.members.remove(&session) {
                    self.sm.udp_gone(&node);
                    if !t.members.values().any(|n| *n == node) {
                        self.fx.set_direct(&node, false);
                    }
                }
            }
            EpEvent::PathChanged { session, .. } => {
                if let Some(node) = t.members.get(&session).copied() {
                    self.fx
                        .set_direct(&node, node_remote(&*ep, &t.members, &node).is_some());
                }
            }
            EpEvent::PeerAwake { session } => {
                if let Some(node) = t.members.get(&session) {
                    let node = *node;
                    self.sm.member_returned(relay_now, &node, &mut self.fx);
                    self.flush();
                }
            }
            _ => {}
        }
    }

    /// A datagram the endpoint wants to send to `remote`: whether it was a relay path address, which names a member
    /// (the datagram then goes to the member's carrier, or is dropped if the slot names nobody).
    pub(crate) fn tunnel(&mut self, now: u64, remote: &SocketAddr, bytes: &[u8]) -> bool {
        let Some((_, slot)) = relay_parts(remote) else {
            return false;
        };
        let node = self.hub.as_ref().and_then(|t| t.slots.get(usize::from(slot)).copied());
        match node {
            Some(n) => {
                // vertexia: a refused packet is counted and traced by the machine
                let _ = self.sm.send_local(now, &n, 0, bytes, &mut self.fx);
                self.flush();
            }
            None => self.counters.hub_dropped += 1,
        }
        true
    }

    /// End the carrier of `node`, if it has one; whether it had.
    pub(crate) fn revoke(&mut self, node: &NodeId) -> bool {
        let Some(&slot) = self.by_node.get(&super::node_key(node)) else {
            return false;
        };
        self.dying(slot, crate::relay::stats::Closed::Revoked);
        true
    }
}
