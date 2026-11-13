//! The hosts the layers talk to: membership's `Host` and broadcast's `Host`, both over the node's session state.
//!
//! Membership needs sessions, carriers, evidence, the broadcast layer and the local node in one object; broadcast
//! needs sessions, the view and the clock. Both borrow the same [`Io`], one at a time, and reach the other layer
//! through a borrow of its machine, so a frame that membership does not own goes straight to broadcast.
//!
//! Route semantics. A frame sent on [`Route::Session`] or [`Route::Direct`] goes down the hub stream, which the
//! transport carries on its active path (the validated direct path if there is one). A probe on [`Route::Via`] is a
//! path challenge to the member through the named hub's relay: the member's answer is transport evidence, not a frame.
//!
//! Invariants: no method blocks; a frame that no session took reports `false`.

use vinc_broadcast::{Event as BcEvent, Host as BcHost, Lane, Topics};
use vinc_membership::session::{Broadcast, Carrier, CloseReason, Evidence, Local, Nanos, Route, Session, StoreError};
use vinc_membership::{Membership, NodeId};

use crate::config::Store;
use crate::ep::Ep;
use crate::event::NodeEvent;
use crate::io::Io;

/// The most path probes waiting for the node to send them.
const PROBES_MAX: usize = 64;

/// Membership's host: the session state, and the broadcast machine when one exists.
pub(crate) struct MemHost<'a, E: Ep, St: Store> {
    pub(crate) io: &'a mut Io<E, St>,
    pub(crate) topics: Option<&'a mut Topics>,
}

impl<E: Ep, St: Store> MemHost<'_, E, St> {
    fn bc(&mut self) -> (Option<&mut Topics>, Bc<'_, E, St>) {
        (
            self.topics.as_deref_mut(),
            Bc {
                io: &mut *self.io,
                mem: None,
            },
        )
    }
}

impl<E: Ep, St: Store> Session for MemHost<'_, E, St> {
    fn send(&mut self, peer: &NodeId, route: Route, frame: &[u8]) -> bool {
        match route {
            Route::Session | Route::Direct => self.io.send_membership(peer, Lane::Main, frame),
            Route::Reply => self.io.send_membership(peer, Lane::Reply, frame),
            Route::Via(hub) => {
                if self.io.probes.len() >= PROBES_MAX {
                    return false;
                }
                self.io.probes.push((hub, *peer));
                true
            }
        }
    }

    fn evidence(&self, peer: &NodeId) -> Option<Evidence> {
        self.io.evidence_of(peer)
    }

    fn carrier(&self, member: &NodeId) -> Carrier {
        self.io.carriers.get(member).copied().unwrap_or_default()
    }

    fn close(&mut self, peer: &NodeId, reason: CloseReason) {
        self.io.close_peer(peer, reason);
    }

    fn give_up(&self, peer: &NodeId) -> Nanos {
        self.io.give_up_of(peer)
    }
}

impl<E: Ep, St: Store> Broadcast for MemHost<'_, E, St> {
    fn floor(&mut self, member: &NodeId, out: &mut [u8]) -> usize {
        self.topics.as_deref_mut().map_or(0, |t| t.floor(member, out))
    }

    fn frame(&mut self, from: &NodeId, ty: u8, topic: &[u8], rest: &[u8]) {
        let now = self.io.now;
        let (t, mut h) = self.bc();
        if let Some(t) = t {
            t.frame(&mut h, now, from, ty, topic, rest);
        }
    }

    fn hold(&mut self, member: &NodeId) {
        let (t, mut h) = self.bc();
        if let Some(t) = t {
            t.hold(&mut h, member);
        }
    }

    fn restore(&mut self, member: &NodeId) {
        let (t, mut h) = self.bc();
        if let Some(t) = t {
            t.restore(&mut h, member);
        }
    }

    fn release(&mut self, member: &NodeId) {
        let (t, mut h) = self.bc();
        if let Some(t) = t {
            t.release(&mut h, member);
        }
    }

    fn resubscribe(&mut self, hub: &NodeId) {
        let now = self.io.now;
        let (t, mut h) = self.bc();
        if let Some(t) = t {
            t.resubscribe(&mut h, now, hub);
        }
    }

    fn primary_changed(&mut self, old: Option<&NodeId>, new: &NodeId) {
        let now = self.io.now;
        let (t, mut h) = self.bc();
        if let Some(t) = t {
            t.primary_changed(&mut h, now, old, new);
        }
    }
}

impl<E: Ep, St: Store> Local for MemHost<'_, E, St> {
    fn version(&self) -> u16 {
        self.io.version
    }

    fn reflexive_known(&self) -> bool {
        self.io.reflexive
    }

    fn address_hash(&self, moves: u8) -> [u8; 8] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(self.io.ticket.get(..self.io.ticket_len).unwrap_or_default());
        hasher.update(&[moves]);
        let digest = hasher.finalize();
        let mut out = [0u8; 8];
        out.copy_from_slice(digest.as_bytes().get(..8).unwrap_or_default());
        out
    }

    fn persistent(&self) -> bool {
        self.io.store.persistent()
    }

    fn unseal_counter(&mut self) -> Result<Option<u64>, StoreError> {
        self.io.store.load()
    }

    fn seal_counter(&mut self, epoch: u64) -> Result<(), StoreError> {
        self.io.store.save(epoch)
    }
}

/// Broadcast's host: the session state, and the membership view when the call has one.
///
/// Inside a membership call the view is borrowed by membership itself, so `mem` is `None` and [`BcHost::in_view`]
/// answers false; the topic machine asks it only when it publishes or retries, which the node does with the view
/// at hand.
pub(crate) struct Bc<'a, E: Ep, St: Store> {
    pub(crate) io: &'a mut Io<E, St>,
    pub(crate) mem: Option<&'a Membership>,
}

impl<E: Ep, St: Store> BcHost for Bc<'_, E, St> {
    fn send(&mut self, peer: &NodeId, lane: Lane, frame: &[u8]) -> bool {
        self.io.send_stream(peer, lane, frame)
    }

    fn backlogged(&self, peer: &NodeId, len: usize) -> bool {
        self.io.backlog_full(peer, len)
    }

    fn send_member(&mut self, peer: &NodeId, frame: &[u8]) -> bool {
        self.io.send_stream(peer, Lane::Main, frame)
    }

    fn hub_up(&self, hub: &NodeId) -> bool {
        *hub == self.io.me || self.io.hub_alive.contains(hub)
    }

    fn in_view(&self, member: &NodeId) -> bool {
        self.mem.is_some_and(|m| m.in_view(member))
    }

    fn wall_ms(&self) -> u64 {
        self.io.wall_ms()
    }

    fn event(&mut self, event: BcEvent<'_>) {
        let e = match event {
            BcEvent::Message {
                topic,
                origin,
                hop,
                mid,
                body,
            } => NodeEvent::Message {
                topic: topic.to_vec(),
                origin: *origin,
                hop: *hop,
                mid,
                body: body.to_vec(),
            },
            BcEvent::PublishAcked { mid } => NodeEvent::PublishAcked { mid },
            BcEvent::PublishGaveUp { mid } => NodeEvent::PublishGaveUp { mid },
            BcEvent::PublishRoom => NodeEvent::PublishRoom,
            BcEvent::GapRepaired { topic, mid } => NodeEvent::GapRepaired {
                topic: topic.to_vec(),
                mid,
            },
            BcEvent::Fallback { topic, mid, to } => NodeEvent::Fallback {
                topic: topic.to_vec(),
                mid,
                to: *to,
            },
            BcEvent::Restored { hub, topic } => NodeEvent::Restored {
                hub: *hub,
                topic: topic.to_vec(),
            },
            BcEvent::AcpCheck { id, origin, topic } => NodeEvent::BroadcastAcpCheck {
                id,
                origin: *origin,
                topic: topic.to_vec(),
            },
        };
        self.io.emit(e);
    }
}
