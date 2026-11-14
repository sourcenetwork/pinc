//! The effects of one call of the state machine, copied out so they can be applied once the call has returned.
//!
//! A frame the machine is handling borrows the carrier it arrived on, and its effects may write to that same carrier,
//! so they cannot be applied while the call runs. The sink encodes each effect into one reusable arena and a list of
//! items; both keep their capacity between calls, so steady traffic allocates nothing.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use vinc_connect::carrier::frame::MAX_FRAME_LEN;
use vinc_connect::relay::{CloseReason, Effect, SessionId, Sink, Trace, UdpTarget};
use vinc_crypto::NodeId;

use super::store::node_key;

/// The largest datagram the relay encodes.
const DATAGRAM_LEN: usize = 2048;

#[derive(Debug, Clone, Copy)]
pub(crate) enum Item {
    /// A frame for a member's carrier: the bytes are `arena[start..end]`.
    Carrier(NodeId, usize, usize),
    /// A frame for the session with a peer relay.
    Peer(NodeId, usize, usize),
    /// A control datagram.
    Udp(UdpTarget, usize, usize),
    /// A packet for the relay's own endpoint.
    Local(NodeId, usize, usize),
    Close(NodeId, SessionId, CloseReason),
    Wake(NodeId),
    Trace(Trace),
}

#[derive(Debug, Default)]
pub(crate) struct Fx {
    pub(crate) arena: Vec<u8>,
    pub(crate) items: Vec<Item>,
    /// Effects whose frame did not encode.
    pub(crate) lost: u64,
    /// The members the endpoint last reported a validated direct route for: what [`Sink::tunnel_ready`] answers.
    direct: BTreeSet<[u8; 33]>,
}

impl Fx {
    /// Record whether `node` has a validated direct route.
    pub(crate) fn set_direct(&mut self, node: &NodeId, up: bool) {
        if up {
            self.direct.insert(node_key(node));
        } else {
            self.direct.remove(&node_key(node));
        }
    }

    /// Append `len` bytes written by `fill` and return their range, or `None` if it failed.
    fn put(&mut self, max: usize, fill: impl FnOnce(&mut [u8]) -> Option<usize>) -> Option<(usize, usize)> {
        let start = self.arena.len();
        self.arena.resize(start + max, 0);
        let written = self.arena.get_mut(start..).and_then(fill);
        match written {
            Some(n) if n <= max => {
                self.arena.truncate(start + n);
                Some((start, start + n))
            }
            _ => {
                self.arena.truncate(start);
                self.lost += 1;
                None
            }
        }
    }

    fn copy(&mut self, bytes: &[u8]) -> (usize, usize) {
        let start = self.arena.len();
        self.arena.extend_from_slice(bytes);
        (start, self.arena.len())
    }
}

impl Sink for Fx {
    fn tunnel_ready(&self, node: &NodeId) -> bool {
        self.direct.contains(&node_key(node))
    }

    fn emit(&mut self, effect: Effect<'_>) {
        let item = match effect {
            Effect::Carrier { to, frame } => self
                .put(MAX_FRAME_LEN, |b| frame.encode(b).ok())
                .map(|(s, e)| Item::Carrier(to, s, e)),
            Effect::PeerRelay { to, frame } => self
                .put(MAX_FRAME_LEN, |b| frame.encode(b).ok())
                .map(|(s, e)| Item::Peer(to, s, e)),
            Effect::Udp { to, datagram } => self
                .put(DATAGRAM_LEN, |b| datagram.encode(b).ok())
                .map(|(s, e)| Item::Udp(to, s, e)),
            Effect::Local { from, packet } => {
                let (s, e) = self.copy(packet);
                Some(Item::Local(from, s, e))
            }
            Effect::Close { node, session, reason } => Some(Item::Close(node, session, reason)),
            Effect::Wake { node } => Some(Item::Wake(node)),
            Effect::Trace(t) => Some(Item::Trace(t)),
        };
        if let Some(i) = item {
            self.items.push(i);
        }
    }
}
