//! The tables a connection builds on, handed over with its [`Resources`](super::Resources) and handed back with them.
//!
//! They are large, written only as far as they are used, and reusable: a node builds them once per session slot, a new
//! session clears and fills the same ones, and an established session holds no more of them than it touched. The
//! table of sent packets and the room of the event queue are reserved by the host with `alloc`, or are plain arrays
//! without it; the pool of handshake machines is shared by the node's sessions.
//!
//! Invariants: a cleared table reads as a new one; the pool of machines is the only part the sessions share.

use super::event::EventTable;
use super::handshake::Machines;
use crate::recovery::SentRing;

/// The tables of one session slot; `F` is the most packets in flight.
#[derive(Debug, Clone, Default)]
pub struct Tables<const F: usize> {
    /// The sent packets.
    pub(crate) sent: SentRing<F>,
    /// The room of the event queue.
    pub(crate) events: EventTable,
    /// The handshake machines the node's sessions share.
    pub(crate) machines: Machines,
}

impl<const F: usize> Tables<F> {
    /// Empty tables with a pool of handshake machines of their own.
    pub fn new() -> Self {
        Self::default()
    }

    /// Empty tables that take handshake machines from `machines`, the pool the node's other sessions use too.
    pub fn sharing(machines: &Machines) -> Self {
        Self {
            sent: SentRing::new(),
            events: EventTable::new(),
            machines: machines.clone(),
        }
    }

    /// Forget what the last session left, keeping the room.
    pub fn clear(&mut self) {
        self.sent.clear();
        self.events.clear();
    }
}
