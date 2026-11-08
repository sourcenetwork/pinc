//! The bounded ring of sent packets.
//!
//! Slots are kept in send order, so packet numbers increase from head to tail and a lookup is a binary search. A slot
//! is in flight, declared lost (kept as a ghost so a late acknowledgement can still be recognised) or done. Done slots
//! at the head are dropped at once; ghosts at the head are dropped after [`GHOST_RETENTION`] or when the ring needs
//! the room. A ring full of packets still in flight refuses new ones.

use super::SECOND;
use super::frame_ref::FrameRefs;

/// How long a packet declared lost stays recognisable to a late acknowledgement (4 s).
pub(crate) const GHOST_RETENTION: u64 = 4 * SECOND;

#[allow(clippy::struct_excessive_bools)]
/// A packet handed to [`super::Recovery::on_packet_sent`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sent {
    /// The packet number; strictly above every earlier one.
    pub pn: u64,
    /// The send time.
    pub time: u64,
    /// The datagram size in bytes.
    pub size: u32,
    /// Whether the packet needs an acknowledgement.
    pub ack_eliciting: bool,
    /// Whether the packet counts toward bytes in flight.
    pub in_flight: bool,
    /// The path the packet left on.
    pub path: u8,
    /// Whether this is a repair packet: its loss is neither retransmitted nor a congestion signal.
    pub is_repair: bool,
    /// Whether this is a path MTU probe: its loss is not a congestion signal.
    pub is_mtu_probe: bool,
    /// What the packet carried.
    pub frames: FrameRefs,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum State {
    InFlight,
    /// Declared lost at the given time; a late acknowledgement can still arrive.
    Lost(u64),
    Done,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Slot {
    pub(crate) sent: Sent,
    pub(crate) state: State,
    /// Whether the loss was counted as a congestion signal (so a late acknowledgement can undo it).
    pub(crate) counted: bool,
}

const EMPTY: Slot = Slot {
    sent: Sent {
        pn: 0,
        time: 0,
        size: 0,
        ack_eliciting: false,
        in_flight: false,
        path: 0,
        is_repair: false,
        is_mtu_probe: false,
        frames: FrameRefs::new(),
    },
    state: State::Done,
    counted: false,
};

/// A ring of at most `N` sent packets.
#[derive(Debug, Clone)]
pub(crate) struct SentRing<const N: usize> {
    slots: [Slot; N],
    head: usize,
    len: usize,
}

impl<const N: usize> SentRing<N> {
    pub(crate) const fn new() -> Self {
        const { assert!(N >= 1 && N <= (1 << 31)) };
        Self {
            slots: [EMPTY; N],
            head: 0,
            len: 0,
        }
    }

    fn phys(&self, i: usize) -> usize {
        (self.head + i) % N
    }

    pub(crate) fn get(&self, i: usize) -> Option<&Slot> {
        if i >= self.len {
            return None;
        }
        self.slots.get(self.phys(i))
    }

    pub(crate) fn get_mut(&mut self, i: usize) -> Option<&mut Slot> {
        if i >= self.len {
            return None;
        }
        let p = self.phys(i);
        self.slots.get_mut(p)
    }

    /// The index of the first slot whose packet number is at least `pn`.
    pub(crate) fn lower_bound(&self, pn: u64) -> usize {
        let (mut lo, mut hi) = (0, self.len);
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.get(mid).is_some_and(|s| s.sent.pn < pn) {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        lo
    }

    fn pop_front(&mut self) {
        if self.len > 0 {
            self.head = (self.head + 1) % N;
            self.len -= 1;
        }
    }

    /// Drop done slots and expired ghosts from the head.
    pub(crate) fn trim(&mut self, now: u64) {
        while let Some(slot) = self.get(0) {
            let drop = match slot.state {
                State::Done => true,
                State::Lost(at) => at.saturating_add(GHOST_RETENTION) <= now,
                State::InFlight => false,
            };
            if !drop {
                break;
            }
            self.pop_front();
        }
    }

    /// Append a packet. Returns false when the ring is full of packets still in flight.
    pub(crate) fn push(&mut self, sent: Sent) -> bool {
        while self.len == N {
            if self.get(0).is_some_and(|s| s.state == State::InFlight) {
                return false;
            }
            self.pop_front();
        }
        let p = self.phys(self.len);
        if let Some(slot) = self.slots.get_mut(p) {
            *slot = Slot {
                sent,
                state: State::InFlight,
                counted: false,
            };
        }
        self.len += 1;
        true
    }
}
