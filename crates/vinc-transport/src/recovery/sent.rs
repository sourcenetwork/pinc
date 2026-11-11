//! The bounded ring of sent packets.
//!
//! Slots are kept in send order, so packet numbers increase from head to tail and a lookup is a binary search. A slot
//! is in flight, declared lost (kept as a ghost so a late acknowledgement can still be recognised) or done. Done slots
//! at the head are dropped at once; ghosts at the head are dropped once older than [`GHOST_RETENTION`] or when the ring needs
//! the room. At most [`MAX_GHOSTS`] ghosts are kept. A ring full of packets still in flight refuses new ones.
//!
//! The slots are a [`Lazy`] table: with `alloc` the room for all of them is reserved and a slot is written the first
//! time the ring reaches it, so a connection that never has many packets in flight never touches most of the memory.
//! An empty ring starts again at the first slot to keep the written part small.
//!
//! Only packets that need an acknowledgement and count toward bytes in flight are recorded here: acknowledgement-only
//! packets and probes are not.

use super::SECOND;
use super::frame_ref::{FrameRef, FrameRefs};
use crate::stream::lazy::{Blank, Lazy};

/// The packets in flight a connection of the facade can track: 8,192 packets of 1,452 bytes are 11.9 MB, the window of
/// a 1 Gbit/s path of 95 ms (a 150 ms path holds 200 Mbit/s). The window the congestion controller grants bounds the
/// packets in flight first; this table is the ceiling behind it. With `alloc` the room is reserved and a record is
/// written only as far as the ring reaches, so a connection that never has many packets in flight touches few.
pub const SENT_PACKETS: usize = 8192;

/// How long a packet declared lost stays recognisable to a late acknowledgement (2 s).
pub(crate) const GHOST_RETENTION: u64 = 2 * SECOND;
/// The most ghosts kept; the oldest go first.
pub(crate) const MAX_GHOSTS: usize = 200;

/// Whether a frame is kept by a ghost: stream data with at least one byte and no stream end. A packet with no such
/// frame leaves no ghost, so a late acknowledgement of it acts on nothing.
pub(crate) const fn is_ghost_data(f: &FrameRef) -> bool {
    matches!(f, FrameRef::Stream { len, fin: false, .. } if *len > 0)
}

/// A packet handed to [`super::Recovery::on_packet_sent`]. Every recorded packet is ack-eliciting and counts toward
/// bytes in flight.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sent {
    /// The packet number; strictly above every earlier one.
    pub pn: u64,
    /// The send time.
    pub time: u64,
    /// The datagram size in bytes.
    pub size: u32,
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
}

impl Blank for Slot {
    const BLANK: Self = EMPTY;
}

const EMPTY: Slot = Slot {
    sent: Sent {
        pn: 0,
        time: 0,
        size: 0,
        path: 0,
        is_repair: false,
        is_mtu_probe: false,
        frames: FrameRefs::new(),
    },
    state: State::Done,
};

/// A ring of at most `N` sent packets: the table of a connection's packets in flight. A connection is handed one in its
/// [`Resources`](crate::conn::Resources) and gives it back with them, so a new session builds no table.
#[derive(Debug, Clone)]
pub struct SentRing<const N: usize> {
    slots: Lazy<Slot, N>,
    head: usize,
    len: usize,
    /// No slot before this index is in flight. A slot only leaves the in-flight state, so the prefix only grows (until
    /// the head is dropped), and a scan for the oldest packet in flight starts here instead of at the head, however
    /// many acknowledged packets wait behind a ghost.
    lead: usize,
}

impl<const N: usize> Default for SentRing<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> SentRing<N> {
    /// An empty table.
    pub fn new() -> Self {
        const { assert!(N >= 1 && N <= (1 << 31)) };
        Self {
            slots: Lazy::new(),
            head: 0,
            len: 0,
            lead: 0,
        }
    }

    /// Forget every packet, keeping the room: the table is ready for the next connection.
    pub fn clear(&mut self) {
        self.slots.clear();
        self.head = 0;
        self.len = 0;
        self.lead = 0;
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

    /// The index before which no packet is in flight.
    pub(crate) fn lead(&mut self) -> usize {
        while self.get(self.lead).is_some_and(|s| s.state != State::InFlight) {
            self.lead += 1;
        }
        self.lead
    }

    /// The index of the oldest packet still in flight.
    pub(crate) fn first_in_flight(&mut self) -> Option<usize> {
        let i = self.lead();
        (i < self.len).then_some(i)
    }

    /// The send time of the newest packet still in flight.
    ///
    /// vertexia: scans back from the tail over acknowledged slots, O(ring) when the head is the only packet in
    /// flight; a cached index would make it O(1) if profiles show it.
    pub(crate) fn newest_in_flight_time(&self) -> Option<u64> {
        (0..self.len)
            .rev()
            .find_map(|i| self.get(i).filter(|s| s.state == State::InFlight).map(|s| s.sent.time))
    }

    /// The packet with number `pn`, if it is still in flight.
    pub(crate) fn in_flight(&self, pn: u64) -> Option<&Sent> {
        let i = self.lower_bound(pn);
        self.get(i)
            .filter(|s| s.sent.pn == pn && s.state == State::InFlight)
            .map(|s| &s.sent)
    }

    fn pop_front(&mut self) {
        if self.len > 0 {
            self.head = if self.len == 1 { 0 } else { (self.head + 1) % N };
            self.len -= 1;
            self.lead = self.lead.saturating_sub(1);
        }
    }

    /// Drop done slots and expired ghosts from the head.
    pub(crate) fn trim(&mut self, now: u64) {
        while let Some(slot) = self.get(0) {
            let drop = match slot.state {
                State::Done => true,
                State::Lost(at) => at.saturating_add(GHOST_RETENTION) < now,
                State::InFlight => false,
            };
            if !drop {
                break;
            }
            self.pop_front();
        }
    }

    /// Whether any packet declared lost is still recognisable to a late acknowledgement.
    pub(crate) fn has_ghost(&self) -> bool {
        (0..self.len).any(|i| self.get(i).is_some_and(|s| matches!(s.state, State::Lost(_))))
    }

    /// Forget the oldest ghosts beyond [`MAX_GHOSTS`].
    pub(crate) fn limit_ghosts(&mut self) {
        let ghosts = (0..self.len)
            .filter(|&i| self.get(i).is_some_and(|s| matches!(s.state, State::Lost(_))))
            .count();
        let mut excess = ghosts.saturating_sub(MAX_GHOSTS);
        for i in 0..self.len {
            if excess == 0 {
                break;
            }
            if let Some(s) = self.get_mut(i).filter(|s| matches!(s.state, State::Lost(_))) {
                s.state = State::Done;
                excess -= 1;
            }
        }
    }

    /// Whether [`Self::push`] would succeed: a free slot, or a head slot that is not in flight.
    pub(crate) fn has_room(&self) -> bool {
        self.len < N || self.get(0).is_some_and(|s| s.state != State::InFlight)
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
            };
        }
        self.len += 1;
        true
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    fn sent(pn: u64) -> Sent {
        Sent {
            pn,
            time: pn,
            size: 1200,
            path: 0,
            is_repair: false,
            is_mtu_probe: false,
            frames: FrameRefs::new(),
        }
    }

    /// The oldest packet in flight the slow way.
    fn naive<const N: usize>(r: &SentRing<N>) -> Option<usize> {
        (0..r.len).find(|&i| r.get(i).is_some_and(|s| s.state == State::InFlight))
    }

    #[test]
    fn the_oldest_packet_in_flight_is_found_from_the_cached_prefix_as_from_the_head() {
        let mut r = SentRing::<8>::new();
        let (mut pn, mut x) = (0u64, 0x2545_f491_4f6c_dd1du64);
        for step in 0..4000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            match x % 4 {
                0 | 1 => {
                    if r.push(sent(pn)) {
                        pn += 1;
                    }
                }
                2 => {
                    // Settle a slot out of order, as a late or out-of-order acknowledgement does.
                    let i = (x >> 8) as usize % (r.len + 1);
                    if let Some(s) = r.get_mut(i).filter(|s| s.state == State::InFlight) {
                        s.state = if x & 0x100 == 0 { State::Done } else { State::Lost(step) };
                    }
                }
                _ => r.trim(step + 10 * GHOST_RETENTION * u64::from(x & 1 == 0)),
            }
            assert_eq!(r.first_in_flight(), naive(&r), "step {step}");
            assert!(r.lead <= r.len);
        }
    }
}
