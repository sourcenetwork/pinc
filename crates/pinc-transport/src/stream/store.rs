//! The chunk store: every 16 KiB chunk an endpoint's sessions may ever hold, made once, when the endpoint is built, as
//! one zeroed allocation the system commits only as its pages are first written (pinc#651, #640).
//!
//! The endpoint owns the store and lends it (`&mut`) to each call that takes, gives or reads a chunk; the slots' pools
//! hold only the numbers of the chunks they took. Every table the store keeps (free chunks, marks, the slots' ledger,
//! the waiters) is made to its full size with the store, so nothing is allocated, freed or mapped after setup.
//!
//! Every slot has a floor of chunks set aside from the start, whether a session holds it or not, so a session is never
//! refused for want of a floor. Above the floor a slot reserves from the burst room, what is left once every slot's
//! floor is set aside. A pool may hold a chunk only within its slot's reservation: it grows the reservation before it
//! promises room to its peer (a window) and shrinks it when the promise is gone, so every promise is backed by a chunk
//! the store still has. A growth the burst room cannot cover is refused and counted; the slot may then wait for room,
//! in a first-in first-out queue: room given back goes to the oldest waiter first, reserved for it at once, and the
//! endpoint tells the waiter's session to try its grant again ([`ChunkStore::pop_ready`]).
//!
//! Each chunk carries the mark of the session that last held it. The store hands out a chunk another session marked
//! only after zeroing it, so a session never reads what another wrote.
//!
//! Invariants: the chunks in pools and in the store are the store's chunks, each in exactly one place; the floors and
//! the reservations above them sum to at most the store's size; a slot is in the waiting queue at most once.

use super::pool::CHUNK_SIZE;
#[cfg(feature = "alloc")]
use super::pool::RawChunk;

/// The chunks a slot keeps reserved whatever its session does: what one stream takes before it carries data, its
/// receive half and its send half, each the [`FIRST_CHARGE`](super::FIRST_CHARGE) the ledger counts for it, or half the
/// pool when that is less (a stream's window is never above half the pool). 8 chunks, 128 KiB, for any pool of 8
/// chunks or more.
pub const fn floor_chunks(chunks: usize) -> usize {
    let half = (super::FIRST_CHARGE as usize).div_ceil(CHUNK_SIZE);
    let cap = chunks / 2;
    2 * if half < cap { half } else { cap }
}

/// What a store holds and what it refused, for an endpoint's statistics.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StoreStats {
    /// The chunks the store was made with.
    pub chunks: u64,
    /// Chunks ever handed out: the store's high-water mark, the memory the system has committed for it.
    pub touched: u64,
    /// Chunks in pools now.
    pub used: u64,
    /// Chunks reserved now: every slot's floor and the reservations above them.
    pub reserved: u64,
    /// Times a slot asked for more reservation than the burst room had left.
    pub full: u64,
    /// Peer stream frames held back because a pool found no chunk for them inside the opening window of a stream the
    /// peer opened on soft credit (credit the store measured but did not reserve); the peer sends them again once room
    /// comes back.
    pub shortage_first: u64,
    /// Frames held back for want of a chunk inside a window the store had reserved. A granted window is backed, so this
    /// stays 0; anything else is a defect.
    pub shortage_backed: u64,
}

/// No slot: the end of a list.
#[cfg(feature = "alloc")]
const NONE: u32 = u32::MAX;

/// Without `alloc` there is no store: every pool has memory of its own, and an endpoint lends this empty stand-in.
#[cfg(not(feature = "alloc"))]
#[derive(Debug, Default)]
pub struct ChunkStore;

/// The chunks of one endpoint, owned by it and lent to its sessions' calls.
#[cfg(feature = "alloc")]
pub struct ChunkStore {
    memory: alloc::boxed::Box<[u8]>,
    /// The mark of the session that last held each chunk; 0 for one never handed out.
    marks: alloc::boxed::Box<[u64]>,
    /// Chunks handed back, most recent last.
    free: alloc::vec::Vec<u32>,
    /// The next chunk never handed out.
    fresh: u32,
    floor: u32,
    /// Each slot's reservation above its floor.
    above: alloc::boxed::Box<[u32]>,
    /// The burst room no slot has reserved.
    burst_left: u64,
    /// The largest reservation above the floor the burst room can ever give one slot.
    burst_total: u64,
    /// The waiting queue, oldest first: each slot's neighbours, its wanted reservation, and the ends.
    prev: alloc::boxed::Box<[u32]>,
    next: alloc::boxed::Box<[u32]>,
    want: alloc::boxed::Box<[u32]>,
    head: u32,
    tail: u32,
    /// Slots given their wanted room and not yet told: a ring the size of the slot table.
    ready: alloc::boxed::Box<[u32]>,
    ready_at: u32,
    ready_len: u32,
    next_mark: u64,
    stats: StoreStats,
}

#[cfg(feature = "alloc")]
impl core::fmt::Debug for ChunkStore {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ChunkStore")
            .field("stats", &self.stats)
            .finish_non_exhaustive()
    }
}

/// An empty store, which allocates nothing: what a pool holds between calls, and what an endpoint whose slots are lent
/// to it lends.
#[cfg(feature = "alloc")]
impl Default for ChunkStore {
    fn default() -> Self {
        Self::new(0, 0, 0)
    }
}

#[cfg(feature = "alloc")]
impl ChunkStore {
    /// A store of `chunks` chunks for `slots` slots whose pools hold up to `pool_chunks` each: one zeroed allocation
    /// of `chunks * CHUNK_SIZE` bytes, which the system commits only as it is used, and every table at its full size.
    /// The floors of all the slots are set aside now; `chunks` below them leaves the slots past what fits with none.
    pub fn new(chunks: usize, slots: usize, pool_chunks: usize) -> Self {
        let chunks = chunks.min(NONE as usize - 1);
        let slots = slots.min(NONE as usize - 1);
        let floor = u32::try_from(floor_chunks(pool_chunks)).unwrap_or(NONE);
        let floors = u64::from(floor) * slots as u64;
        let burst_total = (chunks as u64).saturating_sub(floors);
        Self {
            memory: alloc::vec![0u8; chunks * CHUNK_SIZE].into_boxed_slice(),
            marks: alloc::vec![0; chunks].into_boxed_slice(),
            free: alloc::vec::Vec::with_capacity(chunks),
            fresh: 0,
            floor,
            above: alloc::vec![0; slots].into_boxed_slice(),
            burst_left: burst_total,
            burst_total,
            prev: alloc::vec![NONE; slots].into_boxed_slice(),
            next: alloc::vec![NONE; slots].into_boxed_slice(),
            want: alloc::vec![0; slots].into_boxed_slice(),
            head: NONE,
            tail: NONE,
            ready: alloc::vec![NONE; slots].into_boxed_slice(),
            ready_at: 0,
            ready_len: 0,
            next_mark: 1,
            stats: StoreStats {
                chunks: chunks as u64,
                reserved: floors.min(chunks as u64),
                ..StoreStats::default()
            },
        }
    }

    /// What the store holds now.
    pub const fn stats(&self) -> StoreStats {
        self.stats
    }

    /// Count a frame a pool over the store held back for want of a chunk: the first bytes of a peer stream on soft
    /// credit when `first`, inside a reserved window otherwise.
    pub const fn note_shortage(&mut self, first: bool) {
        if first {
            self.stats.shortage_first += 1;
        } else {
            self.stats.shortage_backed += 1;
        }
    }

    /// The floor every slot keeps.
    pub const fn floor(&self) -> u32 {
        self.floor
    }

    /// Slot `slot`'s reservation: its floor and what it reserved above it.
    pub fn reserved(&self, slot: usize) -> u32 {
        self.above.get(slot).map_or(0, |a| self.floor.saturating_add(*a))
    }

    /// The burst room no slot has reserved, in chunks.
    pub const fn burst_left(&self) -> u64 {
        self.burst_left
    }

    /// The burst room slot `slot` may still reserve: all of it while no slot waits or when it is the oldest waiter,
    /// none otherwise.
    pub fn burst_for(&self, slot: usize) -> u64 {
        if self.head == NONE || self.head as usize == slot {
            self.burst_left
        } else {
            0
        }
    }

    /// Grow slot `slot`'s reservation toward `want` chunks, as far as the burst room allows; its reservation after.
    /// While slots wait, only the oldest may grow, so no slot passes the queue. A growth that is not covered in full
    /// counts as full.
    pub fn grow(&mut self, slot: usize, want: u32) -> u32 {
        let have = self.reserved(slot);
        if want > have {
            let more = u64::from(want - have);
            let open = self.head == NONE || self.head as usize == slot;
            let got = if open { more.min(self.burst_left) } else { 0 };
            if got < more {
                self.stats.full += 1;
            }
            self.add_above(slot, got);
        }
        self.reserved(slot)
    }

    /// Lower slot `slot`'s reservation to `keep` chunks, never below its floor, and give the room to the waiters.
    pub fn shrink(&mut self, slot: usize, keep: u32) {
        let keep = keep.max(self.floor);
        let have = self.reserved(slot);
        if keep < have
            && let Some(a) = self.above.get_mut(slot)
        {
            *a -= have - keep;
            self.burst_left += u64::from(have - keep);
            self.stats.reserved -= u64::from(have - keep);
            self.serve();
        }
    }

    /// Give back everything slot `slot` reserved above its floor and take it out of the queue: its session ended.
    pub fn release(&mut self, slot: usize) {
        self.leave(slot);
        self.shrink(slot, 0);
    }

    /// Queue slot `slot` until its reservation can reach `want` chunks (capped at what the burst room can ever give it).
    /// A slot already queued keeps its place and takes the new want. A slot whose reservation already covers the want
    /// waits only for its own chunks to come back, which its own packets see, so it leaves the queue: the store would
    /// otherwise hand it nothing and wake it, over and over.
    pub fn wait(&mut self, slot: usize, want: u32) {
        let s = slot as u32;
        let cap = u32::try_from(u64::from(self.floor) + self.burst_total).unwrap_or(NONE);
        let want = want.min(cap);
        if want <= self.reserved(slot) {
            self.leave(slot);
            return;
        }
        let Some(w) = self.want.get_mut(slot) else { return };
        *w = want;
        if !self.queued(slot) {
            if let Some(p) = self.prev.get_mut(slot) {
                *p = self.tail;
            }
            match self.next.get_mut(self.tail as usize) {
                Some(n) => *n = s,
                None => self.head = s,
            }
            self.tail = s;
        }
        self.serve();
    }

    /// Take slot `slot` out of the queue, if it is in it.
    pub fn leave(&mut self, slot: usize) {
        if !self.queued(slot) {
            return;
        }
        let p = self.prev.get_mut(slot).map_or(NONE, |x| core::mem::replace(x, NONE));
        let n = self.next.get_mut(slot).map_or(NONE, |x| core::mem::replace(x, NONE));
        match self.next.get_mut(p as usize) {
            Some(x) => *x = n,
            None => self.head = n,
        }
        match self.prev.get_mut(n as usize) {
            Some(x) => *x = p,
            None => self.tail = p,
        }
    }

    /// Whether slot `slot` waits for room.
    pub fn queued(&self, slot: usize) -> bool {
        self.head as usize == slot || self.prev.get(slot).is_some_and(|p| *p != NONE)
    }

    /// The next slot whose wanted room was reserved for it while it waited; the endpoint has its session grant again.
    pub fn pop_ready(&mut self) -> Option<usize> {
        if self.ready_len == 0 {
            return None;
        }
        let s = *self.ready.get(self.ready_at as usize)?;
        self.ready_at = (self.ready_at + 1) % self.ready.len() as u32;
        self.ready_len -= 1;
        Some(s as usize)
    }

    /// Give the burst room to the waiters, oldest first, while it covers the oldest one's want.
    fn serve(&mut self) {
        while let Some(&w) = self.want.get(self.head as usize) {
            let slot = self.head as usize;
            let need = u64::from(w.saturating_sub(self.reserved(slot)));
            if need > self.burst_left {
                return;
            }
            self.add_above(slot, need);
            self.leave(slot);
            let n = self.ready.len() as u32;
            if let Some(r) = self.ready.get_mut(((self.ready_at + self.ready_len) % n) as usize) {
                *r = slot as u32;
                self.ready_len += 1;
            }
        }
    }

    fn add_above(&mut self, slot: usize, n: u64) {
        if let Some(a) = self.above.get_mut(slot) {
            *a += n as u32;
            self.burst_left -= n;
            self.stats.reserved += n;
        }
    }

    /// A mark no session of this store has had.
    pub fn new_mark(&mut self) -> u64 {
        let m = self.next_mark;
        self.next_mark = self.next_mark.wrapping_add(1).max(1);
        m
    }

    /// Hand out a chunk to the session marked `mark`, zeroed when another session held it last. The caller holds a
    /// reservation for it, so the store has one.
    pub fn take(&mut self, mark: u64) -> Option<u32> {
        let id = if let Some(id) = self.free.pop() {
            id
        } else if (self.fresh as usize) < self.marks.len() {
            self.fresh += 1;
            self.stats.touched += 1;
            self.fresh - 1
        } else {
            return None;
        };
        let last = core::mem::replace(self.marks.get_mut(id as usize)?, mark);
        if last != 0 && last != mark {
            self.chunk_mut(id)?.fill(0);
        }
        self.stats.used += 1;
        Some(id)
    }

    /// Take chunk `id` back; false for a chunk this store did not hand out (an empty store, lent where none was).
    pub fn give(&mut self, id: u32) -> bool {
        let ok = (id as usize) < self.marks.len() && self.free.len() < self.free.capacity();
        if ok {
            self.stats.used = self.stats.used.saturating_sub(1);
            self.free.push(id);
        }
        ok
    }

    /// The bytes of chunk `id`.
    pub fn chunk(&self, id: u32) -> Option<&RawChunk> {
        self.memory.as_chunks().0.get(id as usize)
    }

    /// The bytes of chunk `id`, writable.
    pub fn chunk_mut(&mut self, id: u32) -> Option<&mut RawChunk> {
        self.memory.as_chunks_mut().0.get_mut(id as usize)
    }
}

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    #[test]
    fn every_slot_has_its_floor_from_the_start_and_bursts_draw_only_from_the_rest() {
        // 4 slots of floor 8 = 32 chunks set aside; 40 chunks leave 8 of burst room.
        let mut s = ChunkStore::new(40, 4, 1024);
        assert_eq!(s.floor(), 8);
        assert_eq!(s.burst_left(), 8);
        assert_eq!(s.grow(0, 100), 16, "slot 0 takes every burst chunk");
        assert_eq!(s.grow(1, 100), 8, "slot 1 keeps its floor and gets nothing above it");
        assert_eq!(s.stats().full, 2);
        for slot in 0..4 {
            assert!(s.reserved(slot) >= 8, "slot {slot} keeps its floor");
        }
        assert!(s.stats().reserved <= s.stats().chunks);
        s.release(0);
        assert_eq!(s.burst_left(), 8);
        assert_eq!(s.stats().reserved, 32);
    }

    #[test]
    fn room_given_back_goes_to_the_oldest_waiter_first_and_is_reserved_for_it() {
        let mut s = ChunkStore::new(24 + 6, 3, 1024);
        assert_eq!(s.grow(0, 14), 14);
        s.wait(1, 12);
        s.wait(2, 10);
        assert!(s.queued(1) && s.queued(2));
        assert_eq!(s.pop_ready(), None);
        s.shrink(0, 11);
        assert_eq!(
            s.pop_ready(),
            None,
            "3 back: the oldest wants 4 and the younger one may not pass it"
        );
        s.shrink(0, 8);
        assert_eq!(s.pop_ready(), Some(1));
        assert_eq!(s.reserved(1), 12, "the room is the waiter's before it asks again");
        assert_eq!(s.pop_ready(), Some(2));
        assert_eq!(s.reserved(2), 10);
        assert!(!s.queued(1) && !s.queued(2));
        assert_eq!(s.burst_left(), 0);
    }

    #[test]
    fn a_waiter_that_leaves_or_ends_frees_its_place() {
        let mut s = ChunkStore::new(24 + 4, 3, 1024);
        s.grow(0, 12);
        s.wait(1, 12);
        s.wait(2, 9);
        s.release(1);
        assert!(!s.queued(1));
        s.shrink(0, 0);
        assert_eq!(s.pop_ready(), Some(2));
        assert_eq!(s.pop_ready(), None);
    }

    #[test]
    fn a_want_above_what_the_burst_room_can_ever_give_is_capped_so_the_queue_moves() {
        let mut s = ChunkStore::new(16 + 2, 2, 1024);
        s.grow(0, 10);
        s.wait(1, 500);
        s.shrink(0, 0);
        assert_eq!(s.pop_ready(), Some(1));
        assert_eq!(s.reserved(1), 10);
    }

    #[test]
    fn a_slot_whose_reservation_covers_its_want_does_not_queue() {
        let mut s = ChunkStore::new(16 + 2, 2, 1024);
        s.grow(0, 10);
        s.wait(0, 9);
        assert!(!s.queued(0));
        assert_eq!(s.pop_ready(), None, "nothing to hand it, so it is not woken");
        s.wait(1, 10);
        assert!(s.queued(1));
        s.grow(1, 8);
        s.wait(1, 8);
        assert!(
            !s.queued(1),
            "a want the reservation now covers takes the slot out of the queue"
        );
    }

    #[test]
    fn a_chunk_another_session_wrote_is_zeroed_and_one_the_session_wrote_is_not() {
        let mut s = ChunkStore::new(16, 2, 1024);
        let (a, b) = (s.new_mark(), s.new_mark());
        let c = s.take(a).unwrap();
        s.chunk_mut(c).unwrap().fill(7);
        s.give(c);
        let c = s.take(a).unwrap();
        assert!(
            s.chunk(c).unwrap().iter().all(|x| *x == 7),
            "its own chunk comes back as it was"
        );
        s.give(c);
        let c = s.take(b).unwrap();
        assert!(
            s.chunk(c).unwrap().iter().all(|x| *x == 0),
            "another session's chunk comes back zeroed"
        );
    }

    #[test]
    fn every_chunk_is_handed_out_once_until_it_comes_back() {
        let mut s = ChunkStore::new(16, 2, 1024);
        let m = s.new_mark();
        let ids: alloc::vec::Vec<u32> = (0..16).map(|_| s.take(m).unwrap()).collect();
        assert_eq!(s.take(m), None);
        let mut seen = ids.clone();
        seen.sort_unstable();
        seen.dedup();
        assert_eq!(seen.len(), 16);
        for id in ids {
            s.give(id);
        }
        assert_eq!(s.stats().used, 0);
        assert_eq!(s.stats().touched, 16);
    }
}
