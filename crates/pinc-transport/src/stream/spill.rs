//! The spill arena: a fixed set of slots of byte ranges that the range sets of every session of one endpoint move
//! into when they outgrow their inline arrays.
//!
//! Invariants: the arena never holds more slots than it was made with, and its memory is all taken when it is made
//! (a caller slab, or one zeroed buffer the system commits as slots are first written); taking and returning a slot
//! is O(1) and never allocates: fresh slots come from a bump cursor, returned ones form a last-in first-out list kept
//! in their first word. A session holds at most half of the slots, so one session cannot shut out the rest. A
//! [`SpillRef`] is neither `Copy` nor `Clone`, so a slot cannot be returned twice through safe code. With no slot left
//! a range set does what it did with no arena: the received ranges refuse the frame and the lost and acknowledged
//! ranges fall back, each counted as a refusal.
//!
//! The endpoint owns the arena and lends it, by `&mut` in a [`Lent`](crate::conn::Lent), to each connection call that
//! can spill, read a spilled set or return a slot. For that call the arena moves into the session's pool
//! ([`BufferPool::lend_spill`](super::pool::BufferPool::lend_spill)) and moves back when it returns
//! ([`BufferPool::return_spill`](super::pool::BufferPool::return_spill)); between calls a session holds only the
//! indices of its slots. No cell, no reference count: the borrow checker keeps every session's call apart.

use core::num::NonZeroU32;

/// The intervals one slot holds: 8 KiB, over twice the largest set the lab measured spilled (236 ranges, three-site
/// `throughput_16s`).
pub const SLOT_RANGES: usize = 512;
/// The `u64` words of one slot: a start and an end per interval.
const WORDS: usize = SLOT_RANGES * 2;
/// One slot of a caller slab.
pub type SpillSlot = [[u64; 2]; SLOT_RANGES];
/// The slots an endpoint's arena has unless it is told otherwise: 1 MiB, committed only as range sets spill.
pub const DEFAULT_SLOTS: usize = 128;

/// Where the slots live: lent by the caller, or one buffer the arena owns.
enum Store<'a> {
    Borrowed(&'a mut [SpillSlot]),
    #[cfg(feature = "alloc")]
    Owned(alloc::boxed::Box<[u64]>),
}

impl Store<'_> {
    fn words(&self) -> &[u64] {
        match self {
            Store::Borrowed(s) => s.as_flattened().as_flattened(),
            #[cfg(feature = "alloc")]
            Store::Owned(b) => b,
        }
    }

    fn words_mut(&mut self) -> &mut [u64] {
        match self {
            Store::Borrowed(s) => s.as_flattened_mut().as_flattened_mut(),
            #[cfg(feature = "alloc")]
            Store::Owned(b) => b,
        }
    }
}

/// A handle to one slot of a [`SpillArena`], held by the range set that spilled into it.
#[derive(Debug, PartialEq, Eq)]
pub struct SpillRef(NonZeroU32);

impl SpillRef {
    fn words(&self) -> core::ops::Range<usize> {
        let at = (self.0.get() as usize - 1) * WORDS;
        at..at + WORDS
    }
}

/// The slots an endpoint's range sets spill into, made once when the endpoint is set up.
pub struct SpillArena<'a> {
    store: Store<'a>,
    slots: u32,
    /// The next never-used slot.
    fresh: u32,
    /// The head of the free list, as an index plus one (zero is the empty list).
    free_head: u32,
    held: u32,
}

impl core::fmt::Debug for SpillArena<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SpillArena")
            .field("slots", &self.slots)
            .field("held", &self.held)
            .finish()
    }
}

impl Default for SpillArena<'_> {
    /// An arena of no slots: every spill is refused, as if there were no arena.
    fn default() -> Self {
        Self::from_slab(&mut [])
    }
}

impl<'a> SpillArena<'a> {
    /// An arena over slots the caller lends: no heap.
    pub fn from_slab(slab: &'a mut [SpillSlot]) -> Self {
        Self::with_store(Store::Borrowed(slab))
    }

    /// An arena of `slots` slots in one zeroed buffer, allocated now and never again. The system commits a slot's
    /// pages when a range set first spills into it, so an endpoint whose streams never spill holds none of it.
    #[cfg(feature = "alloc")]
    pub fn new_boxed(slots: usize) -> Self {
        // A flat zeroed buffer of words is a calloc the system commits lazily; a vec of slot arrays would be written.
        Self::with_store(Store::Owned(
            alloc::vec![0u64; slots.saturating_mul(WORDS)].into_boxed_slice(),
        ))
    }

    fn with_store(store: Store<'a>) -> Self {
        Self {
            slots: u32::try_from(store.words().len() / WORDS).unwrap_or(u32::MAX - 1),
            store,
            fresh: 0,
            free_head: 0,
            held: 0,
        }
    }

    /// The slots the arena was made with.
    pub const fn slots(&self) -> usize {
        self.slots as usize
    }

    /// The slots range sets hold now.
    pub const fn held(&self) -> usize {
        self.held as usize
    }

    fn take(&mut self) -> Option<SpillRef> {
        let r = if let Some(h) = NonZeroU32::new(self.free_head) {
            let r = SpillRef(h);
            let next = self.store.words().get(r.words().start).copied()?;
            self.free_head = u32::try_from(next).unwrap_or(0);
            r
        } else if self.fresh < self.slots {
            self.fresh += 1;
            SpillRef(NonZeroU32::new(self.fresh)?)
        } else {
            return None;
        };
        self.held += 1;
        Some(r)
    }

    #[allow(
        clippy::needless_pass_by_value,
        reason = "consuming the handle is what rules out a double return"
    )]
    fn give(&mut self, r: SpillRef) {
        let head = u64::from(self.free_head);
        if let Some(w) = self.store.words_mut().get_mut(r.words().start) {
            *w = head;
            self.free_head = r.0.get();
            self.held = self.held.saturating_sub(1);
        }
    }

    pub(super) fn read(&self, r: &SpillRef) -> Option<&[u64]> {
        self.store.words().get(r.words())
    }

    fn write(&mut self, r: &SpillRef) -> Option<&mut [u64]> {
        self.store.words_mut().get_mut(r.words())
    }
}

/// One session's use of its endpoint's arena: the arena while a call has it lent, the slots the session holds, and
/// what it lost: the spills refused and the slots given back with no arena lent.
#[derive(Debug, Default)]
pub(super) struct SpillUse<'p> {
    arena: Option<SpillArena<'p>>,
    held: u32,
    refused: u64,
    lost: u64,
}

impl SpillUse<'_> {
    /// Take a slot, or count the refusal: no arena is lent, the arena is empty, or the session holds its share (half
    /// of the slots, rounded up).
    fn take(&mut self) -> Option<SpillRef> {
        let r = self
            .arena
            .as_mut()
            .filter(|a| self.held < a.slots.div_ceil(2))
            .and_then(SpillArena::take);
        if r.is_some() {
            self.held += 1;
        } else {
            self.refused += 1;
        }
        r
    }

    fn give(&mut self, r: SpillRef) {
        // Every call that can free a range set is lent the arena. A give without one would lose the slot until the
        // endpoint is rebuilt, so it is counted (`spill_lost`) in every build.
        match self.arena.as_mut() {
            Some(a) => {
                self.held = self.held.saturating_sub(1);
                a.give(r);
            }
            None => self.lost += 1,
        }
    }
}

impl<'p> super::pool::BufferPool<'p> {
    /// Hand the session's range sets the endpoint's arena for one call; [`return_spill`](Self::return_spill) gives it
    /// back. A pool with no arena lent refuses every spill, as before the arena existed.
    pub fn lend_spill(&mut self, arena: SpillArena<'p>) {
        self.spill.arena = Some(arena);
    }

    /// The arena [`lend_spill`](Self::lend_spill) handed in, or an empty one if none was.
    pub fn return_spill(&mut self) -> SpillArena<'p> {
        self.spill.arena.take().unwrap_or_default()
    }

    /// Spill slots the session holds now.
    pub const fn spill_held(&self) -> usize {
        self.spill.held as usize
    }

    /// Spills refused for want of a slot since the pool was made or last [`reset`](Self::reset).
    pub const fn spill_refused(&self) -> u64 {
        self.spill.refused
    }

    /// Spill slots given back with no arena lent, so lost to the arena; always 0 unless a call path misses its lend.
    pub const fn spill_lost(&self) -> u64 {
        self.spill.lost
    }

    pub(super) fn reset_spill_counts(&mut self) {
        self.spill.refused = 0;
    }

    pub(super) fn spill_take(&mut self) -> Option<SpillRef> {
        self.spill.take()
    }

    pub(super) fn spill_give(&mut self, r: SpillRef) {
        self.spill.give(r);
    }

    pub(super) fn spill_read(&self, r: &SpillRef) -> Option<&[u64]> {
        self.spill.arena.as_ref()?.read(r)
    }

    pub(super) fn spill_write(&mut self, r: &SpillRef) -> Option<&mut [u64]> {
        self.spill.arena.as_mut()?.write(r)
    }
}
