//! The buffer pool: a fixed set of 16 KiB chunks, the only memory the stream layer, the datagram queues and the
//! early-data buffer use.
//!
//! Invariants: the slab never holds more chunks than it was made for; every [`Chunk`] handed out is charged against
//! the byte budget until it is returned through [`BufferPool::free_chunk`]; a handle is neither `Copy` nor `Clone`, so
//! a chunk cannot be freed twice through safe code. Allocation and free are O(1) (amortized for a grown pool): fresh
//! chunks come from a bump cursor and returned chunks form a last-in first-out free list, stored in their first four
//! bytes, or beside them in a grown pool. Exhaustion is a typed result, never an overflow. After
//! [`BufferPool::trim`] a grown pool holds the memory of the segments with a chunk in use and of no other.
//!
//! A pool is one of three: over a slab the caller lends ([`BufferPool::from_slab`], no heap), over one flat buffer
//! allocated when the pool is made ([`BufferPool::new_boxed`], no allocation afterwards), or grown
//! ([`BufferPool::new_grown`]): a segment's memory is allocated when one of its chunks is handed out and kept while
//! the session is busy; a trim, when the session's streams have all ended, frees every segment with no chunk in use.
//! So a quiet session holds nothing, and its memory goes back to the system, not to the allocator's heap; a busy one
//! allocates nothing per chunk.

use core::fmt;
use core::num::NonZeroU32;

/// The size of one pool chunk in bytes.
pub const CHUNK_SIZE: usize = 16 * 1024;

/// One slab entry.
pub type RawChunk = [u8; CHUNK_SIZE];

/// The pool has no chunk left within its budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PoolExhausted;

impl fmt::Display for PoolExhausted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("buffer pool exhausted")
    }
}

impl core::error::Error for PoolExhausted {}

/// A handle to one chunk of a [`BufferPool`]. Hand it back with [`BufferPool::free_chunk`].
#[derive(Debug, PartialEq, Eq)]
pub struct Chunk(NonZeroU32);

impl Chunk {
    fn index(&self) -> usize {
        self.0.get() as usize - 1
    }
}

enum Slab<'p> {
    Borrowed(&'p mut [RawChunk]),
    #[cfg(feature = "alloc")]
    Boxed(alloc::boxed::Box<[u8]>),
    #[cfg(feature = "alloc")]
    Grown(Grown),
}

/// The chunks of one segment of a grown pool. 2048 (32 MiB) on 64-bit Linux with glibc, which maps every request of
/// 32 MiB or more on its own whatever its dynamic threshold has moved to, commits a page only when it is written and
/// unmaps the whole request when it is freed, so freeing a segment gives its pages back to the system. One chunk
/// everywhere else: in wasm linear memory, which grows committed and never shrinks, on bare metal, on 32-bit targets
/// and under other allocators, a 32 MiB segment could be committed whole or never given back, against the memory
/// budgets of phones, browsers and embedded hosts; there a segment of one chunk is the pool of 16 KiB chunks.
#[cfg(feature = "alloc")]
pub const SEGMENT_CHUNKS: usize = if cfg!(all(target_os = "linux", target_env = "gnu", target_pointer_width = "64")) {
    2048
} else {
    1
};

// Wasm, bare metal and 32-bit targets keep the pool of 16 KiB chunks; a build of this crate with `alloc` for one of
// them checks it.
#[cfg(all(feature = "alloc", any(target_family = "wasm", target_os = "none", not(target_pointer_width = "64"))))]
const _: () = assert!(SEGMENT_CHUNKS == 1);

/// The most freed segments a [`Segments`] cache keeps.
#[cfg(feature = "alloc")]
pub const SPARE_SEGMENTS: usize = 4;

/// The most chunks of a freed segment its pool may have handed out since the segment was made for the cache to keep
/// it: what it keeps resident is at most [`SPARE_SEGMENTS`] times this many chunks (1 MiB). A segment written further,
/// the peak of a burst, goes back to the system.
#[cfg(feature = "alloc")]
pub const SPARE_WRITTEN: usize = 16;

/// The freed segments the grown pools of one thread share, so that a session that goes quiet after every request (its
/// last stream ends each time) takes the segment it just freed again, without asking the system to map it and without
/// faulting its pages in again; a segment its session wrote little of is kept, and every other one goes back to the
/// system. A handle: cloning it shares the cache. Without the `alloc` feature it holds nothing.
#[derive(Clone)]
pub struct Segments {
    #[cfg(feature = "alloc")]
    spare: alloc::rc::Rc<[core::cell::Cell<Option<alloc::boxed::Box<[u8]>>>; SPARE_SEGMENTS]>,
}

impl fmt::Debug for Segments {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Segments").finish_non_exhaustive()
    }
}

impl Default for Segments {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "alloc")]
impl Segments {
    /// An empty cache.
    pub fn new() -> Self {
        Self {
            spare: alloc::rc::Rc::new(core::array::from_fn(|_| core::cell::Cell::new(None))),
        }
    }

    /// A spare segment of `len` bytes, if the cache has one.
    fn take(&self, len: usize) -> Option<alloc::boxed::Box<[u8]>> {
        self.spare.iter().find_map(|cell| {
            let held = cell.take();
            if held.as_ref().is_some_and(|b| b.len() == len) {
                held
            } else {
                cell.set(held);
                None
            }
        })
    }

    /// Keep `segment`, `written` of whose chunks its pool handed out, if it was written little and the cache has room;
    /// otherwise it is freed here.
    fn put(&self, segment: alloc::boxed::Box<[u8]>, written: usize) {
        if written > SPARE_WRITTEN {
            return;
        }
        let empty = self.spare.iter().find(|cell| {
            let held = cell.take();
            let vacant = held.is_none();
            cell.set(held);
            vacant
        });
        if let Some(cell) = empty {
            cell.set(Some(segment));
        }
    }

    /// How many segments the cache keeps now.
    pub fn kept(&self) -> usize {
        self.spare
            .iter()
            .filter(|cell| {
                let held = cell.take();
                let some = held.is_some();
                cell.set(held);
                some
            })
            .count()
    }
}

#[cfg(not(feature = "alloc"))]
impl Segments {
    /// An empty cache.
    pub const fn new() -> Self {
        Self {}
    }
}

/// A grown slab: chunk `i` lives in segment `i / seg`, whose memory is allocated (zeroed, so the system commits a
/// page only when it is written) or taken from the thread's spare segments when a chunk of it is first handed out, and
/// freed whole by a trim once none of its chunks is in use: kept spare if its session wrote little of it, otherwise
/// given back. Freed 16 KiB chunks would stay in the allocator's heap, under the memory of the sessions that outlive
/// them; a segment the system maps on its own goes back to the system when it is freed. The free list of indices, most
/// recently returned last, is the flat pool's.
#[cfg(feature = "alloc")]
struct Grown {
    seg: usize,
    /// The memory of each segment.
    segs: alloc::vec::Vec<Option<alloc::boxed::Box<[u8]>>>,
    /// The chunks of each segment in use.
    busy: alloc::vec::Vec<u32>,
    /// Chunk `i` was handed out since its segment's memory was made: what the segment may have committed.
    made: alloc::vec::Vec<bool>,
    cap: usize,
    free: alloc::vec::Vec<u32>,
    /// Where freed segments go and new ones come from first.
    spare: Option<Segments>,
}

#[cfg(feature = "alloc")]
impl Grown {
    fn new(cap: usize, seg: usize) -> Self {
        Self {
            seg: seg.max(1),
            segs: alloc::vec::Vec::new(),
            busy: alloc::vec::Vec::new(),
            made: alloc::vec::Vec::new(),
            cap,
            free: alloc::vec::Vec::new(),
            spare: None,
        }
    }

    /// Hand out the most recently returned chunk, or the one at the bump cursor `fresh`, with its segment's memory.
    fn take(&mut self, fresh: &mut u32) -> Option<usize> {
        let i = if let Some(i) = self.free.pop() {
            i as usize
        } else {
            let i = *fresh as usize;
            if i >= self.cap {
                return None;
            }
            *fresh += 1;
            i
        };
        let s = i / self.seg;
        if self.segs.len() <= s {
            self.segs.resize_with(s + 1, || None);
            self.busy.resize(s + 1, 0);
        }
        if self.made.len() <= i {
            self.made.resize(i + 1, false);
        }
        let len = self.seg * CHUNK_SIZE;
        let spare = &self.spare;
        let memory = self.segs.get_mut(s)?;
        if memory.is_none() {
            *memory = Some(
                spare
                    .as_ref()
                    .and_then(|c| c.take(len))
                    .unwrap_or_else(|| alloc::vec![0u8; len].into_boxed_slice()),
            );
        }
        *self.busy.get_mut(s)? += 1;
        *self.made.get_mut(i)? = true;
        Some(i)
    }

    /// Take chunk `i` back; its memory stays with its segment.
    fn give(&mut self, i: usize) {
        if let Some(b) = self.busy.get_mut(i / self.seg) {
            *b = b.saturating_sub(1);
        }
        self.free.push(u32::try_from(i).unwrap_or(u32::MAX));
    }

    /// Free the memory of segment `s` (to the spare segments, or to the system) and forget which of its chunks were
    /// handed out.
    fn release(&mut self, s: usize) {
        let first = s * self.seg;
        let last = (first + self.seg).min(self.made.len());
        let marks = self.made.get_mut(first..last).unwrap_or_default();
        let written = marks.iter().filter(|m| **m).count();
        marks.fill(false);
        if let Some(memory) = self.segs.get_mut(s).and_then(Option::take)
            && let Some(c) = &self.spare
        {
            c.put(memory, written);
        }
    }

    /// Free the memory of every segment with no chunk in use.
    fn trim(&mut self) {
        for s in 0..self.segs.len() {
            if self.busy.get(s) == Some(&0) && self.segs.get(s).is_some_and(Option::is_some) {
                self.release(s);
            }
        }
    }

    /// Forget every chunk handed out and free their memory.
    fn reset(&mut self) {
        for s in 0..self.segs.len() {
            self.release(s);
        }
        self.segs.clear();
        self.busy.clear();
        self.made.clear();
        self.free.clear();
    }

    /// Whether chunk `i` is in use or idle in a segment that has its memory.
    fn has(&self, i: usize) -> bool {
        self.made.get(i).copied().unwrap_or(false)
    }

    fn chunk(&self, i: usize) -> Option<&RawChunk> {
        self.segs.get(i / self.seg)?.as_deref()?.as_chunks().0.get(i % self.seg)
    }

    fn chunk_mut(&mut self, i: usize) -> Option<&mut RawChunk> {
        let seg = self.seg;
        self.segs
            .get_mut(i / seg)?
            .as_deref_mut()?
            .as_chunks_mut()
            .0
            .get_mut(i % seg)
    }

    fn held(&self) -> usize {
        self.made.iter().filter(|m| **m).count()
    }
}

impl Slab<'_> {
    /// How many chunks the slab has or may have.
    fn len(&self) -> usize {
        match self {
            Slab::Borrowed(s) => s.len(),
            #[cfg(feature = "alloc")]
            Slab::Boxed(b) => b.len() / CHUNK_SIZE,
            #[cfg(feature = "alloc")]
            Slab::Grown(g) => g.cap,
        }
    }

    fn get(&self, i: usize) -> Option<&RawChunk> {
        match self {
            Slab::Borrowed(s) => s.get(i),
            #[cfg(feature = "alloc")]
            Slab::Boxed(b) => b.as_chunks().0.get(i),
            #[cfg(feature = "alloc")]
            Slab::Grown(g) => g.chunk(i),
        }
    }

    fn get_mut(&mut self, i: usize) -> Option<&mut RawChunk> {
        match self {
            Slab::Borrowed(s) => s.get_mut(i),
            #[cfg(feature = "alloc")]
            Slab::Boxed(b) => b.as_chunks_mut().0.get_mut(i),
            #[cfg(feature = "alloc")]
            Slab::Grown(g) => g.chunk_mut(i),
        }
    }

    /// Chunks of memory held now.
    fn held(&self) -> usize {
        match self {
            #[cfg(feature = "alloc")]
            Slab::Grown(g) => g.held(),
            _ => self.len(),
        }
    }
}

/// A fixed set of 16 KiB chunks with a byte budget.
pub struct BufferPool<'p> {
    slab: Slab<'p>,
    /// The next never-used chunk.
    fresh: u32,
    /// The head of the free list, as an index plus one (zero is the empty list).
    free_head: u32,
    used: u32,
    budget: u32,
}

impl fmt::Debug for BufferPool<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BufferPool")
            .field("used_chunks", &self.used)
            .field("budget_chunks", &self.budget)
            .field("capacity_chunks", &self.slab.len())
            .finish()
    }
}

impl<'p> BufferPool<'p> {
    /// A heap-free pool over a caller-provided slab; the budget is the whole slab.
    pub fn from_slab(slab: &'p mut [RawChunk]) -> Self {
        Self::with_slab(Slab::Borrowed(slab))
    }

    /// A heap-backed pool of `chunks` chunks; the budget is all of them.
    #[cfg(feature = "alloc")]
    pub fn new_boxed(chunks: usize) -> Self {
        // A flat zeroed byte buffer is a calloc the system commits lazily at any optimisation level; a vec of
        // arrays is filled by hand in an unoptimised build and would touch every page.
        let slab = alloc::vec![0u8; chunks * CHUNK_SIZE].into_boxed_slice();
        Self::with_slab(Slab::Boxed(slab))
    }

    /// A heap-backed pool of up to `chunks` chunks; the budget is all of them. A chunk's memory is allocated with its
    /// segment when a chunk of the segment is first handed out, and kept until a [`trim`](Self::trim) finds none of the
    /// segment's chunks in use, or a [`reset`](Self::reset): the pool holds what its session uses, where
    /// [`new_boxed`](Self::new_boxed) asks for the whole budget at once and keeps it. A segment is as large as the
    /// system allocator maps on its own where it gives freed memory back (`SEGMENT_CHUNKS`), so a trimmed segment's
    /// pages go back to the system and do not stay in the allocator's heap; elsewhere it is one chunk.
    #[cfg(feature = "alloc")]
    pub fn new_grown(chunks: usize) -> Self {
        Self::new_grown_in(chunks, SEGMENT_CHUNKS)
    }

    /// Take new segments from `segments`, the spare segments the grown pools of this thread share, and give the freed
    /// ones to it. A pool that shares none frees its segments to the system and allocates every one it needs. Does
    /// nothing to a flat or borrowed pool.
    #[cfg(feature = "alloc")]
    pub fn share_segments(&mut self, segments: &Segments) {
        if let Slab::Grown(g) = &mut self.slab {
            g.spare = Some(segments.clone());
        }
    }

    /// As [`new_grown`](Self::new_grown), with segments of `segment_chunks` chunks: 1 is the pool of 16 KiB chunks, each
    /// its own allocation, which a host whose system does not map and commit a large request lazily, or charges it
    /// whole against a strict commit limit, asks for.
    #[cfg(feature = "alloc")]
    pub fn new_grown_in(chunks: usize, segment_chunks: usize) -> Self {
        Self::with_slab(Slab::Grown(Grown::new(chunks, segment_chunks)))
    }

    /// The chunks of each segment of a grown pool (1 for a pool of 16 KiB chunks); 0 for a flat or borrowed pool.
    pub fn segment_chunks(&self) -> usize {
        match &self.slab {
            #[cfg(feature = "alloc")]
            Slab::Grown(g) => g.seg,
            _ => 0,
        }
    }

    fn with_slab(slab: Slab<'p>) -> Self {
        let total = u32::try_from(slab.len()).unwrap_or(u32::MAX - 1);
        Self {
            slab,
            fresh: 0,
            free_head: 0,
            used: 0,
            budget: total,
        }
    }

    /// Free the memory of every segment of a grown pool with no chunk in use: for a pool whose session is quiet. A flat or borrowed pool holds all its memory anyway; for it this does nothing.
    pub fn trim(&mut self) {
        #[cfg(feature = "alloc")]
        if let Slab::Grown(g) = &mut self.slab {
            g.trim();
        }
    }

    /// Forget every chunk handed out, so the pool is as new: for a pool whose connection ended. Every
    /// [`Chunk`] taken before is dead and must be dropped, not freed.
    pub fn reset(&mut self) {
        self.fresh = 0;
        self.free_head = 0;
        self.used = 0;
        #[cfg(feature = "alloc")]
        if let Slab::Grown(g) = &mut self.slab {
            g.reset();
        }
    }

    /// Chunks of memory the pool holds now: every one of them, or for a grown pool those handed out since their
    /// segment's memory was made (the most of the segments it may have committed).
    pub fn held_chunks(&self) -> usize {
        self.slab.held()
    }

    /// Lower the byte budget to `bytes` (rounded down to whole chunks, never above the slab). Chunks already in use
    /// stay valid; later allocations fail until usage drops below the new budget.
    pub fn set_budget_bytes(&mut self, bytes: u64) {
        let want = u32::try_from(bytes / CHUNK_SIZE as u64).unwrap_or(u32::MAX);
        self.budget = want.min(u32::try_from(self.slab.len()).unwrap_or(u32::MAX - 1));
    }

    /// Take one chunk, charging it to the budget.
    ///
    /// # Errors
    /// [`PoolExhausted`] when the budget or the slab is used up.
    pub fn alloc_chunk(&mut self) -> Result<Chunk, PoolExhausted> {
        if self.used >= self.budget {
            return Err(PoolExhausted);
        }
        #[cfg(feature = "alloc")]
        if let Slab::Grown(g) = &mut self.slab {
            let i = g.take(&mut self.fresh).ok_or(PoolExhausted)?;
            let chunk = u32::try_from(i + 1)
                .ok()
                .and_then(NonZeroU32::new)
                .ok_or(PoolExhausted)?;
            self.used += 1;
            return Ok(Chunk(chunk));
        }
        let index = if let Some(head) = NonZeroU32::new(self.free_head) {
            let chunk = Chunk(head);
            let next = self
                .slab
                .get(chunk.index())
                .map_or(0, |c| u32::from_le_bytes(*c.first_chunk::<4>().unwrap_or(&[0; 4])));
            self.free_head = next;
            chunk.0
        } else if (self.fresh as usize) < self.slab.len() {
            self.fresh += 1;
            NonZeroU32::new(self.fresh).ok_or(PoolExhausted)?
        } else {
            return Err(PoolExhausted);
        };
        self.used += 1;
        Ok(Chunk(index))
    }

    /// Return a chunk to the free list and release its charge.
    #[allow(
        clippy::needless_pass_by_value,
        reason = "consuming the handle is what rules out a double free"
    )]
    pub fn free_chunk(&mut self, chunk: Chunk) {
        #[cfg(feature = "alloc")]
        if let Slab::Grown(g) = &mut self.slab {
            if g.has(chunk.index()) {
                self.used = self.used.saturating_sub(1);
                g.give(chunk.index());
            }
            return;
        }
        let head = self.free_head;
        if let Some(first) = self.slab.get_mut(chunk.index()).and_then(|c| c.first_chunk_mut::<4>()) {
            *first = head.to_le_bytes();
            self.free_head = chunk.0.get();
            self.used = self.used.saturating_sub(1);
        }
    }

    /// The bytes of `chunk`.
    pub fn bytes(&self, chunk: &Chunk) -> &[u8] {
        self.slab.get(chunk.index()).map_or(&[], |c| c.as_slice())
    }

    /// The bytes of `chunk`, writable.
    pub fn bytes_mut(&mut self, chunk: &Chunk) -> &mut [u8] {
        self.slab.get_mut(chunk.index()).map_or(&mut [], |c| c.as_mut_slice())
    }

    /// Chunks currently charged.
    pub const fn used_chunks(&self) -> usize {
        self.used as usize
    }

    /// Bytes currently charged.
    pub const fn used_bytes(&self) -> u64 {
        self.used as u64 * CHUNK_SIZE as u64
    }

    /// The byte budget.
    pub const fn budget_bytes(&self) -> u64 {
        self.budget as u64 * CHUNK_SIZE as u64
    }

    /// Chunks that can still be allocated.
    pub fn available_chunks(&self) -> usize {
        let slab_left = self.slab.len() - self.fresh as usize;
        let free_listed = (self.fresh - self.used.min(self.fresh)) as usize;
        (self.budget.saturating_sub(self.used) as usize).min(slab_left + free_listed)
    }

    /// Bytes that can still be allocated.
    pub fn available_bytes(&self) -> u64 {
        self.available_chunks() as u64 * CHUNK_SIZE as u64
    }
}

/// A sparse run of pool chunks indexed by chunk number modulo `C`: the stream layers keep their reassembly and send
/// buffers in one. The owner guarantees that the live chunk numbers span fewer than `C`.
///
/// An entry is the number of the pool chunk it holds (1 for the first chunk, 0 for none) in 16 bits, so a ring of 257
/// entries is half the size it would be with the handle of the pool; the pool is therefore used up to its 65,535th
/// chunk by streams, and a chunk beyond it is refused as exhausted.
#[derive(Debug)]
pub(super) struct Ring<const C: usize> {
    slots: [u16; C],
    held: usize,
}

#[allow(
    clippy::cast_possible_truncation,
    reason = "the remainder is below C, which is a usize"
)]
const fn ring_index(k: u64, c: usize) -> usize {
    (k % c as u64) as usize
}

impl<const C: usize> Ring<C> {
    pub(super) const EMPTY: Self = Self { slots: [0; C], held: 0 };

    /// How many chunks are held.
    pub(super) const fn held(&self) -> usize {
        self.held
    }

    /// The handle of chunk number `k`, if held. The ring keeps the ownership: the handle is only shown to the pool.
    fn slot(&self, k: u64) -> Option<Chunk> {
        let raw = *self.slots.get(ring_index(k, C))?;
        NonZeroU32::new(u32::from(raw)).map(Chunk)
    }

    /// Whether chunk number `k` is held.
    pub(super) fn has(&self, k: u64) -> bool {
        self.slot(k).is_some()
    }

    /// How many of the chunk numbers `first..=last` are not held.
    pub(super) fn missing(&self, first: u64, last: u64) -> usize {
        (first..=last).filter(|&k| !self.has(k)).count()
    }

    /// The chunk numbers held, given the lowest number that can be live (the live numbers span fewer than `C`).
    #[cfg(feature = "trace")]
    pub(super) fn numbers(&self, base: u64) -> alloc::vec::Vec<u64> {
        (base..base + C as u64).filter(|&k| self.has(k)).collect()
    }

    /// Release chunk number `k`, if held.
    pub(super) fn release(&mut self, pool: &mut BufferPool<'_>, k: u64) {
        if let Some(raw) = self.slots.get_mut(ring_index(k, C)).map(core::mem::take)
            && let Some(chunk) = NonZeroU32::new(u32::from(raw)).map(Chunk)
        {
            self.held -= 1;
            pool.free_chunk(chunk);
        }
    }

    /// Release every chunk.
    pub(super) fn release_all(&mut self, pool: &mut BufferPool<'_>) {
        for raw in &mut self.slots {
            if let Some(chunk) = NonZeroU32::new(u32::from(core::mem::take(raw))).map(Chunk) {
                pool.free_chunk(chunk);
            }
        }
        self.held = 0;
    }

    /// The bytes of chunk number `k` from `from` to `from + len`, clipped to the chunk.
    pub(super) fn span<'a>(&self, pool: &'a BufferPool<'_>, k: u64, from: usize, len: usize) -> Option<&'a [u8]> {
        let chunk = self.slot(k)?;
        pool.bytes(&chunk).get(from..from.checked_add(len)?)
    }

    /// Store `src` at absolute position `pos`, allocating missing chunks.
    pub(super) fn write(&mut self, pool: &mut BufferPool<'_>, pos: u64, src: &[u8]) -> Result<(), PoolExhausted> {
        let mut pos = pos;
        let mut rest = src;
        while !rest.is_empty() {
            let k = pos / CHUNK_SIZE as u64;
            let at = (pos % CHUNK_SIZE as u64) as usize;
            let take = rest.len().min(CHUNK_SIZE - at);
            let slot = self.slots.get_mut(ring_index(k, C)).ok_or(PoolExhausted)?;
            if *slot == 0 {
                let chunk = pool.alloc_chunk()?;
                let Ok(raw) = u16::try_from(chunk.0.get()) else {
                    pool.free_chunk(chunk);
                    return Err(PoolExhausted);
                };
                *slot = raw;
                self.held += 1;
            }
            let dst = NonZeroU32::new(u32::from(*slot))
                .map(Chunk)
                .and_then(|chunk| pool.bytes_mut(&chunk).get_mut(at..at + take))
                .ok_or(PoolExhausted)?;
            let (head, tail) = rest.split_at(take);
            dst.copy_from_slice(head);
            rest = tail;
            pos += take as u64;
        }
        Ok(())
    }

    /// Copy stored bytes at `pos` into `dst`; returns how many were copied (fewer if a chunk is missing).
    pub(super) fn read(&self, pool: &BufferPool<'_>, pos: u64, dst: &mut [u8]) -> usize {
        let mut pos = pos;
        let mut done = 0;
        while done < dst.len() {
            let k = pos / CHUNK_SIZE as u64;
            let at = (pos % CHUNK_SIZE as u64) as usize;
            let take = (dst.len() - done).min(CHUNK_SIZE - at);
            let Some(src) = self.span(pool, k, at, take) else { break };
            let Some(out) = dst.get_mut(done..done + take) else {
                break;
            };
            out.copy_from_slice(src);
            done += take;
            pos += take as u64;
        }
        done
    }

    /// Whether the stored bytes at `pos` equal `expected` (false if any chunk is missing).
    pub(super) fn matches(&self, pool: &BufferPool<'_>, pos: u64, expected: &[u8]) -> bool {
        let mut pos = pos;
        let mut rest = expected;
        while !rest.is_empty() {
            let k = pos / CHUNK_SIZE as u64;
            let at = (pos % CHUNK_SIZE as u64) as usize;
            let take = rest.len().min(CHUNK_SIZE - at);
            let (head, tail) = rest.split_at(take);
            if self.span(pool, k, at, take) != Some(head) {
                return false;
            }
            rest = tail;
            pos += take as u64;
        }
        true
    }
}

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    #[test]
    fn a_ring_refuses_the_chunk_beyond_its_16_bit_handle_and_gives_it_back() {
        let mut pool = BufferPool::new_boxed(65_537);
        let held: alloc::vec::Vec<Chunk> = (0..65_535).map(|_| pool.alloc_chunk().unwrap()).collect();
        let mut ring = Ring::<4>::EMPTY;
        // The 65,536th chunk of the pool cannot be named in 16 bits.
        assert!(ring.write(&mut pool, 0, &[1]).is_err());
        assert_eq!(ring.held(), 0);
        assert_eq!(pool.available_chunks(), 2);
        for c in held {
            pool.free_chunk(c);
        }
        // With the pool back at its start, the same ring stores and reads a byte.
        assert!(ring.write(&mut pool, 0, &[7]).is_ok());
        let mut out = [0u8; 1];
        assert_eq!(ring.read(&pool, 0, &mut out), 1);
        assert_eq!(out, [7]);
    }

    /// The segment sizes the grown pool is tested with: one chunk (wasm, 32-bit), a few, and the mapped segment.
    const SEGS: [usize; 3] = [1, 4, SEGMENT_CHUNKS];

    #[test]
    fn a_grown_pool_makes_a_chunk_when_it_is_first_needed_and_never_more_than_its_budget() {
        for seg in SEGS {
            let cap = 35;
            let mut pool = BufferPool::new_grown_in(cap, seg);
            assert_eq!((pool.held_chunks(), pool.available_chunks()), (0, cap));
            let mut held = alloc::vec::Vec::new();
            for i in 0..cap {
                held.push(pool.alloc_chunk().unwrap());
                assert_eq!(pool.held_chunks(), i + 1, "after chunk {i}");
            }
            assert_eq!(pool.alloc_chunk(), Err(PoolExhausted));
            assert_eq!((pool.held_chunks(), pool.available_chunks()), (cap, 0));
            // Each chunk is its own memory.
            for (i, ch) in held.iter().enumerate() {
                pool.bytes_mut(ch).fill(u8::try_from(i).unwrap());
            }
            for (i, ch) in held.iter().enumerate() {
                let v = u8::try_from(i).unwrap();
                assert!(pool.bytes(ch).len() == CHUNK_SIZE && pool.bytes(ch).iter().all(|x| *x == v));
            }
            // A returned chunk is handed out again; nothing new is made for it.
            let last = held.pop().unwrap();
            pool.free_chunk(last);
            let again = pool.alloc_chunk().unwrap();
            assert!(pool.bytes(&again).iter().all(|x| usize::from(*x) == cap - 1));
            assert_eq!(pool.held_chunks(), cap);
        }
    }

    #[test]
    fn a_grown_pool_frees_its_chunks_when_it_is_reset() {
        for seg in SEGS {
            let mut pool = BufferPool::new_grown_in(64, seg);
            let held: alloc::vec::Vec<Chunk> = (0..17).map(|_| pool.alloc_chunk().unwrap()).collect();
            assert_eq!(pool.held_chunks(), 17);
            drop(held);
            pool.reset();
            assert_eq!(
                (pool.held_chunks(), pool.used_chunks(), pool.available_chunks()),
                (0, 0, 64)
            );
            // The pool is as new: it makes each chunk again as it hands it out.
            let again: alloc::vec::Vec<Chunk> = (0..64).map(|_| pool.alloc_chunk().unwrap()).collect();
            assert_eq!((again.len(), pool.held_chunks()), (64, 64));
            assert_eq!(pool.alloc_chunk(), Err(PoolExhausted));
        }
    }

    #[test]
    fn a_grown_pool_keeps_returned_chunks_until_a_trim() {
        for seg in SEGS {
            let mut pool = BufferPool::new_grown_in(64, seg);
            let mut held: alloc::vec::Vec<Chunk> = (0..20).map(|_| pool.alloc_chunk().unwrap()).collect();
            assert_eq!(pool.held_chunks(), 20);
            // Returned chunks keep their memory, so a busy session allocates nothing for the chunks it reuses.
            for _ in 0..10 {
                pool.free_chunk(held.pop().unwrap());
            }
            assert_eq!((pool.used_chunks(), pool.held_chunks()), (10, 20));
            let again: alloc::vec::Vec<Chunk> = (0..10).map(|_| pool.alloc_chunk().unwrap()).collect();
            assert_eq!((pool.used_chunks(), pool.held_chunks()), (20, 20));
            // A trim frees every segment with no chunk in use, never one with a chunk in use.
            for ch in held.drain(..).chain(again) {
                pool.free_chunk(ch);
            }
            assert_eq!((pool.used_chunks(), pool.held_chunks()), (0, 20));
            pool.trim();
            assert_eq!((pool.used_chunks(), pool.held_chunks()), (0, 0));
            let in_use: alloc::vec::Vec<Chunk> = (0..5).map(|_| pool.alloc_chunk().unwrap()).collect();
            pool.trim();
            assert_eq!((pool.used_chunks(), pool.held_chunks()), (5, 5));
            // A chunk handed out after a trim has its memory, whole.
            assert!(in_use.iter().all(|c| pool.bytes(c).len() == CHUNK_SIZE));
        }
    }

    #[test]
    fn a_trim_keeps_a_segment_with_a_chunk_in_use_and_frees_the_others_whole() {
        for seg in SEGS {
            let mut pool = BufferPool::new_grown_in(64, seg);
            let mut held: alloc::vec::Vec<Chunk> = (0..20).map(|_| pool.alloc_chunk().unwrap()).collect();
            for ch in &held {
                pool.bytes_mut(ch).fill(0xa5);
            }
            // Chunk 0 stays in use; the 19 others come back.
            let first = held.remove(0);
            for ch in held.drain(..) {
                pool.free_chunk(ch);
            }
            pool.trim();
            // Chunk 0's segment keeps the memory of every chunk of it handed out (its first `seg` chunks, at most 20);
            // every other segment is freed.
            assert_eq!((pool.used_chunks(), pool.held_chunks()), (1, seg.min(20)), "seg {seg}");
            assert!(pool.bytes(&first).iter().all(|x| *x == 0xa5));
            pool.free_chunk(first);
            pool.trim();
            assert_eq!((pool.used_chunks(), pool.held_chunks()), (0, 0));
            // A freed segment's memory is gone: a chunk handed out again comes from new, zeroed memory.
            let again: alloc::vec::Vec<Chunk> = (0..20).map(|_| pool.alloc_chunk().unwrap()).collect();
            assert!(again.iter().all(|c| pool.bytes(c).iter().all(|x| *x == 0)));
        }
    }

    #[test]
    fn a_quiet_pool_keeps_a_segment_it_wrote_little_of_spare_and_the_next_pool_takes_it() {
        let spare = Segments::new();
        let mut a = BufferPool::new_grown_in(64, SEGMENT_CHUNKS);
        a.share_segments(&spare);
        let held: alloc::vec::Vec<Chunk> = (0..2).map(|_| a.alloc_chunk().unwrap()).collect();
        for c in held {
            a.free_chunk(c);
        }
        a.trim();
        assert_eq!((a.held_chunks(), spare.kept()), (0, 1));
        // The next pool, another session of the thread, takes the spare segment instead of a new one.
        let mut b = BufferPool::new_grown_in(64, SEGMENT_CHUNKS);
        b.share_segments(&spare);
        let c = b.alloc_chunk().unwrap();
        assert_eq!((b.held_chunks(), spare.kept()), (1, 0));
        b.free_chunk(c);
        b.reset();
        assert_eq!(spare.kept(), 1);
    }

    #[test]
    fn a_segment_written_past_the_spare_bound_goes_back_to_the_system_and_the_spare_ones_are_bounded() {
        let spare = Segments::new();
        let mut a = BufferPool::new_grown_in(64, SEGMENT_CHUNKS);
        a.share_segments(&spare);
        let held: alloc::vec::Vec<Chunk> = (0..=SPARE_WRITTEN).map(|_| a.alloc_chunk().unwrap()).collect();
        for c in held {
            a.free_chunk(c);
        }
        a.trim();
        assert_eq!((a.held_chunks(), spare.kept()), (0, 0));
        // Quiet pools that wrote little fill the spare segments up to their bound, and no further.
        let mut pools: alloc::vec::Vec<BufferPool<'static>> = (0..SPARE_SEGMENTS + 2)
            .map(|_| {
                let mut p = BufferPool::new_grown_in(64, SEGMENT_CHUNKS);
                p.share_segments(&spare);
                let c = p.alloc_chunk().unwrap();
                p.free_chunk(c);
                p
            })
            .collect();
        for p in &mut pools {
            p.trim();
        }
        assert_eq!(spare.kept(), SPARE_SEGMENTS);
    }

    #[test]
    fn a_grown_pool_and_a_flat_one_behave_alike() {
        for seg in SEGS {
            // The same script of takes, returns and trims gives the same handles, the same counts and the same
            // refusals.
            let (mut grown, mut flat) = (BufferPool::new_grown_in(21, seg), BufferPool::new_boxed(21));
            let (mut held_grown, mut held_flat) = (alloc::vec::Vec::new(), alloc::vec::Vec::new());
            let mut seed = 0x9E37_79B9_7F4A_7C15_u64;
            for _ in 0..2000 {
                seed = seed
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                if (seed >> 33).is_multiple_of(17) {
                    grown.trim();
                    assert!(grown.held_chunks() >= grown.used_chunks());
                } else if !(seed >> 33).is_multiple_of(3) || held_grown.is_empty() {
                    let (a, b) = (grown.alloc_chunk(), flat.alloc_chunk());
                    assert_eq!(a.is_ok(), b.is_ok());
                    if let (Ok(a), Ok(b)) = (a, b) {
                        assert_eq!(a, b);
                        held_grown.push(a);
                        held_flat.push(b);
                    }
                } else {
                    let i = usize::try_from(seed >> 40).unwrap() % held_grown.len();
                    grown.free_chunk(held_grown.swap_remove(i));
                    flat.free_chunk(held_flat.swap_remove(i));
                }
                assert_eq!(
                    (grown.used_chunks(), grown.available_chunks(), grown.budget_bytes()),
                    (flat.used_chunks(), flat.available_chunks(), flat.budget_bytes())
                );
            }
        }
    }
}
