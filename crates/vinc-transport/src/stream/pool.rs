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
//! ([`BufferPool::new_grown`]): a chunk's memory is made when it is first handed out (its first [`OWN_CHUNKS`] each on
//! its own, the others in segments) and kept while the session is busy; a trim, when the session's streams have all
//! ended, frees every segment with no chunk in use. So a quiet session holds nothing, and its segments go to the spare
//! segments of its endpoint ([`Segments`]), which the endpoint's timer gives back to the system, not to the
//! allocator's heap; a busy one allocates nothing per chunk. A segment passed to another session is emptied first, so
//! a session never reads another's bytes; one the system refuses becomes chunks of their own (`grown`).

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

#[cfg(feature = "alloc")]
mod grown;
#[cfg(feature = "alloc")]
use grown::Grown;
#[cfg(feature = "alloc")]
pub use grown::{OWN_CHUNKS, SEGMENT_CHUNKS, SEGMENT_DECAY, Segments};

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

    /// A heap-backed pool of up to `chunks` chunks; the budget is all of them. A chunk's memory is made when it is first
    /// handed out: each of the first [`OWN_CHUNKS`] on its own, so a session that only shakes hands maps no segment,
    /// and the others in a segment reserved when a chunk of it is first handed out and committed a chunk at a time. It
    /// is kept until a [`trim`](Self::trim) finds none of the segment's chunks in use, or a [`reset`](Self::reset):
    /// the pool holds what its session uses, where [`new_boxed`](Self::new_boxed) asks for the whole budget at once and
    /// keeps it. A segment is as large as the system allocator maps on its own where it gives freed memory back
    /// ([`SEGMENT_CHUNKS`]), so a trimmed segment's pages go back to the system and do not stay in the allocator's
    /// heap; elsewhere it is one chunk. A segment the system refuses is counted ([`Segments::refused`]) and its chunks,
    /// and those of the session's later segments, are allocations of their own: the pool of 16 KiB chunks.
    #[cfg(feature = "alloc")]
    pub fn new_grown(chunks: usize) -> Self {
        Self::new_grown_in(chunks, SEGMENT_CHUNKS)
    }

    /// Take new segments from `segments`, the spare segments the grown pools of an endpoint share, and give the freed
    /// ones to it; the refusals of the system are counted there. A pool that shares none frees its segments to the
    /// system and allocates every one it needs. Does nothing to a flat or borrowed pool.
    #[cfg(feature = "alloc")]
    pub fn share_segments(&mut self, segments: &Segments) {
        if let Slab::Grown(g) = &mut self.slab {
            g.share(segments);
        }
    }

    /// As [`new_grown`](Self::new_grown), with segments of `segment_chunks` chunks, rounded up to a power of two: 1 is
    /// the pool of 16 KiB chunks, each its own allocation, which a host whose allocator does not map and commit a large
    /// request lazily asks for.
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
    /// [`Chunk`] taken before is dead and must be dropped, not freed. A grown pool serves a new session after it.
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
    /// segment's memory was made (what its session committed of them).
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
}
