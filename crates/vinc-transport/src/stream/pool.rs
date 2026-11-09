//! The buffer pool: a fixed set of 16 KiB chunks, the only memory the stream layer, the datagram queues and the
//! early-data buffer use.
//!
//! Invariants: the slab never grows; every [`Chunk`] handed out is charged against the byte budget until it is
//! returned through [`BufferPool::free_chunk`]; a handle is neither `Copy` nor `Clone`, so a chunk cannot be freed twice
//! through safe code. Allocation and free are O(1): fresh chunks come from a bump cursor and returned chunks form an
//! intrusive free list stored in their first four bytes. Exhaustion is a typed result, never an overflow.

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
    Boxed(alloc::boxed::Box<[RawChunk]>),
}

impl Slab<'_> {
    fn chunks(&self) -> &[RawChunk] {
        match self {
            Slab::Borrowed(s) => s,
            #[cfg(feature = "alloc")]
            Slab::Boxed(b) => b,
        }
    }

    fn chunks_mut(&mut self) -> &mut [RawChunk] {
        match self {
            Slab::Borrowed(s) => s,
            #[cfg(feature = "alloc")]
            Slab::Boxed(b) => b,
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
            .field("capacity_chunks", &self.slab.chunks().len())
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
        let slab = alloc::vec![[0u8; CHUNK_SIZE]; chunks].into_boxed_slice();
        Self::with_slab(Slab::Boxed(slab))
    }

    fn with_slab(slab: Slab<'p>) -> Self {
        let total = u32::try_from(slab.chunks().len()).unwrap_or(u32::MAX - 1);
        Self {
            slab,
            fresh: 0,
            free_head: 0,
            used: 0,
            budget: total,
        }
    }

    /// Forget every chunk handed out, so the pool is as new: for a pool whose connection ended. Every
    /// [`Chunk`] taken before is dead and must be dropped, not freed.
    pub const fn reset(&mut self) {
        self.fresh = 0;
        self.free_head = 0;
        self.used = 0;
    }

    /// Lower the byte budget to `bytes` (rounded down to whole chunks, never above the slab). Chunks already in use
    /// stay valid; later allocations fail until usage drops below the new budget.
    pub fn set_budget_bytes(&mut self, bytes: u64) {
        let want = u32::try_from(bytes / CHUNK_SIZE as u64).unwrap_or(u32::MAX);
        self.budget = want.min(u32::try_from(self.slab.chunks().len()).unwrap_or(u32::MAX - 1));
    }

    /// Take one chunk, charging it to the budget.
    ///
    /// # Errors
    /// [`PoolExhausted`] when the budget or the slab is used up.
    pub fn alloc_chunk(&mut self) -> Result<Chunk, PoolExhausted> {
        if self.used >= self.budget {
            return Err(PoolExhausted);
        }
        let index = if let Some(head) = NonZeroU32::new(self.free_head) {
            let chunk = Chunk(head);
            let next = self
                .slab
                .chunks()
                .get(chunk.index())
                .map_or(0, |c| u32::from_le_bytes(*c.first_chunk::<4>().unwrap_or(&[0; 4])));
            self.free_head = next;
            chunk.0
        } else if (self.fresh as usize) < self.slab.chunks().len() {
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
        let head = self.free_head;
        if let Some(first) = self
            .slab
            .chunks_mut()
            .get_mut(chunk.index())
            .and_then(|c| c.first_chunk_mut::<4>())
        {
            *first = head.to_le_bytes();
            self.free_head = chunk.0.get();
            self.used = self.used.saturating_sub(1);
        }
    }

    /// The bytes of `chunk`.
    pub fn bytes(&self, chunk: &Chunk) -> &[u8] {
        self.slab.chunks().get(chunk.index()).map_or(&[], |c| c.as_slice())
    }

    /// The bytes of `chunk`, writable.
    pub fn bytes_mut(&mut self, chunk: &Chunk) -> &mut [u8] {
        self.slab
            .chunks_mut()
            .get_mut(chunk.index())
            .map_or(&mut [], |c| c.as_mut_slice())
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
        let slab_left = self.slab.chunks().len() - self.fresh as usize;
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
#[derive(Debug)]
pub(super) struct Ring<const C: usize> {
    slots: [Option<Chunk>; C],
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
    pub(super) const EMPTY: Self = Self {
        slots: [const { None }; C],
        held: 0,
    };

    /// How many chunks are held.
    pub(super) const fn held(&self) -> usize {
        self.held
    }

    fn slot(&self, k: u64) -> Option<&Chunk> {
        self.slots.get(ring_index(k, C)).and_then(Option::as_ref)
    }

    /// Whether chunk number `k` is held.
    pub(super) fn has(&self, k: u64) -> bool {
        self.slot(k).is_some()
    }

    /// How many of the chunk numbers `first..=last` are not held.
    pub(super) fn missing(&self, first: u64, last: u64) -> usize {
        (first..=last).filter(|&k| !self.has(k)).count()
    }

    /// Release chunk number `k`, if held.
    pub(super) fn release(&mut self, pool: &mut BufferPool<'_>, k: u64) {
        if let Some(chunk) = self.slots.get_mut(ring_index(k, C)).and_then(Option::take) {
            self.held -= 1;
            pool.free_chunk(chunk);
        }
    }

    /// Release every chunk.
    pub(super) fn release_all(&mut self, pool: &mut BufferPool<'_>) {
        for chunk in self.slots.iter_mut().filter_map(Option::take) {
            pool.free_chunk(chunk);
        }
        self.held = 0;
    }

    /// The bytes of chunk number `k` from `from` to `from + len`, clipped to the chunk.
    pub(super) fn span<'a>(&self, pool: &'a BufferPool<'_>, k: u64, from: usize, len: usize) -> Option<&'a [u8]> {
        let chunk = self.slot(k)?;
        pool.bytes(chunk).get(from..from.checked_add(len)?)
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
            if slot.is_none() {
                *slot = Some(pool.alloc_chunk()?);
                self.held += 1;
            }
            let dst = slot
                .as_ref()
                .and_then(|chunk| pool.bytes_mut(chunk).get_mut(at..at + take))
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
