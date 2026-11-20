//! The buffer pool: a fixed set of 16 KiB chunks, the only memory the stream layer, the datagram queues and the
//! early-data buffer use.
//!
//! Invariants: the slab never holds more chunks than it was made for; every [`Chunk`] handed out is charged against
//! the byte budget until it is returned through [`BufferPool::free_chunk`]; a handle is neither `Copy` nor `Clone`, so
//! a chunk cannot be freed twice through safe code. Allocation and free are O(1): fresh chunks come from a bump cursor
//! and returned chunks form a last-in first-out free list, stored in their first four bytes, or beside them in a pool
//! over a store. Exhaustion is a typed result, never an overflow.
//!
//! A pool is one of three: over a slab the caller lends ([`BufferPool::from_slab`], no heap), over one flat buffer
//! allocated when the pool is made ([`BufferPool::new_boxed`], no allocation afterwards), or over a slot of the
//! endpoint's [`ChunkStore`] ([`BufferPool::over_store`]): a chunk comes from the store when it is handed out and goes
//! back to it when it is returned, so a quiet session holds none and nothing is allocated after the store is made. The
//! endpoint owns the store and lends it for each call that takes, gives or reads a chunk ([`BufferPool::lend_store`]);
//! between calls the pool holds only the numbers of its chunks. Such a pool may hold only what its slot's reservation
//! covers; the stream layer grows it ([`BufferPool::make_room`]) before it promises room to the peer and lowers it
//! ([`BufferPool::trim`]) when a promise is gone, so room a pool reports is room the store keeps for it.

use core::fmt;
use core::num::NonZeroU32;

use super::store::ChunkStore;

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

/// No store chunk.
#[cfg(feature = "alloc")]
const NO_CHUNK: u32 = u32::MAX;

/// A pool's chunks in a slot of the endpoint's store: the store chunk each pool index holds, and the indices free.
#[cfg(feature = "alloc")]
struct StoreSlab {
    /// The slot the pool reserves in.
    slot: usize,
    /// The mark of the pool's session; 0 until the store is first lent to it.
    mark: u64,
    /// The store chunk at each pool index, [`NO_CHUNK`] for none.
    ids: alloc::boxed::Box<[u32]>,
    /// Pool indices given back, most recent last.
    free: alloc::vec::Vec<u32>,
}

enum Slab<'p> {
    Borrowed(&'p mut [RawChunk]),
    #[cfg(feature = "alloc")]
    Boxed(alloc::boxed::Box<[u8]>),
    #[cfg(feature = "alloc")]
    Store(StoreSlab),
}

impl Slab<'_> {
    /// How many chunks the slab has or may have.
    fn len(&self) -> usize {
        match self {
            Slab::Borrowed(s) => s.len(),
            #[cfg(feature = "alloc")]
            Slab::Boxed(b) => b.len() / CHUNK_SIZE,
            #[cfg(feature = "alloc")]
            Slab::Store(s) => s.ids.len(),
        }
    }

    fn get<'s>(&'s self, store: &'s ChunkStore, i: usize) -> Option<&'s RawChunk> {
        let _ = store;
        match self {
            Slab::Borrowed(s) => s.get(i),
            #[cfg(feature = "alloc")]
            Slab::Boxed(b) => b.as_chunks().0.get(i),
            #[cfg(feature = "alloc")]
            Slab::Store(s) => store.chunk(*s.ids.get(i)?),
        }
    }
}

/// A pool and the memory its chunks live in, for a read that holds the pool only by `&`.
#[derive(Clone, Copy)]
pub struct Mem<'m, 'p> {
    pool: &'m BufferPool<'p>,
    store: &'m ChunkStore,
}

impl<'m> Mem<'m, '_> {
    /// The bytes of `chunk`.
    pub fn bytes(self, chunk: &Chunk) -> &'m [u8] {
        self.pool
            .slab
            .get(self.store, chunk.index())
            .map_or(&[], |c| c.as_slice())
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
    /// The session's use of its endpoint's spill arena, which is not part of the chunks or the budget.
    pub(super) spill: super::spill::SpillUse<'p>,
    /// The endpoint's chunk store for the length of one call ([`lend_store`](Self::lend_store)); an empty one between
    /// calls.
    store: ChunkStore,
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

    /// A pool of up to `chunks` chunks in slot `slot` of the endpoint's store; the budget is all of them, and the pool
    /// holds only what the slot's reservation covers. Its tables are made now, so nothing is allocated later.
    #[cfg(feature = "alloc")]
    pub fn over_store(slot: usize, chunks: usize) -> Self {
        Self::with_slab(Slab::Store(StoreSlab {
            slot,
            mark: 0,
            ids: alloc::vec![NO_CHUNK; chunks.min(NO_CHUNK as usize - 1)].into_boxed_slice(),
            free: alloc::vec::Vec::with_capacity(chunks),
        }))
    }

    fn with_slab(slab: Slab<'p>) -> Self {
        let total = u32::try_from(slab.len()).unwrap_or(u32::MAX - 1);
        Self {
            slab,
            fresh: 0,
            free_head: 0,
            used: 0,
            budget: total,
            spill: super::spill::SpillUse::default(),
            store: ChunkStore::default(),
        }
    }

    /// The pool and the store it holds for this call, for a read through [`Mem`].
    pub fn mem(&self) -> Mem<'_, 'p> {
        Mem {
            pool: self,
            store: &self.store,
        }
    }

    /// The pool and `store`, which a pool over a store reads its chunks in, for a read that cannot lend the store to
    /// the pool.
    pub fn mem_in<'m>(&'m self, store: &'m ChunkStore) -> Mem<'m, 'p> {
        Mem { pool: self, store }
    }

    /// Hand the pool the endpoint's store for one call; [`return_store`](Self::return_store) gives it back. A pool's
    /// session takes its mark the first time.
    #[cfg_attr(not(feature = "alloc"), allow(unused_mut))]
    pub fn lend_store(&mut self, mut store: ChunkStore) {
        self.swap_store(&mut store);
    }

    /// Exchange the store the pool holds with `store`: lend the endpoint's store for a call, and exchange again to take
    /// it back. Cheaper than [`lend_store`](Self::lend_store) and [`return_store`](Self::return_store) on a path that
    /// runs for every datagram: nothing is built or dropped. A pool's session takes its mark the first time.
    pub fn swap_store(&mut self, store: &mut ChunkStore) {
        core::mem::swap(&mut self.store, store);
        #[cfg(feature = "alloc")]
        if let Slab::Store(s) = &mut self.slab
            && s.mark == 0
        {
            s.mark = self.store.new_mark();
        }
    }

    /// The store [`lend_store`](Self::lend_store) handed in, or an empty one if none was.
    pub fn return_store(&mut self) -> ChunkStore {
        core::mem::take(&mut self.store)
    }

    /// Count a frame held back for want of a chunk in the store this pool holds now (see
    /// [`ChunkStore::note_shortage`]); nothing for a pool with memory of its own.
    pub fn note_shortage(&mut self, first: bool) {
        #[cfg(feature = "alloc")]
        if self.slot().is_some() {
            self.store.note_shortage(first);
        }
        let _ = first;
    }

    /// The slot and its reservation, for a pool over a store that holds it now.
    #[cfg(feature = "alloc")]
    fn slot(&self) -> Option<usize> {
        match &self.slab {
            Slab::Store(s) => Some(s.slot),
            _ => None,
        }
    }

    /// Reserve, within the budget, so that `bytes` more fit beside the chunks in use, as far as the store has room;
    /// then [`available_bytes`](Self::available_bytes) says how much did. A pool over its own memory has it already.
    pub fn make_room(&mut self, bytes: u64) {
        #[cfg(feature = "alloc")]
        if let Some(slot) = self.slot() {
            self.store.grow(slot, self.want(bytes));
        }
        #[cfg(not(feature = "alloc"))]
        let _ = bytes;
    }

    /// Queue the pool's slot in the store until its reservation covers `bytes` beside the chunks in use: a grant the
    /// store had no room for. The endpoint has the session grant again once the room is reserved
    /// ([`ChunkStore::pop_ready`]). A pool over its own memory never waits.
    pub fn wait_for(&mut self, bytes: u64) {
        #[cfg(feature = "alloc")]
        if let Some(slot) = self.slot() {
            self.store.wait(slot, self.want(bytes));
        }
        #[cfg(not(feature = "alloc"))]
        let _ = bytes;
    }

    /// Take the pool's slot out of the store's queue: no grant of its session waits for room.
    pub fn stop_waiting(&mut self) {
        #[cfg(feature = "alloc")]
        if let Some(slot) = self.slot() {
            self.store.leave(slot);
        }
    }

    /// The chunks in use and `bytes` more, within the budget.
    #[cfg(feature = "alloc")]
    fn want(&self, bytes: u64) -> u32 {
        let room = u32::try_from(bytes.div_ceil(CHUNK_SIZE as u64)).unwrap_or(u32::MAX);
        self.used.saturating_add(room).min(self.budget)
    }

    /// Lower the reservation of a pool over a store to what its chunks in use and the `bytes` it still promises need,
    /// and never below its floor. A pool over its own memory keeps it all; for it this does nothing.
    pub fn trim(&mut self, bytes: u64) {
        #[cfg(feature = "alloc")]
        if let Some(slot) = self.slot() {
            let keep = self
                .used
                .saturating_add(u32::try_from(bytes.div_ceil(CHUNK_SIZE as u64)).unwrap_or(u32::MAX));
            self.store.shrink(slot, keep);
        }
        #[cfg(not(feature = "alloc"))]
        let _ = bytes;
    }

    /// Forget every chunk handed out, so the pool is as new: for a pool whose connection ended. Every
    /// [`Chunk`] taken before is dead and must be dropped, not freed. A pool over a store gives its chunks back with
    /// [`release`](Self::release) instead.
    pub fn reset(&mut self) {
        self.fresh = 0;
        self.free_head = 0;
        self.used = 0;
        self.reset_spill_counts();
    }

    /// As [`reset`](Self::reset), and give every chunk and everything the slot reserved above its floor back to
    /// `store`; the slot's next session takes a new mark, so it reads zeros where this one wrote.
    #[cfg_attr(not(feature = "alloc"), allow(unused_variables))]
    pub fn release(&mut self, store: &mut ChunkStore) {
        #[cfg(feature = "alloc")]
        if let Slab::Store(s) = &mut self.slab {
            for id in &mut s.ids {
                let id = core::mem::replace(id, NO_CHUNK);
                if id != NO_CHUNK {
                    store.give(id);
                }
            }
            s.free.clear();
            s.mark = 0;
            store.release(s.slot);
        }
        self.reset();
    }

    /// Chunks of memory the pool holds now: every one of them, or for a pool over a store those it has taken.
    pub fn held_chunks(&self) -> usize {
        match self.slab {
            #[cfg(feature = "alloc")]
            Slab::Store(_) => self.used as usize,
            _ => self.slab.len(),
        }
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
    /// [`PoolExhausted`] when the budget or the slab is used up, or for a pool over a store, when the store has no
    /// room for one more beside its reservation.
    pub fn alloc_chunk(&mut self) -> Result<Chunk, PoolExhausted> {
        if self.used >= self.budget {
            return Err(PoolExhausted);
        }
        #[cfg(feature = "alloc")]
        if let Slab::Store(s) = &mut self.slab {
            if self.used >= self.store.grow(s.slot, self.used + 1) {
                return Err(PoolExhausted);
            }
            let i = match s.free.pop() {
                Some(i) => i,
                None if (self.fresh as usize) < s.ids.len() => {
                    self.fresh += 1;
                    self.fresh - 1
                }
                None => return Err(PoolExhausted),
            };
            let (Some(id), Some(entry)) = (self.store.take(s.mark), s.ids.get_mut(i as usize)) else {
                s.free.push(i);
                return Err(PoolExhausted);
            };
            *entry = id;
            self.used += 1;
            return NonZeroU32::new(i + 1).map(Chunk).ok_or(PoolExhausted);
        }
        let index = if let Some(head) = NonZeroU32::new(self.free_head) {
            let chunk = Chunk(head);
            let next = self
                .slab
                .get(&self.store, chunk.index())
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

    /// Return a chunk to the free list and release its charge. A pool over a store gives it back only while the store
    /// is lent; a chunk it cannot give back stays its own until [`release`](Self::release).
    #[allow(
        clippy::needless_pass_by_value,
        reason = "consuming the handle is what rules out a double free"
    )]
    pub fn free_chunk(&mut self, chunk: Chunk) {
        #[cfg(feature = "alloc")]
        if let Slab::Store(s) = &mut self.slab {
            if let Some(id) = s.ids.get_mut(chunk.index())
                && *id != NO_CHUNK
                && self.store.give(*id)
            {
                *id = NO_CHUNK;
                s.free.push(chunk.0.get() - 1);
                self.used = self.used.saturating_sub(1);
            }
            return;
        }
        let head = self.free_head;
        if let Some(first) = self.bytes_mut(&chunk).first_chunk_mut::<4>() {
            *first = head.to_le_bytes();
            self.free_head = chunk.0.get();
            self.used = self.used.saturating_sub(1);
        }
    }

    /// The bytes of `chunk`.
    pub fn bytes(&self, chunk: &Chunk) -> &[u8] {
        self.mem().bytes(chunk)
    }

    /// The bytes of `chunk`, writable.
    pub fn bytes_mut(&mut self, chunk: &Chunk) -> &mut [u8] {
        let i = chunk.index();
        let c = match &mut self.slab {
            Slab::Borrowed(s) => s.get_mut(i),
            #[cfg(feature = "alloc")]
            Slab::Boxed(b) => b.as_chunks_mut().0.get_mut(i),
            #[cfg(feature = "alloc")]
            Slab::Store(s) => s.ids.get(i).and_then(|id| self.store.chunk_mut(*id)),
        };
        c.map_or(&mut [], |c| c.as_mut_slice())
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

    /// Chunks that can still be allocated: for a pool over a store, those its reservation covers now.
    pub fn available_chunks(&self) -> usize {
        self.mem().available_chunks()
    }

    /// Bytes that can still be allocated.
    pub fn available_bytes(&self) -> u64 {
        self.mem().available_bytes()
    }

    /// See [`Mem::room_bytes`].
    pub fn room_bytes(&self) -> u64 {
        self.mem().room_bytes()
    }
}

impl Mem<'_, '_> {
    /// Chunks that can still be allocated: for a pool over a store, those its reservation covers now.
    pub fn available_chunks(self) -> usize {
        let p = self.pool;
        #[cfg(feature = "alloc")]
        if let Some(slot) = p.slot() {
            return self.store.reserved(slot).min(p.budget).saturating_sub(p.used) as usize;
        }
        let slab_left = p.slab.len() - p.fresh as usize;
        let free_listed = (p.fresh - p.used.min(p.fresh)) as usize;
        (p.budget.saturating_sub(p.used) as usize).min(slab_left + free_listed)
    }

    /// Bytes that can still be allocated.
    pub fn available_bytes(self) -> u64 {
        self.available_chunks() as u64 * CHUNK_SIZE as u64
    }

    /// Bytes the pool could hold beyond those in use, the burst room it may still reserve counted beside its
    /// reservation, within the budget: what a soft promise (stream credit, which takes no chunk until data arrives and
    /// whose data is held back when none is free) is measured against. While other slots wait for room, only the
    /// oldest may reserve more, so the others count none. Growing the reservation moves room from the burst room into
    /// it, so it leaves this sum alone. A pool over its own memory has [`available_bytes`](Self::available_bytes).
    pub fn room_bytes(self) -> u64 {
        #[cfg(feature = "alloc")]
        if let Some(slot) = self.pool.slot() {
            let reserved = self.store.reserved(slot).min(self.pool.budget);
            let more = u64::from(self.pool.budget - reserved).min(self.store.burst_for(slot));
            return self.available_bytes() + more * CHUNK_SIZE as u64;
        }
        self.available_bytes()
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
    pub(super) fn span<'a>(&self, mem: Mem<'a, '_>, k: u64, from: usize, len: usize) -> Option<&'a [u8]> {
        let chunk = self.slot(k)?;
        mem.bytes(&chunk).get(from..from.checked_add(len)?)
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
            let Some(src) = self.span(pool.mem(), k, at, take) else {
                break;
            };
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
            if self.span(pool.mem(), k, at, take) != Some(head) {
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

    use super::super::store::{ChunkStore, floor_chunks};

    /// Run `f` on `pool` with `store` lent to it, as an endpoint lends its store for one call.
    fn lent<R>(
        pool: &mut BufferPool<'static>,
        store: &mut ChunkStore,
        f: impl FnOnce(&mut BufferPool<'static>) -> R,
    ) -> R {
        pool.lend_store(core::mem::take(store));
        let r = f(pool);
        *store = pool.return_store();
        r
    }

    fn take(pool: &mut BufferPool<'static>, store: &mut ChunkStore, n: usize) -> alloc::vec::Vec<Chunk> {
        lent(pool, store, |p| (0..n).map(|_| p.alloc_chunk().unwrap()).collect())
    }

    #[test]
    fn a_pool_over_a_store_takes_its_chunks_from_it_and_gives_them_straight_back() {
        let mut store = ChunkStore::new(64, 2, 32);
        let mut pool = BufferPool::over_store(0, 32);
        assert_eq!(pool.mem_in(&store).available_chunks(), floor_chunks(32));
        lent(&mut pool, &mut store, |p| p.make_room(20 * CHUNK_SIZE as u64));
        assert_eq!(pool.mem_in(&store).available_chunks(), 20);
        let held = take(&mut pool, &mut store, 20);
        lent(&mut pool, &mut store, |p| {
            for (i, ch) in held.iter().enumerate() {
                p.bytes_mut(ch).fill(u8::try_from(i).unwrap());
            }
        });
        for (i, ch) in held.iter().enumerate() {
            let v = u8::try_from(i).unwrap();
            let bytes = pool.mem_in(&store).bytes(ch);
            assert!(bytes.len() == CHUNK_SIZE && bytes.iter().all(|x| *x == v));
        }
        assert_eq!(
            (pool.held_chunks(), store.stats().used, store.stats().touched),
            (20, 20, 20)
        );
        lent(&mut pool, &mut store, |p| {
            for ch in held {
                p.free_chunk(ch);
            }
        });
        // A quiet session holds no chunk: they are all in the store, which keeps their memory for any session.
        assert_eq!(
            (pool.held_chunks(), store.stats().used, store.stats().touched),
            (0, 0, 20)
        );
        // Its reservation stays until a trim lowers it, never below the floor; the session's end gives it all back.
        let floors = 2 * floor_chunks(32) as u64;
        assert_eq!(store.stats().reserved, floors - floor_chunks(32) as u64 + 20);
        lent(&mut pool, &mut store, |p| p.trim(0));
        assert_eq!(store.stats().reserved, floors);
        pool.release(&mut store);
        assert_eq!((store.stats().used, store.stats().reserved), (0, floors));
    }

    #[test]
    fn every_slot_keeps_its_floor_whatever_another_takes_so_none_is_refused() {
        let floor = floor_chunks(64);
        let mut store = ChunkStore::new(2 * floor + 4, 2, 64);
        let (mut a, mut b) = (BufferPool::over_store(0, 64), BufferPool::over_store(1, 64));
        // a takes its floor and the whole burst room, and no more.
        lent(&mut a, &mut store, |p| p.make_room(64 * CHUNK_SIZE as u64));
        assert_eq!(a.mem_in(&store).available_chunks(), floor + 4);
        let held = take(&mut a, &mut store, floor + 4);
        assert_eq!(lent(&mut a, &mut store, BufferPool::alloc_chunk), Err(PoolExhausted));
        assert!(store.stats().full > 0, "the refusal is counted");
        // b still has its floor, and only its floor: the burst room is a's until a gives it back.
        assert_eq!(b.mem_in(&store).room_bytes(), (floor * CHUNK_SIZE) as u64);
        let own = take(&mut b, &mut store, floor);
        assert_eq!(lent(&mut b, &mut store, BufferPool::alloc_chunk), Err(PoolExhausted));
        // a's session ends: its chunks and burst go back, and b may grow into them.
        drop(held);
        a.release(&mut store);
        assert_eq!(
            b.mem_in(&store).room_bytes(),
            ((floor + 4) * CHUNK_SIZE) as u64 - (floor * CHUNK_SIZE) as u64
        );
        lent(&mut b, &mut store, |p| own.into_iter().for_each(|ch| p.free_chunk(ch)));
    }

    #[test]
    fn a_chunk_another_session_held_is_zeroed_and_one_the_session_held_is_not() {
        let mut store = ChunkStore::new(16, 2, 16);
        let mut a = BufferPool::over_store(0, 16);
        let held = take(&mut a, &mut store, 8);
        lent(&mut a, &mut store, |p| {
            for ch in &held {
                p.bytes_mut(ch).fill(0xa5);
            }
            for ch in held {
                p.free_chunk(ch);
            }
        });
        // The same session takes its own bytes back as they were.
        let own = take(&mut a, &mut store, 3);
        assert!(own.iter().all(|c| a.mem_in(&store).bytes(c).iter().all(|x| *x == 0xa5)));
        drop(own);
        a.release(&mut store);
        // Another session, and the slot's next session, get zeros.
        let mut b = BufferPool::over_store(1, 16);
        let other = take(&mut b, &mut store, 8);
        assert!(other.iter().all(|c| b.mem_in(&store).bytes(c).iter().all(|x| *x == 0)));
        b.release(&mut store);
        let next = take(&mut a, &mut store, 8);
        assert!(next.iter().all(|c| a.mem_in(&store).bytes(c).iter().all(|x| *x == 0)));
    }

    #[test]
    fn the_floor_is_two_first_charges_and_never_passes_half_the_pool_each_way() {
        assert_eq!(floor_chunks(1024), 8);
        assert_eq!(floor_chunks(16), 8);
        assert_eq!(floor_chunks(8), 8);
        assert_eq!(floor_chunks(6), 6);
        assert_eq!(floor_chunks(1), 0);
        for chunks in 0..=64 {
            assert!(floor_chunks(chunks) <= chunks);
        }
    }

    #[test]
    fn a_pool_over_a_store_and_a_flat_one_behave_alike() {
        // The same script of takes and returns gives the same handles, the same counts and the same refusals.
        let mut store = ChunkStore::new(64, 1, 21);
        let (mut shared, mut flat) = (BufferPool::over_store(0, 21), BufferPool::new_boxed(21));
        shared.lend_store(core::mem::take(&mut store));
        shared.make_room(21 * CHUNK_SIZE as u64);
        let (mut held_shared, mut held_flat) = (alloc::vec::Vec::new(), alloc::vec::Vec::new());
        let mut seed = 0x9E37_79B9_7F4A_7C15_u64;
        for _ in 0..2000 {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            if !(seed >> 33).is_multiple_of(3) || held_shared.is_empty() {
                let (a, b) = (shared.alloc_chunk(), flat.alloc_chunk());
                assert_eq!(a.is_ok(), b.is_ok());
                if let (Ok(a), Ok(b)) = (a, b) {
                    assert_eq!(a, b);
                    held_shared.push(a);
                    held_flat.push(b);
                }
            } else {
                let i = usize::try_from(seed >> 40).unwrap() % held_shared.len();
                shared.free_chunk(held_shared.swap_remove(i));
                flat.free_chunk(held_flat.swap_remove(i));
            }
            assert_eq!(
                (shared.used_chunks(), shared.available_chunks(), shared.budget_bytes()),
                (flat.used_chunks(), flat.available_chunks(), flat.budget_bytes())
            );
        }
    }
}
