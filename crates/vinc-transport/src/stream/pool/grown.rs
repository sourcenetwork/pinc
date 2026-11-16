//! The memory of a grown pool (vinc#158, #435): where its chunks live, the spare segments of an endpoint, and the timer
//! that gives them back to the system.
//!
//! Chunk `i` lives at a place its index fixes: each of the first [`OWN_CHUNKS`] in an allocation of its own, the others
//! in segments of `seg` chunks. A segment is reserved whole, fallibly (`Vec::try_reserve_exact`), when a chunk of it is
//! first handed out, and committed a chunk at a time as its chunks are, in the order they are, each zeroed when it is
//! first committed, so the system commits what the session uses and nothing else. Where the system refuses a segment
//! the pool counts the refusal and keeps that segment's chunks, and every later segment's until its session ends, in
//! allocations of their own. A trim or a reset frees a segment to its endpoint's spares ([`Segments`]) with the session
//! that wrote it: a session that takes its own back keeps what it committed, and one that takes another session's finds
//! it empty, so no session reads what another wrote.
//!
//! Invariants: a segment's memory never moves (its chunks are committed within the capacity reserved for it); every
//! byte a session can read through a chunk is its own or a zero; a spare segment goes back to the system only from
//! [`Segments::expire`], which the endpoint's timer calls.

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::cell::{Cell, RefCell};
use core::fmt;

use super::{CHUNK_SIZE, RawChunk};

/// The chunks of one segment of a grown pool. 2048 (32 MiB) on 64-bit Linux with glibc, which maps every request of
/// 32 MiB or more on its own whatever its dynamic threshold has moved to, commits a page only when it is written and
/// unmaps the whole request when it is freed, so freeing a segment gives its pages back to the system. One chunk
/// everywhere else: in wasm linear memory, which grows committed and never shrinks, on bare metal, on 32-bit targets
/// and under other allocators, a 32 MiB segment could be committed whole or never given back, against the memory
/// budgets of phones, browsers and embedded hosts; there a segment of one chunk is the pool of 16 KiB chunks.
pub const SEGMENT_CHUNKS: usize = if cfg!(all(
    target_os = "linux",
    target_env = "gnu",
    target_pointer_width = "64"
)) {
    2048
} else {
    1
};

// Wasm, bare metal and 32-bit targets keep the pool of 16 KiB chunks; a build of this crate with `alloc` for one of
// them checks it.
#[cfg(any(target_family = "wasm", target_os = "none", not(target_pointer_width = "64")))]
const _: () = assert!(SEGMENT_CHUNKS == 1);

/// The first chunks of a grown pool, each an allocation of its own: as many as a session holds at once to shake hands
/// and move a first request and reply (the handshake gives its chunk back before the first stream takes one, so it is
/// one at either end), and such a session maps no segment. Its chunks after these come from segments. Each more is a
/// 16 KiB chunk a quiet session leaves in the allocator's heap after a burst: about 35 KiB a session more retained in
/// `tests/vinc_client_memory.rs` for each one above one, measured at 1, 2 and 3.
pub const OWN_CHUNKS: usize = 1;

/// The period of a [`Segments`] cache, in nanoseconds (500 ms): each period the endpoint's timer gives back to the
/// system the spare segments no session took during the whole period, so a freed segment goes back between one and two
/// periods after its session last used it.
pub const SEGMENT_DECAY: u64 = 500_000_000;

/// The freed segments of the grown pools of one endpoint. A session that goes quiet frees its segments here, the next
/// one that needs a segment takes the one freed last, and only [`expire`](Self::expire), which the endpoint's timer
/// calls, gives segments back to the system: as many of the oldest as the cache held at its lowest since the last
/// expiry, the ones no session needed for a whole period. So a burst takes back the segments its quiet sessions freed
/// instead of mapping new ones, nothing is unmapped while a packet or a command is handled, and once the sessions are
/// quiet the cache empties within two periods. It never holds more segments than the endpoint's sessions held at once.
/// A segment taken by another session than the one that freed it is emptied first (its length cut to nothing, so the
/// bytes it held cannot be read and each chunk is zeroed as the new session commits it). It also counts the segments
/// the system refused. A handle: cloning it shares the cache.
#[derive(Clone, Default)]
pub struct Segments {
    inner: Rc<Spares>,
}

/// The spare segments, oldest first, and how many (read on every deadline without borrowing them); the fewest held
/// since the last expiry; when the next expiry is due; the last session numbered; the refusals.
#[derive(Default)]
struct Spares {
    held: RefCell<Vec<Spare>>,
    count: Cell<usize>,
    low: Cell<usize>,
    due: Cell<Option<u64>>,
    sessions: Cell<u64>,
    refused: Cell<u64>,
}

/// A spare segment and the session that wrote it.
struct Spare {
    bytes: Vec<u8>,
    session: u64,
}

impl fmt::Debug for Segments {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Segments")
            .field("kept", &self.kept())
            .field("refused", &self.refused())
            .finish_non_exhaustive()
    }
}

impl Segments {
    /// An empty cache.
    pub fn new() -> Self {
        Self::default()
    }

    /// A number for a new session of a pool that shares the cache, never given before.
    fn session(&self) -> u64 {
        let n = self.inner.sessions.get().wrapping_add(1);
        self.inner.sessions.set(n);
        n
    }

    /// The spare segment of at least `len` bytes freed last, if the cache has one, for `session`: as it was if that
    /// session freed it, emptied if another did.
    fn take(&self, len: usize, session: u64) -> Option<Vec<u8>> {
        let mut held = self.inner.held.borrow_mut();
        let at = held.iter().rposition(|s| s.bytes.capacity() >= len)?;
        let Spare { mut bytes, session: by } = held.remove(at);
        self.inner.count.set(held.len());
        self.inner.low.set(self.inner.low.get().min(held.len()));
        if by != session {
            bytes.clear();
        }
        Some(bytes)
    }

    /// Keep `bytes`, which `session` wrote, spare; an expiry gives it back once no session took it for a whole period.
    fn put(&self, bytes: Vec<u8>, session: u64) {
        let mut held = self.inner.held.borrow_mut();
        held.push(Spare { bytes, session });
        self.inner.count.set(held.len());
    }

    /// When [`expire`](Self::expire) is next due: `None` while the cache is empty; otherwise one period after `now`
    /// when asked first after an expiry or after the cache was empty, and the same moment until that expiry runs. The
    /// endpoint asks with the time of its last input, the input that freed the segments.
    ///
    /// The first ask after a segment became spare arms the expiry, so this has an effect: it is not a pure read. What
    /// keeps it safe to ask any number of times, and to keep the answer, is that every later ask returns the same
    /// moment until [`expire`](Self::expire) runs at it or the cache empties: a host (the node) that kept the first
    /// answer and asks again, as its debug check does, gets the same one. A change that moves the moment on a later
    /// ask (for instance, one period after each ask's `now`) breaks a host that kept it.
    pub fn deadline(&self, now: u64) -> Option<u64> {
        if self.inner.count.get() == 0 {
            self.inner.due.set(None);
            self.inner.low.set(0);
            return None;
        }
        let due = self.inner.due.get().unwrap_or(now.saturating_add(SEGMENT_DECAY));
        self.inner.due.set(Some(due));
        Some(due)
    }

    /// At or after the deadline: give the segments no session took since the last expiry back to the system, and start
    /// the next period. Before it, nothing.
    pub fn expire(&self, now: u64) {
        if self.inner.due.get().is_none_or(|d| d > now) {
            return;
        }
        let gone: Vec<_> = {
            let mut held = self.inner.held.borrow_mut();
            let n = self.inner.low.get().min(held.len());
            let gone = held.drain(..n).collect();
            self.inner.count.set(held.len());
            gone
        };
        drop(gone);
        self.inner.low.set(self.kept());
        self.inner.due.set(None);
    }

    /// How many segments the cache keeps now.
    pub fn kept(&self) -> usize {
        self.inner.count.get()
    }

    /// How many segments the system refused the pools that share the cache, in all; each such pool kept its later
    /// chunks in allocations of their own until its session ended.
    pub fn refused(&self) -> u64 {
        self.inner.refused.get()
    }
}

/// The memory of one segment.
enum Memory {
    /// Reserved whole: `bytes.len()` covers the chunks committed so far, in the order they were placed, and `next` is
    /// the next place to give.
    Reserved { bytes: Vec<u8>, next: usize },
    /// Each chunk an allocation of its own, at its offset in the segment: the system refused the segment.
    Apart(Vec<Option<Box<[u8]>>>),
}

impl Memory {
    /// A place for the chunk at offset `off` of the segment, committed and zeroed if it is new; the place plus one.
    fn place(&mut self, off: usize) -> Option<u32> {
        match self {
            Self::Reserved { bytes, next } => {
                let p = *next;
                let end = p.checked_add(1)?.checked_mul(CHUNK_SIZE)?;
                if end > bytes.capacity() {
                    return None;
                }
                if bytes.len() < end {
                    bytes.resize(end, 0);
                }
                *next = p + 1;
                u32::try_from(p + 1).ok()
            }
            Self::Apart(chunks) => {
                if chunks.len() <= off {
                    chunks.resize_with(off + 1, || None);
                }
                let c = chunks.get_mut(off)?;
                if c.is_none() {
                    *c = Some(alloc::vec![0u8; CHUNK_SIZE].into_boxed_slice());
                }
                u32::try_from(off.checked_add(1)?).ok()
            }
        }
    }

    /// The bytes of the chunk at place `p` (its offset, for chunks apart).
    fn chunk(&self, p: usize) -> Option<&RawChunk> {
        match self {
            Self::Reserved { bytes, .. } => bytes.get(p.checked_mul(CHUNK_SIZE)?..)?.first_chunk(),
            Self::Apart(chunks) => chunks.get(p)?.as_deref()?.first_chunk(),
        }
    }

    fn chunk_mut(&mut self, p: usize) -> Option<&mut RawChunk> {
        match self {
            Self::Reserved { bytes, .. } => bytes.get_mut(p.checked_mul(CHUNK_SIZE)?..)?.first_chunk_mut(),
            Self::Apart(chunks) => chunks.get_mut(p)?.as_deref_mut()?.first_chunk_mut(),
        }
    }
}

/// A grown slab: the memory of each segment, made or taken from the endpoint's spare segments when a chunk of it is
/// first handed out, and freed whole to them by a trim once none of its chunks is in use. Freed 16 KiB chunks would
/// stay in the allocator's heap, under the memory of the sessions that outlive them; a segment the system maps on its
/// own goes back to the system when it is freed. The free list of indices, most recently returned last, is the flat
/// pool's.
pub(super) struct Grown {
    /// Chunks a segment, a power of two, and its logarithm: a chunk is placed on every access, by a shift.
    pub(super) seg: usize,
    shift: u32,
    /// The memory of each segment.
    segs: Vec<Option<Memory>>,
    /// The chunks of each segment in use.
    busy: Vec<u32>,
    /// Where chunk `i` lives in its segment's memory, plus one; 0 while it has no place (it was not handed out since
    /// its segment's memory was made). The chunks with a place are what the pool may have committed.
    place: Vec<u32>,
    pub(super) cap: usize,
    free: Vec<u32>,
    /// Where freed segments go and new ones come from first.
    spare: Option<Segments>,
    /// The session the pool serves, as its spare segments know it.
    session: u64,
    /// The system refused this session a segment: its later segments keep their chunks apart.
    refused: bool,
}

impl Grown {
    pub(super) fn new(cap: usize, seg: usize) -> Self {
        Self {
            seg: seg.max(1).next_power_of_two(),
            shift: seg.max(1).next_power_of_two().trailing_zeros(),
            segs: Vec::new(),
            busy: Vec::new(),
            place: Vec::new(),
            cap,
            free: Vec::new(),
            spare: None,
            session: 0,
            refused: false,
        }
    }

    /// Take new segments from `segments` and free segments to it, as a new session.
    pub(super) fn share(&mut self, segments: &Segments) {
        self.session = segments.session();
        self.spare = Some(segments.clone());
    }

    /// The segment of chunk `i` and its offset in it.
    fn locate(&self, i: usize) -> (usize, usize) {
        match i.checked_sub(OWN_CHUNKS) {
            None => (i, 0),
            Some(j) => (OWN_CHUNKS + (j >> self.shift), j & (self.seg - 1)),
        }
    }

    /// The chunks of segment `s`, and its first chunk.
    fn span(&self, s: usize) -> (usize, usize) {
        match s.checked_sub(OWN_CHUNKS) {
            None => (1, s),
            Some(t) => (self.seg, OWN_CHUNKS.saturating_add(t.saturating_mul(self.seg))),
        }
    }

    /// New memory for segment `s`: a chunk of its own for one of the first chunks; else a spare segment, a new one, or,
    /// if the system refuses one (now or earlier in the session), chunks apart.
    fn make(&mut self, s: usize) -> Memory {
        let (width, _) = self.span(s);
        if width == 1 {
            return Memory::Reserved {
                bytes: alloc::vec![0u8; CHUNK_SIZE],
                next: 0,
            };
        }
        if !self.refused {
            // A size the system cannot hold saturates and is refused below.
            let len = width.saturating_mul(CHUNK_SIZE);
            if let Some(bytes) = self.spare.as_ref().and_then(|c| c.take(len, self.session)) {
                return Memory::Reserved { bytes, next: 0 };
            }
            let mut bytes = Vec::new();
            if bytes.try_reserve_exact(len).is_ok() {
                return Memory::Reserved { bytes, next: 0 };
            }
            self.refused = true;
            if let Some(c) = &self.spare {
                c.inner.refused.set(c.inner.refused.get().saturating_add(1));
            }
        }
        Memory::Apart(Vec::new())
    }

    /// Hand out the most recently returned chunk, or the one at the bump cursor `fresh`, with its place in its
    /// segment's memory.
    pub(super) fn take(&mut self, fresh: &mut u32) -> Option<usize> {
        let popped = self.free.last().map(|&i| i as usize);
        let i = popped.unwrap_or(*fresh as usize);
        if i >= self.cap {
            return None;
        }
        let (s, off) = self.locate(i);
        if self.segs.len() <= s {
            self.segs.resize_with(s + 1, || None);
            self.busy.resize(s + 1, 0);
        }
        if self.place.len() <= i {
            self.place.resize(i + 1, 0);
        }
        if self.segs.get(s)?.is_none() {
            let memory = self.make(s);
            *self.segs.get_mut(s)? = Some(memory);
        }
        if *self.place.get(i)? == 0 {
            let p = self.segs.get_mut(s)?.as_mut()?.place(off)?;
            *self.place.get_mut(i)? = p;
        }
        *self.busy.get_mut(s)? += 1;
        if popped.is_some() {
            self.free.pop();
        } else {
            *fresh += 1;
        }
        Some(i)
    }

    /// Take chunk `i` back; its memory stays with its segment.
    pub(super) fn give(&mut self, i: usize) {
        let s = self.locate(i).0;
        if let Some(b) = self.busy.get_mut(s) {
            *b = b.saturating_sub(1);
        }
        self.free.push(u32::try_from(i).unwrap_or(u32::MAX));
    }

    /// Free the memory of segment `s` (a segment to the spare segments, or to the system when the pool shares none; a
    /// chunk of its own or chunks apart to the allocator) and forget the places of its chunks.
    fn release(&mut self, s: usize) {
        let (width, first) = self.span(s);
        let last = first.saturating_add(width).min(self.place.len());
        if let Some(p) = self.place.get_mut(first..last) {
            p.fill(0);
        }
        if let Some(Memory::Reserved { bytes, .. }) = self.segs.get_mut(s).and_then(Option::take)
            && width > 1
            && let Some(c) = &self.spare
        {
            c.put(bytes, self.session);
        }
    }

    /// Free the memory of every segment with no chunk in use.
    pub(super) fn trim(&mut self) {
        for s in 0..self.segs.len() {
            if self.busy.get(s) == Some(&0) && self.segs.get(s).is_some_and(Option::is_some) {
                self.release(s);
            }
        }
    }

    /// Forget every chunk handed out and free their memory: the session ended, and the next one is a new session.
    pub(super) fn reset(&mut self) {
        for s in 0..self.segs.len() {
            self.release(s);
        }
        self.segs.clear();
        self.busy.clear();
        self.place.clear();
        self.free.clear();
        self.refused = false;
        if let Some(c) = &self.spare {
            self.session = c.session();
        }
    }

    /// Whether chunk `i` is in use or idle in a segment that has its memory.
    pub(super) fn has(&self, i: usize) -> bool {
        self.place.get(i).is_some_and(|p| *p != 0)
    }

    pub(super) fn chunk(&self, i: usize) -> Option<&RawChunk> {
        let p = (*self.place.get(i)? as usize).checked_sub(1)?;
        self.segs.get(self.locate(i).0)?.as_ref()?.chunk(p)
    }

    pub(super) fn chunk_mut(&mut self, i: usize) -> Option<&mut RawChunk> {
        let p = (*self.place.get(i)? as usize).checked_sub(1)?;
        let s = self.locate(i).0;
        self.segs.get_mut(s)?.as_mut()?.chunk_mut(p)
    }

    pub(super) fn held(&self) -> usize {
        self.place.iter().filter(|p| **p != 0).count()
    }
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    reason = "tests assert"
)]
mod tests;
