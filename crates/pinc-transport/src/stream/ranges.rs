//! A bounded set of disjoint byte ranges with insert and remove, held inline and, past its inline capacity, in one
//! chunk of the session's buffer pool.
//!
//! Invariants: the intervals are sorted, disjoint and non-adjacent (adjacent ones merge), at most `N` are held inline
//! and at most [`SPILL`] once spilled, and a failed insert or remove leaves the set unchanged. A set that does not fit
//! its inline array takes one pool chunk and moves into it (spills); the chunk is charged to the pool's budget like any
//! other, and it is returned by [`RangeSet::clear`], which every owner calls when its stream ends. With no chunk left
//! the operation fails as it would at `N`, so the set's owner falls back to what it did before the spill existed. While
//! spilled, the first inline entry mirrors the lowest interval, so [`RangeSet::first`] needs no pool. It tracks the
//! received ranges of a stream, the acknowledged ranges of a send buffer and the lost ranges waiting to be sent again.

use core::ops::Range;

use super::pool::{BufferPool, CHUNK_SIZE, Chunk};

/// The set would need more than its capacity of intervals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RangeFull;

type Interval = (u64, u64);

/// The bytes of one interval in a spill chunk: start and end, little-endian.
const IV: usize = 16;
/// The intervals a spill chunk holds.
pub(super) const SPILL: usize = CHUNK_SIZE / IV;

/// Read access to a sorted run of intervals.
trait Get {
    fn at(&self, i: usize) -> Interval;
}

/// Write access as well.
trait Store: Get {
    fn put(&mut self, i: usize, iv: Interval);
    /// Move the intervals at `src` so the first lands at `dest`.
    fn shift(&mut self, src: Range<usize>, dest: usize);
}

impl Get for [Interval] {
    fn at(&self, i: usize) -> Interval {
        self.get(i).copied().unwrap_or((0, 0))
    }
}

/// The inline array written as intervals.
struct Inline<'a>(&'a mut [Interval]);

impl Get for Inline<'_> {
    fn at(&self, i: usize) -> Interval {
        self.0.at(i)
    }
}

impl Store for Inline<'_> {
    fn put(&mut self, i: usize, iv: Interval) {
        if let Some(slot) = self.0.get_mut(i) {
            *slot = iv;
        }
    }

    fn shift(&mut self, src: Range<usize>, dest: usize) {
        if src.end <= self.0.len() && dest + src.len() <= self.0.len() {
            self.0.copy_within(src, dest);
        }
    }
}

/// A spill chunk read as intervals.
struct Bytes<'a>(&'a [u8]);
/// A spill chunk written as intervals.
struct BytesMut<'a>(&'a mut [u8]);

fn decode(b: &[u8], i: usize) -> Interval {
    let word = |k: usize| {
        b.get(k..k + 8)
            .and_then(|w| <[u8; 8]>::try_from(w).ok())
            .map_or(0, u64::from_le_bytes)
    };
    (word(i * IV), word(i * IV + 8))
}

impl Get for Bytes<'_> {
    fn at(&self, i: usize) -> Interval {
        decode(self.0, i)
    }
}

impl Get for BytesMut<'_> {
    fn at(&self, i: usize) -> Interval {
        decode(self.0, i)
    }
}

impl Store for BytesMut<'_> {
    fn put(&mut self, i: usize, iv: Interval) {
        if let Some(b) = self.0.get_mut(i * IV..i * IV + IV) {
            let (s, e) = b.split_at_mut(8);
            s.copy_from_slice(&iv.0.to_le_bytes());
            e.copy_from_slice(&iv.1.to_le_bytes());
        }
    }

    fn shift(&mut self, src: Range<usize>, dest: usize) {
        let (from, to) = (src.start * IV..src.end * IV, dest * IV);
        if from.end <= self.0.len() && to + from.len() <= self.0.len() {
            self.0.copy_within(from, to);
        }
    }
}

/// The first index in `0..len` whose interval fails `pred` (the intervals are sorted, so `pred` holds on a prefix).
fn partition<G: Get + ?Sized>(g: &G, len: usize, pred: impl Fn(Interval) -> bool) -> usize {
    let (mut lo, mut hi) = (0, len);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if pred(g.at(mid)) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

/// Merge `range` into the `len` intervals of `s`, holding at most `cap`; the new length.
fn insert_in<S: Store + ?Sized>(s: &mut S, len: usize, cap: usize, range: &Range<u64>) -> Result<usize, RangeFull> {
    let from = partition(s, len, |iv| iv.1 < range.start);
    let to = partition(s, len, |iv| iv.0 <= range.end);
    let merged = if from < to {
        (s.at(from).0.min(range.start), s.at(to - 1).1.max(range.end))
    } else {
        (range.start, range.end)
    };
    let new_len = len - (to - from) + 1;
    if new_len > cap {
        return Err(RangeFull);
    }
    s.shift(to..len, from + 1);
    s.put(from, merged);
    Ok(new_len)
}

/// Cut `range` out of the `len` intervals of `s`, holding at most `cap`; the new length.
fn remove_in<S: Store + ?Sized>(s: &mut S, len: usize, cap: usize, range: &Range<u64>) -> Result<usize, RangeFull> {
    let from = partition(s, len, |iv| iv.1 <= range.start);
    let to = partition(s, len, |iv| iv.0 < range.end);
    if from >= to {
        return Ok(len);
    }
    let first = s.at(from);
    let last = s.at(to - 1);
    let left = (first.0 < range.start).then_some((first.0, range.start));
    let right = (last.1 > range.end).then_some((range.end, last.1));
    let keep = usize::from(left.is_some()) + usize::from(right.is_some());
    let new_len = len - (to - from) + keep;
    if new_len > cap {
        return Err(RangeFull);
    }
    s.shift(to..len, from + keep);
    for (i, iv) in left.into_iter().chain(right).enumerate() {
        s.put(from + i, iv);
    }
    Ok(new_len)
}

/// Take up to `max` offsets from the lowest of the `len` intervals of `s`; the new length and the range taken.
fn take_front_in<S: Store + ?Sized>(s: &mut S, len: usize, max: u64) -> Option<(usize, Range<u64>)> {
    if len == 0 || max == 0 {
        return None;
    }
    let (start, end) = s.at(0);
    let stop = end.min(start.saturating_add(max));
    if stop == end {
        s.shift(1..len, 0);
        Some((len - 1, start..stop))
    } else {
        s.put(0, (stop, end));
        Some((len, start..stop))
    }
}

/// The intervals of a set, wherever they are held.
#[derive(Clone, Copy)]
enum View<'a> {
    Inline(&'a [Interval]),
    Spilled(&'a [u8]),
}

impl View<'_> {
    fn at(&self, i: usize) -> Interval {
        match self {
            Self::Inline(s) => s.at(i),
            Self::Spilled(b) => decode(b, i),
        }
    }

    fn partition(&self, len: usize, pred: impl Fn(Interval) -> bool) -> usize {
        match self {
            Self::Inline(s) => partition(*s, len, pred),
            Self::Spilled(b) => partition(&Bytes(b), len, pred),
        }
    }
}

/// At most `N` disjoint intervals of `u64` offsets inline, or [`SPILL`] in one pool chunk.
#[derive(Debug)]
pub(super) struct RangeSet<const N: usize> {
    items: [Interval; N],
    len: usize,
    spill: Option<Chunk>,
}

impl<const N: usize> RangeSet<N> {
    pub(super) const EMPTY: Self = Self {
        items: [(0, 0); N],
        len: 0,
        spill: None,
    };

    fn view<'a>(&'a self, pool: &'a BufferPool<'_>) -> View<'a> {
        match &self.spill {
            Some(c) => View::Spilled(pool.bytes(c)),
            None => View::Inline(self.items.get(..self.len).unwrap_or(&[])),
        }
    }

    /// The stored intervals, ascending.
    #[cfg(feature = "trace")]
    pub(super) fn to_vec(&self, pool: &BufferPool<'_>) -> alloc::vec::Vec<Interval> {
        let v = self.view(pool);
        (0..self.len).map(|i| v.at(i)).collect()
    }

    pub(super) const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Whether the set holds a pool chunk.
    pub(super) const fn is_spilled(&self) -> bool {
        self.spill.is_some()
    }

    /// Empty the set and give its spill chunk back to the pool.
    pub(super) fn clear(&mut self, pool: &mut BufferPool<'_>) {
        self.len = 0;
        if let Some(c) = self.spill.take() {
            pool.free_chunk(c);
        }
    }

    /// The lowest interval.
    pub(super) fn first(&self) -> Option<Range<u64>> {
        (self.len > 0)
            .then(|| self.items.first().map(|iv| iv.0..iv.1))
            .flatten()
    }

    /// Run `op` on the intervals, spilling into a pool chunk when the inline array cannot hold the result. `op` gets the
    /// storage, the length and the capacity, and returns the new length; on `Err` it must have changed nothing.
    fn edit<R>(
        &mut self,
        pool: &mut BufferPool<'_>,
        op: impl Fn(&mut dyn Store, usize, usize) -> Result<(usize, R), RangeFull>,
    ) -> Result<R, RangeFull> {
        if self.spill.is_none() {
            match op(&mut Inline(self.items.as_mut_slice()), self.len, N) {
                Ok((len, r)) => {
                    self.len = len;
                    return Ok(r);
                }
                Err(RangeFull) if N >= SPILL => return Err(RangeFull),
                Err(RangeFull) => {}
            }
            let chunk = pool.alloc_chunk().map_err(|_| RangeFull)?;
            let mut b = BytesMut(pool.bytes_mut(&chunk));
            for i in 0..self.len {
                b.put(i, self.items.at(i));
            }
            self.spill = Some(chunk);
        }
        let Some(chunk) = &self.spill else {
            return Err(RangeFull);
        };
        let mut b = BytesMut(pool.bytes_mut(chunk));
        let (len, r) = op(&mut b, self.len, SPILL)?;
        let head = (len > 0).then(|| b.at(0));
        self.len = len;
        if let (Some(h), Some(slot)) = (head, self.items.first_mut()) {
            *slot = h;
        }
        Ok(r)
    }

    /// The pool chunks merging `range` in would take: 1 when it needs a new interval the inline array has no room for.
    pub(super) fn insert_cost(&self, pool: &BufferPool<'_>, range: &Range<u64>) -> usize {
        if self.spill.is_some() || self.len < N || range.start >= range.end {
            return 0;
        }
        let v = self.view(pool);
        let from = v.partition(self.len, |iv| iv.1 < range.start);
        let to = v.partition(self.len, |iv| iv.0 <= range.end);
        usize::from(from == to)
    }

    /// Merge `range` in.
    pub(super) fn insert(&mut self, pool: &mut BufferPool<'_>, range: Range<u64>) -> Result<(), RangeFull> {
        if range.start >= range.end {
            return Ok(());
        }
        self.edit(pool, |s, len, cap| insert_in(s, len, cap, &range).map(|l| (l, ())))
    }

    /// Merge `range` in; when the set is full, widen it to also swallow its nearest interval so the insert always
    /// fits. The set then covers a superset of `range`. Returns whether it had to widen.
    pub(super) fn insert_widening(&mut self, pool: &mut BufferPool<'_>, range: Range<u64>) -> bool {
        if self.insert(pool, range.clone()).is_ok() {
            return false;
        }
        let v = self.view(pool);
        let at = v.partition(self.len, |iv| iv.0 < range.start);
        let near = if at < self.len {
            Some(v.at(at))
        } else {
            self.len.checked_sub(1).map(|i| v.at(i))
        };
        let (lo, hi) = near.map_or((range.start, range.end), |iv| {
            (iv.0.min(range.start), iv.1.max(range.end))
        });
        // The widened range now touches `near`, so it replaces at least one interval and fits.
        let _fits = self.insert(pool, lo..hi);
        true
    }

    /// Cut `range` out of the set. Fails (set unchanged) when the cut splits an interval and the set is full.
    pub(super) fn remove(&mut self, pool: &mut BufferPool<'_>, range: &Range<u64>) -> Result<(), RangeFull> {
        if range.start >= range.end {
            return Ok(());
        }
        self.edit(pool, |s, len, cap| remove_in(s, len, cap, range).map(|l| (l, ())))
    }

    /// Take up to `max` offsets from the lowest interval.
    pub(super) fn take_front(&mut self, pool: &mut BufferPool<'_>, max: u64) -> Option<Range<u64>> {
        if self.len == 0 || max == 0 {
            return None;
        }
        self.edit(pool, |s, len, _| take_front_in(s, len, max).ok_or(RangeFull))
            .ok()
    }

    /// The interval that holds `at`.
    pub(super) fn containing(&self, pool: &BufferPool<'_>, at: u64) -> Option<Range<u64>> {
        let v = self.view(pool);
        let i = v.partition(self.len, |iv| iv.1 <= at);
        (i < self.len)
            .then(|| v.at(i))
            .filter(|iv| iv.0 <= at)
            .map(|iv| iv.0..iv.1)
    }

    /// The lowest interval that ends after `from`.
    pub(super) fn first_ending_after(&self, pool: &BufferPool<'_>, from: u64) -> Option<Range<u64>> {
        let v = self.view(pool);
        let i = v.partition(self.len, |iv| iv.1 <= from);
        (i < self.len).then(|| v.at(i)).map(|iv| iv.0..iv.1)
    }

    /// The parts of the stored intervals that fall inside `range`, ascending.
    pub(super) fn overlaps<'a>(
        &'a self,
        pool: &'a BufferPool<'_>,
        range: Range<u64>,
    ) -> impl Iterator<Item = Range<u64>> + 'a {
        let v = self.view(pool);
        let from = v.partition(self.len, |iv| iv.1 <= range.start);
        (from..self.len)
            .map(move |i| v.at(i))
            .take_while(move |iv| iv.0 < range.end)
            .map(move |iv| iv.0.max(range.start)..iv.1.min(range.end))
    }

    /// The parts of `range` that no stored interval covers, ascending.
    pub(super) fn gaps<'a>(&'a self, pool: &'a BufferPool<'_>, range: Range<u64>) -> Gaps<'a> {
        Gaps {
            items: self.view(pool),
            len: self.len,
            at: range.start,
            end: range.end,
        }
    }
}

/// The uncovered parts of a range.
pub(super) struct Gaps<'a> {
    items: View<'a>,
    len: usize,
    at: u64,
    end: u64,
}

impl Iterator for Gaps<'_> {
    type Item = Range<u64>;

    fn next(&mut self) -> Option<Range<u64>> {
        while self.at < self.end {
            let at = self.at;
            let i = self.items.partition(self.len, |iv| iv.1 <= at);
            let next = (i < self.len).then(|| self.items.at(i));
            match next {
                Some(iv) if iv.0 <= self.at => self.at = iv.1,
                Some(iv) => {
                    let gap = self.at..iv.0.min(self.end);
                    self.at = iv.1;
                    return Some(gap);
                }
                None => {
                    let gap = self.at..self.end;
                    self.at = self.end;
                    return Some(gap);
                }
            }
        }
        None
    }
}
