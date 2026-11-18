//! A bounded set of disjoint byte ranges with insert and remove, held inline and, past its inline capacity, in one
//! slot of the endpoint's spill arena.
//!
//! Invariants: the intervals are sorted, disjoint and non-adjacent (adjacent ones merge), at most `N` are held inline
//! and at most [`SLOT_RANGES`] once spilled, and a failed insert or remove leaves the set unchanged and holds no slot it
//! did not hold before. A set that does not fit its inline array takes a slot of the arena and moves into it (spills);
//! a spilled set that holds at most `N / 2` intervals after a change moves back inline and returns its slot in the same
//! call, and [`RangeSet::clear`] returns it too. With no slot to take the operation fails as it would at `N`, so the
//! set's owner does what it did before the arena existed. While spilled, the first inline entry mirrors the lowest
//! interval, so [`RangeSet::first`] reads no slot. It tracks the received ranges of a stream, the acknowledged ranges
//! of a send buffer and the lost ranges waiting to be sent again.

use core::ops::Range;

use super::pool::BufferPool;
use super::spill::{SLOT_RANGES, SpillArena, SpillRef};

/// The set would need more than its capacity of intervals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RangeFull;

type Interval = (u64, u64);

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

/// A spill slot read as intervals: a start and an end word each.
struct Words<'a>(&'a [u64]);
/// A spill slot written as intervals.
struct WordsMut<'a>(&'a mut [u64]);

fn decode(w: &[u64], i: usize) -> Interval {
    let word = |k: usize| w.get(k).copied().unwrap_or(0);
    (word(2 * i), word(2 * i + 1))
}

impl Get for Words<'_> {
    fn at(&self, i: usize) -> Interval {
        decode(self.0, i)
    }
}

impl Get for WordsMut<'_> {
    fn at(&self, i: usize) -> Interval {
        decode(self.0, i)
    }
}

impl Store for WordsMut<'_> {
    fn put(&mut self, i: usize, iv: Interval) {
        if let Some([s, e]) = self.0.get_mut(2 * i..2 * i + 2) {
            (*s, *e) = iv;
        }
    }

    fn shift(&mut self, src: Range<usize>, dest: usize) {
        let (from, to) = (2 * src.start..2 * src.end, 2 * dest);
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
enum View<'a> {
    Inline(&'a [Interval]),
    Spilled(&'a [u64]),
}

impl View<'_> {
    fn at(&self, i: usize) -> Interval {
        match self {
            Self::Inline(s) => s.at(i),
            Self::Spilled(w) => decode(w, i),
        }
    }

    fn partition(&self, len: usize, pred: impl Fn(Interval) -> bool) -> usize {
        match self {
            Self::Inline(s) => partition(*s, len, pred),
            Self::Spilled(w) => partition(&Words(w), len, pred),
        }
    }
}

/// At most `N` disjoint intervals of `u64` offsets inline, or [`SLOT_RANGES`] in one spill slot.
#[derive(Debug)]
pub(super) struct RangeSet<const N: usize> {
    items: [Interval; N],
    len: usize,
    spill: Option<SpillRef>,
    /// Spills since the owner last read the count.
    spills: u32,
}

impl<const N: usize> RangeSet<N> {
    pub(super) const EMPTY: Self = Self {
        items: [(0, 0); N],
        len: 0,
        spill: None,
        spills: 0,
    };

    /// The intervals and how many there are. A spilled set whose slot cannot be read (never: see the arena's module
    /// docs) reads as empty.
    fn view<'a>(&'a self, pool: &'a BufferPool<'_>) -> (View<'a>, usize) {
        self.view_of(self.spill.as_ref().map(|r| pool.spill_read(r)))
    }

    /// As [`view`](Self::view), reading a spilled set from `arena` while it is not lent to the pool.
    fn view_in<'a>(&'a self, arena: &'a SpillArena<'_>) -> (View<'a>, usize) {
        self.view_of(self.spill.as_ref().map(|r| arena.read(r)))
    }

    fn view_of<'a>(&'a self, spilled: Option<Option<&'a [u64]>>) -> (View<'a>, usize) {
        match spilled {
            Some(Some(w)) => (View::Spilled(w), self.len),
            Some(None) => (View::Inline(&[]), 0),
            None => (View::Inline(self.items.get(..self.len).unwrap_or(&[])), self.len),
        }
    }

    /// The stored intervals, ascending.
    #[cfg(any(test, feature = "trace"))]
    pub(super) fn to_vec(&self, pool: &BufferPool<'_>) -> alloc::vec::Vec<Interval> {
        let (v, len) = self.view(pool);
        (0..len).map(|i| v.at(i)).collect()
    }

    pub(super) const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Whether the set holds a spill slot.
    #[cfg(any(test, feature = "trace"))]
    pub(super) const fn is_spilled(&self) -> bool {
        self.spill.is_some()
    }

    /// The spills since the last call, which the owner adds to its counter.
    pub(super) fn take_spills(&mut self) -> u64 {
        u64::from(core::mem::take(&mut self.spills))
    }

    /// Empty the set and return its spill slot.
    pub(super) fn clear(&mut self, pool: &mut BufferPool<'_>) {
        self.len = 0;
        if let Some(r) = self.spill.take() {
            pool.spill_give(r);
        }
    }

    /// The lowest interval.
    pub(super) fn first(&self) -> Option<Range<u64>> {
        (self.len > 0)
            .then(|| self.items.first().map(|iv| iv.0..iv.1))
            .flatten()
    }

    /// Run `op` on the intervals, spilling into an arena slot when the inline array cannot hold the result and moving
    /// back when the result holds at most `N / 2`. `op` gets the storage, the length and the capacity, and returns the
    /// new length; on `Err` it must have changed nothing.
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
                Err(RangeFull) if N >= SLOT_RANGES => return Err(RangeFull),
                Err(RangeFull) => {}
            }
            let r = pool.spill_take().ok_or(RangeFull)?;
            let result = self.edit_spilled(pool, &r, true, op);
            if result.is_ok() && self.len > N / 2 {
                self.spill = Some(r);
                self.spills = self.spills.saturating_add(1);
            } else {
                pool.spill_give(r);
            }
            return result;
        }
        let Some(r) = self.spill.take() else {
            return Err(RangeFull);
        };
        let result = self.edit_spilled(pool, &r, false, op);
        if self.len > N / 2 {
            self.spill = Some(r);
        } else {
            pool.spill_give(r);
        }
        result
    }

    /// Run `op` in slot `r`, first copying the inline intervals in when `fill`; a result that fits in `N / 2` is copied
    /// back inline. On failure the set keeps its intervals where they were.
    fn edit_spilled<R>(
        &mut self,
        pool: &mut BufferPool<'_>,
        r: &SpillRef,
        fill: bool,
        op: impl Fn(&mut dyn Store, usize, usize) -> Result<(usize, R), RangeFull>,
    ) -> Result<R, RangeFull> {
        let Some(w) = pool.spill_write(r) else {
            return Err(RangeFull);
        };
        let mut s = WordsMut(w);
        if fill {
            for i in 0..self.len {
                s.put(i, self.items.at(i));
            }
        }
        let (len, out) = op(&mut s, self.len, SLOT_RANGES)?;
        self.len = len;
        let keep = if len > N / 2 { 1.min(len) } else { len };
        for (i, item) in self.items.iter_mut().enumerate().take(keep) {
            *item = s.at(i);
        }
        Ok(out)
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
        let (lo, hi) = {
            let (v, len) = self.view(pool);
            let at = v.partition(len, |iv| iv.0 < range.start);
            let near = if at < len {
                Some(v.at(at))
            } else {
                len.checked_sub(1).map(|i| v.at(i))
            };
            near.map_or((range.start, range.end), |iv| {
                (iv.0.min(range.start), iv.1.max(range.end))
            })
        };
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

    /// The interval that holds `at`, reading a spilled set from `arena` (the endpoint's, between calls).
    pub(super) fn containing(&self, arena: &SpillArena<'_>, at: u64) -> Option<Range<u64>> {
        let (v, len) = self.view_in(arena);
        let i = v.partition(len, |iv| iv.1 <= at);
        (i < len).then(|| v.at(i)).filter(|iv| iv.0 <= at).map(|iv| iv.0..iv.1)
    }

    /// The lowest interval that ends after `from`, reading a spilled set from `arena`.
    pub(super) fn first_ending_after(&self, arena: &SpillArena<'_>, from: u64) -> Option<Range<u64>> {
        let (v, len) = self.view_in(arena);
        let i = v.partition(len, |iv| iv.1 <= from);
        (i < len).then(|| v.at(i)).map(|iv| iv.0..iv.1)
    }

    /// The parts of the stored intervals that fall inside `range`, ascending.
    pub(super) fn overlaps<'a>(
        &'a self,
        pool: &'a BufferPool<'_>,
        range: Range<u64>,
    ) -> impl Iterator<Item = Range<u64>> + 'a {
        let (v, len) = self.view(pool);
        let from = v.partition(len, |iv| iv.1 <= range.start);
        (from..len)
            .map(move |i| v.at(i))
            .take_while(move |iv| iv.0 < range.end)
            .map(move |iv| iv.0.max(range.start)..iv.1.min(range.end))
    }

    /// The parts of `range` that no stored interval covers, ascending.
    pub(super) fn gaps<'a>(&'a self, pool: &'a BufferPool<'_>, range: Range<u64>) -> Gaps<'a> {
        let (items, len) = self.view(pool);
        Gaps {
            items,
            len,
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

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests;
