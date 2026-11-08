//! A bounded set of disjoint byte ranges with insert and remove.
//!
//! Invariants: the intervals are sorted, disjoint and non-adjacent (adjacent ones merge), at most `N` are held, and a
//! failed insert or remove leaves the set unchanged. It tracks the received ranges of a stream, the acknowledged ranges
//! of a send buffer and the lost ranges waiting to be sent again.

use core::ops::Range;

/// The set would need more than its capacity of intervals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RangeFull;

type Interval = (u64, u64);

/// At most `N` disjoint intervals of `u64` offsets.
#[derive(Debug, Clone)]
pub(super) struct RangeSet<const N: usize> {
    items: [Interval; N],
    len: usize,
}

impl<const N: usize> RangeSet<N> {
    pub(super) const EMPTY: Self = Self {
        items: [(0, 0); N],
        len: 0,
    };

    fn live(&self) -> &[Interval] {
        self.items.get(..self.len).unwrap_or(&[])
    }

    pub(super) const fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub(super) const fn clear(&mut self) {
        self.len = 0;
    }

    /// The lowest interval.
    pub(super) fn first(&self) -> Option<Range<u64>> {
        self.live().first().map(|iv| iv.0..iv.1)
    }

    /// Merge `range` in.
    pub(super) fn insert(&mut self, range: Range<u64>) -> Result<(), RangeFull> {
        if range.start >= range.end {
            return Ok(());
        }
        let items = self.live();
        let from = items.partition_point(|iv| iv.1 < range.start);
        let to = items.partition_point(|iv| iv.0 <= range.end);
        let merged = if from < to {
            let lo = items.get(from).map_or(range.start, |iv| iv.0.min(range.start));
            let hi = to
                .checked_sub(1)
                .and_then(|i| items.get(i))
                .map_or(range.end, |iv| iv.1.max(range.end));
            (lo, hi)
        } else {
            (range.start, range.end)
        };
        let new_len = self.len - (to - from) + 1;
        if new_len > N {
            return Err(RangeFull);
        }
        self.items.copy_within(to..self.len, from + 1);
        if let Some(slot) = self.items.get_mut(from) {
            *slot = merged;
        }
        self.len = new_len;
        Ok(())
    }

    /// Merge `range` in; when the set is full, widen it to also swallow its nearest interval so the insert always
    /// fits. The set then covers a superset of `range`. Returns whether it had to widen.
    pub(super) fn insert_widening(&mut self, range: Range<u64>) -> bool {
        if self.insert(range.clone()).is_ok() {
            return false;
        }
        let items = self.live();
        let at = items.partition_point(|iv| iv.0 < range.start);
        let near = items.get(at).or_else(|| items.last()).copied();
        let (lo, hi) = near.map_or((range.start, range.end), |iv| {
            (iv.0.min(range.start), iv.1.max(range.end))
        });
        // The widened range now touches `near`, so it replaces at least one interval and fits.
        let _fits = self.insert(lo..hi);
        true
    }

    /// Cut `range` out of the set. Fails (set unchanged) when the cut splits an interval and the set is full.
    pub(super) fn remove(&mut self, range: &Range<u64>) -> Result<(), RangeFull> {
        if range.start >= range.end {
            return Ok(());
        }
        let items = self.live();
        let from = items.partition_point(|iv| iv.1 <= range.start);
        let to = items.partition_point(|iv| iv.0 < range.end);
        if from >= to {
            return Ok(());
        }
        let left = items
            .get(from)
            .filter(|iv| iv.0 < range.start)
            .map(|iv| (iv.0, range.start));
        let right = to
            .checked_sub(1)
            .and_then(|i| items.get(i))
            .filter(|iv| iv.1 > range.end)
            .map(|iv| (range.end, iv.1));
        let keep = usize::from(left.is_some()) + usize::from(right.is_some());
        let new_len = self.len - (to - from) + keep;
        if new_len > N {
            return Err(RangeFull);
        }
        self.items.copy_within(to..self.len, from + keep);
        for (i, iv) in left.into_iter().chain(right).enumerate() {
            if let Some(slot) = self.items.get_mut(from + i) {
                *slot = iv;
            }
        }
        self.len = new_len;
        Ok(())
    }

    /// Take up to `max` offsets from the lowest interval.
    pub(super) fn take_front(&mut self, max: u64) -> Option<Range<u64>> {
        let (start, end) = *self.live().first()?;
        if max == 0 {
            return None;
        }
        let stop = end.min(start.saturating_add(max));
        if stop == end {
            self.items.copy_within(1..self.len, 0);
            self.len -= 1;
        } else if let Some(iv) = self.items.first_mut() {
            iv.0 = stop;
        }
        Some(start..stop)
    }

    /// The parts of the stored intervals that fall inside `range`, ascending.
    pub(super) fn overlaps(&self, range: Range<u64>) -> impl Iterator<Item = Range<u64>> + '_ {
        let items = self.live();
        let from = items.partition_point(|iv| iv.1 <= range.start);
        items
            .get(from..)
            .unwrap_or(&[])
            .iter()
            .take_while(move |iv| iv.0 < range.end)
            .map(move |iv| iv.0.max(range.start)..iv.1.min(range.end))
    }

    /// The parts of `range` that no stored interval covers, ascending.
    pub(super) fn gaps(&self, range: Range<u64>) -> Gaps<'_> {
        Gaps {
            items: self.live(),
            at: range.start,
            end: range.end,
        }
    }
}

/// The uncovered parts of a range.
pub(super) struct Gaps<'a> {
    items: &'a [Interval],
    at: u64,
    end: u64,
}

impl Iterator for Gaps<'_> {
    type Item = Range<u64>;

    fn next(&mut self) -> Option<Range<u64>> {
        while self.at < self.end {
            let next = self.items.get(self.items.partition_point(|iv| iv.1 <= self.at));
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
