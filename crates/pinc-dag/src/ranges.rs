//! Verified-range sets: which byte intervals of a value have been verified.
//!
//! A set holds disjoint, sorted `[start, end)` intervals of `u64` offsets, with overlapping and adjacent
//! intervals merged into one. Invariant: the set only ever grows. There is deliberately no removal, clearing or
//! shrinking API, so a byte once recorded as verified stays verified for the life of the set. Because `end` is
//! exclusive, offset `u64::MAX` can never be covered.
//!
//! [`VerifiedRanges`] is fixed-capacity and heap-free; an insert that would need more than `N` disjoint
//! intervals fails with [`CapacityError`] and changes nothing. Under the `alloc` feature,
//! [`VerifiedRangesVec`] has the same operations without a capacity limit.

use core::fmt;
use core::ops::Range;

type Interval = (u64, u64);

/// An insert would need more disjoint intervals than the set can hold; the set is unchanged.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CapacityError;

impl fmt::Display for CapacityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("verified-range set is full")
    }
}

impl core::error::Error for CapacityError {}

/// Where an inserted range lands in a sorted, merged slice: it replaces `from..to` with `merged`.
struct Plan {
    from: usize,
    to: usize,
    merged: Interval,
}

fn plan(items: &[Interval], range: &Range<u64>) -> Plan {
    let from = items.partition_point(|iv| iv.1 < range.start);
    let to = items.partition_point(|iv| iv.0 <= range.end);
    let start = items.get(from).map_or(range.start, |iv| iv.0.min(range.start));
    let end = to
        .checked_sub(1)
        .and_then(|i| items.get(i))
        .map_or(range.end, |iv| iv.1.max(range.end));
    // When nothing overlaps (`from == to`) the neighbours must not leak into the merged interval.
    let merged = if from < to {
        (start, end)
    } else {
        (range.start, range.end)
    };
    Plan { from, to, merged }
}

fn find(items: &[Interval], offset: u64) -> Option<Interval> {
    let at = items.partition_point(|iv| iv.1 <= offset);
    items.get(at).copied().filter(|iv| iv.0 <= offset)
}

fn contains_range(items: &[Interval], range: &Range<u64>) -> bool {
    range.start >= range.end || find(items, range.start).is_some_and(|iv| iv.1 >= range.end)
}

fn covered_len(items: &[Interval]) -> u64 {
    items.iter().fold(0, |acc, iv| acc.saturating_add(iv.1 - iv.0))
}

fn range_of(iv: &Interval) -> Range<u64> {
    iv.0..iv.1
}

/// A heap-free set of at most `N` disjoint, sorted, merged verified intervals. It only ever grows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedRanges<const N: usize> {
    items: [Interval; N],
    len: usize,
}

impl<const N: usize> Default for VerifiedRanges<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> VerifiedRanges<N> {
    /// An empty set.
    pub const fn new() -> Self {
        Self {
            items: [(0, 0); N],
            len: 0,
        }
    }

    fn live(&self) -> &[Interval] {
        self.items.get(..self.len).unwrap_or(&[])
    }

    /// Record `range` as verified, merging with every overlapping or adjacent interval. An empty or reversed
    /// range is a no-op.
    ///
    /// # Errors
    /// [`CapacityError`] if the result would need more than `N` intervals; the set is then unchanged.
    pub fn insert(&mut self, range: Range<u64>) -> Result<(), CapacityError> {
        if range.start >= range.end {
            return Ok(());
        }
        let Plan { from, to, merged } = plan(self.live(), &range);
        let new_len = self.len - (to - from) + 1;
        if new_len > N {
            return Err(CapacityError);
        }
        // Bounds: from <= to <= len <= N and from + 1 + (len - to) = new_len <= N.
        self.items.copy_within(to..self.len, from + 1);
        if let Some(slot) = self.items.get_mut(from) {
            *slot = merged;
        }
        self.len = new_len;
        Ok(())
    }

    /// Whether `offset` is covered.
    pub fn contains(&self, offset: u64) -> bool {
        find(self.live(), offset).is_some()
    }

    /// Whether every offset of `range` is covered; true for an empty range.
    pub fn contains_range(&self, range: Range<u64>) -> bool {
        contains_range(self.live(), &range)
    }

    /// Total number of covered offsets.
    pub fn covered_len(&self) -> u64 {
        covered_len(self.live())
    }

    /// The intervals in ascending order.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = Range<u64>> + '_ {
        self.live().iter().map(range_of)
    }

    /// The number of disjoint intervals.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Whether nothing is covered.
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The most disjoint intervals the set can hold.
    pub const fn capacity(&self) -> usize {
        N
    }
}

/// An unbounded verified-range set backed by a `Vec`; same operations and invariants as [`VerifiedRanges`].
#[cfg(feature = "alloc")]
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct VerifiedRangesVec {
    items: alloc::vec::Vec<Interval>,
}

#[cfg(feature = "alloc")]
impl VerifiedRangesVec {
    /// An empty set.
    pub const fn new() -> Self {
        Self {
            items: alloc::vec::Vec::new(),
        }
    }

    /// Record `range` as verified, merging with every overlapping or adjacent interval. An empty or reversed
    /// range is a no-op. Never fails: there is no capacity limit.
    pub fn insert(&mut self, range: Range<u64>) {
        if range.start >= range.end {
            return;
        }
        let Plan { from, to, merged } = plan(&self.items, &range);
        self.items.splice(from..to, [merged]);
    }

    /// Whether `offset` is covered.
    pub fn contains(&self, offset: u64) -> bool {
        find(&self.items, offset).is_some()
    }

    /// Whether every offset of `range` is covered; true for an empty range.
    pub fn contains_range(&self, range: Range<u64>) -> bool {
        contains_range(&self.items, &range)
    }

    /// Total number of covered offsets.
    pub fn covered_len(&self) -> u64 {
        covered_len(&self.items)
    }

    /// The intervals in ascending order.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = Range<u64>> + '_ {
        self.items.iter().map(range_of)
    }

    /// The number of disjoint intervals.
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Whether nothing is covered.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}
