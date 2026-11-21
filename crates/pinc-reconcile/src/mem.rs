//! An in-memory [`ItemIndex`] over a sorted list, with a prefix table of sums.
//!
//! Invariants: the items are strictly ascending (checked at build time) and immutable. A range sum is the
//! difference of two prefix entries, so it costs two reads and one group subtraction however long the range, and an
//! entry costs `size_of::<SetSum>()` bytes (160 bytes, checked by a test); a rank is a binary search.

use alloc::vec::Vec;

use crate::hash::{SetSum, item_sum};
use crate::index::ItemIndex;

/// Why a [`MemIndex`] could not be built or read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemError {
    /// The items given to the builder are not strictly ascending.
    Unsorted,
    /// A read was given a buffer shorter than the item.
    BufferTooSmall,
    /// A position or range is outside the set.
    OutOfRange,
}

/// A sorted item set held in memory.
///
// vertexia: immutable arrays with a prefix table; a counted B-tree if a host needs inserts between sessions.
#[derive(Debug, Clone, Default)]
pub struct MemIndex {
    data: Vec<u8>,
    ends: Vec<usize>,
    prefix: Vec<SetSum>,
}

impl MemIndex {
    /// The index over `items`, which must be strictly ascending.
    ///
    /// # Errors
    /// [`MemError::Unsorted`] if an item is not greater than the one before.
    pub fn from_sorted<'a>(items: impl IntoIterator<Item = &'a [u8]>) -> Result<Self, MemError> {
        let mut ix = Self {
            data: Vec::new(),
            ends: Vec::new(),
            prefix: alloc::vec![SetSum::zero()],
        };
        let mut acc = SetSum::zero();
        for item in items {
            if ix.item(ix.ends.len().wrapping_sub(1)).is_some_and(|prev| prev >= item) {
                return Err(MemError::Unsorted);
            }
            ix.data.extend_from_slice(item);
            ix.ends.push(ix.data.len());
            acc += item_sum(item);
            ix.prefix.push(acc);
        }
        Ok(ix)
    }

    /// The item at position `i`.
    pub fn item(&self, i: usize) -> Option<&[u8]> {
        let end = *self.ends.get(i)?;
        let start = i.checked_sub(1).map_or(Some(0), |p| self.ends.get(p).copied())?;
        self.data.get(start..end)
    }

    /// The number of items.
    pub fn len(&self) -> usize {
        self.ends.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
    }
}

impl ItemIndex for MemIndex {
    type Error = MemError;

    fn count(&self) -> Result<usize, MemError> {
        Ok(self.len())
    }

    fn rank(&self, bound: &[u8]) -> Result<usize, MemError> {
        let (mut lo, mut hi) = (0, self.len());
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.item(mid).ok_or(MemError::OutOfRange)? < bound {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        Ok(lo)
    }

    fn read(&self, i: usize, buf: &mut [u8]) -> Result<usize, MemError> {
        let item = self.item(i).ok_or(MemError::OutOfRange)?;
        buf.get_mut(..item.len())
            .ok_or(MemError::BufferTooSmall)?
            .copy_from_slice(item);
        Ok(item.len())
    }

    fn sum(&self, a: usize, b: usize) -> Result<SetSum, MemError> {
        if a > b {
            return Err(MemError::OutOfRange);
        }
        match (self.prefix.get(a), self.prefix.get(b)) {
            (Some(&x), Some(&y)) => Ok(y - x),
            _ => Err(MemError::OutOfRange),
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests may assert")]
mod tests {
    use super::*;

    #[test]
    fn a_prefix_entry_is_160_bytes() {
        assert_eq!(core::mem::size_of::<SetSum>(), 160);
    }

    #[test]
    fn a_range_sum_is_the_sum_of_its_items() {
        let items: [&[u8]; 4] = [b"a", b"b", b"c", b"d"];
        let ix = MemIndex::from_sorted(items).unwrap();
        assert_eq!(ix.sum(1, 3), Ok(item_sum(b"b") + item_sum(b"c")));
        assert_eq!(ix.sum(2, 2), Ok(SetSum::zero()));
        assert_eq!(ix.sum(3, 2), Err(MemError::OutOfRange));
        assert_eq!(ix.sum(0, 5), Err(MemError::OutOfRange));
    }
}
