//! An in-memory [`ItemIndex`] over a sorted list, with a prefix table of fingerprints.
//!
//! Invariants: the items are strictly ascending (checked at build time) and immutable. A range fingerprint is the
//! XOR of two prefix entries, so it costs two reads however long the range; a rank is a binary search.

use alloc::vec::Vec;

use crate::hash::Fingerprint;
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
    prefix: Vec<Fingerprint>,
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
            prefix: alloc::vec![Fingerprint::ZERO],
        };
        let mut acc = Fingerprint::ZERO;
        for item in items {
            if ix.item(ix.ends.len().wrapping_sub(1)).is_some_and(|prev| prev >= item) {
                return Err(MemError::Unsorted);
            }
            ix.data.extend_from_slice(item);
            ix.ends.push(ix.data.len());
            acc ^= Fingerprint::of_item(item);
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

    fn fingerprint(&self, a: usize, b: usize) -> Result<Fingerprint, MemError> {
        if a > b {
            return Err(MemError::OutOfRange);
        }
        match (self.prefix.get(a), self.prefix.get(b)) {
            (Some(&x), Some(&y)) => Ok(x ^ y),
            _ => Err(MemError::OutOfRange),
        }
    }
}
