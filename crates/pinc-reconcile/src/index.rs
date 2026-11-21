//! The host's item index: the sorted set, queried by position.
//!
//! Invariants: the items are distinct byte strings in strictly ascending lexicographic order, and the index does not
//! change during a session. The session holds no copy of the set; it re-reads items and range sums from here.

use crate::hash::SetSum;

/// A sorted item set with range sums, the only view of the set a session has.
///
/// Positions are ranks in the ascending order. An item is an opaque byte string of any length up to the session's
/// item limit; the order is the byte order of the whole item, so an application that wants its items ordered by an
/// id puts the id first.
pub trait ItemIndex {
    /// The host's failure: a storage error.
    type Error;

    /// The number of items.
    ///
    /// # Errors
    /// The host's error.
    fn count(&self) -> Result<usize, Self::Error>;

    /// The number of items that sort strictly below `bound`.
    ///
    /// # Errors
    /// The host's error.
    fn rank(&self, bound: &[u8]) -> Result<usize, Self::Error>;

    /// Copy the item at position `i` into `buf` and return its length; `i` is below [`count`](Self::count).
    ///
    /// # Errors
    /// The host's error, including an item longer than `buf`.
    fn read(&self, i: usize, buf: &mut [u8]) -> Result<usize, Self::Error>;

    /// The sum of [`item_sum`](crate::hash::item_sum) over the positions `a..b` (the empty sum when `a == b`), with
    /// `b` at most [`count`](Self::count). A host keeps a prefix table or a tree so this does not scan.
    ///
    /// # Errors
    /// The host's error.
    fn sum(&self, a: usize, b: usize) -> Result<SetSum, Self::Error>;
}

impl<T: ItemIndex + ?Sized> ItemIndex for &T {
    type Error = T::Error;

    fn count(&self) -> Result<usize, Self::Error> {
        (**self).count()
    }

    fn rank(&self, bound: &[u8]) -> Result<usize, Self::Error> {
        (**self).rank(bound)
    }

    fn read(&self, i: usize, buf: &mut [u8]) -> Result<usize, Self::Error> {
        (**self).read(i, buf)
    }

    fn sum(&self, a: usize, b: usize) -> Result<SetSum, Self::Error> {
        (**self).sum(a, b)
    }
}
