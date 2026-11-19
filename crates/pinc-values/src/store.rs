//! The host value store, split into the read half a server needs and the write half a fetch needs.
//!
//! # Invariants
//!
//! A store holds bytes of values by root. Only bytes the fetch verified are ever passed to [`ValueStore::write_at`]
//! and only after that is the range [`commit`](ValueStore::commit)ted, so `verified_from` never reports a byte the
//! fetch did not check against the root. The verified set only grows (it is a `pinc-dag` `VerifiedRanges`), and a
//! committed range survives a restart, which is what a resume reads. The traits are static generics: no `dyn`.

use core::ops::Range;

use pinc_dag::ranges::{CapacityError, VerifiedRanges};

/// The first interval of `set` that ends after `from`: the answer a store gives to [`ValueStore::verified_from`] when
/// it keeps its verified bytes in a `pinc-dag` `VerifiedRanges`. The set holds at most `N` intervals, so this is
/// `O(N)`.
pub fn verified_after<const N: usize>(set: &VerifiedRanges<N>, from: u64) -> Option<Range<u64>> {
    set.iter().find(|r| r.end > from)
}

/// The read side of a store: what serving a value needs.
pub trait ValueRead {
    /// The length of the value under `root` if this store holds all of it with its outboard, so it can be served.
    fn servable_len(&self, root: &[u8; 32]) -> Option<u64>;
    /// Copy value bytes at `offset` into `dst`; returns how many were copied (fewer only at the end of the value).
    fn read_at(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize;
    /// Copy outboard bytes (64-byte parent pairs in pre-order) at `offset` into `dst`; returns how many were copied.
    fn read_outboard(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize;
}

impl<T: ValueRead + ?Sized> ValueRead for &T {
    fn servable_len(&self, root: &[u8; 32]) -> Option<u64> {
        (**self).servable_len(root)
    }
    fn read_at(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        (**self).read_at(root, offset, dst)
    }
    fn read_outboard(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        (**self).read_outboard(root, offset, dst)
    }
}

/// Why the store refused a write or a commit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StoreError {
    /// The store has no room for the bytes.
    Full,
    /// The verified set has too many disjoint ranges.
    Fragmented,
}

impl From<CapacityError> for StoreError {
    fn from(_: CapacityError) -> Self {
        Self::Fragmented
    }
}

/// The write side of a store: what fetching a value needs.
pub trait ValueStore: ValueRead {
    /// The first verified interval of `root` that ends after `from` (it may start before `from`), if any.
    fn verified_from(&self, root: &[u8; 32], from: u64) -> Option<Range<u64>>;
    /// Write already verified bytes at `offset`. Not yet part of the verified set.
    ///
    /// # Errors
    /// [`StoreError::Full`] if the store cannot hold them.
    fn write_at(&mut self, root: &[u8; 32], offset: u64, data: &[u8]) -> Result<(), StoreError>;
    /// Record `range` of `root` as verified; its bytes were written with [`ValueStore::write_at`].
    ///
    /// # Errors
    /// [`StoreError::Fragmented`] if the verified set cannot take another interval.
    fn commit(&mut self, root: &[u8; 32], range: Range<u64>) -> Result<(), StoreError>;
}
