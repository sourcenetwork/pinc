//! Which symbols of a bundle a reception holds, counted per erasure block.
//!
//! [`HeldSet`] is what [`crate::bundle::Receiving`] records verified symbols in. Two sets implement it: the
//! fixed-capacity [`VerifiedRanges`], which refuses an insert past its interval cap, and [`BlockHeld`], one bit per
//! symbol and one count per block in a buffer the caller owns, sized from the layout, so it never refuses a symbol of
//! the bundle whatever its size or however scattered the held symbols are. A data-only reception holds one disjoint
//! run per block (parity sits between the data of consecutive blocks), which is what overflowed an interval cap.
//!
//! Invariants of [`BlockHeld`]: the count of block `b` is the number of held symbols of `b`, so it is at most the
//! block's `k + m` (proved in `proofs/lean/Pinc/DtnHeld.lean`); a symbol once held stays held; only whole symbols
//! are recorded.

use core::ops::Range;

use pinc_dag::ranges::{CapacityError, VerifiedRanges};

use crate::error::DtnError;
use crate::layout::SliceLayout;

/// A set of held byte ranges a reception records verified symbols in.
pub trait HeldSet {
    /// Record `bytes` as held. An `Err` leaves the set unchanged.
    ///
    /// # Errors
    /// [`CapacityError`] if the set cannot record the range.
    fn insert(&mut self, bytes: Range<u64>) -> Result<(), CapacityError>;

    /// Whether every byte of `bytes` is held.
    fn contains_range(&self, bytes: Range<u64>) -> bool;
}

impl<const N: usize> HeldSet for VerifiedRanges<N> {
    fn insert(&mut self, bytes: Range<u64>) -> Result<(), CapacityError> {
        Self::insert(self, bytes)
    }

    fn contains_range(&self, bytes: Range<u64>) -> bool {
        Self::contains_range(self, bytes)
    }
}

/// A set the caller keeps, lent to a reception for one call.
impl<T> HeldSet for &mut T
where
    T: HeldSet + ?Sized,
{
    fn insert(&mut self, bytes: Range<u64>) -> Result<(), CapacityError> {
        (**self).insert(bytes)
    }

    fn contains_range(&self, bytes: Range<u64>) -> bool {
        (**self).contains_range(bytes)
    }
}

/// The held symbols of one bundle: a bit per symbol, then a count per block, in the buffer `B`.
#[derive(Debug, Clone)]
pub struct BlockHeld<B> {
    g: u64,
    per: u64,
    symbols: u64,
    bits_len: usize,
    /// The held symbols, counted as they are inserted.
    held: u64,
    buf: B,
}

/// The buffer size a [`BlockHeld`] of `layout` needs: a bit per symbol and a byte per block.
///
/// # Errors
/// [`DtnError::Buffer`] if it does not fit `usize`.
pub fn held_len(layout: &SliceLayout) -> Result<usize, DtnError> {
    let blocks = usize::try_from(layout.blocks()).map_err(|_| DtnError::Buffer)?;
    bits_len(layout)?.checked_add(blocks).ok_or(DtnError::Buffer)
}

fn bits_len(layout: &SliceLayout) -> Result<usize, DtnError> {
    usize::try_from(layout.total_symbols().div_ceil(8)).map_err(|_| DtnError::Buffer)
}

fn bit(s: u64) -> Option<(usize, u8)> {
    Some((usize::try_from(s / 8).ok()?, 1 << (s % 8)))
}

impl<B> BlockHeld<B>
where
    B: AsRef<[u8]>,
{
    /// The held set of `layout` in `buf`, exactly [`held_len`] bytes: all zero for an empty set, or the buffer of an
    /// earlier set of the same layout to continue it.
    ///
    /// # Errors
    /// [`DtnError::Buffer`] if `buf` is the wrong size.
    pub fn new(layout: &SliceLayout, buf: B) -> Result<Self, DtnError> {
        if buf.as_ref().len() != held_len(layout)? {
            return Err(DtnError::Buffer);
        }
        let bits_len = bits_len(layout)?;
        let counts = buf.as_ref().get(bits_len..).unwrap_or_default();
        let held = counts.iter().map(|c| u64::from(*c)).sum();
        Ok(Self {
            g: layout.slice_len(),
            per: u64::from(layout.k()) + u64::from(layout.m()),
            symbols: layout.total_symbols(),
            bits_len,
            held,
            buf,
        })
    }

    /// Whether symbol `s` is held.
    pub fn holds(&self, s: u64) -> bool {
        s < self.symbols && bit(s).is_some_and(|(i, mask)| self.buf.as_ref().get(i).is_some_and(|b| b & mask != 0))
    }

    /// The number of held symbols of block `b`.
    pub fn count(&self, b: u64) -> usize {
        usize::try_from(b)
            .ok()
            .and_then(|b| self.bits_len.checked_add(b))
            .and_then(|i| self.buf.as_ref().get(i))
            .map_or(0, |c| usize::from(*c))
    }

    /// The bytes of every held symbol.
    pub fn covered_len(&self) -> u64 {
        self.held * self.g
    }

    /// The held symbols as maximal runs of bytes, in order.
    pub fn runs(&self) -> impl Iterator<Item = Range<u64>> + '_ {
        let mut s = 0;
        core::iter::from_fn(move || {
            while s < self.symbols && !self.holds(s) {
                s += 1;
            }
            let start = s;
            while s < self.symbols && self.holds(s) {
                s += 1;
            }
            (start < s).then(|| start * self.g..s * self.g)
        })
    }
}

impl<B> BlockHeld<B>
where
    B: AsRef<[u8]> + AsMut<[u8]>,
{
    /// Record symbol `s` as held; `false` (and nothing changes) past the last symbol.
    pub fn insert_symbol(&mut self, s: u64) -> bool {
        if s >= self.symbols {
            return false;
        }
        if self.holds(s) {
            return true;
        }
        let (Some((i, mask)), Ok(b)) = (bit(s), usize::try_from(s / self.per)) else {
            return false;
        };
        let (bits, counts) = self.buf.as_mut().split_at_mut(self.bits_len);
        let (Some(byte), Some(count)) = (bits.get_mut(i), counts.get_mut(b)) else {
            return false;
        };
        *byte |= mask;
        *count = count.saturating_add(1);
        self.held += 1;
        true
    }
}

impl<B> HeldSet for BlockHeld<B>
where
    B: AsRef<[u8]> + AsMut<[u8]>,
{
    /// Only whole symbols are recorded: a range that does not start and end on a symbol is refused.
    fn insert(&mut self, bytes: Range<u64>) -> Result<(), CapacityError> {
        let (a, b) = (bytes.start / self.g, bytes.end / self.g);
        if !bytes.start.is_multiple_of(self.g) || !bytes.end.is_multiple_of(self.g) || a > b || b > self.symbols {
            return Err(CapacityError);
        }
        for s in a..b {
            self.insert_symbol(s);
        }
        Ok(())
    }

    fn contains_range(&self, bytes: Range<u64>) -> bool {
        let (a, b) = (bytes.start / self.g, bytes.end.div_ceil(self.g));
        bytes.start >= bytes.end || (b <= self.symbols && (a..b).all(|s| self.holds(s)))
    }
}
