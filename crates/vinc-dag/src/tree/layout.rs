//! Tree layout arithmetic: group counts, depth, outboard size and range rounding.
//!
//! Everything here is pure `u64` arithmetic. Invariants: the group-size log is at most [`MAX_GROUP_LOG`]; a value of
//! `len` bytes has `ceil(len / group_len)` groups, so for any `len <= u64::MAX` the group count is at most 2^54 and
//! no operation overflows. The tree over groups is the BLAKE3 tree: a node of `n >= 2` groups splits into a left
//! subtree of the largest power of two strictly below `n` groups and a right subtree of the rest.

use core::ops::Range;

use super::TreeError;

/// BLAKE3 chunk size in bytes.
pub const CHUNK_LEN: u64 = 1024;
/// Largest supported group-size log (groups of 1 GiB).
pub const MAX_GROUP_LOG: u32 = 20;
/// Default group-size log: groups of 16 chunks, 16 KiB.
pub const DEFAULT_GROUP_LOG: u32 = 4;
/// Size in bytes of one parent record in the outboard and in the encoded stream.
pub const PARENT_LEN: usize = 64;
/// Capacity of the chaining-value stacks; any layout of up to 2^54 groups needs at most 55 entries.
pub(crate) const STACK_CAP: usize = 64;

/// The shape of the group tree of a value of a given length and group-size log.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Layout {
    len: u64,
    log: u32,
}

/// Number of groups in the left subtree of a node of `count >= 2` groups; 0 when `count < 2`.
pub(crate) fn left_groups(count: u64) -> u64 {
    match count.checked_sub(1) {
        Some(m) if m > 0 => 1 << m.ilog2(),
        _ => 0,
    }
}

impl Layout {
    /// The layout of a value of `len` bytes with groups of `1024 << log` bytes.
    ///
    /// # Errors
    /// [`TreeError::InvalidGroupSize`] if `log` exceeds [`MAX_GROUP_LOG`].
    pub const fn new(len: u64, log: u32) -> Result<Self, TreeError> {
        if log > MAX_GROUP_LOG {
            return Err(TreeError::InvalidGroupSize);
        }
        Ok(Self { len, log })
    }

    /// The layout for a group buffer of `group_bytes` bytes, which must be `1024 << log` for a supported `log`.
    ///
    /// # Errors
    /// [`TreeError::InvalidGroupSize`] if `group_bytes` is not such a size.
    pub fn for_group_bytes(len: u64, group_bytes: usize) -> Result<Self, TreeError> {
        let chunks = group_bytes / 1024;
        if !group_bytes.is_multiple_of(1024) || !chunks.is_power_of_two() {
            return Err(TreeError::InvalidGroupSize);
        }
        Self::new(len, chunks.trailing_zeros())
    }

    /// The value length in bytes.
    pub const fn value_len(&self) -> u64 {
        self.len
    }

    /// The group-size log: a group holds `2^log` chunks.
    pub const fn log(&self) -> u32 {
        self.log
    }

    /// The group size in bytes.
    pub const fn group_len(&self) -> u64 {
        CHUNK_LEN << self.log
    }

    /// The number of groups; 0 for an empty value.
    pub const fn groups(&self) -> u64 {
        let g = self.group_len();
        self.len / g + if self.len.is_multiple_of(g) { 0 } else { 1 }
    }

    /// The tree depth: the number of parent levels above the groups (0 for zero or one group).
    pub const fn depth(&self) -> u32 {
        let n = self.groups();
        if n <= 1 { 0 } else { 64 - (n - 1).leading_zeros() }
    }

    /// The outboard size in bytes: one 64-byte pair per parent, `groups - 1` parents.
    pub const fn outboard_size(&self) -> u64 {
        match self.groups().checked_sub(1) {
            Some(parents) => parents * PARENT_LEN as u64,
            None => 0,
        }
    }

    /// Byte length of group `index`: the group size, or the remainder for the last group; 0 past the end.
    pub const fn group_size(&self, index: u64) -> u64 {
        let start = index.saturating_mul(self.group_len());
        if start >= self.len {
            return 0;
        }
        let rest = self.len - start;
        if rest < self.group_len() {
            rest
        } else {
            self.group_len()
        }
    }

    /// The half-open group-index range covering the byte `range`, rounded out to group boundaries.
    /// An empty byte range gives an empty group range.
    ///
    /// # Errors
    /// [`TreeError::RangeOutOfBounds`] if the range is reversed or ends past the value.
    pub fn group_range(&self, range: &Range<u64>) -> Result<Range<u64>, TreeError> {
        if range.start > range.end || range.end > self.len {
            return Err(TreeError::RangeOutOfBounds);
        }
        if range.start == range.end {
            return Ok(0..0);
        }
        Ok(range.start / self.group_len()..(range.end - 1) / self.group_len() + 1)
    }
}

/// Pre-order index among the parents of the node `[lo, hi)` in the tree of `groups` leaves.
///
/// `[lo, hi)` must be a node of that tree; the walk then ends within 64 steps. A non-node yields a meaningless
/// index but still terminates.
pub(crate) fn preorder_index(groups: u64, lo: u64, hi: u64) -> u64 {
    let (mut nlo, mut nhi, mut idx) = (0, groups, 0u64);
    while (nlo, nhi) != (lo, hi) && nhi.saturating_sub(nlo) >= 2 {
        let left = left_groups(nhi - nlo);
        let mid = nlo + left;
        if hi <= mid {
            idx += 1;
            nhi = mid;
        } else {
            idx += left;
            nlo = mid;
        }
    }
    idx
}
