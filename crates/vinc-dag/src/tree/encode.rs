//! Range encoding: the combined stream of parent pairs and group bytes that proves a byte range.
//!
//! The stream is the pre-order walk of the group tree restricted to the nodes that intersect the range (rounded
//! out to groups): before each parent's subtrees comes its 64-byte pair, and each group's bytes appear at the
//! leaf. [`RangeEncoder`] yields that walk as [`Step`]s without touching any data, so a provider streams
//! straight from its value and outboard storage; [`encode_range`] is the in-memory convenience on top of it.

use core::ops::Range;

use super::TreeError;
use super::layout::{Layout, PARENT_LEN, STACK_CAP, left_groups};
use super::stack::Stack;

/// One element of an encoded range stream, in stream order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    /// Emit the 64-byte parent pair stored at this byte offset of the outboard.
    Parent {
        /// Byte offset of the pair in the outboard.
        outboard_offset: u64,
    },
    /// Emit `len` bytes of the value starting at `offset`: one whole group.
    Group {
        /// Byte offset of the group in the value.
        offset: u64,
        /// Length of the group in bytes (shorter only for the last group).
        len: u64,
    },
}

#[derive(Debug, Clone, Copy)]
struct Node {
    lo: u64,
    hi: u64,
    /// Pre-order index of this node among the parents (meaningful for parents only).
    idx: u64,
}

/// An iterator over the [`Step`]s of the stream proving a byte range; holds a fixed stack, no heap.
#[derive(Debug, Clone)]
pub struct RangeEncoder {
    layout: Layout,
    first: u64,
    last: u64,
    stack: Stack<Node, STACK_CAP>,
}

impl RangeEncoder {
    /// The steps proving `range` of a value with `layout`.
    ///
    /// # Errors
    /// [`TreeError::RangeOutOfBounds`] if the range is reversed or ends past the value.
    pub fn new(layout: Layout, range: &Range<u64>) -> Result<Self, TreeError> {
        let groups = layout.group_range(range)?;
        let mut stack = Stack::new(Node { lo: 0, hi: 0, idx: 0 });
        if groups.start < groups.end {
            stack.push(Node {
                lo: 0,
                hi: layout.groups(),
                idx: 0,
            })?;
        }
        Ok(Self {
            layout,
            first: groups.start,
            last: groups.end,
            stack,
        })
    }

    fn step(&mut self, node: Node) -> Result<Step, TreeError> {
        let count = node.hi - node.lo;
        if count == 1 {
            return Ok(Step::Group {
                offset: node.lo * self.layout.group_len(),
                len: self.layout.group_size(node.lo),
            });
        }
        let left = left_groups(count);
        let mid = node.lo + left;
        if mid < self.last {
            self.stack.push(Node {
                lo: mid,
                hi: node.hi,
                idx: node.idx + left,
            })?;
        }
        if mid > self.first {
            self.stack.push(Node {
                lo: node.lo,
                hi: mid,
                idx: node.idx + 1,
            })?;
        }
        Ok(Step::Parent {
            outboard_offset: node.idx * PARENT_LEN as u64,
        })
    }
}

impl Iterator for RangeEncoder {
    type Item = Result<Step, TreeError>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;
        Some(self.step(node))
    }
}

/// The size in bytes of the encoded stream for `range` of a value with `layout`.
///
/// # Errors
/// [`TreeError::RangeOutOfBounds`] if the range is reversed or ends past the value, and
/// [`TreeError::EncodedTooLong`] if the encoded stream would be longer than `u64::MAX` bytes.
pub fn encoded_len(layout: Layout, range: &Range<u64>) -> Result<u64, TreeError> {
    RangeEncoder::new(layout, range)?.try_fold(0u64, |acc, step| {
        let n = match step? {
            Step::Parent { .. } => PARENT_LEN as u64,
            Step::Group { len, .. } => len,
        };
        acc.checked_add(n).ok_or(TreeError::EncodedTooLong)
    })
}

/// Encode the stream proving `range` of `value` into `out`, returning the bytes written.
///
/// `outboard` is the outboard built for `value` with the same `log`; `out` must hold [`encoded_len`] bytes.
///
/// # Errors
/// [`TreeError::InvalidGroupSize`], [`TreeError::RangeOutOfBounds`], [`TreeError::OutboardSize`] if `outboard` is
/// not the layout's size, or [`TreeError::OutputTooSmall`].
pub fn encode_range(
    value: &[u8],
    outboard: &[u8],
    log: u32,
    range: &Range<u64>,
    out: &mut [u8],
) -> Result<usize, TreeError> {
    let len = u64::try_from(value.len()).map_err(|_| TreeError::RangeOutOfBounds)?;
    let layout = Layout::new(len, log)?;
    if u64::try_from(outboard.len()) != Ok(layout.outboard_size()) {
        return Err(TreeError::OutboardSize);
    }
    let mut at = 0usize;
    for step in RangeEncoder::new(layout, range)? {
        let src = match step? {
            Step::Parent { outboard_offset } => slice_at(outboard, outboard_offset, PARENT_LEN as u64),
            Step::Group { offset, len } => slice_at(value, offset, len),
        }
        .ok_or(TreeError::RangeOutOfBounds)?;
        let end = at.checked_add(src.len()).ok_or(TreeError::OutputTooSmall)?;
        out.get_mut(at..end)
            .ok_or(TreeError::OutputTooSmall)?
            .copy_from_slice(src);
        at = end;
    }
    Ok(at)
}

fn slice_at(data: &[u8], offset: u64, len: u64) -> Option<&[u8]> {
    let start = usize::try_from(offset).ok()?;
    data.get(start..start.checked_add(usize::try_from(len).ok()?)?)
}
