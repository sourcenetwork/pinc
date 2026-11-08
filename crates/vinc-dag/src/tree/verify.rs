//! Incremental range verification against a known root and value length.
//!
//! [`RangeVerifier`] consumes the stream of [`super::encode_range`] in arbitrary pieces. It keeps one buffer of
//! `GROUP` bytes (a parent pair or a group is assembled there) and a fixed stack of at most 64 pending nodes,
//! each carrying the chaining value it must hash to; there is no heap. A group's bytes are handed out only after
//! they hash to the chaining value committed by already-verified parents, so no unverified byte reaches the
//! caller. Any mismatch returns a typed error, releases nothing of the bad item and leaves the verifier failed.
//!
//! The value length is not committed separately by a BLAKE3 root: it is authenticated only by a proof that
//! reaches the last group (whose size and position bind it). A proof of earlier groups only authenticates those
//! bytes, which are true bytes of the value for any claimed length.

use core::ops::Range;

use blake3::Hasher;
use blake3::hazmat::{HasherExt, Mode, merge_subtrees_non_root, merge_subtrees_root};

use super::layout::{Layout, PARENT_LEN, STACK_CAP, left_groups};
use super::stack::Stack;
use super::{Cv, TreeError};

#[derive(Debug, Clone, Copy)]
struct Node {
    cv: Cv,
    lo: u64,
    hi: u64,
}

/// A group released by the verifier: verified bytes and where they sit in the value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Verified<'a> {
    /// Byte offset of the group in the value.
    pub offset: u64,
    /// The verified bytes of the whole group.
    pub data: &'a [u8],
}

/// The outcome of one [`RangeVerifier::feed`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fed<'a> {
    /// How many bytes of the input were consumed; feed the rest again.
    pub consumed: usize,
    /// The group that this input completed and verified, if any.
    pub verified: Option<Verified<'a>>,
}

/// Verifies a range stream against a root, one item at a time, with `GROUP` bytes of buffer.
///
/// `GROUP` must be `1024 << log` for a supported log (the group size); [`RangeVerifier::new`] rejects others.
#[derive(Debug, Clone)]
pub struct RangeVerifier<const GROUP: usize> {
    layout: Layout,
    first: u64,
    last: u64,
    root: Cv,
    stack: Stack<Node, STACK_CAP>,
    buf: [u8; GROUP],
    filled: usize,
    failed: Option<TreeError>,
}

impl<const GROUP: usize> RangeVerifier<GROUP> {
    /// A verifier for the stream proving `range` of a value of `len` bytes whose root is `root`.
    ///
    /// # Errors
    /// [`TreeError::InvalidGroupSize`] if `GROUP` is not a supported group size;
    /// [`TreeError::RangeOutOfBounds`] if the range is reversed or ends past `len`;
    /// [`TreeError::RootMismatch`] if `len` is 0 and `root` is not the hash of the empty value.
    pub fn new(root: Cv, len: u64, range: &Range<u64>) -> Result<Self, TreeError> {
        let layout = Layout::for_group_bytes(len, GROUP)?;
        let groups = layout.group_range(range)?;
        if len == 0 && root != *blake3::hash(b"").as_bytes() {
            return Err(TreeError::RootMismatch);
        }
        let mut stack = Stack::new(Node {
            cv: [0; 32],
            lo: 0,
            hi: 0,
        });
        if groups.start < groups.end {
            stack.push(Node {
                cv: root,
                lo: 0,
                hi: layout.groups(),
            })?;
        }
        Ok(Self {
            layout,
            first: groups.start,
            last: groups.end,
            root,
            stack,
            buf: [0; GROUP],
            filled: 0,
            failed: None,
        })
    }

    /// The layout of the value being verified.
    pub const fn layout(&self) -> &Layout {
        &self.layout
    }

    /// True once every group of the range has been verified and released.
    pub fn is_complete(&self) -> bool {
        self.failed.is_none() && self.stack.len() == 0
    }

    /// How many more bytes the current stream item needs; `None` when complete or failed.
    pub fn next_len(&self) -> Option<usize> {
        if self.failed.is_some() {
            return None;
        }
        self.next_item().map(|(_, need)| need - self.filled)
    }

    /// Feed stream bytes. At most one item (a parent pair or a group) is completed per call; call again with the
    /// unconsumed tail. A completed group is returned only after it verified.
    ///
    /// # Errors
    /// [`TreeError::ParentMismatch`] or [`TreeError::GroupMismatch`] on a bad item, after which every call
    /// returns the same error; [`TreeError::TooMuchData`] if the stream is already complete and `input` is not empty.
    pub fn feed(&mut self, input: &[u8]) -> Result<Fed<'_>, TreeError> {
        if let Some(e) = self.failed {
            return Err(e);
        }
        if input.is_empty() {
            return Ok(Fed {
                consumed: 0,
                verified: None,
            });
        }
        let Some((node, need)) = self.next_item() else {
            return Err(TreeError::TooMuchData);
        };
        let take = input.len().min(need - self.filled);
        let (head, _) = input.split_at_checked(take).ok_or(TreeError::TooMuchData)?;
        let dst = self
            .buf
            .get_mut(self.filled..self.filled + take)
            .ok_or(TreeError::OutputTooSmall)?;
        dst.copy_from_slice(head);
        self.filled += take;
        if self.filled < need {
            return Ok(Fed {
                consumed: take,
                verified: None,
            });
        }
        self.filled = 0;
        let released = match self.complete(node, need) {
            Ok(released) => released,
            Err(e) => {
                self.failed = Some(e);
                return Err(e);
            }
        };
        let verified = match released {
            Some(offset) => Some(Verified {
                offset,
                data: self.buf.get(..need).ok_or(TreeError::OutputTooSmall)?,
            }),
            None => None,
        };
        Ok(Fed {
            consumed: take,
            verified,
        })
    }

    fn next_item(&self) -> Option<(Node, usize)> {
        let node = self.stack.top()?;
        let size = if node.hi - node.lo == 1 {
            self.layout.group_size(node.lo)
        } else {
            PARENT_LEN as u64
        };
        Some((node, usize::try_from(size).ok()?))
    }

    fn complete(&mut self, node: Node, need: usize) -> Result<Option<u64>, TreeError> {
        let is_root = (node.lo, node.hi) == (0, self.layout.groups());
        if node.hi - node.lo == 1 {
            let data = self.buf.get(..need).ok_or(TreeError::GroupMismatch)?;
            let mut hasher = Hasher::new();
            let cv = if is_root {
                *hasher.update(data).finalize().as_bytes()
            } else {
                hasher.set_input_offset(node.lo * self.layout.group_len()).update(data);
                hasher.finalize_non_root()
            };
            if cv != node.cv {
                return Err(TreeError::GroupMismatch);
            }
            self.stack.pop();
            return Ok(Some(node.lo * self.layout.group_len()));
        }
        let (left, rest) = self.buf.split_first_chunk::<32>().ok_or(TreeError::ParentMismatch)?;
        let (right, _) = rest.split_first_chunk::<32>().ok_or(TreeError::ParentMismatch)?;
        let cv = if is_root {
            *merge_subtrees_root(left, right, Mode::Hash).as_bytes()
        } else {
            merge_subtrees_non_root(left, right, Mode::Hash)
        };
        if cv != node.cv {
            return Err(TreeError::ParentMismatch);
        }
        let (left, right) = (*left, *right);
        self.stack.pop();
        let mid = node.lo + left_groups(node.hi - node.lo);
        if mid < self.last {
            self.stack.push(Node {
                cv: right,
                lo: mid,
                hi: node.hi,
            })?;
        }
        if mid > self.first {
            self.stack.push(Node {
                cv: left,
                lo: node.lo,
                hi: mid,
            })?;
        }
        Ok(None)
    }

    /// The root this verifier checks against.
    pub const fn root(&self) -> &Cv {
        &self.root
    }
}
