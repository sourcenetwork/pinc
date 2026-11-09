//! The incremental, caller-retains verifier: hash bytes where they sit, copy nothing into a group buffer.
//!
//! [`GroupVerifier`] checks the same stream as `vinc_dag::tree::RangeVerifier` (parent pairs and groups in the
//! pre-order of a range) against the same root, with the same decisions, but it never holds a group. Group bytes are
//! fed to a BLAKE3 hasher as the pieces arrive and the caller keeps the pieces (the packets) until the verifier
//! reports [`Fed::group`], when the group hash matched; the caller then writes them to the store and releases the
//! packets. A mismatch returns the error `RangeVerifier` returns and the caller drops what it kept.
//!
//! # Invariants
//!
//! - Memory is fixed: one 64-byte pair buffer, one hasher (its own one-chunk state) and a stack of at most 64
//!   pending nodes. No allocation, no group buffer.
//! - A group is reported only when its bytes hash to the chaining value committed by already verified parents, and a
//!   pair is accepted only when it merges to the chaining value it must; so a reported group is a true part of the
//!   value. Once an error is returned every later call returns it again.
//! - Decisions equal the copying verifier's for every split of the same bytes into pieces (the tests prove this by
//!   comparing both on valid and corrupted streams).
//! - [`GroupVerifier::skip_group`] passes over a group already verified elsewhere, without hashing it.

use core::ops::Range;

use blake3::Hasher;
use blake3::hazmat::{HasherExt, Mode, merge_subtrees_non_root, merge_subtrees_root};
use vinc_dag::tree::{Cv, Layout, PARENT_LEN, TreeError};

/// The depth of the node stack; any value up to 2^64 bytes needs at most 55.
const STACK: usize = 64;

#[derive(Debug, Clone, Copy)]
struct Node {
    cv: Cv,
    lo: u64,
    hi: u64,
}

/// A group whose bytes hashed to the value's committed hash.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GroupMatch {
    /// The byte offset of the group in the value.
    pub offset: u64,
    /// The group's length in bytes.
    pub len: u64,
}

/// What the next bytes of the stream must be.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Item {
    /// A 64-byte parent pair.
    Pair,
    /// A group of `len` bytes at value offset `offset`.
    Group {
        /// The byte offset of the group in the value.
        offset: u64,
        /// The group's length in bytes.
        len: u64,
    },
}

/// The outcome of one [`GroupVerifier::feed`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fed {
    /// How many bytes of the input were consumed; feed the rest again.
    pub consumed: usize,
    /// The group this input completed, if its hash matched.
    pub group: Option<GroupMatch>,
}

/// Verifies a range stream against a root as its bytes arrive, without holding a group.
#[derive(Debug, Clone)]
pub struct GroupVerifier {
    layout: Layout,
    first: u64,
    last: u64,
    stack: [Node; STACK],
    depth: usize,
    pair: [u8; PARENT_LEN],
    pair_n: usize,
    hasher: Hasher,
    group_n: u64,
    failed: Option<TreeError>,
}

impl GroupVerifier {
    /// A verifier for the stream proving `range` of a value of `len` bytes with group size `1024 << log` and `root`.
    ///
    /// # Errors
    /// [`TreeError::InvalidGroupSize`] for an unsupported `log`, [`TreeError::RangeOutOfBounds`] for a reversed range
    /// or one past `len`, [`TreeError::RootMismatch`] if `len` is 0 and `root` is not the hash of the empty value.
    pub fn new(root: Cv, len: u64, log: u32, range: &Range<u64>) -> Result<Self, TreeError> {
        let layout = Layout::new(len, log)?;
        let groups = layout.group_range(range)?;
        if len == 0 && root != *blake3::hash(b"").as_bytes() {
            return Err(TreeError::RootMismatch);
        }
        let mut v = Self {
            layout,
            first: groups.start,
            last: groups.end,
            stack: [Node {
                cv: [0; 32],
                lo: 0,
                hi: 0,
            }; STACK],
            depth: 0,
            pair: [0; PARENT_LEN],
            pair_n: 0,
            hasher: Hasher::new(),
            group_n: 0,
            failed: None,
        };
        if groups.start < groups.end {
            v.push(Node {
                cv: root,
                lo: 0,
                hi: layout.groups(),
            })?;
        }
        Ok(v)
    }

    fn push(&mut self, n: Node) -> Result<(), TreeError> {
        *self.stack.get_mut(self.depth).ok_or(TreeError::StackOverflow)? = n;
        self.depth += 1;
        Ok(())
    }

    fn top(&self) -> Option<Node> {
        self.stack.get(self.depth.checked_sub(1)?).copied()
    }

    /// The layout of the value.
    pub const fn layout(&self) -> &Layout {
        &self.layout
    }

    /// True once every group of the range has been verified and reported.
    pub const fn is_complete(&self) -> bool {
        self.failed.is_none() && self.depth == 0
    }

    /// The error that failed the verifier, if one did.
    pub const fn failure(&self) -> Option<TreeError> {
        self.failed
    }

    /// What the next bytes must be; `None` when complete or failed.
    pub fn next_item(&self) -> Option<Item> {
        if self.failed.is_some() {
            return None;
        }
        let node = self.top()?;
        Some(if node.hi - node.lo == 1 {
            Item::Group {
                offset: node.lo * self.layout.group_len(),
                len: self.layout.group_size(node.lo),
            }
        } else {
            Item::Pair
        })
    }

    /// How many bytes the current item still needs; `None` when complete or failed.
    pub fn next_len(&self) -> Option<u64> {
        Some(match self.next_item()? {
            Item::Pair => (PARENT_LEN - self.pair_n) as u64,
            Item::Group { len, .. } => len - self.group_n,
        })
    }

    /// Whether the verifier sits at the start of an item (no pair or group is half fed).
    pub const fn at_boundary(&self) -> bool {
        self.pair_n == 0 && self.group_n == 0
    }

    fn fail(&mut self, e: TreeError) -> TreeError {
        self.failed = Some(e);
        e
    }

    /// Feed stream bytes. At most one item (a pair or a group) is completed per call; call again with the unconsumed
    /// tail. A group is reported only after its hash matched; its bytes are not returned, the caller holds them.
    ///
    /// # Errors
    /// [`TreeError::ParentMismatch`] or [`TreeError::GroupMismatch`] on a bad item, after which every call returns the
    /// same error; [`TreeError::TooMuchData`] if the stream is already complete and `input` is not empty.
    pub fn feed(&mut self, input: &[u8]) -> Result<Fed, TreeError> {
        if let Some(e) = self.failed {
            return Err(e);
        }
        if input.is_empty() {
            return Ok(Fed {
                consumed: 0,
                group: None,
            });
        }
        let node = self.top().ok_or(TreeError::TooMuchData)?;
        if node.hi - node.lo == 1 {
            self.feed_group(node, input)
        } else {
            self.feed_pair(node, input)
        }
    }

    fn feed_pair(&mut self, node: Node, input: &[u8]) -> Result<Fed, TreeError> {
        let need = PARENT_LEN - self.pair_n;
        let take = input.len().min(need);
        let head = input.get(..take).ok_or(TreeError::TooMuchData)?;
        let whole = if self.pair_n == 0 && take == PARENT_LEN {
            head.first_chunk::<PARENT_LEN>().copied()
        } else {
            self.pair
                .get_mut(self.pair_n..self.pair_n + take)
                .ok_or(TreeError::OutputTooSmall)?
                .copy_from_slice(head);
            self.pair_n += take;
            None
        };
        if whole.is_none() && self.pair_n < PARENT_LEN {
            return Ok(Fed {
                consumed: take,
                group: None,
            });
        }
        let pair = whole.unwrap_or(self.pair);
        self.pair_n = 0;
        self.complete_pair(node, &pair).map_err(|e| self.fail(e))?;
        Ok(Fed {
            consumed: take,
            group: None,
        })
    }

    fn complete_pair(&mut self, node: Node, pair: &[u8; PARENT_LEN]) -> Result<(), TreeError> {
        let (left, rest) = pair.split_first_chunk::<32>().ok_or(TreeError::ParentMismatch)?;
        let (right, _) = rest.split_first_chunk::<32>().ok_or(TreeError::ParentMismatch)?;
        let is_root = (node.lo, node.hi) == (0, self.layout.groups());
        let cv = if is_root {
            *merge_subtrees_root(left, right, Mode::Hash).as_bytes()
        } else {
            merge_subtrees_non_root(left, right, Mode::Hash)
        };
        if cv != node.cv {
            return Err(TreeError::ParentMismatch);
        }
        self.depth -= 1;
        let span = node.hi - node.lo;
        let mid = node.lo
            + match span.checked_sub(1) {
                Some(m) if m > 0 => 1 << m.ilog2(),
                _ => 0,
            };
        if mid < self.last {
            self.push(Node {
                cv: *right,
                lo: mid,
                hi: node.hi,
            })?;
        }
        if mid > self.first {
            self.push(Node {
                cv: *left,
                lo: node.lo,
                hi: mid,
            })?;
        }
        Ok(())
    }

    fn feed_group(&mut self, node: Node, input: &[u8]) -> Result<Fed, TreeError> {
        let size = self.layout.group_size(node.lo);
        let is_root = (node.lo, node.hi) == (0, self.layout.groups());
        if self.group_n == 0 {
            self.hasher = Hasher::new();
            if !is_root {
                self.hasher.set_input_offset(node.lo * self.layout.group_len());
            }
        }
        let take = usize::try_from(size - self.group_n).map_or(input.len(), |n| n.min(input.len()));
        let head = input.get(..take).ok_or(TreeError::TooMuchData)?;
        self.hasher.update(head);
        self.group_n += take as u64;
        if self.group_n < size {
            return Ok(Fed {
                consumed: take,
                group: None,
            });
        }
        self.group_n = 0;
        let cv = if is_root {
            *self.hasher.finalize().as_bytes()
        } else {
            self.hasher.finalize_non_root()
        };
        if cv != node.cv {
            return Err(self.fail(TreeError::GroupMismatch));
        }
        self.depth -= 1;
        Ok(Fed {
            consumed: take,
            group: Some(GroupMatch {
                offset: node.lo * self.layout.group_len(),
                len: size,
            }),
        })
    }

    /// Pass over the next group without hashing it: the caller has it verified already (from another stream). Only
    /// valid at the start of a group item.
    ///
    /// # Errors
    /// [`TreeError::TooMuchData`] if the next item is not a whole, unstarted group.
    pub fn skip_group(&mut self) -> Result<GroupMatch, TreeError> {
        if self.failed.is_some() || !self.at_boundary() {
            return Err(TreeError::TooMuchData);
        }
        match (self.next_item(), self.top()) {
            (Some(Item::Group { offset, len }), Some(_)) => {
                self.depth -= 1;
                Ok(GroupMatch { offset, len })
            }
            _ => Err(TreeError::TooMuchData),
        }
    }
}
