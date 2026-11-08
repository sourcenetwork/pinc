//! Incremental outboard construction.
//!
//! The builder hashes the value one group at a time and merges group chaining values on a fixed stack of at most
//! 64 entries, so its memory is one BLAKE3 hasher state plus that stack, whatever the value length. Because the
//! value length is declared up front, every parent's pre-order position is known when it completes, and the
//! 64-byte pair is written straight to its slot in the caller's outboard buffer. The root equals
//! `blake3::hash(value)` for every length, including 0.

use blake3::Hasher;
use blake3::hazmat::{HasherExt, Mode, merge_subtrees_non_root, merge_subtrees_root};

use super::layout::{Layout, PARENT_LEN, STACK_CAP, preorder_index};
use super::stack::Stack;
use super::{Cv, TreeError};

/// Builds the outboard and root of a value of known length from incremental input.
#[derive(Debug, Clone)]
pub struct OutboardBuilder {
    layout: Layout,
    hasher: Hasher,
    in_group: u64,
    consumed: u64,
    /// Chaining values of complete subtrees with their size in groups.
    stack: Stack<(Cv, u64), STACK_CAP>,
    root: Cv,
}

impl OutboardBuilder {
    /// A builder for a value of `len` bytes with groups of `1024 << log` bytes.
    ///
    /// # Errors
    /// [`TreeError::InvalidGroupSize`] if `log` is unsupported.
    pub fn new(len: u64, log: u32) -> Result<Self, TreeError> {
        let layout = Layout::new(len, log)?;
        let root = if len == 0 {
            *blake3::hash(b"").as_bytes()
        } else {
            [0; 32]
        };
        Ok(Self {
            layout,
            hasher: Hasher::new(),
            in_group: 0,
            consumed: 0,
            stack: Stack::new(([0; 32], 0)),
            root,
        })
    }

    /// The layout being built.
    pub const fn layout(&self) -> &Layout {
        &self.layout
    }

    /// Feed the next bytes of the value, writing every parent they complete into `out`, which must be exactly
    /// [`Layout::outboard_size`] bytes and is the same buffer on every call.
    ///
    /// # Errors
    /// [`TreeError::TooMuchData`] if `data` runs past the declared length (nothing is consumed);
    /// [`TreeError::OutboardSize`] if `out` has the wrong size.
    pub fn update(&mut self, mut data: &[u8], out: &mut [u8]) -> Result<(), TreeError> {
        if u64::try_from(out.len()) != Ok(self.layout.outboard_size()) {
            return Err(TreeError::OutboardSize);
        }
        if u64::try_from(data.len()).map_or(true, |n| n > self.layout.value_len() - self.consumed) {
            return Err(TreeError::TooMuchData);
        }
        let group = self.layout.group_len();
        while !data.is_empty() {
            if self.in_group == 0 {
                self.hasher = Hasher::new();
                self.hasher.set_input_offset(self.consumed / group * group);
            }
            let room = usize::try_from(group - self.in_group).unwrap_or(usize::MAX);
            let (head, tail) = data
                .split_at_checked(room.min(data.len()))
                .ok_or(TreeError::TooMuchData)?;
            self.hasher.update(head);
            let taken = head.len() as u64;
            self.in_group += taken;
            self.consumed += taken;
            data = tail;
            if self.in_group == group || self.consumed == self.layout.value_len() {
                self.in_group = 0;
                self.complete_group(out)?;
            }
        }
        Ok(())
    }

    /// Finish: merge the remaining subtrees and return the root, equal to `blake3::hash` of the whole value.
    ///
    /// # Errors
    /// [`TreeError::Incomplete`] if fewer bytes than the declared length were fed;
    /// [`TreeError::OutboardSize`] if `out` has the wrong size.
    pub fn finish(mut self, out: &mut [u8]) -> Result<Cv, TreeError> {
        if u64::try_from(out.len()) != Ok(self.layout.outboard_size()) {
            return Err(TreeError::OutboardSize);
        }
        if self.consumed != self.layout.value_len() {
            return Err(TreeError::Incomplete);
        }
        let n = self.layout.groups();
        while self.stack.len() >= 2 {
            let (Some((right, rs)), Some((left, ls))) = (self.stack.pop(), self.stack.pop()) else {
                break;
            };
            let size = ls + rs;
            let cv = self.parent(n - size, n, &left, &right, out)?;
            self.stack.push((cv, size))?;
        }
        Ok(self.root)
    }

    fn complete_group(&mut self, out: &mut [u8]) -> Result<(), TreeError> {
        let n = self.layout.groups();
        if n == 1 {
            self.root = *self.hasher.finalize().as_bytes();
            return Ok(());
        }
        self.stack.push((self.hasher.finalize_non_root(), 1))?;
        let done = self.consumed.div_ceil(self.layout.group_len());
        while let (Some((_, rs)), Some((_, ls))) = (self.stack.top(), self.stack.below_top()) {
            if rs != ls {
                break;
            }
            let (Some((right, _)), Some((left, _))) = (self.stack.pop(), self.stack.pop()) else {
                break;
            };
            let cv = self.parent(done - 2 * rs, done, &left, &right, out)?;
            self.stack.push((cv, 2 * rs))?;
        }
        Ok(())
    }

    /// Write the pair of node `[lo, hi)` to its pre-order slot and return its chaining value (the root, when the
    /// node spans the whole tree).
    fn parent(&mut self, lo: u64, hi: u64, left: &Cv, right: &Cv, out: &mut [u8]) -> Result<Cv, TreeError> {
        let at = preorder_index(self.layout.groups(), lo, hi) * PARENT_LEN as u64;
        let slot = usize::try_from(at)
            .ok()
            .and_then(|a| out.get_mut(a..a.checked_add(PARENT_LEN)?))
            .and_then(|s| s.split_at_mut_checked(32))
            .ok_or(TreeError::OutboardSize)?;
        slot.0.copy_from_slice(left);
        slot.1.copy_from_slice(right);
        if (lo, hi) == (0, self.layout.groups()) {
            self.root = *merge_subtrees_root(left, right, Mode::Hash).as_bytes();
            Ok(self.root)
        } else {
            Ok(merge_subtrees_non_root(left, right, Mode::Hash))
        }
    }
}

/// Build the outboard of `value` into `out` (exactly [`Layout::outboard_size`] bytes) and return the root.
///
/// # Errors
/// [`TreeError::InvalidGroupSize`] or [`TreeError::OutboardSize`].
pub fn build_outboard(value: &[u8], log: u32, out: &mut [u8]) -> Result<Cv, TreeError> {
    let mut b = OutboardBuilder::new(u64::try_from(value.len()).map_err(|_| TreeError::TooMuchData)?, log)?;
    b.update(value, out)?;
    b.finish(out)
}

/// Build the outboard of `value` into a new `Vec` and return it with the root.
///
/// # Errors
/// [`TreeError::InvalidGroupSize`], or [`TreeError::OutboardSize`] if the outboard does not fit in memory.
#[cfg(feature = "alloc")]
pub fn build_outboard_vec(value: &[u8], log: u32) -> Result<(Cv, alloc::vec::Vec<u8>), TreeError> {
    let len = u64::try_from(value.len()).map_err(|_| TreeError::TooMuchData)?;
    let size = usize::try_from(Layout::new(len, log)?.outboard_size()).map_err(|_| TreeError::OutboardSize)?;
    let mut out = alloc::vec![0; size];
    let root = build_outboard(value, log, &mut out)?;
    Ok((root, out))
}
