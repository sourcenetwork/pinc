//! A fixed-capacity stack on the caller's stack frame.
//!
//! Invariant: `len <= N`; a push beyond `N` fails with [`TreeError::StackOverflow`] and changes nothing.

use super::TreeError;

/// A heap-free LIFO of at most `N` copyable entries.
#[derive(Debug, Clone)]
pub(crate) struct Stack<T: Copy, const N: usize> {
    items: [T; N],
    len: usize,
}

impl<T: Copy, const N: usize> Stack<T, N> {
    /// An empty stack; `filler` only initialises the unused slots.
    pub(crate) const fn new(filler: T) -> Self {
        Self {
            items: [filler; N],
            len: 0,
        }
    }

    pub(crate) fn push(&mut self, item: T) -> Result<(), TreeError> {
        let slot = self.items.get_mut(self.len).ok_or(TreeError::StackOverflow)?;
        *slot = item;
        self.len += 1;
        Ok(())
    }

    pub(crate) fn pop(&mut self) -> Option<T> {
        self.len = self.len.checked_sub(1)?;
        self.items.get(self.len).copied()
    }

    pub(crate) fn top(&self) -> Option<T> {
        self.items.get(self.len.checked_sub(1)?).copied()
    }

    pub(crate) fn below_top(&self) -> Option<T> {
        self.items.get(self.len.checked_sub(2)?).copied()
    }

    pub(crate) const fn len(&self) -> usize {
        self.len
    }
}
