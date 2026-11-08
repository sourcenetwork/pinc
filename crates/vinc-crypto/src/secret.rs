//! Fixed-size secret bytes and constant-time comparison.
//!
//! Invariants: a [`Secret`] is zeroized when dropped, is never printed by `Debug`, and is compared only in constant
//! time. Tags, MACs and binders are compared with [`ct_eq`], never with `==`.

use core::fmt;

use subtle::ConstantTimeEq;
use zeroize::{Zeroize, ZeroizeOnDrop};

/// `N` secret bytes, zeroized on drop.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct Secret<const N: usize>([u8; N]);

impl<const N: usize> Secret<N> {
    /// Wrap `bytes`. The caller's copy is not erased.
    pub const fn new(bytes: [u8; N]) -> Self {
        Self(bytes)
    }

    /// The secret bytes.
    pub const fn expose(&self) -> &[u8; N] {
        &self.0
    }
}

impl<const N: usize> PartialEq for Secret<N> {
    fn eq(&self, other: &Self) -> bool {
        self.0.ct_eq(&other.0).into()
    }
}

impl<const N: usize> Eq for Secret<N> {}

impl<const N: usize> fmt::Debug for Secret<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Secret(..)")
    }
}

/// Compare two byte strings in constant time (in their contents; a difference in length returns early).
///
/// Use it for tags, MACs, binders and tokens.
pub fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    a.ct_eq(b).into()
}
