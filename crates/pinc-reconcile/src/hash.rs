//! The keyed hashes of reconciliation: the range fingerprint and the item id.
//!
//! Invariants: both are `pinc_crypto::kdf::extract` (the BLAKE3 keyed hash) over the item bytes, truncated. The
//! fingerprint key and the id key differ, so an id says nothing about a fingerprint. A range fingerprint is the XOR
//! of the item fingerprints, so it is independent of order, and `fp(A) ^ fp(B) == fp(A xor B)` for sets: that is what
//! lets one side check a claimed difference against the whole set.

use core::ops::{BitXor, BitXorAssign};

use pinc_crypto::kdf::extract;

/// The length of a range fingerprint on the wire.
pub const FP_LEN: usize = 16;
/// The length of an item id on the wire.
pub const ID_LEN: usize = 8;

/// A 32-byte keyed-hash key made of `label` and zero padding.
#[allow(clippy::indexing_slicing, reason = "constant indexes below the array length")]
const fn key(label: &[u8]) -> [u8; 32] {
    let mut k = [0u8; 32];
    let mut i = 0;
    while i < label.len() && i < 32 {
        k[i] = label[i];
        i += 1;
    }
    k
}

const KEY_FP: [u8; 32] = key(b"vrc1");
const KEY_ID: [u8; 32] = key(b"vrc1i");

/// The XOR of the keyed hashes of a set of items; the empty set is [`Fingerprint::ZERO`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct Fingerprint(u128);

impl Fingerprint {
    /// The fingerprint of the empty set.
    pub const ZERO: Self = Self(0);

    /// The fingerprint of the one-item set `{item}`.
    #[allow(clippy::indexing_slicing, reason = "the first 16 bytes of a 32-byte array")]
    pub fn of_item(item: &[u8]) -> Self {
        let h = extract(&KEY_FP, item);
        let mut head = [0u8; FP_LEN];
        head.copy_from_slice(&h[..FP_LEN]);
        Self(u128::from_be_bytes(head))
    }

    /// The wire form, big endian.
    pub const fn to_bytes(self) -> [u8; FP_LEN] {
        self.0.to_be_bytes()
    }

    /// The fingerprint of the wire form.
    pub const fn from_bytes(b: [u8; FP_LEN]) -> Self {
        Self(u128::from_be_bytes(b))
    }
}

impl BitXor for Fingerprint {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

impl BitXorAssign for Fingerprint {
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

/// The 8-byte id of an item, used in leaf parts. Two items can share an id; the final fingerprint check catches it.
#[allow(clippy::indexing_slicing, reason = "the first 8 bytes of a 32-byte array")]
pub fn item_id(item: &[u8]) -> [u8; ID_LEN] {
    let h = extract(&KEY_ID, item);
    let mut id = [0u8; ID_LEN];
    id.copy_from_slice(&h[..ID_LEN]);
    id
}
