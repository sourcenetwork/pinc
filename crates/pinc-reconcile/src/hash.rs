//! The hashes of reconciliation: the range fingerprint and the item id.
//!
//! Invariants: an item maps to a point of the Ristretto group ([`item_sum`], 64 bytes of the BLAKE3 keyed XOF under
//! a public key of this crate), the sum of a range is the group sum of its items' points ([`SetSum`]), and the
//! fingerprint of a range is the BLAKE3 keyed hash of the 32-byte encoding of that sum followed by the item count as
//! eight big-endian bytes ([`Fingerprint::of`]). The sum is independent of order, adds and subtracts, so one side
//! can check a claimed difference against the whole set, and the count is part of the hash, so two sums are never
//! compared across different sizes. The keys of the item point, the fingerprint and the item id are three different
//! labels, so none says anything about another.
//!
//! The keys are public constants: they name the scheme, they are not secrets, so the guarantee does not rest on a
//! key. Making two different multisets compare equal takes either two multisets with the same sum (a discrete
//! logarithm in the Ristretto group, about 2^125 work) or a collision on the 32-byte BLAKE3 value (about 2^128
//! work). The XOR of item hashes this replaces fell to about 129 chosen items. [`FP_LEN`] is the length of the wire
//! value and of the hash it keeps.

use pinc_crypto::kdf::extract;
pub use pinc_crypto::setsum::SetSum;

/// The length of a range fingerprint on the wire: the whole BLAKE3 keyed hash.
pub const FP_LEN: usize = 32;
/// The length of an item id on the wire.
pub const ID_LEN: usize = 8;

const _: () = assert!(FP_LEN <= 32, "a fingerprint is cut from one 32-byte hash");

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

/// The key of the item point.
const KEY_POINT: [u8; 32] = key(b"vrc2p");
/// The key of the range fingerprint.
const KEY_FP: [u8; 32] = key(b"vrc2");
/// The key of the item id.
const KEY_ID: [u8; 32] = key(b"vrc1i");

/// The group point of one item: the sum of the one-item set `{item}`.
pub fn item_sum(item: &[u8]) -> SetSum {
    SetSum::of_item(&KEY_POINT, item)
}

/// The fingerprint of a range: the keyed hash of the sum of its items and their count.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fingerprint([u8; FP_LEN]);

impl Fingerprint {
    /// The fingerprint of a range whose items sum to `sum` and number `count`.
    // vertexia: one encoding per fingerprint, which is one field inversion (about 4.6 us); a batch would share it
    // across the parts of a message, but the curve library's batch function allocates and a warm session allocates
    // nothing. Upgrade: a batch encoding that writes into the caller's buffers.
    #[allow(clippy::indexing_slicing, reason = "FP_LEN is at most 32, checked above")]
    pub fn of(sum: &SetSum, count: u64) -> Self {
        let mut msg = [0u8; 40];
        msg[..32].copy_from_slice(&sum.encode());
        msg[32..].copy_from_slice(&count.to_be_bytes());
        let h = extract(&KEY_FP, &msg);
        let mut fp = [0u8; FP_LEN];
        fp.copy_from_slice(&h[..FP_LEN]);
        Self(fp)
    }

    /// The wire form.
    pub const fn to_bytes(self) -> [u8; FP_LEN] {
        self.0
    }

    /// The fingerprint of the wire form.
    pub const fn from_bytes(b: [u8; FP_LEN]) -> Self {
        Self(b)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_count_is_part_of_the_fingerprint() {
        let s = item_sum(b"a");
        assert_ne!(Fingerprint::of(&s, 1), Fingerprint::of(&s, 2));
        assert_ne!(Fingerprint::of(&SetSum::zero(), 0), Fingerprint::of(&SetSum::zero(), 1));
    }

    #[test]
    fn the_empty_range_is_pinned() {
        assert_eq!(SetSum::zero().encode(), [0u8; 32]);
        assert_eq!(Fingerprint::of(&SetSum::zero(), 0).to_bytes(), EMPTY);
    }

    #[test]
    fn the_wire_form_round_trips() {
        let fp = Fingerprint::of(&item_sum(b"x"), 1);
        assert_eq!(Fingerprint::from_bytes(fp.to_bytes()), fp);
    }

    #[test]
    fn the_three_keys_differ() {
        assert!(KEY_POINT != KEY_FP && KEY_FP != KEY_ID && KEY_POINT != KEY_ID);
    }

    #[test]
    fn a_repeated_item_does_not_collapse() {
        let (a, b) = (item_sum(b"a"), item_sum(b"b"));
        assert_ne!(Fingerprint::of(&(a + b + b), 3), Fingerprint::of(&a, 1));
        assert_ne!(Fingerprint::of(&(a + b + b), 3), Fingerprint::of(&(a + b), 2));
    }

    #[test]
    fn order_does_not_matter() {
        let (a, b) = (item_sum(b"a"), item_sum(b"b"));
        assert_eq!(Fingerprint::of(&(a + b), 2), Fingerprint::of(&(b + a), 2));
    }

    const EMPTY: [u8; 32] = [
        0x10, 0xa1, 0x57, 0xa8, 0xa6, 0x79, 0x82, 0xa0, 0xb7, 0x64, 0xb1, 0xd7, 0xda, 0x5f, 0x70, 0x7d, 0xdf, 0xe3,
        0x05, 0xe3, 0x64, 0xe9, 0x96, 0x8b, 0x7a, 0xd4, 0x8a, 0x74, 0x5a, 0xd4, 0x14, 0x1d,
    ];
}
