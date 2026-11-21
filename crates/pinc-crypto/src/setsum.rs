//! A multiset hash: the sum of keyed hash-to-group points, so two different multisets collide only through a
//! discrete logarithm.
//!
//! Invariants: an item maps to the Ristretto point made from exactly 64 bytes of the BLAKE3 keyed XOF over the item
//! (the two-map `from_uniform_bytes` construction, uniform over the group), and a [`SetSum`] is the group sum of the
//! points of its items. The empty set is the identity, the sum does not depend on order, an item added twice counts
//! twice, and adding then subtracting an item returns the sum, so a prefix table or a tree with per-node sums answers
//! a range in constant time. Equality is the full comparison of the group element, whose canonical encoding is 32
//! bytes. Nothing here allocates, panics or reads randomness. Two different multisets with the same sum is a
//! discrete logarithm in the group (about 2^125 work for a chosen-item attacker), which the XOR of hashes it
//! replaces did not resist (about 129 chosen items solve it). The key is public: it names the scheme, it is not a
//! secret.

use core::fmt;
use core::ops::{Add, AddAssign, Neg, Sub, SubAssign};

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::traits::Identity;

/// The sum of the group points of a multiset of items; the empty multiset is [`SetSum::zero`].
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct SetSum(RistrettoPoint);

impl SetSum {
    /// The sum of the empty set: the identity of the group.
    pub fn zero() -> Self {
        Self(RistrettoPoint::identity())
    }

    /// The sum of the one-item set `{item}`: the point of 64 bytes of the BLAKE3 keyed XOF of `item` under `key`.
    pub fn of_item(key: &[u8; 32], item: &[u8]) -> Self {
        let mut uniform = [0u8; 64];
        blake3::Hasher::new_keyed(key)
            .update(item)
            .finalize_xof()
            .fill(&mut uniform);
        Self(RistrettoPoint::from_uniform_bytes(&uniform))
    }

    /// The canonical 32-byte encoding of the sum; the empty sum is 32 zero bytes.
    pub fn encode(&self) -> [u8; 32] {
        self.0.compress().to_bytes()
    }

    /// The sum with this encoding, or `None` when the bytes are not the canonical encoding of a group element.
    pub fn decode(bytes: &[u8; 32]) -> Option<Self> {
        CompressedRistretto(*bytes).decompress().map(Self)
    }
}

impl Default for SetSum {
    fn default() -> Self {
        Self::zero()
    }
}

impl fmt::Debug for SetSum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SetSum(")?;
        self.encode().iter().try_for_each(|b| write!(f, "{b:02x}"))?;
        f.write_str(")")
    }
}

impl Add for SetSum {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Sub for SetSum {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl AddAssign for SetSum {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl SubAssign for SetSum {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl Neg for SetSum {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::SetSum;

    // Pinned from this implementation, whose map is `from_uniform_bytes` over 64 bytes of the keyed XOF.
    const KEY: [u8; 32] = [7; 32];
    const EMPTY: [u8; 32] = [0; 32];
    const ONE: [u8; 32] = [
        0x0e, 0x36, 0x06, 0xaa, 0xe6, 0x0f, 0x93, 0x84, 0x2c, 0x00, 0xec, 0x85, 0x89, 0xda, 0xbb, 0xe2, 0x7a, 0x07,
        0x72, 0xe5, 0x7b, 0x7b, 0x6c, 0x72, 0x0d, 0x14, 0x81, 0x3b, 0xfe, 0x42, 0x46, 0x33,
    ];
    const TWO: [u8; 32] = [
        0x60, 0x96, 0x5a, 0x55, 0x8e, 0xda, 0x3f, 0x04, 0x9f, 0xb6, 0xd3, 0xb3, 0xbf, 0xb6, 0x85, 0xd3, 0x5a, 0x1d,
        0x4a, 0x78, 0x92, 0x24, 0x21, 0x1b, 0xc4, 0x04, 0xa1, 0x4a, 0xe7, 0xb2, 0x55, 0x7a,
    ];
    const BOTH: [u8; 32] = [
        0xd4, 0xea, 0xa0, 0x2c, 0x2c, 0x47, 0xbd, 0x9f, 0x98, 0x96, 0xa6, 0x0d, 0x73, 0x72, 0x08, 0x22, 0x62, 0xc9,
        0x6d, 0xaa, 0xa1, 0x73, 0xb7, 0x67, 0x16, 0xf5, 0xb8, 0xb3, 0xe2, 0x08, 0x11, 0x1a,
    ];

    fn sum(items: &[&[u8]]) -> SetSum {
        items.iter().fold(SetSum::zero(), |s, i| s + SetSum::of_item(&KEY, i))
    }

    #[test]
    fn known_answers() {
        assert_eq!(SetSum::zero().encode(), EMPTY);
        assert_eq!(SetSum::default(), SetSum::zero());
        assert_eq!(SetSum::of_item(&KEY, b"one").encode(), ONE);
        assert_eq!(SetSum::of_item(&KEY, b"two").encode(), TWO);
        assert_eq!(sum(&[b"one", b"two"]).encode(), BOTH);
    }

    #[test]
    fn order_does_not_matter() {
        assert_eq!(sum(&[b"a", b"b", b"c"]), sum(&[b"c", b"a", b"b"]));
    }

    #[test]
    fn add_then_subtract_returns_the_sum() {
        let base = sum(&[b"a", b"b"]);
        let item = SetSum::of_item(&KEY, b"z");
        assert_eq!(base + item - item, base);
        let mut s = base;
        s += item;
        s -= item;
        assert_eq!(s, base);
        assert_eq!(base + -base, SetSum::zero());
    }

    #[test]
    fn an_item_twice_is_not_the_item_once_nor_none() {
        let (none, once, twice) = (sum(&[b"a"]), sum(&[b"a", b"x"]), sum(&[b"a", b"x", b"x"]));
        assert_ne!(twice, once);
        assert_ne!(twice, none);
    }

    #[test]
    fn the_key_and_the_item_both_matter() {
        assert_ne!(SetSum::of_item(&KEY, b"a"), SetSum::of_item(&[8; 32], b"a"));
        assert_ne!(SetSum::of_item(&KEY, b"a"), SetSum::of_item(&KEY, b"b"));
    }

    #[test]
    fn decode_inverts_encode() {
        for s in [SetSum::zero(), sum(&[b"a"]), sum(&[b"a", b"b", b"c"])] {
            assert_eq!(SetSum::decode(&s.encode()), Some(s));
        }
    }

    #[test]
    fn decode_refuses_a_non_canonical_encoding() {
        assert_eq!(SetSum::decode(&[0xff; 32]), None);
        let mut negative = [0u8; 32];
        negative[0] = 1;
        assert_eq!(SetSum::decode(&negative), None);
    }

    #[test]
    fn debug_prints_the_encoding() {
        extern crate alloc;
        assert_eq!(
            alloc::format!("{:?}", SetSum::zero()),
            alloc::format!("SetSum({})", "00".repeat(32))
        );
    }
}
