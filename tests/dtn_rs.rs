//! Tests of the GF(2^8) arithmetic and the systematic Reed-Solomon code.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop,
    clippy::trivially_copy_pass_by_ref,
    clippy::cast_lossless
)]

use proptest::prelude::*;
use vinc_dtn::error::DtnError;
use vinc_dtn::gf256::{inv, mul, mul_add, scale};
use vinc_dtn::rs::Rs;
use vinc_tests::SplitMix64;

fn block(rs: &Rs, len: usize, seed: u64) -> Vec<u8> {
    let mut b = vec![0; rs.n() * len];
    SplitMix64::new(seed).fill(&mut b[..rs.k() * len]);
    rs.encode(len, &mut b).unwrap();
    b
}

/// Erase the symbols not in `keep` (scrambling their bytes), reconstruct and compare with `whole`.
fn recovers(rs: &Rs, len: usize, whole: &[u8], keep: &dyn Fn(usize) -> bool) -> bool {
    let present: Vec<bool> = (0..rs.n()).map(keep).collect();
    let mut b = whole.to_vec();
    for (s, p) in present.iter().enumerate() {
        if !p {
            b[s * len..(s + 1) * len].fill(0xA5);
        }
    }
    rs.reconstruct(len, &mut b, &present).unwrap();
    b == whole
}

#[test]
fn field_axioms() {
    for a in 0..=255u8 {
        assert_eq!(mul(a, 1), a);
        assert_eq!(mul(a, 0), 0);
        if a != 0 {
            assert_eq!(mul(a, inv(a)), 1, "inverse of {a}");
        }
        for b in 0..=255u8 {
            assert_eq!(mul(a, b), mul(b, a));
        }
    }
    for (a, b, c) in [(3u8, 77u8, 200u8), (255, 254, 1), (16, 16, 16), (0x53, 0xca, 0x11)] {
        assert_eq!(mul(a, b ^ c), mul(a, b) ^ mul(a, c), "distributive");
        assert_eq!(mul(mul(a, b), c), mul(a, mul(b, c)), "associative");
    }
    // The generator 2 has order 255.
    let mut x = 1u8;
    for i in 1..=255 {
        x = mul(x, 2);
        assert_eq!(x == 1, i == 255);
    }
}

#[test]
fn kernels_match_scalar_arithmetic() {
    let src: Vec<u8> = (0..=255).collect();
    for c in [0u8, 1, 2, 29, 255] {
        let mut dst = vec![0x3c; 256];
        mul_add(&mut dst, &src, c);
        for i in 0..256 {
            assert_eq!(dst[i], 0x3c ^ mul(src[i], c));
        }
        let mut s = src.clone();
        scale(&mut s, c);
        for i in 0..256 {
            assert_eq!(s[i], mul(src[i], c));
        }
    }
}

/// Every k-subset (and every larger subset) of a small code, exhaustively.
#[test]
fn every_subset_of_at_least_k_symbols_recovers_exhaustively() {
    for (k, m) in [(1, 1), (1, 3), (2, 2), (3, 3), (4, 3), (5, 4), (6, 2), (3, 6)] {
        let rs = Rs::new(k, m).unwrap();
        let len = 13;
        let whole = block(&rs, len, (k * 31 + m) as u64);
        let mut checked = 0;
        for mask in 0u32..(1 << rs.n()) {
            if mask.count_ones() as usize >= k {
                assert!(
                    recovers(&rs, len, &whole, &|s| mask >> s & 1 == 1),
                    "k={k} m={m} mask={mask:b}"
                );
                checked += 1;
            }
        }
        assert!(checked > 0);
    }
}

#[test]
fn fewer_than_k_symbols_is_incomplete_and_leaves_the_block_alone() {
    let rs = Rs::new(4, 3).unwrap();
    let len = 8;
    let whole = block(&rs, len, 1);
    let mut b = whole.clone();
    let present = [true, false, true, false, true, false, false];
    assert_eq!(rs.reconstruct(len, &mut b, &present).err(), Some(DtnError::Incomplete));
    assert_eq!(b, whole);
}

#[test]
fn parameters_and_buffers_are_validated() {
    assert!(Rs::new(0, 1).is_err());
    assert!(Rs::new(200, 56).is_err());
    assert!(Rs::new(255, 0).is_ok());
    assert!(Rs::new(1, 254).is_ok());
    let rs = Rs::new(2, 1).unwrap();
    assert_eq!(rs.encode(0, &mut []).err(), Some(DtnError::Buffer));
    assert_eq!(rs.encode(4, &mut [0; 11]).err(), Some(DtnError::Buffer));
    assert_eq!(
        rs.reconstruct(4, &mut [0; 12], &[true, true]).err(),
        Some(DtnError::Buffer)
    );
    // m = 0 is the identity code: encode is a no-op and nothing can be recovered.
    let id = Rs::new(3, 0).unwrap();
    let mut b = [1u8, 2, 3];
    id.encode(1, &mut b).unwrap();
    assert_eq!(b, [1, 2, 3]);
    assert_eq!(
        id.reconstruct(1, &mut b, &[true, false, true]).err(),
        Some(DtnError::Incomplete)
    );
}

#[test]
fn the_largest_block_recovers_the_worst_erasures() {
    // k + m = 255 with 127 missing data symbols replaced by 127 parity symbols: the largest solve.
    let rs = Rs::new(128, 127).unwrap();
    let len = 5;
    let whole = block(&rs, len, 9);
    assert!(recovers(&rs, len, &whole, &|s| s >= 127));
    let rs = Rs::new(127, 128).unwrap();
    let whole = block(&rs, len, 10);
    assert!(recovers(&rs, len, &whole, &|s| s >= 127));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    #[test]
    fn random_erasures_recover(
        k in 1usize..64,
        m in 0usize..40,
        len in 1usize..48,
        seed in any::<u64>(),
        drop_seed in any::<u64>(),
    ) {
        let rs = Rs::new(k, m).unwrap();
        let whole = block(&rs, len, seed);
        // Keep a random subset of exactly k + extra symbols: choose which to erase by a seeded shuffle.
        let mut order: Vec<usize> = (0..rs.n()).collect();
        let mut rng = SplitMix64::new(drop_seed);
        for i in (1..order.len()).rev() {
            order.swap(i, (rng.next_u64() % (i as u64 + 1)) as usize);
        }
        let extra = (rng.next_u64() % (m as u64 + 1)) as usize;
        let kept: Vec<usize> = order[..k + extra.min(m)].to_vec();
        prop_assert!(recovers(&rs, len, &whole, &|s| kept.contains(&s)));
    }

    #[test]
    fn encoding_is_systematic_and_linear(k in 1usize..16, m in 1usize..16, len in 1usize..32, a in any::<u64>(), b in any::<u64>()) {
        let rs = Rs::new(k, m).unwrap();
        let (x, y) = (block(&rs, len, a), block(&rs, len, b));
        // Systematic: the data prefix is untouched by encoding.
        let mut data = vec![0; rs.n() * len];
        SplitMix64::new(a).fill(&mut data[..k * len]);
        prop_assert_eq!(&x[..k * len], &data[..k * len]);
        // Linear: the XOR of two code words is the code word of the XOR of the data.
        let sum: Vec<u8> = x.iter().zip(&y).map(|(p, q)| p ^ q).collect();
        let mut again = sum.clone();
        rs.encode(len, &mut again).unwrap();
        prop_assert_eq!(sum, again);
    }
}
