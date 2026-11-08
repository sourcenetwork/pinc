//! Tests of vinc-dag's BLAKE3 tree and verified ranges.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop
)]

use std::collections::BTreeSet;
use std::ops::Range;

use proptest::prelude::*;
use vinc_dag::ranges::{VerifiedRanges, VerifiedRangesVec};
use vinc_dag::tree::{
    Layout, OutboardBuilder, RangeVerifier, TreeError, build_outboard, build_outboard_vec, encode_range, encoded_len,
};
use vinc_tests::SplitMix64;

fn data(seed: u64, len: usize) -> Vec<u8> {
    let mut v = vec![0; len];
    SplitMix64::new(seed).fill(&mut v);
    v
}

fn blake(v: &[u8]) -> [u8; 32] {
    *blake3::hash(v).as_bytes()
}

fn layout(len: usize, log: u32) -> Layout {
    Layout::new(len as u64, log).unwrap()
}

fn stream(value: &[u8], outboard: &[u8], log: u32, range: &Range<u64>) -> Vec<u8> {
    let mut out = vec![0; encoded_len(layout(value.len(), log), range).unwrap() as usize];
    assert_eq!(encode_range(value, outboard, log, range, &mut out).unwrap(), out.len());
    out
}

/// Feed `stream` in pieces of `piece` bytes; returns the released (offset, bytes) groups or the first error.
fn verify<const G: usize>(
    root: [u8; 32],
    len: u64,
    range: &Range<u64>,
    stream: &[u8],
    piece: usize,
) -> Result<Vec<(u64, Vec<u8>)>, TreeError> {
    let mut v = RangeVerifier::<G>::new(root, len, range)?;
    let mut released = Vec::new();
    for part in stream.chunks(piece) {
        let mut rest = part;
        while !rest.is_empty() {
            let fed = v.feed(rest)?;
            if let Some(g) = fed.verified {
                released.push((g.offset, g.data.to_vec()));
            }
            rest = &rest[fed.consumed..];
        }
    }
    if v.is_complete() {
        Ok(released)
    } else {
        Err(TreeError::Incomplete)
    }
}

#[test]
fn root_matches_blake3_for_edge_lengths() {
    let lens = [0usize, 1, 1023, 1024, 1025, 16383, 16384, 16385, 65536, (1 << 20) + 1];
    for log in [0, 2, 4, 6] {
        for &len in &lens {
            let v = data(len as u64, len);
            let (root, ob) = build_outboard_vec(&v, log).unwrap();
            assert_eq!(root, blake(&v), "len {len} log {log}");
            assert_eq!(ob.len() as u64, layout(len, log).outboard_size());
        }
    }
}

#[test]
fn root_matches_blake3_for_random_lengths_and_split_updates() {
    let mut rng = SplitMix64::new(7);
    for _ in 0..60 {
        let len = (rng.next_u64() % 200_000) as usize;
        let log = (rng.next_u64() % 7) as u32;
        let v = data(rng.next_u64(), len);
        let l = layout(len, log);
        let mut ob = vec![0; l.outboard_size() as usize];
        let mut b = OutboardBuilder::new(len as u64, log).unwrap();
        let mut rest = &v[..];
        while !rest.is_empty() {
            let n = ((rng.next_u64() % 5000) as usize + 1).min(rest.len());
            b.update(&rest[..n], &mut ob).unwrap();
            rest = &rest[n..];
        }
        assert_eq!(b.finish(&mut ob).unwrap(), blake(&v));
        let (root, ob2) = build_outboard_vec(&v, log).unwrap();
        assert_eq!((root, ob2), (blake(&v), ob));
    }
}

#[test]
fn builder_rejects_bad_input() {
    let mut ob = vec![0; layout(10, 0).outboard_size() as usize];
    let mut b = OutboardBuilder::new(10, 0).unwrap();
    assert_eq!(b.update(&[0; 11], &mut ob), Err(TreeError::TooMuchData));
    b.update(&[0; 4], &mut ob).unwrap();
    assert_eq!(b.finish(&mut ob), Err(TreeError::Incomplete));
    assert_eq!(OutboardBuilder::new(1, 21).unwrap_err(), TreeError::InvalidGroupSize);
    let mut small = [0u8; 1];
    assert_eq!(
        build_outboard(&data(1, 5000), 0, &mut small),
        Err(TreeError::OutboardSize)
    );
}

#[test]
fn layout_arithmetic() {
    let l = layout(16385, 4);
    assert_eq!((l.groups(), l.depth(), l.outboard_size()), (2, 1, 64));
    assert_eq!(
        (
            layout(0, 4).groups(),
            layout(0, 4).depth(),
            layout(0, 4).outboard_size()
        ),
        (0, 0, 0)
    );
    assert_eq!(
        (
            layout(1, 4).groups(),
            layout(1, 4).depth(),
            layout(1, 4).outboard_size()
        ),
        (1, 0, 0)
    );
    assert_eq!(layout(5 * 16384, 4).depth(), 3);
    assert_eq!(layout(4 * 16384, 4).depth(), 2);
}

#[test]
fn layout_arithmetic_at_u64_max() {
    for log in 0..=20u32 {
        let l = Layout::new(u64::MAX, log).unwrap();
        let g = 1024u64 << log;
        let groups = u64::MAX / g + 1;
        assert_eq!(l.groups(), groups);
        assert_eq!(l.outboard_size(), (groups - 1) * 64);
        assert_eq!(l.depth(), 64 - (groups - 1).leading_zeros());
        assert!(l.depth() <= 54);
        assert_eq!(l.group_size(groups - 1), u64::MAX - (groups - 1) * g);
        assert_eq!(l.group_range(&(u64::MAX - 1..u64::MAX)).unwrap(), groups - 1..groups);
    }
    assert!(Layout::new(0, 21).is_err());
}

#[test]
fn range_proofs_verify_for_random_ranges() {
    let mut rng = SplitMix64::new(11);
    for case in 0..80 {
        let len = (rng.next_u64() % 120_000) as usize + 1;
        let v = data(case, len);
        let a = rng.next_u64() % len as u64;
        let b = a + rng.next_u64() % (len as u64 - a + 1);
        let range = a..b;
        let piece = (rng.next_u64() % 3000) as usize + 1;
        macro_rules! run {
            ($g:expr, $log:expr) => {{
                let (root, ob) = build_outboard_vec(&v, $log).unwrap();
                let s = stream(&v, &ob, $log, &range);
                let got = verify::<$g>(root, len as u64, &range, &s, piece).unwrap();
                let l = layout(len, $log);
                let gr = l.group_range(&range).unwrap();
                let mut expect = Vec::new();
                for g in gr.clone() {
                    let off = g * l.group_len();
                    expect.push((off, v[off as usize..(off + l.group_size(g)) as usize].to_vec()));
                }
                assert_eq!(got, expect, "case {case} log {}", $log);
            }};
        }
        run!(1024, 0);
        run!(4096, 2);
        run!(16384, 4);
        run!(65536, 6);
    }
}

#[test]
fn full_and_empty_ranges() {
    let v = data(3, 50_000);
    let (root, ob) = build_outboard_vec(&v, 4).unwrap();
    let full = 0..v.len() as u64;
    let s = stream(&v, &ob, 4, &full);
    let got = verify::<16384>(root, v.len() as u64, &full, &s, 777).unwrap();
    assert_eq!(got.into_iter().flat_map(|(_, b)| b).collect::<Vec<_>>(), v);
    let empty = 5..5;
    assert_eq!(stream(&v, &ob, 4, &empty), Vec::<u8>::new());
    assert!(
        RangeVerifier::<16384>::new(root, v.len() as u64, &empty)
            .unwrap()
            .is_complete()
    );
    assert!(
        RangeVerifier::<16384>::new(blake(b""), 0, &(0..0))
            .unwrap()
            .is_complete()
    );
    assert_eq!(
        RangeVerifier::<16384>::new([1; 32], 0, &(0..0)).unwrap_err(),
        TreeError::RootMismatch
    );
    assert_eq!(
        RangeVerifier::<16384>::new(root, 10, &(0..11)).unwrap_err(),
        TreeError::RangeOutOfBounds
    );
    assert_eq!(
        RangeVerifier::<1000>::new(root, 10, &(0..1)).unwrap_err(),
        TreeError::InvalidGroupSize
    );
}

#[test]
fn trailing_data_is_rejected() {
    let v = data(4, 3000);
    let (root, ob) = build_outboard_vec(&v, 0).unwrap();
    let range = 0..1;
    let mut s = stream(&v, &ob, 0, &range);
    s.push(0);
    assert!(verify::<1024>(root, 3000, &range, &s, 4096).is_err());
}

#[test]
fn every_bit_flip_is_rejected_and_releases_nothing_bad() {
    for (len, log, range) in [
        (5000usize, 0u32, 1500..3500u64),
        (3000, 0, 0..3000),
        (1024, 0, 0..1),
        (40_000, 2, 9000..30_000),
    ] {
        let v = data(len as u64, len);
        let (root, ob) = build_outboard_vec(&v, log).unwrap();
        let good = stream(&v, &ob, log, &range);
        for bit in 0..good.len() * 8 {
            let mut bad = good.clone();
            bad[bit / 8] ^= 1 << (bit % 8);
            let mut released: Vec<(u64, Vec<u8>)> = Vec::new();
            macro_rules! run {
                ($g:expr) => {{
                    let mut ver = RangeVerifier::<$g>::new(root, len as u64, &range).unwrap();
                    let mut rest = &bad[..];
                    let mut err = None;
                    while !rest.is_empty() {
                        match ver.feed(rest) {
                            Ok(f) => {
                                if let Some(g) = f.verified {
                                    released.push((g.offset, g.data.to_vec()));
                                }
                                rest = &rest[f.consumed..];
                            }
                            Err(e) => {
                                err = Some(e);
                                break;
                            }
                        }
                    }
                    assert!(err.is_some(), "flip of bit {bit} accepted (len {len})");
                    assert_eq!(ver.feed(&[0]).unwrap_err(), err.unwrap());
                    assert!(!ver.is_complete());
                }};
            }
            if log == 0 {
                run!(1024);
            } else {
                run!(4096);
            }
            for (off, bytes) in &released {
                assert_eq!(
                    bytes[..],
                    v[*off as usize..*off as usize + bytes.len()],
                    "unverified bytes released"
                );
            }
        }
    }
}

#[test]
fn wrong_root_and_wrong_length_are_rejected() {
    let v = data(9, 40_000);
    let (root, ob) = build_outboard_vec(&v, 2).unwrap();
    let range = 30_000..40_000;
    let s = stream(&v, &ob, 2, &range);
    assert!(verify::<4096>(root, 40_000, &range, &s, 5000).is_ok());
    let mut wrong = root;
    wrong[0] ^= 1;
    assert!(verify::<4096>(wrong, 40_000, &range, &s, 5000).is_err());
    // Lengths that reach the last group: same group count, different count, and shorter last group.
    for bad_len in [39_999u64, 40_001, 36_864, 45_000, 100_000] {
        assert!(
            verify::<4096>(root, bad_len, &(range.start..range.end.min(bad_len)), &s, 5000).is_err(),
            "len {bad_len}"
        );
    }
}

#[test]
fn verified_group_is_released_only_after_whole_group_arrives() {
    let v = data(5, 8192);
    let (root, ob) = build_outboard_vec(&v, 2).unwrap();
    let range = 0..8192;
    let s = stream(&v, &ob, 2, &range);
    let mut ver = RangeVerifier::<4096>::new(root, 8192, &range).unwrap();
    let mut released = 0;
    for b in &s {
        let f = ver.feed(std::slice::from_ref(b)).unwrap();
        if let Some(g) = f.verified {
            released += g.data.len();
        }
    }
    assert_eq!(released, 8192);
    assert!(ver.is_complete());
}

// VerifiedRanges against a model.

const DOMAIN: u64 = 48;

fn model_covered(model: &BTreeSet<u64>) -> Vec<Range<u64>> {
    let mut out: Vec<Range<u64>> = Vec::new();
    for &o in model {
        match out.last_mut() {
            Some(r) if r.end == o => r.end += 1,
            _ => out.push(o..o + 1),
        }
    }
    out
}

fn ranges_strategy() -> impl Strategy<Value = Vec<(u64, u64)>> {
    prop::collection::vec((0..DOMAIN, 0..12u64), 0..40)
}

proptest! {
    #[test]
    fn verified_ranges_match_model(ops in ranges_strategy()) {
        let mut set = VerifiedRanges::<6>::new();
        let mut vec_set = VerifiedRangesVec::new();
        let mut model = BTreeSet::new();
        let mut prev: BTreeSet<u64> = BTreeSet::new();
        for (start, width) in ops {
            let range = start..start + width;
            let before = set.clone();
            let mut next = model.clone();
            next.extend(range.clone());
            let expect = model_covered(&next);
            vec_set.insert(range.clone());
            if set.insert(range.clone()).is_ok() {
                model = next;
                prop_assert_eq!(set.iter().collect::<Vec<_>>(), expect);
            } else {
                prop_assert!(expect.len() > 6);
                prop_assert_eq!(&set, &before);
                // The unbounded set still took it; resync it with the bounded one.
                vec_set = VerifiedRangesVec::new();
                for r in before.iter() {
                    vec_set.insert(r);
                }
            }
            let ivs: Vec<_> = set.iter().collect();
            prop_assert_eq!(set.len(), ivs.len());
            for w in ivs.windows(2) {
                prop_assert!(w[0].end < w[1].start, "not sorted/disjoint/merged");
            }
            prop_assert!(ivs.iter().all(|r| r.start < r.end));
            let cov: BTreeSet<u64> = (0..DOMAIN + 12).filter(|o| set.contains(*o)).collect();
            prop_assert_eq!(&cov, &model);
            prop_assert!(prev.is_subset(&cov), "set shrank");
            prop_assert_eq!(set.covered_len(), model.len() as u64);
            prop_assert_eq!(vec_set.iter().collect::<Vec<_>>(), ivs.clone());
            prop_assert_eq!(vec_set.covered_len(), set.covered_len());
            for a in 0..DOMAIN {
                for b in a..(a + 4) {
                    let exp = (a..b).all(|o| model.contains(&o));
                    prop_assert_eq!(set.contains_range(a..b), exp);
                    prop_assert_eq!(vec_set.contains_range(a..b), exp);
                }
            }
            prev = cov;
        }
    }
}

#[test]
fn verified_ranges_basics() {
    let mut s = VerifiedRanges::<2>::new();
    assert!(s.is_empty());
    s.insert(0..10).unwrap();
    s.insert(20..30).unwrap();
    assert!(s.insert(40..50).is_err());
    assert_eq!(s.len(), 2);
    s.insert(10..20).unwrap();
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![0..30]);
    s.insert(5..5).unwrap();
    assert_eq!(s.capacity(), 2);
    assert!(s.contains(29) && !s.contains(30));
    let mut m = VerifiedRanges::<1>::new();
    m.insert(0..u64::MAX).unwrap();
    assert_eq!(m.covered_len(), u64::MAX);
    assert!(!m.contains(u64::MAX));
}

// Zero allocations on the verification and range-set paths.

#[test]
fn verifier_and_ranges_do_not_allocate() {
    let v = data(21, 100_000);
    let (root, ob) = build_outboard_vec(&v, 4).unwrap();
    let range = 3000..90_000;
    let s = stream(&v, &ob, 4, &range);
    let len = v.len() as u64;

    let info = allocation_counter::measure(|| {
        let mut ver = RangeVerifier::<16384>::new(root, len, &range).unwrap();
        let mut rest = &s[..];
        let mut total = 0;
        while !rest.is_empty() {
            let f = ver.feed(rest).unwrap();
            total += f.verified.map_or(0, |g| g.data.len());
            rest = &rest[f.consumed..];
        }
        assert!(ver.is_complete() && total > 0);
    });
    assert_eq!(info.count_total, 0);

    let info = allocation_counter::measure(|| {
        let mut set = VerifiedRanges::<4>::new();
        for i in 0..50u64 {
            let _ = set.insert(i * 10..i * 10 + 5);
            let _ = set.insert(i * 10 + 5..i * 10 + 10);
            let _ = (
                set.contains(i),
                set.contains_range(0..i),
                set.covered_len(),
                set.iter().count(),
                set.len(),
            );
        }
    });
    assert_eq!(info.count_total, 0);
}
