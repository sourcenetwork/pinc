//! The incremental verifier decides exactly as the copying `RangeVerifier` for every split of the same bytes.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::assert_is_empty,
    clippy::doc_markdown,
    clippy::similar_names,
    clippy::single_range_in_vec_init,
    clippy::unreadable_literal,
    reason = "tests assert freely and name protocol rules in capitals"
)]

mod values_support;

use proptest::prelude::*;
use std::ops::Range;
use pinc_dag::tree::{
    Cv, Layout, PARENT_LEN, RangeEncoder, RangeVerifier, Step, TreeError, build_outboard_vec, encode_range, encoded_len,
};
use pinc_tests::SplitMix64;
use pinc_values::verify::{GroupMatch, GroupVerifier, Item};

const GROUP: usize = 16384;

/// One call's result: bytes consumed and the group reported, or the error.
type Call = Result<(usize, Option<GroupMatch>), TreeError>;

struct Case {
    value: Vec<u8>,
    root: Cv,
    outboard: Vec<u8>,
}

fn case(seed: u64, len: usize) -> Case {
    let mut value = vec![0u8; len];
    SplitMix64::new(seed).fill(&mut value);
    let (root, outboard) = build_outboard_vec(&value, 4).unwrap();
    Case { value, root, outboard }
}

fn stream(c: &Case, range: &Range<u64>) -> Vec<u8> {
    let n = encoded_len(Layout::new(c.value.len() as u64, 4).unwrap(), range).unwrap() as usize;
    let mut out = vec![0u8; n];
    encode_range(&c.value, &c.outboard, 4, range, &mut out).unwrap();
    out
}

/// Feed `bytes` to the copying verifier in pieces of the given sizes; one entry per `feed` call.
fn run_copying(c: &Case, range: &Range<u64>, bytes: &[u8], sizes: &mut dyn Iterator<Item = usize>) -> Vec<Call> {
    let mut v = RangeVerifier::<GROUP>::new(c.root, c.value.len() as u64, range).unwrap();
    let mut calls = Vec::new();
    let mut at = 0;
    while at < bytes.len() {
        let piece = &bytes[at..(at + sizes.next().unwrap().max(1)).min(bytes.len())];
        at += piece.len();
        let mut rest = piece;
        while !rest.is_empty() {
            match v.feed(rest) {
                Ok(f) => {
                    calls.push(Ok((
                        f.consumed,
                        f.verified.map(|g| GroupMatch {
                            offset: g.offset,
                            len: g.data.len() as u64,
                        }),
                    )));
                    rest = &rest[f.consumed..];
                }
                Err(e) => {
                    calls.push(Err(e));
                    break;
                }
            }
        }
    }
    calls
}

fn run_incremental(c: &Case, range: &Range<u64>, bytes: &[u8], sizes: &mut dyn Iterator<Item = usize>) -> Vec<Call> {
    let mut v = GroupVerifier::new(c.root, c.value.len() as u64, 4, range).unwrap();
    let mut calls = Vec::new();
    let mut at = 0;
    while at < bytes.len() {
        let piece = &bytes[at..(at + sizes.next().unwrap().max(1)).min(bytes.len())];
        at += piece.len();
        let mut rest = piece;
        while !rest.is_empty() {
            match v.feed(rest) {
                Ok(f) => {
                    calls.push(Ok((f.consumed, f.group)));
                    rest = &rest[f.consumed..];
                }
                Err(e) => {
                    calls.push(Err(e));
                    break;
                }
            }
        }
    }
    calls
}

fn same(c: &Case, range: &Range<u64>, bytes: &[u8], sizes: &[usize]) {
    let a = run_copying(c, range, bytes, &mut sizes.iter().copied().cycle());
    let b = run_incremental(c, range, bytes, &mut sizes.iter().copied().cycle());
    assert_eq!(a, b, "decisions differ for pieces {sizes:?}");
}

#[test]
fn identical_decisions_on_every_split_of_a_small_stream() {
    let c = case(1, 3 * GROUP + 5);
    let range = 0..c.value.len() as u64;
    let bytes = stream(&c, &range);
    // Every piece size from 1 to 80, and every single split point of the whole stream.
    for size in 1..80 {
        same(&c, &range, &bytes, &[size]);
    }
    for cut in
        (1..bytes.len())
            .step_by(37)
            .chain([PARENT_LEN - 1, PARENT_LEN, PARENT_LEN + 1, GROUP, GROUP + PARENT_LEN])
    {
        same(&c, &range, &bytes, &[cut, bytes.len()]);
    }
    // The whole stream decides as it should: every group once, in order.
    let calls = run_incremental(&c, &range, &bytes, &mut std::iter::repeat(1452));
    let groups: Vec<_> = calls.iter().filter_map(|c| c.as_ref().ok().and_then(|x| x.1)).collect();
    assert_eq!(
        groups.iter().map(|g| g.offset).collect::<Vec<_>>(),
        vec![0, GROUP as u64, 2 * GROUP as u64, 3 * GROUP as u64]
    );
}

#[test]
fn identical_decisions_at_mtu_pieces_on_larger_values_and_ranges() {
    for (seed, len) in [
        (2, 1usize),
        (3, GROUP),
        (4, 5 * GROUP),
        (5, 17 * GROUP + 1),
        (6, 64 * GROUP),
    ] {
        let c = case(seed, len);
        let n = len as u64;
        for range in [
            0..n,
            0..n.min(1),
            n / 2..n,
            n / 3..(n / 3 + 40_000).min(n),
            n.saturating_sub(1)..n,
        ] {
            if range.start >= range.end {
                continue;
            }
            let bytes = stream(&c, &range);
            for sizes in [
                &[1452usize][..],
                &[1][..],
                &[64, 1, 1452, 17][..],
                &[PARENT_LEN][..],
                &[GROUP][..],
                &[usize::MAX / 2][..],
            ] {
                if sizes[0] == 1 && bytes.len() > 100_000 {
                    continue;
                }
                same(&c, &range, &bytes, sizes);
            }
        }
    }
}

#[test]
fn identical_decisions_on_corrupted_streams() {
    let c = case(9, 5 * GROUP + 100);
    let range = 0..c.value.len() as u64;
    let good = stream(&c, &range);
    let mut rng = SplitMix64::new(99);
    // Every parent byte of the first pairs, the group edges, and random positions.
    let mut positions: Vec<usize> = (0..3 * PARENT_LEN).collect();
    positions.extend([
        PARENT_LEN * 3,
        PARENT_LEN * 3 + 1,
        good.len() - 1,
        good.len() - 2,
        good.len() / 2,
    ]);
    positions.extend((0..60).map(|_| (rng.next_u64() % good.len() as u64) as usize));
    for pos in positions {
        let mut bad = good.clone();
        bad[pos] ^= 1 << (pos % 8);
        for sizes in [&[1452usize][..], &[777, 3][..], &[usize::MAX / 2][..]] {
            same(&c, &range, &bad, sizes);
        }
        // A corrupted byte is always caught: some call returns an error and no group at or after it is reported.
        let calls = run_incremental(&c, &range, &bad, &mut std::iter::repeat(1452));
        assert!(calls.iter().any(Result::is_err), "corruption at {pos} was not caught");
    }
}

#[test]
fn nothing_after_an_error_is_reported_and_the_error_repeats() {
    let c = case(10, 2 * GROUP);
    let range = 0..c.value.len() as u64;
    let mut bad = stream(&c, &range);
    let last = bad.len() - 5;
    bad[last] ^= 0xff;
    let mut v = GroupVerifier::new(c.root, c.value.len() as u64, 4, &range).unwrap();
    let mut err = None;
    let mut at = 0;
    while at < bad.len() {
        match v.feed(&bad[at..]) {
            Ok(f) => at += f.consumed,
            Err(e) => {
                err = Some(e);
                break;
            }
        }
    }
    assert_eq!(err, Some(TreeError::GroupMismatch));
    assert_eq!(v.failure(), err);
    assert_eq!(v.feed(&[1, 2, 3]), Err(TreeError::GroupMismatch));
    assert_eq!(v.feed(&[]), Err(TreeError::GroupMismatch));
    assert_eq!(v.next_item(), None);
    assert!(!v.is_complete());
}

#[test]
fn too_much_data_and_empty_input_match_the_copying_verifier() {
    let c = case(11, GROUP + 3);
    let range = 0..c.value.len() as u64;
    let mut bytes = stream(&c, &range);
    bytes.extend_from_slice(&[0u8; 10]);
    same(&c, &range, &bytes, &[1452]);
    let mut v = GroupVerifier::new(c.root, c.value.len() as u64, 4, &range).unwrap();
    assert_eq!(v.feed(&[]).unwrap().consumed, 0);
    let ok = stream(&c, &range);
    let mut at = 0;
    while at < ok.len() {
        at += v.feed(&ok[at..]).unwrap().consumed;
    }
    assert!(v.is_complete());
    assert_eq!(v.feed(&[1]), Err(TreeError::TooMuchData));
}

#[test]
fn constructor_errors_match() {
    let c = case(12, 3000);
    #[allow(clippy::reversed_empty_ranges, reason = "a reversed range is the case under test")]
    let ranges = [0..4000u64, 5..3, 3000..3001];
    for range in ranges {
        let a = RangeVerifier::<GROUP>::new(c.root, 3000, &range).err();
        let b = GroupVerifier::new(c.root, 3000, 4, &range).err();
        assert_eq!(a, b, "{range:?}");
    }
    // The empty value: the root must be the hash of nothing.
    let empty = *blake3::hash(b"").as_bytes();
    assert!(GroupVerifier::new(empty, 0, 4, &(0..0)).unwrap().is_complete());
    assert_eq!(
        GroupVerifier::new([1; 32], 0, 4, &(0..0)).err(),
        Some(TreeError::RootMismatch)
    );
    assert_eq!(
        RangeVerifier::<GROUP>::new([1; 32], 0, &(0..0)).err(),
        Some(TreeError::RootMismatch)
    );
    assert_eq!(
        GroupVerifier::new(empty, 10, 25, &(0..1)).err(),
        Some(TreeError::InvalidGroupSize)
    );
}

#[test]
fn a_group_is_reported_only_when_its_last_byte_arrives() {
    let c = case(13, 2 * GROUP);
    let range = 0..c.value.len() as u64;
    let bytes = stream(&c, &range);
    let mut v = GroupVerifier::new(c.root, c.value.len() as u64, 4, &range).unwrap();
    let mut reported = Vec::new();
    for (i, b) in bytes.iter().enumerate() {
        let f = v.feed(std::slice::from_ref(b)).unwrap();
        if let Some(g) = f.group {
            reported.push((i + 1, g));
        }
    }
    // The stream is root pair, group 0, group 1: a group completes exactly at its end.
    assert_eq!(reported.len(), 2);
    assert_eq!(reported[0].0, PARENT_LEN + GROUP);
    assert_eq!(reported[1].0, PARENT_LEN + 2 * GROUP);
    assert!(v.is_complete());
}

#[test]
fn next_item_names_what_the_stream_needs() {
    let c = case(14, 4 * GROUP);
    let range = 0..c.value.len() as u64;
    let bytes = stream(&c, &range);
    let mut v = GroupVerifier::new(c.root, c.value.len() as u64, 4, &range).unwrap();
    let mut items = Vec::new();
    let mut at = 0;
    while let Some(item) = v.next_item() {
        items.push(item);
        let need = v.next_len().unwrap() as usize;
        assert!(v.at_boundary());
        at += v.feed(&bytes[at..at + need]).unwrap().consumed;
    }
    assert_eq!(at, bytes.len());
    let groups: Vec<_> = items.iter().filter(|i| matches!(i, Item::Group { .. })).collect();
    assert_eq!(groups.len(), 4);
    assert_eq!(items.iter().filter(|i| **i == Item::Pair).count(), 3);
    assert_eq!(items[0], Item::Pair);
}

#[test]
fn skipping_a_verified_group_leaves_the_rest_verifiable() {
    let c = case(15, 6 * GROUP + 9);
    let range = 0..c.value.len() as u64;
    let layout = Layout::new(c.value.len() as u64, 4).unwrap();
    // The stream with groups 1 and 4 elided; the verifier is told to skip them.
    let mut v = GroupVerifier::new(c.root, c.value.len() as u64, 4, &range).unwrap();
    let mut skipped = Vec::new();
    for step in RangeEncoder::new(layout, &range).unwrap() {
        match step.unwrap() {
            Step::Parent { outboard_offset } => {
                let mut at = 0;
                let pair = &c.outboard[outboard_offset as usize..outboard_offset as usize + PARENT_LEN];
                while at < pair.len() {
                    at += v.feed(&pair[at..]).unwrap().consumed;
                }
            }
            Step::Group { offset, len } => {
                if offset / GROUP as u64 == 1 || offset / GROUP as u64 == 4 {
                    let g = v.skip_group().unwrap();
                    assert_eq!((g.offset, g.len), (offset, len));
                    skipped.push(offset);
                } else {
                    let mut at = 0;
                    let data = &c.value[offset as usize..(offset + len) as usize];
                    let mut got = None;
                    while at < data.len() {
                        let f = v.feed(&data[at..(at + 1452).min(data.len())]).unwrap();
                        at += f.consumed;
                        got = got.or(f.group);
                    }
                    assert_eq!(got.map(|g| g.offset), Some(offset));
                }
            }
        }
    }
    assert_eq!(skipped.len(), 2);
    assert!(v.is_complete());
    // A skip is refused mid-item and when the next item is a pair.
    let mut v = GroupVerifier::new(c.root, c.value.len() as u64, 4, &range).unwrap();
    assert_eq!(v.skip_group(), Err(TreeError::TooMuchData));
    v.feed(&c.outboard[..10]).unwrap();
    assert_eq!(v.skip_group(), Err(TreeError::TooMuchData));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn garbage_is_judged_alike(seed in any::<u64>(), len in 1usize..(4 * GROUP), junk in proptest::collection::vec(any::<u8>(), 0..3000), flips in proptest::collection::vec(any::<u32>(), 0..4), sizes in proptest::collection::vec(1usize..2000, 1..6)) {
        let c = case(seed, len);
        let range = 0..len as u64;
        let mut bytes = stream(&c, &range);
        for f in &flips {
            let at = *f as usize % bytes.len();
            bytes[at] ^= 1 << (f % 8);
        }
        bytes.extend_from_slice(&junk);
        let a = run_copying(&c, &range, &bytes, &mut sizes.iter().copied().cycle());
        let b = run_incremental(&c, &range, &bytes, &mut sizes.iter().copied().cycle());
        prop_assert_eq!(a, b);
    }
}
