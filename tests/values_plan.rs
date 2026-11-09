//! The response geometry and the store-reading source: the closed-form plan equals the `vinc-dag` range encoding
//! byte for byte, and the source reproduces any byte of a response from the store.
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
use values_support::*;
use vinc_dag::tree::{Layout, PARENT_LEN, RangeEncoder, Step, build_outboard_vec, encoded_len};
use vinc_transport::stream::StreamSource;
use vinc_values::knobs::SERVE_BATCH;
use vinc_values::plan::Plan;
use vinc_values::source::ValueSource;
use vinc_values::span::Span;
use vinc_values::wire::{GROUP_HDR, GroupHeader};

/// The response to `spans` built the slow way from the `vinc-dag` encoder: header, proof pairs, group bytes.
fn reference(value: &[u8], outboard: &[u8], spans: &[Span]) -> Vec<u8> {
    let layout = Layout::new(value.len() as u64, 4).unwrap();
    let mut out = Vec::new();
    for s in spans.iter().filter(|s| s.len > 0) {
        let range = s.off..s.off + s.len;
        let mut proof: Vec<u8> = Vec::new();
        let mut first = true;
        for step in RangeEncoder::new(layout, &range).unwrap() {
            match step.unwrap() {
                Step::Parent { outboard_offset } => {
                    proof.extend_from_slice(&outboard[outboard_offset as usize..outboard_offset as usize + PARENT_LEN]);
                }
                Step::Group { offset, len } => {
                    let h = GroupHeader {
                        off: offset,
                        len: len as u32,
                        plen: proof.len() as u16,
                        follows: !first,
                    };
                    out.extend_from_slice(&h.encode());
                    out.extend_from_slice(&proof);
                    out.extend_from_slice(&value[offset as usize..(offset + len) as usize]);
                    proof.clear();
                    first = false;
                }
            }
        }
    }
    out
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    #[test]
    fn the_plan_and_the_source_equal_the_range_encoding(
        len in 0usize..(70 * 16384),
        seed in any::<u64>(),
        picks in proptest::collection::vec(any::<(u16, u16)>(), 1..4),
        reads in proptest::collection::vec((any::<u32>(), 1usize..3000), 1..40),
    ) {
        let store = PStore::random(seed, len);
        let value = store.content().bytes(0, len as u64);
        let (_, outboard) = build_outboard_vec(&value, 4).unwrap();
        let spans: Vec<Span> = picks.iter().map(|(a, b)| {
            let off = (usize::from(*a) * 17) % (len.max(1));
            Span { off: off as u64, len: ((usize::from(*b) * 29) % (len - off + 1)) as u64 }
        }).collect();
        let want = reference(&value, &outboard, &spans);
        let plan = Plan::new(len as u64, &spans).unwrap();
        prop_assert_eq!(plan.total(), want.len() as u64);

        let mut src = ValueSource::new(store, store_root(&value), plan.clone());
        // Sequential read of everything in odd-sized pieces, then random reads (backwards seeks included).
        let mut got = Vec::new();
        let mut buf = vec![0u8; 1452];
        while got.len() < want.len() {
            let n = src.read_at(got.len() as u64, &mut buf);
            prop_assert!(n > 0);
            got.extend_from_slice(&buf[..n]);
        }
        prop_assert_eq!(&got, &want);
        for (at, n) in reads {
            if want.is_empty() { break; }
            let at = (u64::from(at)) % want.len() as u64;
            let mut b = vec![0u8; n];
            let k = src.read_at(at, &mut b);
            let end = (at as usize + n).min(want.len());
            prop_assert_eq!(&b[..k], &want[at as usize..end]);
        }
        prop_assert_eq!(src.read_at(want.len() as u64, &mut buf), 0);
    }

    #[test]
    fn frames_tile_the_stream_and_locate_finds_each_byte(len in 1usize..(40 * 16384), picks in proptest::collection::vec(any::<(u16, u16)>(), 1..4)) {
        let spans: Vec<Span> = picks.iter().map(|(a, b)| {
            let off = (usize::from(*a) * 13) % len;
            Span { off: off as u64, len: ((usize::from(*b) * 31) % (len - off + 1)) as u64 }
        }).collect();
        let plan = Plan::new(len as u64, &spans).unwrap();
        let mut at = 0u64;
        for r in 0..plan.ranges() {
            for k in 0..plan.range_groups(r).unwrap() {
                let f = plan.frame(r, k).unwrap();
                prop_assert_eq!(f.start, at);
                for probe in [f.start, f.proof_start(), f.data_start(), f.end() - 1] {
                    prop_assert_eq!(plan.locate(probe), Some(f));
                }
                prop_assert_eq!(f.follows, k > 0);
                at = f.end();
            }
        }
        prop_assert_eq!(at, plan.total());
        prop_assert_eq!(plan.locate(at), None);
    }

    #[test]
    fn spans_are_validated(len in 0u64..100_000, off in 0u64..200_000, n in 1u64..200_000) {
        let r = Plan::new(len, &[Span { off, len: n }]);
        prop_assert_eq!(r.is_err(), off + n > len);
    }
}

fn store_root(value: &[u8]) -> [u8; 32] {
    *blake3::hash(value).as_bytes()
}

#[test]
fn the_plan_is_closed_form_at_any_size() {
    // 2^30 bytes: the plan equals the encoder's length without walking a single group.
    let len = 1u64 << 30;
    let layout = Layout::new(len, 4).unwrap();
    let range = (len / 3)..(len / 3 + 5_000_000);
    let plan = Plan::new(
        len,
        &[Span {
            off: range.start,
            len: range.end - range.start,
        }],
    )
    .unwrap();
    let groups = range.end.div_ceil(16384) - range.start / 16384;
    assert_eq!(
        plan.total(),
        groups * GROUP_HDR as u64
            + encoded_len(
                layout,
                &(range.start / 16384 * 16384..range.end.div_ceil(16384) * 16384)
            )
            .unwrap()
    );
    // Near the largest value: no overflow, frames still tile.
    let huge = (1u64 << 62) - 1000;
    let plan = Plan::new(
        huge,
        &[
            Span {
                off: huge - 5000,
                len: 3000,
            },
            Span { off: 0, len: 1 },
        ],
    )
    .unwrap();
    let f0 = plan.frame(0, 0).unwrap();
    assert!(f0.plen > 0 && !f0.follows);
    assert_eq!(
        plan.locate(f0.end()),
        plan.frame(1, 0)
            .filter(|_| plan.range_groups(0) == Some(1))
            .or_else(|| plan.frame(0, 1))
    );
    assert!(
        Plan::new(huge, &[Span { off: 0, len: huge }; 32]).is_err(),
        "a response over 2^62 - 1 bytes is refused"
    );
    assert!(Plan::new(10, &[Span { off: 0, len: 1 }; 33]).is_err());
}

#[test]
fn the_source_window_is_the_serve_batch() {
    assert_eq!(SERVE_BATCH, 16);
    // A read in the middle of a long range, then one far before it, then one far after: all exact.
    let store = PStore::random(77, 200 * 16384);
    let value = store.content().bytes(0, store.len());
    let (_, ob) = build_outboard_vec(&value, 4).unwrap();
    let spans = [Span {
        off: 0,
        len: store.len(),
    }];
    let want = reference(&value, &ob, &spans);
    let plan = Plan::new(store.len(), &spans).unwrap();
    let mut src = ValueSource::new(store, store_root(&value), plan);
    for at in [want.len() / 2, 3, want.len() - 100, want.len() / 3, 0] {
        let mut b = vec![0u8; 5000];
        let n = src.read_at(at as u64, &mut b);
        assert_eq!(&b[..n], &want[at..(at + 5000).min(want.len())]);
    }
}

#[test]
fn a_source_over_a_store_that_lost_bytes_reads_short() {
    struct Gone(PStore);
    impl vinc_values::store::ValueRead for Gone {
        fn servable_len(&self, r: &[u8; 32]) -> Option<u64> {
            self.0.servable_len(r)
        }
        fn read_at(&self, _: &[u8; 32], _: u64, _: &mut [u8]) -> usize {
            0
        }
        fn read_outboard(&self, r: &[u8; 32], o: u64, d: &mut [u8]) -> usize {
            self.0.read_outboard(r, o, d)
        }
    }
    let store = PStore::random(78, 5 * 16384);
    let plan = Plan::new(
        store.len(),
        &[Span {
            off: 0,
            len: store.len(),
        }],
    )
    .unwrap();
    let root = store.root();
    let mut src = ValueSource::new(Gone(store), root, plan);
    let mut b = vec![0u8; 100_000];
    // The header and the proof come, the group bytes do not: short, so the transport resets the stream.
    let n = src.read_at(0, &mut b);
    assert!(n > 0 && n < 100_000);
}

#[test]
fn the_span_of_a_range_of_a_value_near_the_top_of_u64_does_not_overflow() {
    // The last group of a value of u64::MAX bytes ends past 2^64: rounding the range out to whole groups must clip to
    // the value (as `Plan::new` does), not wrap or panic.
    for len in [u64::MAX, u64::MAX - 1, u64::MAX - 16383, u64::MAX - 16384] {
        let tail = Plan::new(len, &[Span { off: len - 1, len: 1 }]).unwrap();
        let sp = tail.range_span(0).unwrap();
        assert_eq!(sp.end(), len, "the range ends at the value end");
        assert!(sp.off < len);
    }
}
