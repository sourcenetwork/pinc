//! Property tests: the bound, varint and frame codecs round-trip, the index fingerprints behave as a set XOR, the
//! state machines reconcile arbitrary set pairs exactly under arbitrary limits, and arbitrary bytes never panic them.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::expect_used
)]

#[path = "reconcile_common.rs"]
mod common;

use common::{index, run_with, sorted, sym_diff};
use proptest::prelude::*;
use vinc_reconcile::wire::{count, frame_body, frame_len, put_bound, put_varint, read_bound};
use vinc_reconcile::{Fingerprint, Initiator, ItemIndex, Limits, Responder};
use vinc_wire::Reader;

fn small_item() -> impl Strategy<Value = Vec<u8>> {
    // A narrow alphabet makes shared prefixes, and items that are prefixes of others, common.
    prop::collection::vec(0u8..4, 0..24)
}

fn small_set() -> impl Strategy<Value = Vec<Vec<u8>>> {
    prop::collection::vec(small_item(), 0..120).prop_map(sorted)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn bounds_round_trip_against_the_previous_bound(bounds in prop::collection::vec(prop::collection::vec(0u8..3, 0..400), 1..8)) {
        let (mut buf, mut last_w) = (Vec::new(), Vec::new());
        for b in &bounds {
            put_bound(&mut buf, &mut last_w, b).unwrap();
        }
        let (mut r, mut last_r) = (Reader::new(&buf), Vec::new());
        for b in &bounds {
            read_bound(&mut last_r, &mut r, 400).unwrap();
            prop_assert_eq!(&last_r, b);
        }
        prop_assert!(r.is_empty());
    }

    #[test]
    fn a_bound_never_decodes_past_its_limit_or_its_predecessor(bytes in prop::collection::vec(any::<u8>(), 0..64), last in prop::collection::vec(any::<u8>(), 0..32), max in 0usize..40) {
        let mut l = last.clone();
        let mut r = Reader::new(&bytes);
        if read_bound(&mut l, &mut r, max).is_ok() {
            prop_assert!(l.len() <= max.max(last.len()));
        }
    }

    #[test]
    fn counts_round_trip(v in 0usize..(1 << 40)) {
        let mut buf = Vec::new();
        put_varint(&mut buf, v).unwrap();
        let mut r = Reader::new(&buf);
        prop_assert_eq!(count(&mut r).unwrap(), v);
        prop_assert!(r.is_empty());
    }

    #[test]
    fn frames_round_trip(body in prop::collection::vec(any::<u8>(), 0..2000)) {
        let mut msg = vec![(body.len() >> 16) as u8, (body.len() >> 8) as u8, body.len() as u8];
        msg.extend_from_slice(&body);
        prop_assert_eq!(frame_body(&msg).unwrap(), &body[..]);
        prop_assert_eq!(frame_len([msg[0], msg[1], msg[2]]), body.len());
        msg.push(0);
        prop_assert!(frame_body(&msg).is_err());
    }

    #[test]
    fn a_range_fingerprint_is_the_xor_of_its_items(set in small_set(), x in 0usize..130, y in 0usize..130) {
        let ix = index(&set);
        let (a, b) = (x.min(y).min(set.len()), x.max(y).min(set.len()));
        let want = set[a..b].iter().fold(Fingerprint::ZERO, |acc, it| acc ^ Fingerprint::of_item(it));
        prop_assert_eq!(ix.fingerprint(a, b).unwrap(), want);
    }

    #[test]
    fn the_xor_of_two_set_fingerprints_is_the_fingerprint_of_the_difference(a in small_set(), b in small_set()) {
        let (only_b, only_a) = sym_diff(&a, &b);
        let fp = |s: &[Vec<u8>]| s.iter().fold(Fingerprint::ZERO, |acc, it| acc ^ Fingerprint::of_item(it));
        prop_assert_eq!(fp(&a) ^ fp(&b), fp(&only_a) ^ fp(&only_b));
    }

    #[test]
    fn rank_is_the_count_of_smaller_items(set in small_set(), bound in small_item()) {
        let ix = index(&set);
        prop_assert_eq!(ix.rank(&bound).unwrap(), set.iter().filter(|it| **it < bound).count());
    }

    #[test]
    fn any_two_sets_reconcile_exactly_under_any_limits(
        a in small_set(),
        b in small_set(),
        max_message in 64usize..8192,
        swap in any::<bool>(),
    ) {
        let (a, b) = if swap { (b, a) } else { (a, b) };
        let limits = Limits { max_item: 32, max_message, ..Limits::default() };
        let (ia, ib) = (index(&a), index(&b));
        let res = run_with(&mut Initiator::new(limits), &mut Responder::new(limits), &ia, &ib, |_, _| {});
        match res {
            Ok(o) => {
                let (only_b, only_a) = sym_diff(&a, &b);
                prop_assert_eq!(sorted(o.here.clone()), only_b);
                prop_assert_eq!(sorted(o.there.clone()), only_a);
                prop_assert_eq!(o.here.len() + o.there.len(), sym_diff(&a, &b).0.len() + sym_diff(&a, &b).1.len());
            }
            // A message limit smaller than one differing range's description is a loud refusal, never a wrong answer.
            Err(e) => prop_assert!(matches!(e, vinc_reconcile::Error::MessageTooLarge), "{e:?}"),
        }
    }

    #[test]
    fn a_session_is_deterministic(a in small_set(), b in small_set()) {
        let (ia, ib) = (index(&a), index(&b));
        let mut runs = Vec::new();
        for _ in 0..2 {
            let mut log = Vec::new();
            run_with(&mut Initiator::new(Limits::default()), &mut Responder::new(Limits::default()), &ia, &ib, |_, m| log.push(m.clone())).unwrap();
            runs.push(log);
        }
        prop_assert_eq!(&runs[0], &runs[1]);
    }

    #[test]
    fn arbitrary_bytes_never_panic_either_state_machine(bytes in prop::collection::vec(any::<u8>(), 0..300), framed in any::<bool>(), set in small_set()) {
        let mut msg = bytes;
        if framed {
            let n = msg.len();
            msg.splice(0..0, [(n >> 16) as u8, (n >> 8) as u8, n as u8]);
        }
        let ix = index(&set);
        let limits = Limits { max_item: 32, max_message: 512, max_report: 512, max_rounds: 4 };
        let mut out = Vec::new();
        let _ = Responder::new(limits).handle(&ix, &msg, &mut out);
        let mut init = Initiator::new(limits);
        init.start(&ix, b"s", &mut out).unwrap();
        let _ = init.handle(&ix, &msg, &mut out);
    }
}
