//! Reconciliation of whole sets: the transferred items equal the symmetric difference at every difference size, the
//! cost follows the difference, cold and tiny sides stream, and items of any length work.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::expect_used
)]

#[path = "reconcile_common.rs"]
mod common;

use common::{Item, assert_exact, fixed_set, index, mutate, run, run_with, sym_diff, var_set};
use pinc_reconcile::{Initiator, Limits, Responder};
use pinc_tests::SplitMix64;

/// Set sizes of the exactness test: the specification's 10^6.
const BIG: usize = 1_000_000;
const ITEM: usize = 40;

#[test]
fn million_item_sets_with_every_difference_transfer_exactly_the_symmetric_difference() {
    let mut rng = SplitMix64::new(0xA11CE);
    let base = fixed_set(&mut rng, BIG, ITEM);
    let ia = index(&base);
    for d in [0usize, 1, 10, 1000, 100_000] {
        let (b, added, removed) = mutate(&mut rng, &base, d, ITEM);
        let ib = index(&b);
        let o = run_with(
            &mut Initiator::new(Limits::default()),
            &mut Responder::new(Limits::default()),
            &ia,
            &ib,
            |_, _| {},
        )
        .unwrap();
        assert_eq!(o.here.len(), added.len(), "d = {d}");
        assert_eq!(o.there.len(), removed.len(), "d = {d}");
        assert_eq!(common::sorted(o.here.clone()), added, "d = {d}: missing here");
        assert_eq!(common::sorted(o.there.clone()), removed, "d = {d}: missing there");
        eprintln!("d = {d:>6}: {:>9} bytes, {:>3} messages", o.bytes(), o.messages);
    }
}

#[test]
fn identical_sets_cost_one_round_trip() {
    let mut rng = SplitMix64::new(1);
    let a = fixed_set(&mut rng, 5000, ITEM);
    let o = run(&a, &a);
    assert!(o.here.is_empty() && o.there.is_empty());
    assert_eq!(o.messages, 2, "the opening message and the empty answer");
    assert!(o.bytes() < 1000, "{} bytes", o.bytes());
}

#[test]
fn cost_follows_the_difference_not_the_set() {
    let mut rng = SplitMix64::new(2);
    let n = 200_000;
    let base = fixed_set(&mut rng, n, ITEM);
    let ia = index(&base);
    let mut rows = Vec::new();
    for d in [1usize, 10, 100, 1000, 10_000] {
        let (b, ..) = mutate(&mut rng, &base, d, ITEM);
        let ib = index(&b);
        let o = run_with(
            &mut Initiator::new(Limits::default()),
            &mut Responder::new(Limits::default()),
            &ia,
            &ib,
            |_, _| {},
        )
        .unwrap();
        // The item bytes alone are the floor: every differing item crosses the wire once.
        let floor = d * (ITEM + 1);
        assert!(
            o.bytes() >= floor,
            "d = {d}: {} bytes is below the floor {floor}",
            o.bytes()
        );
        rows.push((d, o.bytes(), o.messages));
        eprintln!(
            "n = {n}, d = {d:>6}: {:>8} bytes ({:.1} per item), {:>3} messages",
            o.bytes(),
            o.bytes() as f64 / d as f64,
            o.messages
        );
    }
    for &(d, bytes, messages) in &rows {
        // An isolated difference costs one 16-way split per level (about 4.4 levels at this size, 16 parts of about
        // 25 bytes each) plus a leaf, so under 2 KiB; denser differences share the splits and cost less each. The
        // rounds follow log16 of the set, not the difference.
        assert!(bytes <= 2000 * d + 2000, "d = {d}: {bytes} bytes is not proportional");
        assert!(messages <= 14, "d = {d}: {messages} messages");
    }
    // A tenfold larger difference costs between 2 and 15 times the bytes: proportional, not constant, not quadratic.
    for w in rows.windows(2) {
        let ratio = w[1].1 as f64 / w[0].1 as f64;
        assert!(
            (1.5..=15.0).contains(&ratio),
            "d {} -> {}: cost ratio {ratio:.1}",
            w[0].0,
            w[1].0
        );
    }
    // A ten times larger set with the same difference costs under three times the bytes: sparser differences need
    // more levels of splits (log16 of the set), but nothing near ten times.
    let small = &base[..n / 10];
    let (b, ..) = mutate(&mut rng, small, 100, ITEM);
    let o_small = run(small, &b);
    let (b2, ..) = mutate(&mut rng, &base, 100, ITEM);
    let o_big = run(&base, &b2);
    assert!(
        o_big.bytes() < 3 * o_small.bytes(),
        "{} vs {}",
        o_big.bytes(),
        o_small.bytes()
    );
}

#[test]
fn disjoint_and_one_sided_sets_are_exact() {
    let mut rng = SplitMix64::new(3);
    let a = fixed_set(&mut rng, 3000, ITEM);
    let b = fixed_set(&mut rng, 4000, ITEM);
    assert_exact(&run(&a, &b), &a, &b);
    assert_exact(&run(&a, &a[..1000]), &a, &a[..1000]);
    assert_exact(&run(&a[..1000], &a), &a[..1000], &a);
}

#[test]
fn a_cold_initiator_makes_the_responder_stream_its_list() {
    let mut rng = SplitMix64::new(4);
    let big = fixed_set(&mut rng, 20_000, ITEM);
    for na in [0usize, 5, 1999] {
        let small: Vec<Item> = big
            .iter()
            .step_by(big.len() / na.max(1) + 1)
            .take(na)
            .cloned()
            .collect();
        let o = run(&small, &big);
        assert_exact(&o, &small, &big);
        // The responder sent its whole list once and the initiator needed no further round.
        assert!(o.bytes_down >= big.len() * ITEM, "na = {na}");
        assert_eq!(o.messages, 2, "na = {na}: one opening message and the stream");
    }
    // At a tenth of the responder's size the rule no longer applies.
    let tenth: Vec<Item> = big.iter().step_by(10).cloned().collect();
    let o = run(&tenth, &big);
    assert_exact(&o, &tenth, &big);
    assert!(o.messages > 2);
}

#[test]
fn a_tiny_responder_streams_its_list() {
    let mut rng = SplitMix64::new(5);
    let a = fixed_set(&mut rng, 10_000, ITEM);
    for nb in [0usize, 1, 32] {
        let b = fixed_set(&mut rng, nb, ITEM);
        let o = run(&a, &b);
        assert_exact(&o, &a, &b);
        assert_eq!(o.messages, 2, "nb = {nb}");
    }
    // A tiny initiator against a tiny responder, including two empty sets.
    for (na, nb) in [(0, 0), (1, 0), (0, 1), (3, 3), (32, 33)] {
        let a = fixed_set(&mut rng, na, ITEM);
        let b = fixed_set(&mut rng, nb, ITEM);
        assert_exact(&run(&a, &b), &a, &b);
    }
}

#[test]
fn a_long_cold_stream_is_cut_into_chunks_within_the_message_limit() {
    let mut rng = SplitMix64::new(6);
    let big = fixed_set(&mut rng, 30_000, ITEM);
    let a: Vec<Item> = big.iter().step_by(1000).cloned().collect();
    let limits = Limits {
        max_message: 16_384,
        ..Limits::default()
    };
    let (ia, ib) = (index(&a), index(&big));
    let mut largest = 0;
    let o = run_with(
        &mut Initiator::new(limits),
        &mut Responder::new(limits),
        &ia,
        &ib,
        |_, m| {
            largest = largest.max(m.len());
        },
    )
    .unwrap();
    assert_exact(&o, &a, &big);
    assert!(o.messages > 60, "{} messages", o.messages);
    assert!(largest <= 16_384 + 100, "largest message {largest}");
}

#[test]
fn items_of_any_length_reconcile_exactly() {
    let mut rng = SplitMix64::new(7);
    for max_len in [2usize, 9, 70, 700] {
        let a = var_set(&mut rng, 4000, max_len);
        let mut b = a.clone();
        b.retain(|_| !rng.next_u64().is_multiple_of(7));
        b.extend(var_set(&mut rng, 300, max_len));
        let b = common::sorted(b);
        assert_exact(&run(&a, &b), &a, &b);
        assert_exact(&run(&b, &a), &b, &a);
    }
    // Empty and prefix-related items.
    let a: Vec<Item> = vec![vec![0], vec![0, 0], vec![0, 0, 0], vec![1], vec![1, 0]];
    let b: Vec<Item> = vec![vec![0, 0], vec![0, 0, 1], vec![1], vec![1, 0, 0]];
    assert_exact(&run(&a, &b), &a, &b);
}

#[test]
fn an_item_longer_than_the_limit_is_refused_loudly() {
    let a = vec![vec![7u8; 100]];
    let b = vec![vec![8u8; 10]];
    let (ia, ib) = (index(&a), index(&b));
    let limits = Limits {
        max_item: 50,
        ..Limits::default()
    };
    let r = run_with(
        &mut Initiator::new(limits),
        &mut Responder::new(Limits::default()),
        &ia,
        &ib,
        |_, _| {},
    );
    assert!(r.is_err(), "{r:?}");
}

#[test]
fn the_difference_is_independent_of_which_side_starts() {
    let mut rng = SplitMix64::new(8);
    let a = fixed_set(&mut rng, 20_000, ITEM);
    let (b, ..) = mutate(&mut rng, &a, 500, ITEM);
    let ab = run(&a, &b);
    let ba = run(&b, &a);
    assert_eq!(common::sorted(ab.here), common::sorted(ba.there));
    assert_eq!(common::sorted(ab.there), common::sorted(ba.here));
    let (only_b, only_a) = sym_diff(&a, &b);
    assert_eq!(only_b.len() + only_a.len(), 500);
}
