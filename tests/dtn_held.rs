//! Tests of the per-block held set: its counts against its bits, and a reception into it that no interval cap
//! limits, finished from parity.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_lossless
)]

mod dtn_common;

use dtn_common::{bytes, keypair, make, plan, recipient};
use pinc_crypto::IdentityAlg;
use pinc_dtn::bundle::{Receiving, Reception};
use pinc_dtn::error::DtnError;
use pinc_dtn::held::{BlockHeld, HeldSet, held_len};
use pinc_dtn::layout::SliceLayout;
use proptest::prelude::*;

const NOW: u64 = 2_000;

proptest! {
    /// After any inserts, every block's count is the number of its held symbols, at most `k + m`, and a symbol is
    /// held exactly when it was inserted.
    #[test]
    fn counts_match_bits(k in 1u8..6, m in 0u8..4, data in 1u64..40, picks in prop::collection::vec(0u64..80, 0..60)) {
        let layout = SliceLayout::new(k, m, 0, data * 1008).unwrap();
        let mut h = BlockHeld::new(&layout, vec![0; held_len(&layout).unwrap()]).unwrap();
        let total = layout.total_symbols();
        for s in &picks {
            prop_assert_eq!(h.insert_symbol(*s), *s < total);
        }
        for s in 0..total {
            prop_assert_eq!(h.holds(s), picks.contains(&s));
        }
        for b in 0..layout.blocks() {
            let start = layout.block_start(b);
            let n = layout.block_n(b) as u64;
            let held = (start..start + n).filter(|s| h.holds(*s)).count();
            prop_assert_eq!(h.count(b), held);
            prop_assert!(h.count(b) <= layout.block_n(b));
        }
        let covered: u64 = (0..total).filter(|s| h.holds(*s)).count() as u64 * layout.slice_len();
        prop_assert_eq!(h.covered_len(), covered);
        let runs: u64 = h.runs().map(|r| r.end - r.start).sum();
        prop_assert_eq!(runs, covered);
        // The covered length is a running total: a set continued from an earlier set's buffer starts from its count.
        let mut buf = vec![0; held_len(&layout).unwrap()];
        let mut first = BlockHeld::new(&layout, &mut buf[..]).unwrap();
        for s in &picks {
            first.insert_symbol(*s);
        }
        let again = BlockHeld::new(&layout, &buf[..]).unwrap();
        prop_assert_eq!(again.covered_len(), covered);
    }
}

#[test]
fn only_whole_symbols_are_recorded() {
    let layout = SliceLayout::new(2, 1, 0, 3 * 1008).unwrap();
    let mut h = BlockHeld::new(&layout, vec![0; held_len(&layout).unwrap()]).unwrap();
    assert!(h.insert(1..1024).is_err(), "a range that starts inside a symbol");
    assert!(h.insert(0..1000).is_err(), "a range that ends inside a symbol");
    assert!(
        h.insert(0..layout.total_len() + 1024).is_err(),
        "a range past the bundle"
    );
    assert_eq!(h.covered_len(), 0, "a refused insert changes nothing");
    h.insert(1024..3072).unwrap();
    assert!(h.contains_range(1024..3072) && !h.contains_range(0..1024));
    assert_eq!(BlockHeld::new(&layout, vec![0; 1]).err(), Some(DtnError::Buffer));
}

/// A bundle of 300 blocks, received data only into a per-block held set, with one data symbol of every block left
/// out: a capped range set refuses it, the per-block set takes it, and finish rebuilds every block from parity.
#[test]
fn a_reception_of_many_blocks_finishes_from_parity() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let payload = bytes(3, 600 * 1008);
    let s = make(&sender, &to, plan(2, 1, 0), &payload, 4);
    let layout = s.signed.head().layout().unwrap();
    assert_eq!(layout.blocks(), 300);

    // Data symbol 0 of every block, and parity in place of data symbol 1.
    let asked: Vec<u64> = (0..layout.blocks())
        .flat_map(|b| [layout.block_start(b), layout.block_start(b) + 2])
        .collect();

    let mut capped_buf = vec![0; layout.total_len() as usize];
    let mut capped = Reception::<256>::new(&s.signed, &mut capped_buf, NOW).unwrap();
    let overflow = asked
        .iter()
        .map(|x| capped.feed(*x..*x + 1, &s.proof(*x..*x + 1)))
        .find(Result::is_err);
    assert_eq!(
        overflow,
        Some(Err(DtnError::ReceptionFull)),
        "a capped range set overflows"
    );

    let mut buf = vec![0; layout.total_len() as usize];
    let mut held = BlockHeld::new(&layout, vec![0; held_len(&layout).unwrap()]).unwrap();
    let mut rx = Receiving::resume(&s.signed, &mut buf, &mut held, NOW).unwrap();
    for x in &asked {
        rx.feed(*x..*x + 1, &s.proof(*x..*x + 1)).unwrap();
    }
    assert!(rx.is_decodable() && !rx.is_complete());
    let mut outboard = vec![0; layout.outboard_len().unwrap() as usize];
    let mut scratch = vec![0; rx.scratch_len().unwrap()];
    rx.finish(&mut outboard, &mut scratch).unwrap();
    assert!(rx.is_complete());
    assert_eq!(
        rx.sealed(),
        &s.sealed[..],
        "every block rebuilt to the sender's symbols"
    );
    assert_eq!(outboard, s.outboard);
    assert_eq!(held.covered_len(), layout.total_len());
}
