//! Tests of the loss estimate, the tail repair decision and the burst tracker. Part of the `transport_recovery` test
//! target.
#![allow(clippy::unwrap_used, clippy::indexing_slicing)]

use pinc_transport::recovery::{LossEstimate, REPAIR_MIN_AGE, REPAIR_THRESHOLD, SECOND, TailRepair};
use proptest::prelude::*;

// ---------------------------------------------------------------------------------------------------------------
// The loss estimate and tail repair
// ---------------------------------------------------------------------------------------------------------------

/// The estimate by its own rule: each acknowledged packet does `v -= v >> 5`, each lost one `v += (65536 - v) >> 5`.
fn model(mut v: u32, acked: u32, lost: u32) -> u32 {
    for _ in 0..acked {
        v -= v >> 5;
    }
    for _ in 0..lost {
        v += (65_536 - v) >> 5;
    }
    v
}

#[test]
fn a_reset_loss_estimate_is_the_estimate_of_a_new_endpoint() {
    let e = LossEstimate::new();
    e.record(500, 0);
    assert!(e.get() >= REPAIR_THRESHOLD);
    e.reset();
    assert_eq!(e.get(), LossEstimate::new().get());
    assert!(
        !e.should_send_repair(REPAIR_MIN_AGE, true, true),
        "a reset estimate repairs nothing"
    );
}

#[test]
fn the_loss_estimate_steps_once_per_packet_with_gain_1_32() {
    let e = LossEstimate::new();
    assert_eq!(e.get(), 0);
    e.record(0, 0);
    assert_eq!(e.get(), 0, "an empty batch is ignored");
    e.record(0, 100);
    assert_eq!(e.get(), 0);
    e.record(1, 0);
    assert_eq!(e.get(), 2048, "one lost packet: 65536 >> 5");
    e.record(1, 0);
    assert_eq!(e.get(), 2048 + ((65_536 - 2048) >> 5));
    e.record(0, 1);
    assert_eq!(
        e.get(),
        model(0, 0, 2) - (model(0, 0, 2) >> 5),
        "one acknowledged packet: v - (v >> 5)"
    );
    // Per packet, in order: acknowledged packets first, then lost ones.
    let e = LossEstimate::new();
    e.record(3, 0);
    e.record(2, 5);
    assert_eq!(e.get(), model(model(0, 0, 3), 5, 2));
    // Decay reaches the fixed point below 32 and growth the one above 65504; extremes do not overflow or hang.
    let e = LossEstimate::new();
    e.record(1, 0);
    e.record(0, 100_000);
    assert!(e.get() < 32);
    e.record(u32::MAX, u32::MAX);
    assert!(e.get() >= 65_504 && e.get() <= 65_536);
}

#[test]
fn a_one_percent_loss_pattern_keeps_the_estimate_above_the_threshold_after_each_loss() {
    // 1 lost in 100: right after each loss the average is far above the threshold of 328.
    let e = LossEstimate::new();
    for _ in 0..3000 {
        e.record(0, 99);
        e.record(1, 0);
    }
    assert!(e.get() > REPAIR_THRESHOLD, "got {}", e.get());
}

#[test]
fn tail_repair_needs_at_least_the_threshold_and_at_least_two_seconds() {
    assert_eq!(REPAIR_THRESHOLD, 328);
    assert_eq!(REPAIR_MIN_AGE, 2 * SECOND);
    let e = LossEstimate::new();
    let age = 3 * SECOND;
    assert!(!e.should_send_repair(age, true, true), "no loss yet");
    e.record(1, 0);
    assert!(e.should_send_repair(age, true, true));
    assert!(!e.should_send_repair(age, false, true), "queue not drained");
    assert!(!e.should_send_repair(age, true, false), "not a direct path");
    assert!(!e.should_send_repair(2 * SECOND - 1, true, true));
    assert!(
        e.should_send_repair(2 * SECOND, true, true),
        "exactly 2 s is old enough"
    );
    // Walk the estimate down by acknowledged packets; the decision flips exactly where v crosses 328, with 328 itself
    // enough.
    let e = LossEstimate::new();
    e.record(1, 0);
    let mut v = e.get();
    let mut seen_below = false;
    while v > 0 {
        assert_eq!(e.should_send_repair(age, true, true), v >= 328, "v = {v}");
        seen_below |= v < 328;
        let before = v;
        e.record(0, 1);
        v = e.get();
        if v == before {
            break;
        }
    }
    assert!(seen_below);
}

#[test]
fn the_loss_estimate_is_shared_by_reference_across_threads() {
    let e = LossEstimate::new();
    std::thread::scope(|s| {
        for t in 0..4u32 {
            let e = &e;
            s.spawn(move || {
                for i in 0..10_000u32 {
                    e.record(u32::from(i % 7 == t), 3);
                }
            });
        }
    });
    assert!(e.get() <= 65_536);
}

#[test]
fn tail_repair_follows_a_burst_of_exactly_one_plain_packet() {
    // One packet of plain bytes, then the queue drains: repair that packet.
    let mut t = TailRepair::new();
    t.on_packet(7, true, false);
    assert_eq!(t.on_drain(), Some(7));
    assert_eq!(t.on_drain(), None, "the drain resets the tracker");
    // A burst of two packets is never repaired, however plain.
    t.on_packet(8, true, false);
    t.on_packet(9, true, false);
    assert_eq!(t.on_drain(), None);
    // A third packet does not revive it.
    t.on_packet(10, true, false);
    t.on_packet(11, true, false);
    t.on_packet(12, true, false);
    assert_eq!(t.on_drain(), None);
    // A single packet that carried anything a repair cannot re-carry is not repaired...
    t.on_packet(13, true, true);
    assert_eq!(t.on_drain(), None);
    // ...nor is one without stream bytes.
    t.on_packet(14, false, false);
    assert_eq!(t.on_drain(), None);
    // A fresh burst after a drain starts over.
    t.on_packet(15, true, false);
    assert_eq!(t.on_drain(), Some(15));
}

#[test]
fn a_packet_with_no_stream_bytes_still_counts_in_the_burst() {
    let mut t = TailRepair::new();
    t.on_packet(1, true, false);
    t.on_packet(2, false, false);
    assert_eq!(t.on_drain(), None, "two packets in the burst");
}

proptest! {
    /// The loss estimate equals its per-packet rule.
    #[test]
    fn the_loss_estimate_equals_the_per_packet_model(batches in proptest::collection::vec((0u32..400, 0u32..400), 1..30)) {
        let e = LossEstimate::new();
        let mut v = 0u32;
        for (lost, acked) in batches {
            e.record(lost, acked);
            v = model(v, acked, lost);
            prop_assert_eq!(e.get(), v);
        }
    }

    /// The tracker offers a packet only after a burst of exactly one eligible packet.
    #[test]
    fn tail_repair_offers_only_single_packet_bursts(bursts in proptest::collection::vec(proptest::collection::vec((any::<bool>(), any::<bool>()), 0..5), 1..20)) {
        let mut t = TailRepair::new();
        let mut pn = 0;
        for burst in bursts {
            for &(plain, bad) in &burst {
                t.on_packet(pn, plain, bad);
                pn += 1;
            }
            let want = match burst.as_slice() {
                [(true, false)] => Some(pn - 1),
                _ => None,
            };
            prop_assert_eq!(t.on_drain(), want);
        }
    }
}
