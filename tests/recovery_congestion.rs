//! Tests of application-limited growth and persistent congestion. Part of the `transport_recovery` test target.
#![allow(clippy::unwrap_used, clippy::indexing_slicing)]

use proptest::prelude::*;
use vinc_transport::recovery::{MIN_CWND, MS, SECOND, Sent};

use crate::{MSS, Rec, ack, assert_conserved, established, sent};

// ---------------------------------------------------------------------------------------------------------------
// Application-limited sending and persistent congestion
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn only_acks_of_packets_sent_with_the_window_in_use_grow_it() {
    let mut rec = Rec::new(MSS);
    let start = rec.cwnd();
    // One packet alone is far from filling the window: application limited.
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 10 * MS, &[(0, 0)], 0);
    assert_eq!(rec.cwnd(), start, "an application-limited ack does not grow the window");
    // Fill the window: the packets that reach (cwnd - one segment) in flight count as using it.
    for pn in 1..=40 {
        rec.on_packet_sent(sent(pn, 20 * MS)).unwrap();
    }
    ack(&mut rec, 30 * MS, &[(1, 1)], 0);
    assert_eq!(rec.cwnd(), start, "pn 1 was sent with an almost empty window");
    ack(&mut rec, 31 * MS, &[(2, 40)], 0);
    // Only pn 36 to 40 were sent with at least (cwnd - one segment) in flight.
    assert_eq!(
        rec.cwnd(),
        start + 5 * 1200,
        "five packets were sent with the window in use"
    );
}

#[test]
fn persistent_congestion_collapses_the_window() {
    let (mut rec, last) = persistent_setup(|_| false);
    let before = rec.cwnd();
    assert!(before > MIN_CWND);
    let (s, _) = ack(&mut rec, 1410 * MS, &[(last, last)], 0);
    assert!(
        !s.persistent_congestion,
        "only pn 1 and 2 are lost so far, 500 ms apart"
    );
    let t = rec.on_timeout(rec.next_timeout().unwrap(), |_| {});
    assert!(t.summary.persistent_congestion);
    assert_eq!(rec.cwnd(), MIN_CWND);
    assert!(!rec.cc().can_undo(), "nothing to undo after a collapse");
    assert!(rec.cc().recovery_start().is_none());
    assert!(rec.cc().ssthresh() >= MIN_CWND);
    assert_conserved(&rec);
}

/// pn 1..=3 sent at 200, 700 and 1300 ms (1100 ms apart, over three timeouts of about 825 ms), then pn 4 and 5;
/// `repair` picks the repair packets. Returns the recovery and the pn to acknowledge.
fn persistent_setup(repair: impl Fn(u64) -> bool) -> (Rec, u64) {
    let mut rec = established();
    for (pn, t) in [(1, 200), (2, 700), (3, 1300), (4, 1310), (5, 1311)] {
        let p = Sent {
            is_repair: repair(pn),
            ..sent(pn, t * MS)
        };
        rec.on_packet_sent(p).unwrap();
    }
    (rec, 5)
}

#[test]
fn a_short_run_of_losses_is_not_persistent_congestion() {
    let mut rec = established();
    for (pn, t) in [(1, 200), (2, 300), (3, 400), (4, 500), (5, 501)] {
        rec.on_packet_sent(sent(pn, t * MS)).unwrap();
    }
    ack(&mut rec, 700 * MS, &[(5, 5)], 0);
    let t = rec.on_timeout(rec.next_timeout().unwrap(), |_| {});
    assert!(!t.summary.persistent_congestion);
    assert!(rec.cwnd() > MIN_CWND);
}

#[test]
fn an_acknowledged_packet_breaks_the_run() {
    let (mut rec, _) = persistent_setup(|_| false);
    let (s, _) = ack(&mut rec, 1410 * MS, &[(5, 5), (2, 2)], 0);
    assert!(!s.persistent_congestion);
    let t = rec.on_timeout(rec.next_timeout().unwrap(), |_| {});
    assert!(
        !t.summary.persistent_congestion,
        "pn 2 was acknowledged between pn 1 and pn 3"
    );
    assert!(rec.cwnd() > MIN_CWND);
}

#[test]
fn repair_losses_are_never_persistent_congestion() {
    let (mut rec, last) = persistent_setup(|pn| pn <= 3);
    let before = rec.cwnd();
    let (s, _) = ack(&mut rec, 1410 * MS, &[(last, last)], 0);
    assert_eq!(s.lost_packets, 2);
    assert!(rec.cwnd() >= before, "repair losses do not touch the window");
    let t = rec.on_timeout(rec.next_timeout().unwrap(), |_| {});
    assert!(!t.summary.persistent_congestion);
}

#[test]
fn persistent_congestion_needs_an_earlier_round_trip_sample() {
    let mut rec = Rec::new(MSS);
    for (pn, t) in [(1, 200), (2, 700), (3, 1300), (4, 1400)] {
        rec.on_packet_sent(sent(pn, t * MS)).unwrap();
    }
    // A packet that is not ack-eliciting gives an acknowledgement but no round-trip sample.
    rec.on_packet_sent(Sent {
        ack_eliciting: false,
        ..sent(5, 1401 * MS)
    })
    .unwrap();
    ack(&mut rec, 1500 * MS, &[(5, 5)], 0);
    assert!(!rec.rtt().has_sample());
    let t = rec.on_timeout(rec.next_timeout().unwrap(), |_| {});
    let t2 = rec.on_timeout(rec.next_timeout().unwrap_or(10 * SECOND), |_| {});
    assert!(!t.summary.persistent_congestion && !t2.summary.persistent_congestion);
    assert!(rec.cwnd() > MIN_CWND);
}

proptest! {
    /// While every packet is sent with the window nearly empty, the window never grows.
    #[test]
    fn the_window_does_not_grow_across_an_app_limited_stretch(
        steps in proptest::collection::vec((1u32..=1200, 1u64..200, 0u64..30), 1..120)
    ) {
        let mut rec = Rec::new(MSS);
        let start = rec.cwnd();
        let (mut pn, mut now) = (0u64, SECOND);
        for (size, rtt_ms, idle_ms) in steps {
            now += idle_ms * MS;
            rec.on_packet_sent(Sent { size, ..sent(pn, now) }).unwrap();
            now += rtt_ms * MS;
            let (s, _) = ack(&mut rec, now, &[(pn, pn)], 0);
            prop_assert_eq!(s.acked_packets, 1);
            prop_assert_eq!(rec.cwnd(), start);
            pn += 1;
        }
    }
}

#[test]
fn persistent_congestion_scan_and_collapse_do_not_allocate() {
    let (mut rec, last) = persistent_setup(|_| false);
    let before = rec.cwnd();
    let mut collapsed = false;
    let stats = vinc_tests::measure(|| {
        rec.on_ack_received(1410 * MS, std::iter::once(last..=last), 0, |_| {})
            .unwrap();
        let due = rec.next_timeout().unwrap();
        collapsed = rec.on_timeout(due, |_| {}).summary.persistent_congestion;
    });
    assert_eq!(stats.count(), 0, "the persistent-congestion path allocated");
    assert!(collapsed);
    assert!(before > rec.cwnd());
}
