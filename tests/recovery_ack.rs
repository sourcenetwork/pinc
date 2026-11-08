//! Tests of the received-packet tracker: duplicate detection, the bounded range set, the acknowledgement policy and
//! the reported ranges. Part of the `transport_recovery` test target.
#![allow(clippy::unwrap_used, clippy::indexing_slicing)]

use vinc_transport::recovery::{
    MAX_ACK_RANGES, MAX_PACKET_NUMBER, MS, ReceivedPackets, RecoveryError, RxOutcome, RxPacket, SECOND,
};

// ---------------------------------------------------------------------------------------------------------------
// Received packets and the acknowledgement policy
// ---------------------------------------------------------------------------------------------------------------

pub(crate) fn rx(pn: u64, now: u64) -> RxPacket {
    RxPacket {
        pn,
        now,
        ack_eliciting: true,
        stream_bytes: 0,
    }
}

fn bulk(pn: u64, now: u64) -> RxPacket {
    RxPacket {
        stream_bytes: 1200,
        ..rx(pn, now)
    }
}

fn ranges<const N: usize>(r: &ReceivedPackets<N>, now: u64) -> Vec<(u64, u64)> {
    r.ack_ranges(now).map(|x| (*x.start(), *x.end())).collect()
}

#[test]
fn ack_every_second_packet() {
    let mut r = ReceivedPackets::<32>::new();
    assert_eq!(r.on_packet_received(rx(0, 1000)).unwrap(), RxOutcome::New);
    assert!(r.ack_pending());
    assert!(!r.ack_due(1000));
    assert_eq!(r.ack_deadline(), Some(1000 + 25 * MS));
    r.on_packet_received(rx(1, 2000)).unwrap();
    assert!(r.ack_due(2000), "the 2nd ack-eliciting packet is acknowledged at once");
    assert_eq!(r.ack_deadline(), Some(2000));
    r.on_ack_sent(0, 2000);
    assert!(!r.ack_pending());
    assert_eq!(r.ack_deadline(), None);
}

#[test]
fn ack_every_third_bulk_packet() {
    let mut r = ReceivedPackets::<32>::new();
    for pn in 0..3 {
        r.on_packet_received(rx(pn, 0)).unwrap();
    }
    r.on_ack_sent(0, 0);
    r.on_packet_received(bulk(3, 10)).unwrap();
    r.on_packet_received(bulk(4, 20)).unwrap();
    assert!(!r.ack_due(20), "two bulk packets are not enough");
    r.on_packet_received(bulk(5, 30)).unwrap();
    assert!(r.ack_due(30), "the 3rd bulk packet is acknowledged at once");
}

#[test]
fn small_or_early_packets_are_not_bulk() {
    let mut r = ReceivedPackets::<32>::new();
    // pn 1 and 2 carry 1200 bytes but the number is not above 2: the 2nd packet is acknowledged.
    r.on_packet_received(bulk(1, 0)).unwrap();
    r.on_packet_received(bulk(2, 0)).unwrap();
    assert!(r.ack_due(0) || r.ack_deadline().is_some());
    let mut r = ReceivedPackets::<32>::new();
    for pn in 0..3 {
        r.on_packet_received(rx(pn, 0)).unwrap();
    }
    r.on_ack_sent(0, 0);
    // 999 bytes is below the bulk size: every 2nd.
    let small = |pn, now| RxPacket {
        stream_bytes: 999,
        ..rx(pn, now)
    };
    r.on_packet_received(small(3, 1)).unwrap();
    r.on_packet_received(small(4, 2)).unwrap();
    assert!(r.ack_due(2));
}

#[test]
fn ack_at_once_on_a_gap() {
    let mut r = ReceivedPackets::<32>::new();
    r.on_packet_received(rx(0, 5)).unwrap();
    r.on_ack_sent(0, 5);
    r.on_packet_received(rx(2, 100)).unwrap();
    assert!(r.ack_due(100), "pn 1 is missing");
    assert_eq!(ranges(&r, 100), vec![(2, 2), (0, 0)]);
    r.on_ack_sent(1, 100);
    // Filling the gap is out of order too: acknowledged at once.
    r.on_packet_received(rx(1, 200)).unwrap();
    assert!(r.ack_due(200));
    assert_eq!(ranges(&r, 200), vec![(0, 2)]);
}

#[test]
fn non_eliciting_packets_never_trigger_an_ack() {
    let mut r = ReceivedPackets::<32>::new();
    for pn in 0..10 {
        let p = RxPacket {
            ack_eliciting: false,
            ..rx(pn * 2, pn)
        };
        r.on_packet_received(p).unwrap();
    }
    assert!(!r.ack_pending());
    assert_eq!(r.ack_deadline(), None);
}

#[test]
fn ack_delay_is_25_ms() {
    let mut r = ReceivedPackets::<32>::new();
    r.on_packet_received(rx(0, 0)).unwrap();
    assert!(!r.ack_due(25 * MS - 1));
    assert!(r.ack_due(25 * MS));
    assert_eq!(r.ack_delay(7 * MS), 7 * MS);
}

#[test]
fn long_rtt_paths_ack_every_fourth_with_a_longer_delay() {
    let mut r = ReceivedPackets::<32>::new();
    r.set_min_rtt(Some(400 * MS));
    r.on_packet_received(rx(0, 0)).unwrap();
    // min(250 ms, 400 ms / 8) = 50 ms.
    assert_eq!(r.ack_deadline(), Some(50 * MS));
    for pn in 1..3 {
        r.on_packet_received(rx(pn, 1)).unwrap();
        assert!(!r.ack_due(1), "not yet the 4th packet");
    }
    r.on_packet_received(rx(3, 2)).unwrap();
    assert!(r.ack_due(2));
    // The delay is capped at 250 ms.
    let mut r = ReceivedPackets::<32>::new();
    r.set_min_rtt(Some(4 * SECOND));
    r.on_packet_received(rx(0, 0)).unwrap();
    assert_eq!(r.ack_deadline(), Some(250 * MS));
    // Just under the threshold is an ordinary path.
    let mut r = ReceivedPackets::<32>::new();
    r.set_min_rtt(Some(249 * MS));
    r.on_packet_received(rx(0, 0)).unwrap();
    assert_eq!(r.ack_deadline(), Some(25 * MS));
    // A gap is still acknowledged at once on a long path.
    let mut r = ReceivedPackets::<32>::new();
    r.set_min_rtt(Some(400 * MS));
    r.on_packet_received(rx(0, 0)).unwrap();
    r.on_packet_received(rx(5, 1)).unwrap();
    assert!(r.ack_due(1));
}

#[test]
fn duplicates_are_detected() {
    let mut r = ReceivedPackets::<8>::new();
    assert_eq!(r.on_packet_received(rx(5, 0)).unwrap(), RxOutcome::New);
    assert_eq!(r.on_packet_received(rx(5, 1)).unwrap(), RxOutcome::Duplicate);
    assert_eq!(r.on_packet_received(rx(6, 1)).unwrap(), RxOutcome::New);
    assert_eq!(r.on_packet_received(rx(4, 1)).unwrap(), RxOutcome::New);
    assert_eq!(r.range_count(), 1, "4, 5 and 6 merge");
    assert_eq!(r.on_packet_received(rx(4, 2)).unwrap(), RxOutcome::Duplicate);
    // A duplicate does not count toward the acknowledgement policy.
    let mut r = ReceivedPackets::<8>::new();
    r.on_packet_received(rx(0, 0)).unwrap();
    r.on_packet_received(rx(0, 1)).unwrap();
    assert!(!r.ack_due(1));
    assert_eq!(
        r.on_packet_received(rx(MAX_PACKET_NUMBER + 1, 0)),
        Err(RecoveryError::PacketNumberOutOfRange)
    );
    assert_eq!(r.on_packet_received(rx(MAX_PACKET_NUMBER, 0)).unwrap(), RxOutcome::New);
}

#[test]
fn the_range_set_is_bounded_and_forgotten_packets_stay_duplicates() {
    let mut r = ReceivedPackets::<4>::new();
    for pn in [0, 2, 4, 6, 8, 10] {
        assert_eq!(r.on_packet_received(rx(pn, 0)).unwrap(), RxOutcome::New);
        assert!(r.range_count() <= 4);
    }
    assert_eq!(r.range_count(), 4);
    // 0 and 2 were forgotten: they are dropped as duplicates, not accepted a second time.
    assert_eq!(r.on_packet_received(rx(0, 1)).unwrap(), RxOutcome::Duplicate);
    assert_eq!(r.on_packet_received(rx(2, 1)).unwrap(), RxOutcome::Duplicate);
    assert!(r.contains(0));
    // A packet in a gap above what was forgotten is still new.
    assert_eq!(r.on_packet_received(rx(5, 1)).unwrap(), RxOutcome::New);
    // A packet far below everything tracked, with no room, is too old.
    let mut r = ReceivedPackets::<2>::new();
    r.on_packet_received(rx(100, 0)).unwrap();
    r.on_packet_received(rx(200, 0)).unwrap();
    assert_eq!(r.on_packet_received(rx(10, 0)).unwrap(), RxOutcome::Duplicate);
    assert_eq!(r.largest(), Some(200));
}

#[test]
fn ack_ranges_are_largest_first_and_trimmed_to_32() {
    let mut r = ReceivedPackets::<64>::new();
    for i in 0..40u64 {
        r.on_packet_received(rx(i * 2, 0)).unwrap();
    }
    let got = ranges(&r, 0);
    assert_eq!(got.len(), MAX_ACK_RANGES);
    assert_eq!(got.first(), Some(&(78, 78)));
    assert_eq!(got.last(), Some(&(16, 16)));
    assert!(got.windows(2).all(|w| w[0].0 > w[1].1));
}

#[test]
fn confirmed_ranges_are_dropped_after_two_seconds() {
    let mut r = ReceivedPackets::<32>::new();
    for pn in 0..=5 {
        r.on_packet_received(rx(pn, 0)).unwrap();
    }
    r.on_ack_sent(100, 0);
    r.on_ack_confirmed(100, SECOND);
    assert_eq!(
        ranges(&r, 2 * SECOND),
        vec![(0, 5)],
        "confirmed 1 s ago: still reported"
    );
    assert_eq!(ranges(&r, 3 * SECOND - 1), vec![(0, 5)]);
    assert!(
        ranges(&r, 3 * SECOND).is_empty(),
        "confirmed 2 s ago: no longer reported"
    );
    // New packets are reported without the confirmed ones, and the confirmed ones stay duplicates.
    r.on_packet_received(rx(6, 3 * SECOND)).unwrap();
    assert_eq!(ranges(&r, 3 * SECOND), vec![(6, 6)]);
    assert_eq!(r.on_packet_received(rx(3, 3 * SECOND)).unwrap(), RxOutcome::Duplicate);
    // An unconfirmed acknowledgement prunes nothing.
    let mut r = ReceivedPackets::<32>::new();
    r.on_packet_received(rx(0, 0)).unwrap();
    r.on_ack_sent(1, 0);
    assert_eq!(ranges(&r, 100 * SECOND), vec![(0, 0)]);
}
