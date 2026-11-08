//! Tests of the received-packet tracker: duplicate detection, the bounded range set, the acknowledgement policy, the
//! reported ranges and the confirmation bookkeeping. Part of the `transport_recovery` test target.
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

fn one(a: u64, b: u64) -> std::iter::Once<std::ops::RangeInclusive<u64>> {
    std::iter::once(a..=b)
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
    // Rule: every 2nd ack-eliciting packet is acknowledged at once; otherwise 25 ms after the first pending one.
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
fn bulk_packets_are_acknowledged_every_third_once_the_largest_received_number_is_2() {
    // Rule: bulk (at least 1000 stream bytes) when the largest received number is at least 2: every 3rd.
    let mut r = ReceivedPackets::<32>::new();
    r.on_packet_received(bulk(0, 0)).unwrap();
    r.on_packet_received(bulk(1, 1)).unwrap();
    assert!(
        r.ack_due(1),
        "the largest received number is 1: not bulk yet, so every 2nd"
    );
    r.on_ack_sent(100, 1);
    r.on_packet_received(bulk(2, 10)).unwrap();
    r.on_packet_received(bulk(3, 20)).unwrap();
    assert!(!r.ack_due(20), "from pn 2 on, two bulk packets are not enough");
    r.on_packet_received(bulk(4, 30)).unwrap();
    assert!(r.ack_due(30), "the 3rd bulk packet is acknowledged at once");
}

#[test]
fn small_packets_are_never_bulk() {
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
fn a_member_s_hub_session_acknowledges_every_fourth_packet() {
    let mut r = ReceivedPackets::<32>::new();
    r.set_every(Some(4));
    for pn in 0..3 {
        r.on_packet_received(rx(pn, pn)).unwrap();
        assert!(!r.ack_due(pn), "packet {pn}");
    }
    assert_eq!(
        r.ack_deadline(),
        Some(25 * MS),
        "the delay still runs from the first pending packet"
    );
    r.on_packet_received(rx(3, 3)).unwrap();
    assert!(r.ack_due(3), "the 4th");
    r.on_ack_sent(0, 3);
    // Bulk does not change the override; a gap is still acknowledged at once.
    r.on_packet_received(bulk(4, 10)).unwrap();
    r.on_packet_received(bulk(5, 11)).unwrap();
    r.on_packet_received(bulk(6, 12)).unwrap();
    assert!(!r.ack_due(12));
    r.on_packet_received(rx(8, 13)).unwrap();
    assert!(r.ack_due(13));
    // Restoring the default: every 2nd again.
    let mut r = ReceivedPackets::<32>::new();
    r.set_every(Some(4));
    r.set_every(None);
    r.on_packet_received(rx(0, 0)).unwrap();
    r.on_packet_received(rx(1, 1)).unwrap();
    assert!(r.ack_due(1));
}

#[test]
fn ack_at_once_when_the_number_is_not_the_one_after_the_largest() {
    // Rule: pn != largest + 1 (the first packet expects 0).
    let mut r = ReceivedPackets::<32>::new();
    r.on_packet_received(rx(3, 5)).unwrap();
    assert!(r.ack_due(5), "the first packet is 3, not 0");
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
fn the_ack_delay_is_25_ms_from_the_first_pending_packet() {
    let mut r = ReceivedPackets::<32>::new();
    r.on_packet_received(rx(0, 0)).unwrap();
    assert!(!r.ack_due(25 * MS - 1));
    assert!(r.ack_due(25 * MS));
    assert_eq!(r.ack_deadline(), Some(25 * MS));
}

#[test]
fn long_rtt_paths_ack_every_fourth_with_a_longer_delay() {
    // From a minimum of 250 ms: delay = min(250 ms, max(25 ms, min_rtt / 8)), at least every 4th packet.
    for (min_rtt, delay) in [
        (250 * MS, 250 * MS / 8),
        (400 * MS, 50 * MS),
        (4 * SECOND, 250 * MS),
        (10 * SECOND, 250 * MS),
    ] {
        let mut r = ReceivedPackets::<32>::new();
        r.set_min_rtt(Some(min_rtt));
        r.on_packet_received(rx(0, 0)).unwrap();
        assert_eq!(r.ack_deadline(), Some(delay), "min_rtt {min_rtt}");
        for pn in 1..3 {
            r.on_packet_received(rx(pn, 1)).unwrap();
            assert!(!r.ack_due(1), "not yet the 4th packet");
        }
        r.on_packet_received(rx(3, 2)).unwrap();
        assert!(r.ack_due(2));
    }
    // Just under the threshold is an ordinary path.
    let mut r = ReceivedPackets::<32>::new();
    r.set_min_rtt(Some(249 * MS));
    r.on_packet_received(rx(0, 0)).unwrap();
    assert_eq!(r.ack_deadline(), Some(25 * MS));
    r.on_packet_received(rx(1, 1)).unwrap();
    assert!(r.ack_due(1));
    // A gap is still acknowledged at once on a long path.
    let mut r = ReceivedPackets::<32>::new();
    r.set_min_rtt(Some(400 * MS));
    r.on_packet_received(rx(0, 0)).unwrap();
    r.on_packet_received(rx(5, 1)).unwrap();
    assert!(r.ack_due(1));
}

#[test]
fn the_delay_is_fixed_when_the_first_packet_arrives() {
    let mut r = ReceivedPackets::<32>::new();
    r.on_packet_received(rx(0, 0)).unwrap();
    r.set_min_rtt(Some(400 * MS));
    r.on_packet_received(rx(1, MS)).unwrap();
    // On a long path the 2nd packet is no longer enough, but the deadline set by the first (25 ms) holds.
    assert_eq!(r.ack_deadline(), Some(25 * MS));
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
fn thirty_two_ranges_are_tracked_and_forgotten_packets_stay_duplicates() {
    let mut r = ReceivedPackets::<32>::new();
    for i in 0..32u64 {
        assert_eq!(r.on_packet_received(rx(i * 2, 0)).unwrap(), RxOutcome::New);
    }
    assert_eq!(r.range_count(), 32);
    // The 33rd range pushes the lowest one out; it and everything below stay duplicates (the replay floor).
    assert_eq!(r.on_packet_received(rx(100, 0)).unwrap(), RxOutcome::New);
    assert_eq!(r.range_count(), 32);
    assert_eq!(r.on_packet_received(rx(0, 1)).unwrap(), RxOutcome::Duplicate);
    assert!(r.contains(0));
    // A packet in a gap above what was forgotten is still new.
    assert_eq!(r.on_packet_received(rx(3, 1)).unwrap(), RxOutcome::New);
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

// ---------------------------------------------------------------------------------------------------------------
// Confirmed ranges: 48 acknowledgement records, 32 queued confirmations, a 2 s hold
// ---------------------------------------------------------------------------------------------------------------

/// Old isolated ranges (0), (2), (4), (6), then `run` consecutive packets from 10, one acknowledgement sent after
/// each (our packet number 100 + k reports the largest number 10 + k).
fn with_a_run(run: u64) -> ReceivedPackets<64> {
    let mut r = ReceivedPackets::<64>::new();
    for pn in [0, 2, 4, 6] {
        r.on_packet_received(rx(pn, 0)).unwrap();
    }
    for k in 0..run {
        r.on_packet_received(rx(10 + k, 0)).unwrap();
        r.on_ack_sent(100 + k, 0);
    }
    r
}

#[test]
fn only_the_newest_range_is_reported_two_seconds_after_the_peer_confirmed_an_ack_above_the_older_ranges() {
    // pn 0..=2 and 4..=5 arrive and an ACK reporting 5 goes out as our packet 100; the peer acknowledges it at 1 s.
    let mut r = ReceivedPackets::<32>::new();
    for pn in [0, 1, 2, 4, 5] {
        r.on_packet_received(rx(pn, 0)).unwrap();
    }
    r.on_ack_sent(100, 0);
    r.on_peer_ack(SECOND, &one(100, 100));
    // pn 6 extends the newest range: the older range (0..=2) ends below the confirmed 5.
    r.on_packet_received(rx(6, 2 * SECOND)).unwrap();
    assert_eq!(
        ranges(&r, 3 * SECOND - 1),
        vec![(4, 6), (0, 2)],
        "confirmed 2 s - 1 ns ago: all ranges"
    );
    assert_eq!(
        ranges(&r, 3 * SECOND),
        vec![(4, 6)],
        "confirmed 2 s ago: only the newest range"
    );
    // pn 9 makes (4..=6) the second-newest, ending at 6 >= 5: everything is reported again.
    r.on_packet_received(rx(9, 3 * SECOND)).unwrap();
    assert_eq!(ranges(&r, 3 * SECOND), vec![(9, 9), (4, 6), (0, 2)]);
    // The old numbers stay duplicates.
    assert_eq!(r.on_packet_received(rx(1, 3 * SECOND)).unwrap(), RxOutcome::Duplicate);
}

#[test]
fn an_unconfirmed_acknowledgement_prunes_nothing() {
    let mut r = ReceivedPackets::<32>::new();
    r.on_packet_received(rx(0, 0)).unwrap();
    r.on_packet_received(rx(2, 0)).unwrap();
    r.on_ack_sent(1, 0);
    r.on_packet_received(rx(3, 0)).unwrap();
    assert_eq!(ranges(&r, 100 * SECOND), vec![(2, 3), (0, 0)]);
}

#[test]
fn an_ack_of_a_packet_that_carried_no_acknowledgement_confirms_nothing() {
    let mut r = with_a_run(3);
    r.on_peer_ack(SECOND, &one(500, 600));
    assert_eq!(ranges(&r, 10 * SECOND).len(), 5);
}

#[test]
fn forty_eight_acknowledgement_records_are_remembered() {
    // 52 acknowledgements sent: records 100..=103 are forgotten (the oldest), 104..=151 are kept.
    let mut r = with_a_run(52);
    r.on_peer_ack(SECOND, &one(100, 100));
    assert_eq!(
        ranges(&r, 10 * SECOND).len(),
        5,
        "a forgotten record confirms nothing: the old ranges are still reported"
    );
    // A kept record reports the largest number 10 + 10 = 20: the old ranges end below it.
    r.on_peer_ack(SECOND, &one(110, 110));
    assert_eq!(ranges(&r, 10 * SECOND), vec![(10, 61)]);
}

#[test]
fn thirty_two_confirmations_are_queued() {
    // 32 acknowledgements reporting 50..=81, then a 33rd reporting 300.
    let mut r = ReceivedPackets::<64>::new();
    r.on_packet_received(rx(0, 0)).unwrap();
    for k in 0..32u64 {
        r.on_packet_received(rx(50 + k, 0)).unwrap();
        r.on_ack_sent(100 + k, 0);
    }
    r.on_packet_received(rx(300, 0)).unwrap();
    r.on_ack_sent(200, 0);
    for k in 0..32u64 {
        r.on_peer_ack(SECOND + k, &one(100 + k, 100 + k));
    }
    r.on_peer_ack(SECOND + 40, &one(200, 200));
    // pn 301 extends the newest range. The 33rd confirmation (300) was dropped, so the floor is 81 and the run
    // (50..=81), ending at 81, is not below it: everything is reported.
    r.on_packet_received(rx(301, 2 * SECOND)).unwrap();
    assert_eq!(ranges(&r, 4 * SECOND), vec![(300, 301), (50, 81), (0, 0)]);
}

#[test]
fn a_confirmation_takes_effect_two_seconds_after_it_was_made() {
    let mut r = ReceivedPackets::<64>::new();
    for pn in [0, 2] {
        r.on_packet_received(rx(pn, 0)).unwrap();
    }
    r.on_packet_received(rx(10, 0)).unwrap();
    r.on_ack_sent(100, 0);
    r.on_peer_ack(5 * SECOND, &one(100, 100));
    r.on_packet_received(rx(11, 5 * SECOND)).unwrap();
    assert_eq!(ranges(&r, 7 * SECOND - 1).len(), 3);
    assert_eq!(ranges(&r, 7 * SECOND), vec![(10, 11)]);
}
