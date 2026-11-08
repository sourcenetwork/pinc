//! Tests of vinc-transport's recovery: received-packet tracking, the acknowledgement policy, loss detection, the probe
//! timer, spurious-loss repair, tail repair and the byte accounting.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::type_complexity,
    clippy::too_many_lines
)]

use proptest::prelude::*;
use vinc_transport::recovery::{
    Event, FrameRef, FrameRefs, Health, LossEstimate, MAX_ACK_RANGES, MAX_PACKET_NUMBER, MIN_CWND, MS, PathKind,
    ReceivedPackets, Recovery, RecoveryError, RxOutcome, RxPacket, SECOND, Sent, Timeout,
};

mod recovery_ack;

use recovery_ack::rx;

vinc_tests::install_counting_allocator!();

const MSS: u64 = 1200;

/// A single acknowledged range.
fn one(a: u64, b: u64) -> std::iter::Once<std::ops::RangeInclusive<u64>> {
    std::iter::once(a..=b)
}

// ---------------------------------------------------------------------------------------------------------------
// The sent ring, RTT and the byte accounting
// ---------------------------------------------------------------------------------------------------------------

fn sent(pn: u64, time: u64) -> Sent {
    Sent {
        pn,
        time,
        size: 1200,
        ack_eliciting: true,
        in_flight: true,
        path: 0,
        is_repair: false,
        is_mtu_probe: false,
        frames: FrameRefs::new(),
    }
}

fn stream_frame(pn: u64) -> FrameRefs {
    let mut f = FrameRefs::new();
    f.push(FrameRef::Stream {
        id: 4,
        offset: pn * 1000,
        len: 1000,
        fin: false,
    })
    .unwrap();
    f
}

type Rec = Recovery<256>;

fn ack(rec: &mut Rec, now: u64, ranges: &[(u64, u64)], delay: u64) -> (vinc_transport::recovery::Summary, Vec<String>) {
    let mut log = Vec::new();
    let s = rec
        .on_ack_received(now, ranges.iter().map(|&(a, b)| a..=b), delay, |e| {
            log.push(describe(&e));
        })
        .unwrap();
    (s, log)
}

fn describe(e: &Event<'_>) -> String {
    match e {
        Event::Acked { pn, .. } => format!("acked {pn}"),
        Event::LateAcked { pn, .. } => format!("late {pn}"),
        Event::Lost {
            pn, requeue, mtu_probe, ..
        } => format!("lost {pn} requeue={requeue} probe={mtu_probe}"),
    }
}

/// A recovery with a 100 ms round trip established by pn 0 (sent at 0, acknowledged at 100 ms).
fn established() -> Rec {
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)], 0);
    rec
}

fn assert_conserved<const N: usize>(rec: &Recovery<N>) {
    assert_eq!(
        rec.bytes_sent(),
        rec.bytes_acked() + u128::from(rec.bytes_in_flight()) + rec.bytes_lost()
    );
}

#[test]
fn rtt_estimation_follows_rfc_9002() {
    let mut rec = Rec::new(MSS);
    assert_eq!(rec.rtt().min_rtt(), None);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)], 0);
    assert_eq!(rec.rtt().smoothed(), 100 * MS);
    assert_eq!(rec.rtt().rttvar(), 50 * MS);
    assert_eq!(rec.rtt().min_rtt(), Some(100 * MS));
    // 200 ms measured, 10 ms reported: adjusted 190 ms.
    rec.on_packet_sent(sent(1, 100 * MS)).unwrap();
    ack(&mut rec, 300 * MS, &[(1, 1)], 10 * MS);
    assert_eq!(rec.rtt().latest(), 200 * MS);
    assert_eq!(rec.rtt().rttvar(), (3 * 50 * MS + 90 * MS) / 4);
    assert_eq!(rec.rtt().smoothed(), (7 * 100 * MS + 190 * MS) / 8);
}

#[test]
fn ack_delay_is_capped_at_the_maximum() {
    let mut rec = established();
    // 200 ms measured with a 1 s reported delay: only 25 ms may be subtracted.
    rec.on_packet_sent(sent(1, 100 * MS)).unwrap();
    ack(&mut rec, 300 * MS, &[(1, 1)], SECOND);
    assert_eq!(rec.rtt().smoothed(), (7 * 100 * MS + 175 * MS) / 8);
    // A delay that would push the sample below the minimum is ignored.
    let mut rec = established();
    rec.on_packet_sent(sent(1, 100 * MS)).unwrap();
    ack(&mut rec, 205 * MS, &[(1, 1)], 20 * MS);
    assert_eq!(rec.rtt().smoothed(), (7 * 100 * MS + 105 * MS) / 8);
}

#[test]
fn no_sample_from_a_non_eliciting_packet() {
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(Sent {
        ack_eliciting: false,
        ..sent(0, 0)
    })
    .unwrap();
    ack(&mut rec, 50 * MS, &[(0, 0)], 0);
    assert!(!rec.rtt().has_sample());
}

#[test]
fn ack_errors_and_ignored_acks() {
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    rec.on_packet_sent(sent(1, 0)).unwrap();
    assert_eq!(
        rec.on_ack_received(1, one(0, 2), 0, |_| {}),
        Err(RecoveryError::AckOfUnsentPacket)
    );
    assert_eq!(
        rec.on_ack_received(1, one(u64::MAX, u64::MAX), 0, |_| {}),
        Err(RecoveryError::AckOfUnsentPacket)
    );
    assert_eq!(
        rec.on_ack_received(1, [std::ops::RangeInclusive::new(1, 0)], 0, |_| {}),
        Err(RecoveryError::InvalidAckRange)
    );
    // Acknowledging again, and acknowledging the empty past, are ignored.
    let (s, log) = ack(&mut rec, 10 * MS, &[(0, 1)], 0);
    assert_eq!(s.acked_packets, 2);
    assert_eq!(log, vec!["acked 0", "acked 1"]);
    let (s, log) = ack(&mut rec, 20 * MS, &[(0, 1)], 0);
    assert_eq!(s.acked_packets, 0);
    assert_eq!(log.len(), 0);
    assert_eq!(rec.bytes_in_flight(), 0);
    assert_conserved(&rec);
}

#[test]
fn sent_packet_numbers_must_increase_and_the_ring_is_bounded() {
    let mut rec = Recovery::<4>::new(MSS);
    rec.on_packet_sent(sent(5, 0)).unwrap();
    assert_eq!(
        rec.on_packet_sent(sent(5, 0)),
        Err(RecoveryError::PacketNumberNotIncreasing)
    );
    assert_eq!(
        rec.on_packet_sent(sent(3, 0)),
        Err(RecoveryError::PacketNumberNotIncreasing)
    );
    assert_eq!(
        rec.on_packet_sent(sent(MAX_PACKET_NUMBER + 1, 0)),
        Err(RecoveryError::PacketNumberOutOfRange)
    );
    assert_eq!(
        rec.on_packet_sent(Sent { path: 8, ..sent(6, 0) }),
        Err(RecoveryError::PathOutOfRange)
    );
    for pn in 6..9 {
        rec.on_packet_sent(sent(pn, 0)).unwrap();
    }
    assert_eq!(rec.on_packet_sent(sent(9, 0)), Err(RecoveryError::RingFull));
    rec.on_ack_received(MS, one(5, 5), 0, |_| {}).unwrap();
    rec.on_packet_sent(sent(9, MS)).unwrap();
    assert_conserved(&rec);
}

#[test]
fn frames_are_reported_on_ack_and_on_loss() {
    let mut rec = established();
    for pn in 1..=4 {
        rec.on_packet_sent(Sent {
            frames: stream_frame(pn),
            ..sent(pn, 100 * MS + pn)
        })
        .unwrap();
    }
    let mut acked = Vec::new();
    let mut lost = Vec::new();
    rec.on_ack_received(200 * MS, one(4, 4), 0, |e| match e {
        Event::Acked { frames, .. } => acked.extend(frames.iter().copied()),
        Event::Lost { frames, requeue, .. } => {
            assert!(requeue);
            lost.extend(frames.iter().copied());
        }
        Event::LateAcked { .. } => panic!("no late ack yet"),
    })
    .unwrap();
    assert_eq!(acked, stream_frame(4).as_slice());
    assert_eq!(lost, stream_frame(1).as_slice(), "only pn 1 is 3 behind pn 4");
}

// ---------------------------------------------------------------------------------------------------------------
// Loss detection
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn loss_by_packet_threshold() {
    let mut rec = established();
    for pn in 1..=5 {
        rec.on_packet_sent(sent(pn, 100 * MS + pn * MS)).unwrap();
    }
    let (s, log) = ack(&mut rec, 150 * MS, &[(5, 5)], 0);
    // Packets 1 and 2 are at least 3 behind pn 5; 3 and 4 are not.
    assert_eq!(
        log,
        vec![
            "acked 5",
            "lost 1 requeue=true probe=false",
            "lost 2 requeue=true probe=false"
        ]
    );
    assert_eq!(s.lost_packets, 2);
    assert_eq!(s.lost_bytes, 2400);
    assert_eq!(rec.bytes_in_flight(), 2400);
    assert_conserved(&rec);
}

#[test]
fn loss_by_time_threshold() {
    let mut rec = established();
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    rec.on_packet_sent(sent(2, 201 * MS)).unwrap();
    let (s, _) = ack(&mut rec, 300 * MS, &[(2, 2)], 0);
    assert_eq!(s.lost_packets, 0, "pn 1 is only 1 behind and not old enough");
    // 9/8 of max(latest, srtt), after the send time.
    let rtt = rec.rtt().latest().max(rec.rtt().smoothed());
    let due = 200 * MS + rtt * 9 / 8;
    assert_eq!(rec.next_timeout(), Some(due));
    let t = rec.on_timeout(due - 1, |_| panic!("too early"));
    assert_eq!(t, Timeout::default());
    let mut log = Vec::new();
    let t = rec.on_timeout(due, |e| log.push(describe(&e)));
    assert_eq!(t.summary.lost_packets, 1);
    assert_eq!(t.probes, 0);
    assert_eq!(log, vec!["lost 1 requeue=true probe=false"]);
    assert_conserved(&rec);
}

#[test]
fn old_path_packets_wait_four_rtt_plus_50_ms() {
    let mut rec = Rec::new(MSS);
    rec.set_path_kind(1, PathKind::Direct).unwrap();
    rec.on_packet_sent(sent(0, 0)).unwrap();
    assert!(rec.switch_path(1).unwrap(), "a new path restarts the estimators");
    for pn in 1..=5 {
        rec.on_packet_sent(Sent {
            path: 1,
            ..sent(pn, 10 * MS)
        })
        .unwrap();
    }
    // Round trip of 100 ms on the new path.
    let (s, log) = ack(&mut rec, 110 * MS, &[(5, 5)], 0);
    assert_eq!(rec.rtt().smoothed(), 100 * MS);
    // pn 1 and 2 are lost by count; pn 0, from the old path, is not.
    assert_eq!(s.lost_packets, 2, "{log:?}");
    let due = 4 * 100 * MS + 50 * MS;
    let mut lost = Vec::new();
    // Not before 4 RTT + 50 ms after its send time (the loss timer may fire earlier for pn 3 and 4).
    rec.on_timeout(due - 1, |e| lost.push(describe(&e)));
    assert!(!lost.iter().any(|l| l.starts_with("lost 0 ")), "{lost:?}");
    rec.on_timeout(due, |e| lost.push(describe(&e)));
    assert!(lost.iter().any(|l| l.starts_with("lost 0 ")), "{lost:?}");
}

#[test]
fn the_active_relay_path_uses_the_time_threshold_only() {
    let mut rec = Rec::new(MSS);
    rec.set_path_kind(1, PathKind::Relay).unwrap();
    assert!(rec.switch_path(1).unwrap());
    for pn in 0..=5 {
        rec.on_packet_sent(Sent {
            path: 1,
            ..sent(pn, 10 * MS)
        })
        .unwrap();
    }
    let (s, _) = ack(&mut rec, 110 * MS, &[(5, 5)], 0);
    assert_eq!(
        s.lost_packets, 0,
        "5 packets behind is not a loss on an active relay path"
    );
    let due = 10 * MS + 112_500_000;
    assert_eq!(rec.next_timeout(), Some(due));
    let t = rec.on_timeout(due, |_| {});
    assert_eq!(t.summary.lost_packets, 5);
}

#[test]
fn a_relay_path_that_is_no_longer_active_waits_at_least_1500_ms() {
    let mut rec = Rec::new(MSS);
    rec.set_path_kind(1, PathKind::Relay).unwrap();
    rec.set_path_kind(2, PathKind::Direct).unwrap();
    rec.switch_path(1).unwrap();
    rec.on_packet_sent(Sent { path: 1, ..sent(0, 0) }).unwrap();
    assert!(rec.switch_path(2).unwrap(), "relay to direct restarts");
    for pn in 1..=5 {
        rec.on_packet_sent(Sent {
            path: 2,
            ..sent(pn, 10 * MS)
        })
        .unwrap();
    }
    ack(&mut rec, 110 * MS, &[(5, 5)], 0);
    // 4 x 100 ms + 50 ms = 450 ms would apply to a direct old path; the relay floor is 1.5 s.
    let mut lost = Vec::new();
    rec.on_timeout(1_499 * MS, |e| lost.push(describe(&e)));
    assert!(!lost.iter().any(|l| l.starts_with("lost 0 ")), "{lost:?}");
    rec.on_timeout(1_500 * MS, |e| lost.push(describe(&e)));
    assert!(lost.iter().any(|l| l.starts_with("lost 0 ")), "{lost:?}");
}

#[test]
fn a_relay_to_relay_switch_keeps_the_estimators() {
    let mut rec = established();
    rec.set_path_kind(1, PathKind::Relay).unwrap();
    rec.set_path_kind(2, PathKind::Relay).unwrap();
    assert!(rec.switch_path(1).unwrap());
    rec.on_packet_sent(Sent {
        path: 1,
        ..sent(1, 200 * MS)
    })
    .unwrap();
    ack(&mut rec, 300 * MS, &[(1, 1)], 0);
    let (cwnd, srtt) = (rec.cwnd(), rec.rtt().smoothed());
    assert!(!rec.switch_path(2).unwrap());
    assert_eq!(rec.cwnd(), cwnd);
    assert_eq!(rec.rtt().smoothed(), srtt);
    assert!(
        !rec.switch_path(2).unwrap(),
        "switching to the active path does nothing"
    );
    assert_eq!(rec.switch_path(8), Err(RecoveryError::PathOutOfRange));
}

// ---------------------------------------------------------------------------------------------------------------
// The probe timer
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn pto_formula_and_backoff() {
    let mut rec = established();
    // srtt 100 ms, rttvar 50 ms: 100 + 200 + 25 = 325 ms.
    assert_eq!(rec.pto_duration(), 325 * MS);
    assert_eq!(rec.next_timeout(), None, "nothing in flight");
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    assert_eq!(rec.next_timeout(), Some(200 * MS + 325 * MS));
    let t = rec.on_timeout(525 * MS, |_| {});
    assert_eq!(t.probes, 1, "the first timeout sends 1 probe");
    assert_eq!(rec.pto_count(), 1);
    assert_eq!(rec.pto_duration(), 650 * MS);
    assert_eq!(rec.next_timeout(), Some(200 * MS + 650 * MS));
    let t = rec.on_timeout(850 * MS, |_| {});
    assert_eq!(t.probes, 2, "later timeouts send 2");
    assert_eq!(rec.pto_duration(), 1300 * MS);
    rec.on_timeout(1500 * MS, |_| {});
    assert_eq!(rec.pto_count(), 3);
    assert_eq!(rec.pto_duration(), 2 * SECOND, "capped at 2 s");
    assert_eq!(rec.on_timeout(500 * MS, |_| {}).probes, 0, "not expired: nothing to do");
}

#[test]
fn pto_backoff_stops_at_six_doublings() {
    // A 1 ms round trip: srtt 1 ms, rttvar 0.5 ms, PTO = 1 + 2 + 25 = 28 ms.
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, MS, &[(0, 0)], 0);
    assert_eq!(rec.pto_duration(), 28 * MS);
    rec.on_packet_sent(sent(1, 10 * MS)).unwrap();
    let mut expect = 28 * MS;
    for count in 1..=9u32 {
        let due = rec.next_timeout().unwrap();
        rec.on_timeout(due, |_| {});
        assert_eq!(rec.pto_count(), count);
        // Doubling stops at 2^6: 28 ms x 64 = 1792 ms, under the 2 s cap.
        if count <= 6 {
            expect *= 2;
        }
        assert_eq!(rec.pto_duration(), expect, "count {count}");
    }
    assert_eq!(expect, 1792 * MS);
}

#[test]
fn pto_cap_is_larger_on_slow_paths() {
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 1200 * MS, &[(0, 0)], 0);
    assert!(rec.rtt().is_long_rtt());
    // The raw PTO is 1200 + 2400 + 25 ms; the cap is max(2 s, 2 x srtt) = 2.4 s.
    assert_eq!(rec.pto_duration(), 2400 * MS);
}

#[test]
fn pto_counters_and_health() {
    let mut rec = established();
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    assert_eq!(rec.health(0), Health::Healthy);
    let mut now = 0;
    for count in 1..=10u32 {
        now = rec.next_timeout().unwrap();
        rec.on_timeout(now, |_| {});
        let want = match count {
            0..=2 => Health::Healthy,
            3..=9 => Health::Degraded,
            _ => Health::Dead,
        };
        assert_eq!(rec.health(now), want, "after {count} timeouts");
    }
    // An acknowledgement of a new packet resets the count.
    ack(&mut rec, now + MS, &[(1, 1)], 0);
    assert_eq!(rec.pto_count(), 0);
    assert_eq!(rec.health(now), Health::Healthy);
}

#[test]
fn giving_up_on_a_slow_path_needs_twenty_seconds_of_silence() {
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 1200 * MS, &[(0, 0)], 0);
    rec.on_packet_sent(sent(1, 1300 * MS)).unwrap();
    for _ in 0..10 {
        let due = rec.next_timeout().unwrap();
        rec.on_timeout(due, |_| {});
    }
    assert_eq!(rec.pto_count(), 10);
    assert_eq!(rec.health(1200 * MS + 19 * SECOND), Health::Degraded);
    assert_eq!(rec.health(1200 * MS + 20 * SECOND), Health::Dead);
    rec.note_peer_activity(1200 * MS + 19 * SECOND);
    assert_eq!(rec.health(1200 * MS + 20 * SECOND), Health::Degraded);
}

#[test]
fn pto_count_does_not_grow_while_the_peer_sleeps() {
    let mut rec = established();
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    rec.on_timeout(rec.next_timeout().unwrap(), |_| {});
    assert_eq!(rec.pto_count(), 1);
    rec.set_peer_asleep(true);
    for _ in 0..20 {
        let due = rec.next_timeout().unwrap();
        let t = rec.on_timeout(due, |_| {});
        assert!(t.probes >= 1);
    }
    assert_eq!(rec.pto_count(), 1, "the backoff is frozen");
    assert_eq!(rec.health(0), Health::Healthy);
    rec.set_peer_asleep(false);
    rec.on_timeout(rec.next_timeout().unwrap(), |_| {});
    assert_eq!(rec.pto_count(), 2);
}

// ---------------------------------------------------------------------------------------------------------------
// Spurious-loss repair
// ---------------------------------------------------------------------------------------------------------------

/// Packets 1..=5 sent, 5 acknowledged: 1 and 2 are declared lost and the window is cut.
fn with_two_losses() -> (Rec, u64) {
    let mut rec = established();
    for pn in 1..=5 {
        rec.on_packet_sent(Sent {
            frames: stream_frame(pn),
            ..sent(pn, 200 * MS + pn)
        })
        .unwrap();
    }
    let before = rec.cwnd();
    let (s, _) = ack(&mut rec, 300 * MS, &[(3, 5)], 0);
    assert_eq!(s.lost_packets, 2);
    assert!(rec.cwnd() < before + 1200, "the loss cut the window");
    (rec, before)
}

#[test]
fn a_late_ack_counts_as_acknowledged_and_reports_the_frames() {
    let (mut rec, _) = with_two_losses();
    assert_eq!(rec.bytes_lost(), 2400);
    let mut late = Vec::new();
    let s = rec
        .on_ack_received(310 * MS, one(1, 2), 0, |e| {
            if let Event::LateAcked { pn, frames } = e {
                late.push((pn, frames.as_slice().to_vec()));
            }
        })
        .unwrap();
    assert_eq!(s.late_acked_packets, 2);
    assert_eq!(late.len(), 2);
    assert_eq!(late[0], (1, stream_frame(1).as_slice().to_vec()));
    assert_eq!(rec.bytes_lost(), 0, "the bytes moved from lost to acknowledged");
    assert_conserved(&rec);
    // A second late ack changes nothing.
    let s = rec
        .on_ack_received(320 * MS, one(1, 2), 0, |_| panic!("already acknowledged"))
        .unwrap();
    assert_eq!(s.acked_packets, 0);
}

#[test]
fn a_late_ack_seeds_the_rtt() {
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    for pn in 1..=4 {
        rec.on_packet_sent(sent(pn, pn)).unwrap();
    }
    // pn 4 acknowledged after 50 ms: pn 0 and 1 are lost by count.
    ack(&mut rec, 50 * MS, &[(4, 4)], 0);
    assert_eq!(rec.rtt().latest(), 50 * MS - 4);
    // pn 1 comes back 3 s after it was sent.
    let (s, _) = ack(&mut rec, 3 * SECOND + 1, &[(0, 1)], 0);
    assert_eq!(s.late_acked_packets, 2);
    assert_eq!(
        rec.rtt().latest(),
        3 * SECOND,
        "the sample is from the largest late packet, pn 1"
    );
}

#[test]
fn a_late_rtt_sample_is_capped_at_four_seconds() {
    let mut rec = Rec::new(MSS);
    for pn in 0..=4 {
        rec.on_packet_sent(sent(pn, 0)).unwrap();
    }
    ack(&mut rec, 300 * MS, &[(4, 4)], 0);
    // Declared lost at 300 ms; still recognised at 4.2 s.
    let (s, _) = ack(&mut rec, 4 * SECOND + 200 * MS, &[(0, 1)], 0);
    assert_eq!(s.late_acked_packets, 2);
    assert_eq!(rec.rtt().latest(), 4 * SECOND);
}

#[test]
fn an_old_ghost_is_forgotten() {
    let (mut rec, _) = with_two_losses();
    // A later send trims ghosts older than 4 s from the head.
    rec.on_packet_sent(sent(6, 10 * SECOND)).unwrap();
    let s = rec
        .on_ack_received(10 * SECOND + MS, one(1, 2), 0, |_| panic!("forgotten"))
        .unwrap();
    assert_eq!(s.acked_packets, 0);
}

#[test]
fn the_congestion_response_is_undone_when_every_loss_is_spurious() {
    let (mut rec, before) = with_two_losses();
    let cut = rec.cwnd();
    // The recovery episode ends when a packet sent after it began is acknowledged.
    rec.on_packet_sent(sent(6, 400 * MS)).unwrap();
    let (s, _) = ack(&mut rec, 500 * MS, &[(6, 6)], 0);
    assert!(!s.congestion_undone, "the losses are not known to be spurious yet");
    let (s, _) = ack(&mut rec, 510 * MS, &[(1, 1)], 0);
    assert!(!s.congestion_undone, "one of two losses is still unexplained");
    let (s, _) = ack(&mut rec, 520 * MS, &[(2, 2)], 0);
    assert!(s.congestion_undone);
    assert!(rec.cwnd() > cut);
    assert!(rec.cwnd() >= before, "the window is back at least where it was");
    assert_conserved(&rec);
}

#[test]
fn the_response_stays_when_a_loss_was_real() {
    let (mut rec, _) = with_two_losses();
    let cut = rec.cwnd();
    rec.on_packet_sent(sent(6, 400 * MS)).unwrap();
    ack(&mut rec, 500 * MS, &[(6, 6)], 0);
    let (s, _) = ack(&mut rec, 510 * MS, &[(1, 1)], 0);
    assert!(!s.congestion_undone);
    assert!(rec.cwnd() <= cut + 1200 * 2, "no undo: only ordinary growth");
}

#[test]
fn repair_and_probe_losses_are_neither_retransmitted_nor_congestion() {
    let mut rec = established();
    let cwnd = rec.cwnd();
    rec.on_packet_sent(Sent {
        is_repair: true,
        ..sent(1, 200 * MS)
    })
    .unwrap();
    rec.on_packet_sent(Sent {
        is_mtu_probe: true,
        ..sent(2, 200 * MS + 1)
    })
    .unwrap();
    for pn in 3..=6 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn)).unwrap();
    }
    let before_lost = rec.bytes_lost();
    let (s, log) = ack(&mut rec, 300 * MS, &[(6, 6)], 0);
    assert_eq!(
        log,
        vec![
            "acked 6",
            "lost 1 requeue=false probe=false",
            "lost 2 requeue=false probe=true",
            "lost 3 requeue=true probe=false"
        ]
    );
    assert_eq!(s.lost_packets, 3);
    assert!(rec.bytes_lost() > before_lost);
    // Pn 3 is a real loss and cuts the window; the first two did not trigger a cut by themselves.
    assert!(rec.cwnd() < cwnd + 1200 * 2);
    let mut rec = established();
    rec.on_packet_sent(Sent {
        is_repair: true,
        ..sent(1, 200 * MS)
    })
    .unwrap();
    for pn in 2..=4 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn)).unwrap();
    }
    let cwnd = rec.cwnd();
    let (s, _) = ack(&mut rec, 300 * MS, &[(4, 4)], 0);
    assert_eq!(s.lost_packets, 1);
    assert!(
        rec.cwnd() >= cwnd,
        "a lost repair packet alone does not reduce the window (it only grows)"
    );
    assert!(rec.cc().recovery_start().is_none());
}

// ---------------------------------------------------------------------------------------------------------------
// Tail repair
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn loss_estimate_is_an_ewma_in_65536ths_with_gain_1_32() {
    let e = LossEstimate::new();
    assert_eq!(e.get(), 0);
    e.record(0, 0);
    assert_eq!(e.get(), 0, "an empty batch is ignored");
    e.record(0, 100);
    assert_eq!(e.get(), 0);
    e.record(1, 0);
    assert_eq!(e.get(), 2048, "one step of 1/32 toward 65536");
    e.record(1, 0);
    assert_eq!(e.get(), 2048 + (65_536 - 2048) / 32);
    // A 1% batch converges toward 655.
    let e = LossEstimate::new();
    for _ in 0..2000 {
        e.record(1, 99);
    }
    assert!((i64::from(e.get()) - 655).abs() <= 33, "got {}", e.get());
    // Decay reaches zero.
    let e = LossEstimate::new();
    e.record(1, 0);
    for _ in 0..1000 {
        e.record(0, 1);
    }
    assert_eq!(e.get(), 0);
    // Extremes do not overflow.
    e.record(u32::MAX, u32::MAX);
    e.record(u32::MAX, 0);
    e.record(0, u32::MAX);
}

#[test]
fn tail_repair_decision() {
    let e = LossEstimate::new();
    let age = 3 * SECOND;
    assert!(!e.should_send_repair(age, true, true), "no loss yet");
    e.record(1, 0);
    assert!(e.should_send_repair(age, true, true));
    assert!(!e.should_send_repair(age, false, true), "queue not drained");
    assert!(!e.should_send_repair(age, true, false), "not a UDP path");
    assert!(!e.should_send_repair(2 * SECOND, true, true), "must be older than 2 s");
    assert!(e.should_send_repair(2 * SECOND + 1, true, true));
    // The threshold is 655/65536: at the threshold no repair, one above it repair.
    let e = LossEstimate::new();
    let mut last = 0;
    while e.get() < 655 {
        last = e.get();
        e.record(1, 98);
    }
    assert!(last < 655);
    assert_eq!(e.should_send_repair(age, true, true), e.get() > 655);
    for _ in 0..200 {
        e.record(0, 1000);
    }
    assert!(!e.should_send_repair(age, true, true), "the estimate decayed below 1%");
}

#[test]
fn loss_estimate_is_shared_by_reference_across_threads() {
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

// ---------------------------------------------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum Op {
    Send {
        size: u32,
        eliciting: bool,
        in_flight: bool,
        repair: bool,
        probe: bool,
        path: u8,
        gap: u64,
    },
    Ack {
        ranges: Vec<(u64, u64)>,
        delay: u64,
        at: u64,
    },
    Timeout {
        at: u64,
    },
    Switch {
        path: u8,
    },
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        4 => (1u32..3000, any::<bool>(), any::<bool>(), any::<bool>(), any::<bool>(), 0u8..3, 1u64..4, ).prop_map(
            |(size, eliciting, in_flight, repair, probe, path, gap)| Op::Send { size, eliciting, in_flight, repair, probe, path, gap }
        ),
        4 => (proptest::collection::vec((0u64..40, 0u64..6), 0..4), 0u64..50_000_000, 0u64..2_000_000_000).prop_map(
            |(r, delay, at)| Op::Ack { ranges: r, delay, at }
        ),
        2 => (0u64..3_000_000_000).prop_map(|at| Op::Timeout { at }),
        1 => (0u8..3).prop_map(|path| Op::Switch { path }),
    ]
}

proptest! {
    /// Acked bytes + in-flight bytes + lost bytes always equal sent bytes, and the window stays above its minimum.
    #[test]
    fn bytes_are_conserved(ops in proptest::collection::vec(op_strategy(), 1..200)) {
        let mut rec = Recovery::<32>::new(MSS);
        rec.set_path_kind(1, PathKind::Relay).unwrap();
        let mut next_pn = 0u64;
        let mut now = 0u64;
        for op in ops {
            match op {
                Op::Send { size, eliciting, in_flight, repair, probe, path, gap } => {
                    now += gap * MS;
                    let p = Sent { size, ack_eliciting: eliciting, in_flight, path, is_repair: repair, is_mtu_probe: probe, ..sent(next_pn, now) };
                    if rec.on_packet_sent(p).is_ok() {
                        next_pn += 1;
                    }
                }
                Op::Ack { ranges, delay, at } => {
                    now = now.max(at);
                    let top = rec.largest_sent().unwrap_or(0);
                    // Descending ranges ending at or below the largest sent.
                    let mut r: Vec<(u64, u64)> = ranges.iter().map(|&(a, b)| {
                        let end = top.saturating_sub(a);
                        (end.saturating_sub(b), end)
                    }).collect();
                    r.sort_by_key(|x| std::cmp::Reverse(x.1));
                    let res = rec.on_ack_received(now, r.iter().map(|&(a, b)| a..=b), delay, |_| {});
                    if rec.largest_sent().is_some() {
                        prop_assert!(res.is_ok());
                    }
                }
                Op::Timeout { at } => {
                    now = now.max(at);
                    rec.on_timeout(now, |_| {});
                }
                Op::Switch { path } => {
                    let _ = rec.switch_path(path);
                }
            }
            prop_assert_eq!(rec.bytes_sent(), rec.bytes_acked() + u128::from(rec.bytes_in_flight()) + rec.bytes_lost());
            prop_assert!(rec.cwnd() >= MIN_CWND);
        }
    }

    /// No input panics, including `u64` extremes.
    #[test]
    fn extremes_never_panic(
        times in proptest::collection::vec(prop_oneof![Just(0u64), Just(1), Just(u64::MAX), Just(u64::MAX - 1), any::<u64>()], 1..40),
        sizes in proptest::collection::vec(prop_oneof![Just(0u32), Just(u32::MAX), any::<u32>()], 1..40),
        pns in proptest::collection::vec(prop_oneof![Just(0u64), Just(MAX_PACKET_NUMBER), any::<u64>()], 1..40),
    ) {
        let mut rec = Recovery::<8>::new(u64::MAX);
        let mut rxp = ReceivedPackets::<4>::new();
        let est = LossEstimate::new();
        for (i, &t) in times.iter().enumerate() {
            let size = sizes[i % sizes.len()];
            let pn = pns[i % pns.len()];
            let _ = rec.on_packet_sent(Sent { size, ..sent(pn, t) });
            let _ = rec.on_ack_received(t, one(pn.min(rec.largest_sent().unwrap_or(0)), rec.largest_sent().unwrap_or(0)), t, |_| {});
            let _ = rec.on_ack_received(t, one(0, pn), t, |_| {});
            rec.on_timeout(t, |_| {});
            let _ = rec.next_timeout();
            let _ = rec.pacer().next_release(t);
            let _ = rec.pto_duration();
            let _ = rec.health(t);
            let _ = rxp.on_packet_received(RxPacket { pn, now: t, ack_eliciting: true, stream_bytes: size });
            let _ = rxp.ack_ranges(t).count();
            let _ = rxp.ack_delay(t);
            rxp.on_ack_sent(pn, t);
            rxp.on_ack_confirmed(pn, t);
            est.record(size, size);
            let _ = est.should_send_repair(t, true, true);
        }
    }

    /// The received-pn set agrees with a model: a packet is new exactly once, ranges descend and are disjoint.
    #[test]
    fn received_set_matches_a_model(pns in proptest::collection::vec(0u64..200, 1..300)) {
        let mut r = ReceivedPackets::<256>::new();
        let mut seen = std::collections::BTreeSet::new();
        for pn in pns {
            let out = r.on_packet_received(rx(pn, 0)).unwrap();
            prop_assert_eq!(out == RxOutcome::New, seen.insert(pn));
        }
        let got: Vec<(u64, u64)> = r.ack_ranges(0).map(|x| (*x.start(), *x.end())).collect();
        let covered: std::collections::BTreeSet<u64> = got.iter().flat_map(|&(a, b)| a..=b).collect();
        if got.len() < MAX_ACK_RANGES {
            prop_assert_eq!(covered, seen);
        }
        prop_assert!(got.windows(2).all(|w| w[0].0 > w[1].1 + 1));
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Zero allocation
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn the_hot_paths_do_not_allocate() {
    let mut rec = Box::new(Rec::new(MSS));
    let mut rxp = ReceivedPackets::<64>::new();
    let est = LossEstimate::new();
    let mut count = 0u64;
    let stats = vinc_tests::measure(|| {
        for pn in 0..200u64 {
            rec.on_packet_sent(Sent {
                frames: stream_frame(pn),
                ..sent(pn, pn * MS)
            })
            .unwrap();
        }
    });
    assert_eq!(stats.count(), 0, "on_packet_sent allocated");
    let stats = vinc_tests::measure(|| {
        rec.on_ack_received(300 * MS, [190..=199, 100..=150, 0..=50], MS, |e| {
            if let Event::Acked { .. } = e {
                count += 1;
            }
        })
        .ok();
    });
    assert_eq!(stats.count(), 0, "ack processing allocated");
    let stats = vinc_tests::measure(|| {
        let mut now = 400 * MS;
        for _ in 0..12 {
            if let Some(t) = rec.next_timeout() {
                now = now.max(t);
                rec.on_timeout(now, |_| {});
            }
            let _ = rec.pacer().next_release(now);
        }
    });
    assert_eq!(stats.count(), 0, "the timers allocated");
    let stats = vinc_tests::measure(|| {
        for pn in 0..100u64 {
            rxp.on_packet_received(rx(pn * 3, pn)).unwrap();
        }
        let _ = rxp.ack_ranges(0).count();
        rxp.on_ack_sent(1, 0);
        rxp.on_ack_confirmed(1, 0);
        est.record(1, 2);
        let _ = est.should_send_repair(3 * SECOND, true, true);
    });
    assert_eq!(stats.count(), 0, "receive tracking allocated");
    assert!(count > 0);
}
