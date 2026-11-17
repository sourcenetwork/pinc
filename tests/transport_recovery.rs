//! Tests of vinc-transport's recovery: received-packet tracking, the acknowledgement policy, loss detection by path,
//! the probe timer and the give-up rules, ghosts and late acknowledgements, the loss estimate, tail repair and the
//! byte accounting.
//!
//! Each rule is pinned to its own formula, written out in the test: the expected loss time of a packet is its send
//! time plus the threshold of the rule for its path, the expected probe deadline is the later of the newest packet
//! in flight and the last probe, plus the shifted timeout, and so on.
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
    Event, FrameRef, FrameRefs, LossEstimate, MAX_ACK_RANGES, MAX_PACKET_NUMBER, MIN_CWND, MS, PathKind,
    ReceivedPackets, Recovery, RecoveryError, RxOutcome, RxPacket, SECOND, Sent, Summary, TailRepair, Timeout,
};

mod recovery_ack;
mod recovery_congestion;
mod recovery_pto;
mod recovery_tail;

use recovery_ack::rx;

vinc_tests::install_counting_allocator!();

pub(crate) const MSS: u64 = 1200;

/// A single acknowledged range.
pub(crate) fn one(a: u64, b: u64) -> std::iter::Once<std::ops::RangeInclusive<u64>> {
    std::iter::once(a..=b)
}

// ---------------------------------------------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------------------------------------------

pub(crate) type Rec = Recovery<256>;

pub(crate) fn sent(pn: u64, time: u64) -> Sent {
    Sent {
        pn,
        time,
        size: 1200,
        path: 0,
        is_repair: false,
        is_mtu_probe: false,
        frames: stream_frame(pn),
    }
}

pub(crate) fn on_path(pn: u64, time: u64, path: u8) -> Sent {
    Sent { path, ..sent(pn, time) }
}

pub(crate) fn stream_frame(pn: u64) -> FrameRefs {
    let mut f = FrameRefs::new();
    f.push(FrameRef::Stream {
        id: 4,
        offset: pn.wrapping_mul(1000),
        len: 1000,
        fin: false,
    })
    .unwrap();
    f
}

pub(crate) fn describe(e: &Event<'_>) -> String {
    match e {
        Event::Acked { pn, .. } => format!("acked {pn}"),
        Event::LateAcked { pn, .. } => format!("late {pn}"),
        Event::Lost {
            pn, requeue, mtu_probe, ..
        } => format!("lost {pn} requeue={requeue} probe={mtu_probe}"),
    }
}

pub(crate) fn ack<const N: usize>(rec: &mut Recovery<N>, now: u64, ranges: &[(u64, u64)]) -> (Summary, Vec<String>) {
    let mut log = Vec::new();
    let s = rec
        .on_ack_received(now, ranges.iter().map(|&(a, b)| a..=b), |e| {
            log.push(describe(&e));
        })
        .unwrap();
    (s, log)
}

/// A recovery with a 100 ms round trip established by pn 0 (sent at 0, acknowledged at 100 ms): srtt 100 ms, rttvar
/// 50 ms, minimum 100 ms, window 44,000 + 1200.
pub(crate) fn established() -> Rec {
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)]);
    rec
}

pub(crate) fn assert_conserved<const N: usize>(rec: &Recovery<N>) {
    assert_eq!(
        rec.bytes_sent(),
        rec.bytes_acked() + u128::from(rec.bytes_in_flight()) + rec.bytes_lost()
    );
}

/// Run the next timer at its own deadline.
pub(crate) fn fire<const N: usize>(rec: &mut Recovery<N>) -> (u64, Timeout, Vec<String>) {
    let t = rec.next_timeout().expect("a timer is armed");
    let mut log = Vec::new();
    let to = rec.on_timeout(t, |e| log.push(describe(&e)));
    (t, to, log)
}

pub(crate) fn lost_ev(pn: u64) -> String {
    format!("lost {pn} requeue=true probe=false")
}

/// The loss threshold of the rule for a packet on the active direct path: `max(9/8 x max(latest, srtt), 1 ms)`.
fn direct_delay<const N: usize>(rec: &Recovery<N>) -> u64 {
    let rtt = rec.rtt().latest().unwrap().max(rec.rtt().smoothed());
    (rtt * 9 / 8).max(MS)
}

// ---------------------------------------------------------------------------------------------------------------
// The round trip
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn samples_are_used_as_measured() {
    // First sample: srtt = s, rttvar = s / 2. Then rttvar = (3 rttvar + |srtt - s|) / 4, srtt = (7 srtt + s) / 8.
    let mut rec = established();
    let rtt = rec.rtt();
    assert_eq!(
        (rtt.smoothed(), rtt.rttvar(), rtt.min_rtt(), rtt.latest()),
        (100 * MS, 50 * MS, Some(100 * MS), Some(100 * MS))
    );
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    ack(&mut rec, 330 * MS, &[(1, 1)]);
    let rtt = rec.rtt();
    assert_eq!(rtt.rttvar(), (3 * 50 * MS + 30 * MS) / 4);
    assert_eq!(rtt.smoothed(), (7 * 100 * MS + 130 * MS) / 8);
    assert_eq!((rtt.min_rtt(), rtt.latest()), (Some(100 * MS), Some(130 * MS)));
}

#[test]
fn a_sample_comes_only_from_the_largest_acknowledged_packet() {
    let mut rec = established();
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    rec.on_packet_sent(sent(2, 210 * MS)).unwrap();
    ack(&mut rec, 300 * MS, &[(2, 2)]);
    assert_eq!(rec.rtt().latest(), Some(90 * MS));
    let srtt = rec.rtt().smoothed();
    // pn 1 is newly acknowledged but the acknowledgement's largest (2) is not new: no sample.
    let (s, _) = ack(&mut rec, 310 * MS, &[(1, 2)]);
    assert_eq!(s.acked_packets, 1);
    assert_eq!(rec.rtt().latest(), Some(90 * MS));
    assert_eq!(rec.rtt().smoothed(), srtt);
}

#[test]
fn an_acknowledgement_names_no_delay() {
    // The API carries no delay: a sample is always the elapsed time, even for a 1 ms round trip right after a long
    // one (no subtraction of anything).
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 500 * MS, &[(0, 0)]);
    rec.on_packet_sent(sent(1, SECOND)).unwrap();
    ack(&mut rec, SECOND + 400 * MS, &[(1, 1)]);
    assert_eq!(rec.rtt().latest(), Some(400 * MS));
    assert_eq!(rec.rtt().smoothed(), (7 * 500 * MS + 400 * MS) / 8);
}

#[test]
fn a_zero_sample_is_a_sample() {
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 5 * MS)).unwrap();
    ack(&mut rec, 5 * MS, &[(0, 0)]);
    assert!(rec.rtt().has_sample());
    assert_eq!(rec.rtt().smoothed(), 0);
    // The timeout floor: srtt + max(4 x rttvar, 1 ms) + 25 ms.
    assert_eq!(rec.pto_duration(), 26 * MS);
}

#[test]
fn acknowledgements_of_unrecorded_packets_change_nothing() {
    let mut rec = established();
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    rec.on_packet_untracked(2).unwrap();
    assert_eq!(rec.largest_sent(), Some(2));
    let in_flight = rec.bytes_in_flight();
    let (s, log) = ack(&mut rec, 250 * MS, &[(2, 2)]);
    assert_eq!(s, Summary::default());
    assert_eq!(log, Vec::<String>::new());
    assert_eq!(rec.bytes_in_flight(), in_flight);
    assert_eq!(
        rec.rtt().latest(),
        Some(100 * MS),
        "no sample from an unrecorded packet"
    );
    assert_eq!(rec.largest_acked(), Some(2));
    assert_eq!(
        rec.on_ack_received(250 * MS, one(3, 3), |_| {}),
        Err(RecoveryError::AckOfUnsentPacket)
    );
    assert_eq!(
        rec.on_packet_untracked(2),
        Err(RecoveryError::PacketNumberNotIncreasing)
    );
    assert_eq!(
        rec.on_packet_untracked(MAX_PACKET_NUMBER + 1),
        Err(RecoveryError::PacketNumberOutOfRange)
    );
    rec.on_packet_sent(sent(3, 260 * MS)).unwrap();
    assert_conserved(&rec);
}

#[test]
fn acknowledgement_errors_and_ignored_acknowledgements() {
    let mut rec = Rec::new(MSS);
    assert_eq!(
        rec.on_ack_received(0, one(0, 0), |_| {}),
        Err(RecoveryError::AckOfUnsentPacket),
        "nothing was sent"
    );
    rec.on_packet_sent(sent(0, 0)).unwrap();
    rec.on_packet_sent(sent(1, 0)).unwrap();
    assert_eq!(
        rec.on_ack_received(1, one(0, 2), |_| {}),
        Err(RecoveryError::AckOfUnsentPacket)
    );
    #[allow(clippy::reversed_empty_ranges)]
    let reversed = 1..=0u64;
    assert_eq!(
        rec.on_ack_received(1, std::iter::once(reversed), |_| {}),
        Err(RecoveryError::InvalidAckRange)
    );
    // Acknowledging twice is harmless.
    ack(&mut rec, 10 * MS, &[(0, 1)]);
    let (s, log) = ack(&mut rec, 11 * MS, &[(0, 1)]);
    assert_eq!(s, Summary::default());
    assert_eq!(log, Vec::<String>::new());
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
    assert_eq!(rec.on_packet_sent(on_path(6, 0, 8)), Err(RecoveryError::PathOutOfRange));
    for pn in 6..9 {
        rec.on_packet_sent(sent(pn, 0)).unwrap();
    }
    assert_eq!(rec.on_packet_sent(sent(9, 0)), Err(RecoveryError::RingFull));
    rec.on_ack_received(MS, one(5, 5), |_| {}).unwrap();
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
    rec.on_ack_received(200 * MS, one(4, 4), |e| match e {
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
    assert_eq!(
        rec.sent_frames(2).map(FrameRefs::as_slice),
        Some(stream_frame(2).as_slice())
    );
    assert!(rec.sent_frames(1).is_none(), "lost");
    assert!(rec.sent_frames(4).is_none(), "acknowledged");
}

// ---------------------------------------------------------------------------------------------------------------
// Loss detection
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn loss_by_packet_threshold() {
    // Rule: on the active direct path a packet is lost once pn + 3 <= the largest acknowledged.
    let mut rec = established();
    for pn in 1..=5 {
        rec.on_packet_sent(sent(pn, 200 * MS + (pn - 1) * MS)).unwrap();
    }
    let (s, log) = ack(&mut rec, 210 * MS, &[(5, 5)]);
    assert_eq!(log, ["acked 5".to_string(), lost_ev(1), lost_ev(2)]);
    assert_eq!((s.lost_packets, s.lost_bytes), (2, 2400));
    // pn 3 and 4 wait for the time threshold: sent time + max(9/8 x rtt, 1 ms).
    let delay = direct_delay(&rec);
    assert_eq!(rec.next_timeout(), Some(202 * MS + delay));
    assert_conserved(&rec);
}

#[test]
fn loss_by_time_threshold() {
    let mut rec = established();
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    rec.on_packet_sent(sent(2, 201 * MS)).unwrap();
    let (s, _) = ack(&mut rec, 205 * MS, &[(2, 2)]);
    assert_eq!(s.lost_packets, 0, "pn 1 is only one behind");
    let due = 200 * MS + direct_delay(&rec);
    assert_eq!(rec.next_timeout(), Some(due));
    let mut log = Vec::new();
    let to = rec.on_timeout(due - 1, |e| log.push(describe(&e)));
    assert_eq!(to.summary, Summary::default());
    let to = rec.on_timeout(due, |e| log.push(describe(&e)));
    assert_eq!(log, [lost_ev(1)]);
    assert_eq!(to.summary.lost_packets, 1);
    assert!(!to.ping, "a loss timer is not a probe timeout");
}

#[test]
fn the_time_threshold_uses_the_larger_of_the_latest_and_smoothed_round_trip_and_has_a_1_ms_floor() {
    // A slow latest sample: rtt = latest (200 ms) > srtt, delay = 225 ms.
    let mut rec = established();
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    rec.on_packet_sent(sent(2, 201 * MS)).unwrap();
    ack(&mut rec, 401 * MS, &[(2, 2)]);
    assert_eq!(rec.rtt().latest(), Some(200 * MS));
    assert_eq!(rec.next_timeout(), Some(200 * MS + 225 * MS));
    // Zero round trips: the floor is 1 ms.
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 0, &[(0, 0)]);
    rec.on_packet_sent(sent(1, 10 * MS)).unwrap();
    rec.on_packet_sent(sent(2, 10 * MS)).unwrap();
    ack(&mut rec, 10 * MS, &[(2, 2)]);
    assert_eq!(rec.next_timeout(), Some(11 * MS));
}

#[test]
fn before_a_sample_the_round_trip_is_333_ms() {
    // An acknowledgement whose largest number is an unrecorded packet gives no sample: loss detection then judges
    // pn 0 with the assumed 333 ms round trip, so its time threshold is max(9/8 x 333 ms, 1 ms).
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    rec.on_packet_sent(sent(1, MS)).unwrap();
    rec.on_packet_untracked(2).unwrap();
    ack(&mut rec, 2 * MS, &[(1, 2)]);
    assert!(!rec.rtt().has_sample());
    assert_eq!(rec.next_timeout(), Some(333 * MS * 9 / 8));
}

#[test]
fn old_path_packets_wait_four_round_trips_of_the_wider_path_plus_50_ms() {
    // Rule: a packet sent on a path that is no longer active is lost once it is
    // max(rtt, that path's rtt) x 4 + 50 ms old; the count rule does not apply.
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(on_path(0, 0, 1)).unwrap();
    ack(&mut rec, 80 * MS, &[(0, 0)]);
    assert_eq!(rec.path_rtt(1), Some(80 * MS), "the round trip measured on path 1");
    rec.on_packet_sent(on_path(1, 100 * MS, 1)).unwrap();
    rec.on_packet_sent(sent(2, 101 * MS)).unwrap();
    ack(&mut rec, 111 * MS, &[(2, 2)]);
    let rtt = rec.rtt().latest().unwrap().max(rec.rtt().smoothed());
    assert!(rtt < 80 * MS, "the connection round trip is below the old path's");
    // A keeper later than the due time, so the probe timer does not come first.
    rec.on_packet_sent(sent(3, 460 * MS)).unwrap();
    let due = 100 * MS + 4 * 80 * MS + 50 * MS;
    assert_eq!(rec.next_timeout(), Some(due));
    let mut log = Vec::new();
    rec.on_timeout(due - 1, |e| log.push(describe(&e)));
    assert_eq!(log, Vec::<String>::new());
    rec.on_timeout(due, |e| log.push(describe(&e)));
    assert_eq!(log, [lost_ev(1)]);
}

#[test]
fn an_old_relay_path_waits_at_least_1500_ms() {
    // Rule: an old relay path adds max(4 x max(rtt, path rtt), 1.5 s) to the same threshold.
    let mut rec = Rec::new(MSS);
    rec.set_path_kind(1, PathKind::Relay).unwrap();
    rec.on_packet_sent(on_path(0, 0, 1)).unwrap();
    ack(&mut rec, 80 * MS, &[(0, 0)]);
    rec.on_packet_sent(on_path(1, 100 * MS, 1)).unwrap();
    rec.on_packet_sent(sent(2, 101 * MS)).unwrap();
    ack(&mut rec, 111 * MS, &[(2, 2)]);
    rec.on_packet_sent(sent(3, 1590 * MS)).unwrap();
    let due = 100 * MS + (4 * 80 * MS + 50 * MS).max(4 * 80 * MS).max(1500 * MS);
    assert_eq!(due, 1600 * MS);
    assert_eq!(rec.next_timeout(), Some(due));
    // With a very slow relay (rtt 1 s) the multiple wins.
    let mut rec = Rec::new(MSS);
    rec.set_path_kind(1, PathKind::Relay).unwrap();
    rec.on_packet_sent(on_path(0, 0, 1)).unwrap();
    ack(&mut rec, SECOND, &[(0, 0)]);
    rec.on_packet_sent(on_path(1, 2 * SECOND, 1)).unwrap();
    rec.on_packet_sent(sent(2, 2 * SECOND + MS)).unwrap();
    ack(&mut rec, 2 * SECOND + 2 * MS, &[(2, 2)]);
    rec.on_packet_sent(sent(3, 6 * SECOND)).unwrap();
    assert_eq!(rec.next_timeout(), Some(2 * SECOND + 4 * SECOND + 50 * MS));
}

#[test]
fn the_active_relay_path_uses_the_time_threshold_only_at_two_round_trips_plus_50_ms() {
    // Rule: on the active relay path a packet is lost once it is max(2 x rtt, 9/8 x rtt) + 50 ms old, with no
    // packet count.
    let mut rec = Rec::new(MSS);
    rec.set_path_kind(0, PathKind::Relay).unwrap();
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)]);
    for pn in 1..=6 {
        rec.on_packet_sent(sent(pn, 200 * MS + (pn - 1) * MS)).unwrap();
    }
    let (s, _) = ack(&mut rec, 210 * MS, &[(6, 6)]);
    assert_eq!(
        s.lost_packets, 0,
        "five packets are 3 or more behind, yet none is lost by count"
    );
    rec.on_packet_sent(sent(7, 400 * MS)).unwrap();
    let rtt = rec.rtt().latest().unwrap().max(rec.rtt().smoothed());
    let delay = (rtt * 9 / 8).max(MS);
    let d2 = (rtt * 2).max(delay) + 50 * MS;
    assert_eq!(rec.next_timeout(), Some(200 * MS + d2));
}

#[test]
fn a_relay_packet_sent_before_the_latest_switch_waits_at_least_1500_ms() {
    // Rule: on the active relay path, a packet sent at or before the latest path switch is lost once it is
    // max(4 x rtt + 50 ms, 1.5 s) old; one sent after the switch uses the 2 x rtt + 50 ms rule.
    let mut rec = Rec::new(MSS);
    rec.set_path_kind(1, PathKind::Relay).unwrap();
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)]);
    rec.on_packet_sent(on_path(1, SECOND, 1)).unwrap();
    rec.note_peer_activity(2 * SECOND);
    assert!(rec.switch_path(1).unwrap(), "direct to relay restarts the controller");
    rec.on_packet_sent(on_path(2, 2100 * MS, 1)).unwrap();
    rec.on_packet_sent(on_path(3, 2200 * MS, 1)).unwrap();
    ack(&mut rec, 2300 * MS, &[(3, 3)]);
    assert_eq!(rec.rtt().smoothed(), 100 * MS);
    rec.on_packet_sent(on_path(4, 2340 * MS, 1)).unwrap();
    let after_switch = 2100 * MS + (2 * 100 * MS).max(direct_delay(&rec)) + 50 * MS;
    let before_switch = SECOND + (4 * 100 * MS + 50 * MS).max(1500 * MS);
    assert_eq!((after_switch, before_switch), (2350 * MS, 2500 * MS));
    assert_eq!(rec.next_timeout(), Some(after_switch));
    let (_, _, log) = fire(&mut rec);
    assert_eq!(log, [lost_ev(2)]);
    assert_eq!(rec.next_timeout(), Some(before_switch));
    let (_, _, log) = fire(&mut rec);
    assert_eq!(log, [lost_ev(1)]);
}

#[test]
fn a_relay_to_relay_switch_keeps_the_controller_and_the_switch_time() {
    let mut rec = Rec::new(MSS);
    rec.set_path_kind(0, PathKind::Relay).unwrap();
    rec.set_path_kind(1, PathKind::Relay).unwrap();
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)]);
    let (cwnd, srtt) = (rec.cwnd(), rec.rtt().smoothed());
    assert!(!rec.switch_path(1).unwrap());
    assert_eq!((rec.cwnd(), rec.rtt().smoothed()), (cwnd, srtt));
    assert!(rec.cc().recovery_start().is_none(), "no recovery mark");
    assert_eq!(rec.switch_path(8), Err(RecoveryError::PathOutOfRange));
    assert_eq!(
        rec.set_path_kind(8, PathKind::Relay),
        Err(RecoveryError::PathOutOfRange)
    );
}

#[test]
fn repair_and_probe_losses_are_neither_retransmitted_nor_a_congestion_signal() {
    let mut rec = established();
    let repair = Sent {
        is_repair: true,
        frames: stream_frame(1),
        ..sent(1, 200 * MS)
    };
    let probe = Sent {
        is_mtu_probe: true,
        size: 1452,
        ..sent(2, 201 * MS)
    };
    rec.on_packet_sent(repair).unwrap();
    rec.on_packet_sent(probe).unwrap();
    for pn in 3..=6 {
        rec.on_packet_sent(sent(pn, 202 * MS + pn)).unwrap();
    }
    let (s, log) = ack(&mut rec, 300 * MS, &[(6, 6)]);
    assert_eq!(
        log,
        [
            "acked 6".to_string(),
            "lost 1 requeue=false probe=false".to_string(),
            "lost 2 requeue=false probe=true".to_string(),
            lost_ev(3),
        ]
    );
    assert_eq!(s.lost_packets, 3);
    assert!(rec.cc().recovery_start().is_some(), "pn 3 is a congestion signal");
    // Without pn 3 the window is only ever grown.
    let mut rec = established();
    rec.on_packet_sent(Sent {
        is_repair: true,
        ..sent(1, 200 * MS)
    })
    .unwrap();
    rec.on_packet_sent(Sent {
        is_mtu_probe: true,
        ..sent(2, 201 * MS)
    })
    .unwrap();
    for pn in 3..=5 {
        rec.on_packet_sent(sent(pn, 202 * MS + pn)).unwrap();
    }
    let before = rec.cwnd();
    let (s, _) = ack(&mut rec, 300 * MS, &[(5, 5)]);
    assert_eq!(s.lost_packets, 2);
    assert!(rec.cwnd() >= before);
    assert!(rec.cc().recovery_start().is_none());
    assert_conserved(&rec);
}

// ---------------------------------------------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum Op {
    Send {
        size: u32,
        repair: bool,
        probe: bool,
        path: u8,
        gap: u64,
    },
    Untracked {
        gap: u64,
    },
    Ack {
        ranges: Vec<(u64, u64)>,
        at: u64,
    },
    Timeout {
        at: u64,
    },
    Switch {
        path: u8,
    },
    Follow {
        path: u8,
    },
    Flush {
        at: u64,
    },
    Sleep(bool),
    Dark(bool),
    Peer {
        at: u64,
    },
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        5 => (1u32..3000, any::<bool>(), any::<bool>(), 0u8..3, 1u64..4).prop_map(
            |(size, repair, probe, path, gap)| Op::Send { size, repair, probe, path, gap }
        ),
        1 => (1u64..4).prop_map(|gap| Op::Untracked { gap }),
        4 => (proptest::collection::vec((0u64..40, 0u64..6), 0..4), 0u64..2_000_000_000).prop_map(
            |(ranges, at)| Op::Ack { ranges, at }
        ),
        2 => (0u64..3_000_000_000).prop_map(|at| Op::Timeout { at }),
        1 => (0u8..3).prop_map(|path| Op::Switch { path }),
        1 => (0u8..3).prop_map(|path| Op::Follow { path }),
        1 => (0u64..3_000_000_000).prop_map(|at| Op::Flush { at }),
        1 => any::<bool>().prop_map(Op::Sleep),
        1 => any::<bool>().prop_map(Op::Dark),
        1 => (0u64..3_000_000_000).prop_map(|at| Op::Peer { at }),
    ]
}

proptest! {
    /// Acked bytes + in-flight bytes + lost bytes always equal sent bytes, and the window stays above its minimum.
    #[test]
    fn bytes_are_conserved(ops in proptest::collection::vec(op_strategy(), 1..200)) {
        let mut rec = Recovery::<32>::new(MSS);
        rec.set_path_kind(1, PathKind::Relay).unwrap();
        let mut now = 0u64;
        for op in ops {
            match op {
                Op::Send { size, repair, probe, path, gap } => {
                    now += gap * MS;
                    let p = Sent { size, path, is_repair: repair, is_mtu_probe: probe, ..sent(rec.next_pn(), now) };
                    let _ = rec.on_packet_sent(p);
                }
                Op::Untracked { gap } => {
                    now += gap * MS;
                    prop_assert!(rec.on_packet_untracked(rec.next_pn()).is_ok());
                }
                Op::Ack { ranges, at } => {
                    now = now.max(at);
                    let top = rec.largest_sent().unwrap_or(0);
                    // Descending ranges ending at or below the largest sent.
                    let mut r: Vec<(u64, u64)> = ranges.iter().map(|&(a, b)| {
                        let end = top.saturating_sub(a);
                        (end.saturating_sub(b), end)
                    }).collect();
                    r.sort_by_key(|x| std::cmp::Reverse(x.1));
                    let res = rec.on_ack_received(now, r.iter().map(|&(a, b)| a..=b), |_| {});
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
                Op::Follow { path } => {
                    let _ = rec.follow_path(path);
                }
                Op::Flush { at } => {
                    now = now.max(at);
                    rec.flush_in_flight(now, |_| {});
                }
                Op::Sleep(b) => rec.set_peer_asleep(b),
                Op::Dark(b) => rec.set_link_down(b),
                Op::Peer { at } => {
                    now = now.max(at);
                    rec.note_peer_activity(now);
                }
            }
            prop_assert_eq!(rec.bytes_sent(), rec.bytes_acked() + u128::from(rec.bytes_in_flight()) + rec.bytes_lost());
            prop_assert!(rec.cwnd() >= MIN_CWND);
            let _ = rec.next_timeout();
            let _ = rec.health(now);
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
        let mut tail = TailRepair::new();
        let est = LossEstimate::new();
        for (i, &t) in times.iter().enumerate() {
            let size = sizes[i % sizes.len()];
            let pn = pns[i % pns.len()];
            let _ = rec.on_packet_sent(Sent { size, ..sent(pn, t) });
            let _ = rec.on_packet_untracked(pn.wrapping_add(1));
            let _ = rec.on_ack_received(t, one(pn.min(rec.largest_sent().unwrap_or(0)), rec.largest_sent().unwrap_or(0)), |_| {});
            let _ = rec.on_ack_received(t, one(0, pn), |_| {});
            rec.on_timeout(t, |_| {});
            let _ = rec.next_timeout();
            let _ = rec.pacer().next_release(t);
            let _ = rec.pto_duration();
            let _ = rec.health(t);
            let _ = rec.can_send();
            let _ = rec.segment_size();
            rec.set_node_rtt(t);
            rec.set_max_datagram_size(t);
            rec.note_peer_activity(t);
            let _ = rec.switch_path(u8::try_from(i % 3).unwrap());
            let _ = rxp.on_packet_received(RxPacket { pn, now: t, ack_eliciting: true, stream_bytes: size });
            let _ = rxp.ack_ranges(t).count();
            rxp.on_ack_sent(pn, t);
            rxp.on_peer_ack(t, &one(0, pn));
            est.record(size, size);
            let _ = est.should_send_repair(t, true, true);
            tail.on_packet(pn, true, false);
            let _ = tail.on_drain();
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
    let mut rxp = ReceivedPackets::<32>::new();
    let est = LossEstimate::new();
    let mut tail = TailRepair::new();
    let mut count = 0u64;
    let stats = vinc_tests::measure(|| {
        for pn in 0..200u64 {
            rec.on_packet_sent(Sent {
                frames: stream_frame(pn),
                ..sent(pn, pn * MS)
            })
            .unwrap();
        }
        rec.on_packet_untracked(200).unwrap();
    });
    assert_eq!(stats.count(), 0, "on_packet_sent allocated");
    let stats = vinc_tests::measure(|| {
        rec.on_ack_received(300 * MS, [190..=199, 100..=150, 0..=50], |e| {
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
            let _ = rec.can_send();
        }
        rec.flush_in_flight(now, |_| {});
    });
    assert_eq!(stats.count(), 0, "the timers allocated");
    let stats = vinc_tests::measure(|| {
        for pn in 0..100u64 {
            rxp.on_packet_received(rx(pn * 3, pn)).unwrap();
            if pn % 7 == 0 {
                rxp.on_ack_sent(pn, pn);
                rxp.on_peer_ack(pn, &one(pn, pn));
            }
        }
        let _ = rxp.ack_ranges(0).count();
        est.record(1, 2);
        let _ = est.should_send_repair(3 * SECOND, true, true);
        tail.on_packet(1, true, false);
        let _ = tail.on_drain();
    });
    assert_eq!(stats.count(), 0, "receive tracking allocated");
    assert!(count > 0);
}

#[test]
fn an_acknowledgement_of_packets_sent_before_the_path_left_its_slot_sets_neither_the_round_trip_nor_the_seen_fact() {
    let mut rec = Rec::new(MSS);
    for pn in 0..=3 {
        rec.on_packet_sent(on_path(pn, pn * MS, 2)).unwrap();
    }
    rec.forget_path(2);
    ack(&mut rec, 80 * MS, &[(0, 3)]);
    assert_eq!(rec.path_rtt(2), None, "the old path's packets gave the slot a round trip");
    assert!(!rec.path_seen(2), "the old path's packets marked the slot seen");
    rec.on_packet_sent(on_path(4, 100 * MS, 2)).unwrap();
    ack(&mut rec, 150 * MS, &[(4, 4)]);
    assert!(rec.path_seen(2), "a packet sent on the new path did not mark the slot seen");
    assert!(rec.path_rtt(2).is_some());
}
