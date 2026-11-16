//! Tests of the recovery engine's window rules: the window check, the segment size, where pacing starts, what a path
//! switch resets, the window saved by the first probe timeout, and the rate gate fed by real acknowledgements. Part
//! of the `transport_recovery` test target.
#![allow(clippy::unwrap_used, clippy::indexing_slicing)]

use vinc_transport::recovery::{BURST_PACKETS, INITIAL_CWND, MIN_CWND, MS, PathKind, Recovery, SECOND, Sent};

use crate::{MSS, Rec, ack, assert_conserved, established, fire, on_path, sent};

// ---------------------------------------------------------------------------------------------------------------
// The window check
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn data_goes_only_if_inflight_plus_the_datagram_size_fits_the_window() {
    // Rule: inflight + mtu <= cwnd. The window is 44,000 and the datagram 1200: up to 42,800 in flight still sends.
    let mut rec = Rec::new(MSS);
    assert!(rec.can_send());
    rec.on_packet_sent(Sent {
        size: 42_800,
        ..sent(0, 0)
    })
    .unwrap();
    assert_eq!(rec.cwnd(), 44_000);
    assert!(rec.can_send(), "42,800 + 1200 = 44,000 fits exactly");
    rec.on_packet_sent(Sent { size: 1, ..sent(1, 0) }).unwrap();
    assert!(!rec.can_send(), "42,801 + 1200 does not");
    // A larger datagram shrinks the room.
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(Sent {
        size: 42_800,
        ..sent(0, 0)
    })
    .unwrap();
    rec.set_max_datagram_size(1452);
    assert!(!rec.can_send(), "42,800 + 1452 > 44,000");
    // Acknowledgements make room again.
    ack(&mut rec, 10 * MS, &[(0, 0)]);
    assert!(rec.can_send());
}

#[test]
fn a_lone_packet_grows_the_window_and_the_rate_gate_then_holds_it_to_what_was_delivered() {
    // No application-limited rule: one packet in an empty window still grows the window by its size.
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 10 * MS, &[(0, 0)]);
    assert_eq!(rec.cwnd(), INITIAL_CWND + 1200);
    // A second lone packet a second later grows it again. The rate gate bounds the window only when the sender
    // resumes, by what was delivered: 2400 bytes in the 1 s interval = 2400 bytes/s, a BDP of 24 bytes at 10 ms, so
    // the gate is max(44,000, 2 x 24 + 44,000).
    rec.on_packet_sent(sent(1, SECOND)).unwrap();
    ack(&mut rec, SECOND + 10 * MS, &[(1, 1)]);
    assert_eq!(rec.cc().delivery_rate(), 2400);
    assert_eq!(
        rec.cwnd(),
        INITIAL_CWND + 2400,
        "an acknowledgement alone does not apply the gate"
    );
    rec.on_packet_sent(sent(2, 2 * SECOND)).unwrap();
    assert_eq!(rec.cwnd(), 44_048);
}

// ---------------------------------------------------------------------------------------------------------------
// The segment size
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn the_segment_size_is_1200_except_on_a_fast_direct_path() {
    // Rule: 1200, or the path datagram size when the minimum round trip is below 2 ms on a direct path.
    let sample = |rtt: u64, kind: PathKind, mtu: u64| {
        let mut rec = Rec::new(MSS);
        rec.set_path_kind(0, kind).unwrap();
        rec.set_max_datagram_size(mtu);
        assert_eq!(rec.segment_size(), 1200, "no sample yet");
        rec.on_packet_sent(sent(0, 0)).unwrap();
        ack(&mut rec, rtt, &[(0, 0)]);
        rec.segment_size()
    };
    assert_eq!(sample(MS, PathKind::Direct, 8952), 8952);
    assert_eq!(sample(MS, PathKind::Direct, 1452), 1452);
    assert_eq!(sample(MS, PathKind::Direct, 1200), 1200);
    assert_eq!(sample(2 * MS - 1, PathKind::Direct, 1452), 1452);
    assert_eq!(sample(2 * MS, PathKind::Direct, 1452), 1200, "2 ms is not below 2 ms");
    assert_eq!(sample(20 * MS, PathKind::Direct, 1452), 1200);
    assert_eq!(
        sample(MS, PathKind::Relay, 1452),
        1200,
        "a relay path never grows in jumbo units"
    );
}

// ---------------------------------------------------------------------------------------------------------------
// Pacing
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn pacing_starts_with_the_first_round_trip_sample_and_holds_after_ten_packets() {
    // No sample: nothing paces, however many packets leave.
    let mut rec = Rec::new(MSS);
    for pn in 0..30 {
        rec.on_packet_sent(sent(pn, 5 * MS)).unwrap();
        assert_eq!(rec.pacer().next_release(5 * MS), 5 * MS);
    }
    // With a sample: ten packets leave, the 10th sets a pause of 10 gaps, gap = mtu x srtt x 4 / (5 x cwnd).
    let mut rec = established();
    let (srtt, cwnd) = (rec.rtt().smoothed(), rec.cwnd());
    let gap = MSS * srtt * 4 / (5 * cwnd);
    let now = 200 * MS;
    for i in 0..u64::from(BURST_PACKETS) {
        assert_eq!(rec.pacer().next_release(now), now, "packet {i}");
        rec.on_packet_sent(sent(1 + i, now)).unwrap();
    }
    assert_eq!(rec.pacer().next_release(now), now + 10 * gap);
    assert_eq!(rec.pacer().next_release(now + 10 * gap), now + 10 * gap);
}

#[test]
fn the_pause_uses_the_active_paths_datagram_size() {
    let mut rec = established();
    rec.set_max_datagram_size(1452);
    let (srtt, cwnd) = (rec.rtt().smoothed(), rec.cwnd());
    for i in 0..10 {
        rec.on_packet_sent(sent(1 + i, 200 * MS)).unwrap();
    }
    assert_eq!(
        rec.pacer().next_release(200 * MS),
        200 * MS + 10 * (1452 * srtt * 4 / (5 * cwnd))
    );
}

/// The recovery engine charges the pacer each packet's own size: four inner packets of 3,600 bytes, as a relay carrier
/// forwards on a path of 1,200, cost three tokens each, so the fourth ends the burst and the sender waits twelve gaps.
#[test]
fn a_relay_sized_packet_costs_the_pacer_the_datagrams_it_is_worth() {
    let mut rec = established();
    let (srtt, cwnd) = (rec.rtt().smoothed(), rec.cwnd());
    let now = 200 * MS;
    for i in 0..3 {
        rec.on_packet_sent(Sent {
            size: 3600,
            ..sent(1 + i, now)
        })
        .unwrap();
        assert_eq!(rec.pacer().next_release(now), now, "packet {i} ended the burst");
    }
    rec.on_packet_sent(Sent {
        size: 3600,
        ..sent(4, now)
    })
    .unwrap();
    assert_eq!(rec.pacer().next_release(now), now + 12 * (MSS * srtt * 4 / (5 * cwnd)));
}

// ---------------------------------------------------------------------------------------------------------------
// Path switches
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn a_path_switch_restarts_only_the_controller_and_marks_the_recovery() {
    let mut rec = established();
    for pn in 1..=3 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn)).unwrap();
    }
    fire(&mut rec); // pn 1 declared lost at 525 ms + 3 ns: a filtered cut, one probe timeout counted
    assert_eq!(rec.pto_count(), 1);
    assert_eq!(rec.cwnd(), (INITIAL_CWND + 1200) * 9 / 10);
    let (srtt, min_rtt) = (rec.rtt().smoothed(), rec.rtt().min_rtt());
    rec.note_peer_activity(600 * MS);
    assert!(rec.switch_path(1).unwrap());
    assert_eq!((rec.cwnd(), rec.cc().ssthresh()), (INITIAL_CWND, u64::MAX));
    assert_eq!(rec.pto_count(), 1, "the probe count is kept");
    assert_eq!(
        (rec.rtt().smoothed(), rec.rtt().min_rtt()),
        (srtt, min_rtt),
        "the estimate is kept"
    );
    assert_eq!(
        rec.cc().recovery_start(),
        Some(600 * MS),
        "the recovery is marked at the switch"
    );
    // Packets sent before the switch are lost without a cut: their loss belongs to the old path.
    let (_, _, log) = fire(&mut rec);
    assert_eq!(log, ["lost 2 requeue=true probe=false".to_string()]);
    assert_eq!(rec.cwnd(), INITIAL_CWND);
    // A packet sent after it cuts the new window (the filter: no queueing delay, so x 0.9).
    rec.on_packet_sent(on_path(4, 2 * SECOND, 1)).unwrap();
    fire(&mut rec); // pn 3
    assert_eq!(rec.cwnd(), INITIAL_CWND);
    let (_, _, log) = fire(&mut rec); // pn 4
    assert_eq!(log, ["lost 4 requeue=true probe=false".to_string()]);
    assert_eq!(rec.cwnd(), INITIAL_CWND * 9 / 10);
    assert_conserved(&rec);
}

#[test]
fn following_the_peer_onto_another_path_restarts_nothing() {
    let mut rec = established();
    let cwnd = rec.cwnd();
    rec.follow_path(1).unwrap();
    assert_eq!(rec.cwnd(), cwnd);
    assert!(rec.cc().recovery_start().is_none());
    assert!(!rec.switch_path(1).unwrap(), "already active");
    assert!(rec.follow_path(8).is_err());
}

// ---------------------------------------------------------------------------------------------------------------
// The first probe timeout and the window it saved
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn the_window_is_restored_when_the_packet_the_first_timeout_declared_lost_is_acknowledged() {
    let mut rec = established();
    for pn in 1..=3 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn)).unwrap();
    }
    let saved = rec.cwnd();
    fire(&mut rec);
    assert_eq!(rec.cwnd(), saved * 9 / 10, "the timeout's loss cut the window");
    // An unrelated acknowledgement (pn 2) restores nothing; it only adds its bytes.
    ack(&mut rec, 600 * MS, &[(2, 2)]);
    assert_eq!(rec.cwnd(), saved * 9 / 10 + 1200);
    // The original arrives after all: the window returns to what it was before the probe, and slow start with it.
    // (The ghosts are looked at once every 25 ms and the acknowledgement at 600 ms took this period's look.)
    let (s, log) = ack(&mut rec, 630 * MS, &[(1, 1)]);
    assert_eq!((s.late_acked_packets, log), (1, vec!["late 1".to_string()]));
    assert_eq!(rec.cwnd(), saved);
    assert_eq!(rec.cc().ssthresh(), u64::MAX);
    // Only once: a second late acknowledgement changes nothing.
    ack(&mut rec, 660 * MS, &[(1, 1)]);
    assert_eq!(rec.cwnd(), saved);
}

#[test]
fn only_the_first_timeout_saves_the_window() {
    let mut rec = established();
    for pn in 1..=4 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn)).unwrap();
    }
    let saved = rec.cwnd();
    fire(&mut rec); // pn 1, saved
    fire(&mut rec); // pn 2, count 2: nothing new is saved
    ack(&mut rec, 2 * SECOND, &[(2, 2)]);
    assert!(
        rec.cwnd() < saved,
        "a late ack of the second declared packet restores nothing"
    );
    ack(&mut rec, 2 * SECOND + MS, &[(1, 1)]);
    assert_eq!(rec.cwnd(), saved);
}

#[test]
fn repeated_timeouts_cut_once_per_episode_and_never_collapse_the_window() {
    let mut rec = established();
    for pn in 1..=8 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn)).unwrap();
    }
    let cut = rec.cwnd() * 9 / 10;
    for n in 1..=6 {
        fire(&mut rec);
        assert_eq!(rec.cwnd(), cut, "timeout {n}");
    }
    assert!(rec.cwnd() > MIN_CWND);
}

// ---------------------------------------------------------------------------------------------------------------
// The rate gate fed by acknowledgements
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn a_burst_of_acknowledgements_after_a_long_silence_cannot_inflate_the_window() {
    // min_rtt 50 ms. pn 0 is acknowledged at 50 ms (1200 bytes open the first interval); 20 packets sent at 1 s are
    // acknowledged at 1.05 s. The interval is 1 s long and carries 25,200 bytes: 25,200 bytes/s, a BDP of 1260 bytes,
    // a gate of 2 x 1260 + 44,000 = 46,520. Slow start alone would have reached 44,000 + 25,200; the sender's next
    // send, after an idle stretch, is where the gate bounds it.
    for relay in [false, true] {
        let mut rec = Rec::new(MSS);
        if relay {
            rec.set_path_kind(0, PathKind::Relay).unwrap();
        }
        rec.on_packet_sent(sent(0, 0)).unwrap();
        ack(&mut rec, 50 * MS, &[(0, 0)]);
        for pn in 1..=20 {
            rec.on_packet_sent(sent(pn, SECOND)).unwrap();
        }
        ack(&mut rec, SECOND + 50 * MS, &[(1, 20)]);
        assert_eq!(rec.cc().delivery_rate(), 25_200);
        assert_eq!(rec.cwnd(), INITIAL_CWND + 1200 + 24_000, "relay {relay}");
        rec.on_packet_sent(sent(21, 2 * SECOND)).unwrap();
        assert_eq!(rec.cwnd(), 46_520, "relay {relay}");
        assert_eq!(rec.cc().ssthresh(), 46_520);
    }
}

/// `rounds` rounds of window-limited sending: send until the window is full, acknowledge everything one round trip
/// later. `pn` and `now` carry on from one call to the next.
fn full_rounds<const N: usize>(rec: &mut Recovery<N>, pn: &mut u64, now: &mut u64, rounds: usize, rtt: u64) {
    for _ in 0..rounds {
        let first = *pn;
        while rec.can_send() {
            rec.on_packet_sent(sent(*pn, *now)).unwrap();
            *pn += 1;
        }
        *now += rtt;
        ack(rec, *now, &[(first, *pn - 1)]);
    }
}

#[test]
fn slow_start_on_a_busy_mid_range_path_is_not_cut_by_the_rate_gate() {
    // 20 ms path, the sender always has data: the window limits it in every round trip, so the gate never applies and
    // slow start adds every acknowledged byte, as in the algorithm. Applied on every acknowledgement the gate would
    // end slow start at about 2 x the delivery rate x 20 ms + 44,000 bytes.
    let mut rec = Recovery::<1024>::new(MSS);
    let (mut pn, mut now) = (0, 0);
    rec.on_packet_sent(sent(pn, now)).unwrap();
    pn += 1;
    now += 20 * MS;
    ack(&mut rec, now, &[(0, 0)]);
    full_rounds(&mut rec, &mut pn, &mut now, 8, 20 * MS);
    assert_eq!(rec.cc().ssthresh(), u64::MAX, "slow start was not left");
    assert_eq!(u128::from(rec.cwnd()), u128::from(INITIAL_CWND) + rec.bytes_acked());
    assert!(rec.cwnd() > 1_000_000, "{}", rec.cwnd());
}

#[test]
fn a_trickle_cannot_inflate_the_first_burst_after_it() {
    // min_rtt 50 ms. One packet per 100 ms for 20 s, each acknowledged 50 ms later: slow start would add 1200 bytes
    // per acknowledgement, 240,000 in all. Every send is a resumption, so the window never leaves the gate
    // (12,000 bytes/s measured, 2 x 12,000 x 50 ms + 44,000), and the burst that follows is bounded by it.
    let mut rec = Recovery::<1024>::new(MSS);
    for i in 0..200 {
        let t = i * 100 * MS;
        rec.on_packet_sent(sent(i, t)).unwrap();
        ack(&mut rec, t + 50 * MS, &[(i, i)]);
    }
    let cap = rec.cc().gate_cap(50 * MS).unwrap();
    assert_eq!(cap, 2 * 600 + 44_000);
    let (mut pn, now) = (200, 21 * SECOND);
    let mut burst = 0;
    while rec.can_send() {
        rec.on_packet_sent(sent(pn, now)).unwrap();
        pn += 1;
        burst += 1200;
    }
    assert!(burst <= cap, "burst {burst} over the gate {cap}");
    assert!(burst > cap - 3 * 1200, "burst {burst}");
}

#[test]
fn after_the_gate_caps_a_resuming_sender_the_window_grows_again() {
    // Capped once at the resumption; the burst then limits the window, so later rounds are not capped and the window
    // grows by the congestion avoidance rules.
    let mut rec = Recovery::<1024>::new(MSS);
    for i in 0..200 {
        let t = i * 100 * MS;
        rec.on_packet_sent(sent(i, t)).unwrap();
        ack(&mut rec, t + 50 * MS, &[(i, i)]);
    }
    let cap = rec.cc().gate_cap(50 * MS).unwrap();
    let (mut pn, mut now) = (200, 21 * SECOND);
    full_rounds(&mut rec, &mut pn, &mut now, 1, 50 * MS);
    assert!(rec.cwnd() >= cap, "{} under the gate {cap}", rec.cwnd());
    let after_first = rec.cwnd();
    full_rounds(&mut rec, &mut pn, &mut now, 3, 50 * MS);
    assert!(
        rec.cwnd() > after_first,
        "{} did not grow past {after_first}",
        rec.cwnd()
    );
}

#[test]
fn a_full_ring_closes_the_window_like_a_full_window() {
    // 8 slots, a window of 44,000: 8 packets in flight fill the ring long before the window.
    let mut rec = Recovery::<8>::new(MSS);
    for pn in 0..8 {
        assert!(rec.can_send(), "slot {pn} is free");
        rec.on_packet_sent(sent(pn, pn)).unwrap();
    }
    assert!(rec.bytes_in_flight() + MSS <= rec.cwnd(), "the window has room");
    assert!(!rec.can_send(), "the ring has none");
    // The head is acknowledged: a done head slot is room.
    ack(&mut rec, 10 * MS, &[(0, 0)]);
    assert!(rec.can_send());
    rec.on_packet_sent(sent(8, 11 * MS)).unwrap();
    assert!(!rec.can_send());
}
