//! Tests of the probe timer, the give-up rules and ghosts with late acknowledgements. Part of the `transport_recovery`
//! test target.
#![allow(clippy::unwrap_used, clippy::indexing_slicing)]

use vinc_transport::recovery::{Event, FrameRef, FrameRefs, Health, MS, Recovery, SECOND, Sent, Summary, Timeout};

use crate::{MSS, Rec, ack, assert_conserved, describe, established, fire, lost_ev, one, sent, stream_frame};

// ---------------------------------------------------------------------------------------------------------------
// The probe timer
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn the_probe_timeout_formula() {
    // srtt + max(4 x rttvar, 1 ms) + 25 ms; 333 ms and 166.5 ms before a sample.
    assert_eq!(Rec::new(MSS).pto_duration(), 333 * MS + 666 * MS + 25 * MS);
    assert_eq!(established().pto_duration(), 100 * MS + 200 * MS + 25 * MS);
}

#[test]
fn the_probe_timeout_shifts_by_the_count_up_to_six_doublings() {
    let mut rec = Recovery::<64>::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, MS, &[(0, 0)]);
    let base = MS + 4 * (MS / 2) + 25 * MS;
    assert_eq!(base, 28 * MS);
    for pn in 1..=12 {
        rec.on_packet_sent(sent(pn, 10 * MS)).unwrap();
    }
    for count in 0..9u32 {
        assert_eq!(rec.pto_count(), count);
        assert_eq!(rec.pto_duration(), base << count.min(6), "count {count}");
        rec.on_timeout(rec.next_timeout().unwrap(), |_| {});
    }
}

#[test]
fn the_probe_timeout_is_capped_at_2_s() {
    let mut rec = established();
    for pn in 1..=8 {
        rec.on_packet_sent(sent(pn, 200 * MS)).unwrap();
    }
    let want = [325, 650, 1300, 2000, 2000];
    for (i, w) in want.iter().enumerate() {
        assert_eq!(rec.pto_duration(), w * MS, "count {i}");
        fire(&mut rec);
    }
}

#[test]
fn the_cap_follows_the_round_trip_on_slow_paths() {
    // Rule: the cap is max(2 s, 2 x srtt) when the minimum round trip is 250 ms or more, or the smoothed round trip is
    // 1 s or more.
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 1200 * MS, &[(0, 0)]);
    // srtt 1.2 s, rttvar 0.6 s: the timeout is 1.2 + 2.4 + 0.025 s, capped at 2 x 1.2 = 2.4 s.
    assert_eq!(rec.pto_duration(), 2400 * MS);
    // A fast path whose smoothed round trip rose to 1 s or more takes the same cap.
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)]);
    rec.on_packet_sent(sent(1, SECOND)).unwrap();
    ack(&mut rec, 9 * SECOND, &[(1, 1)]);
    let srtt = rec.rtt().smoothed();
    assert_eq!(srtt, (7 * 100 * MS + 8 * SECOND) / 8);
    assert!(srtt >= SECOND && rec.rtt().min_rtt() < Some(250 * MS));
    assert_eq!(rec.pto_duration(), (2 * srtt).max(2 * SECOND));
    assert!(rec.pto_duration() > 2 * SECOND);
}

#[test]
fn the_deadline_counts_from_the_later_of_the_newest_packet_in_flight_and_the_last_probe() {
    let mut rec = established();
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    rec.on_packet_sent(sent(2, 210 * MS)).unwrap();
    assert_eq!(rec.next_timeout(), Some(210 * MS + 325 * MS));
    let (t, to, log) = fire(&mut rec);
    assert_eq!(t, 535 * MS);
    assert!(to.ping);
    assert_eq!(log, [lost_ev(1)], "the oldest packet is declared lost");
    assert_eq!(rec.pto_count(), 1);
    // pn 2 is still in flight; the next deadline counts from the probe (535 ms), not from the send (210 ms).
    assert_eq!(rec.next_timeout(), Some(535 * MS + 650 * MS));
}

#[test]
fn a_timeout_with_nothing_in_flight_arms_no_timer() {
    let mut rec = established();
    assert_eq!(rec.next_timeout(), None);
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    let (_, to, _) = fire(&mut rec);
    assert!(to.ping);
    assert_eq!(rec.next_timeout(), None, "the only packet was declared lost");
    let to = rec.on_timeout(10 * SECOND, |_| panic!("nothing to report"));
    assert_eq!(to, Timeout::default());
}

#[test]
fn the_first_timeout_declares_only_the_oldest_packet_lost_and_asks_for_a_ping() {
    let mut rec = established();
    for pn in 1..=3 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn)).unwrap();
    }
    let (_, to, log) = fire(&mut rec);
    assert!(to.ping);
    assert_eq!(log, [lost_ev(1)]);
    assert_eq!((to.summary.lost_packets, to.summary.lost_bytes), (1, 1200));
    let (_, to, log) = fire(&mut rec);
    assert!(to.ping);
    assert_eq!(log, [lost_ev(2)]);
    assert_eq!(rec.pto_count(), 2);
    assert_conserved(&rec);
}

#[test]
fn any_newly_acknowledged_packet_resets_the_probe_count() {
    let mut rec = established();
    for pn in 1..=4 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn)).unwrap();
    }
    fire(&mut rec);
    fire(&mut rec);
    assert_eq!(rec.pto_count(), 2);
    // A late acknowledgement of a ghost is no new acknowledgement: the count stays.
    let (s, log) = ack(&mut rec, 1500 * MS, &[(1, 1)]);
    assert_eq!((s.late_acked_packets, log), (1, vec!["late 1".to_string()]));
    assert_eq!(rec.pto_count(), 2);
    // An acknowledgement of a packet in flight resets it.
    ack(&mut rec, 1500 * MS + MS, &[(4, 4)]);
    assert_eq!(rec.pto_count(), 0);
}

#[test]
fn the_count_resets_on_an_acknowledgement_whatever_the_packet_was() {
    // The reset follows any newly acknowledged packet, not only an ack-eliciting one: here a repair packet.
    let mut rec = established();
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    rec.on_packet_sent(Sent {
        is_repair: true,
        ..sent(2, 210 * MS)
    })
    .unwrap();
    fire(&mut rec);
    assert_eq!(rec.pto_count(), 1);
    ack(&mut rec, SECOND, &[(2, 2)]);
    assert_eq!(rec.pto_count(), 0);
}

#[test]
fn the_probe_timer_holds_while_the_peer_sleeps() {
    let mut rec = established();
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    rec.on_packet_sent(sent(2, 210 * MS)).unwrap();
    rec.set_peer_asleep(true);
    let (t, to, log) = fire(&mut rec);
    assert!(!to.ping && log.is_empty() && to.summary == Summary::default());
    assert_eq!(rec.pto_count(), 0);
    assert_eq!(
        rec.next_timeout(),
        Some(t + 325 * MS),
        "the anchor moved to the firing time"
    );
    assert_eq!(rec.health(100 * SECOND), Health::Healthy);
    rec.set_peer_asleep(false);
    let (_, to, _) = fire(&mut rec);
    assert!(to.ping);
    assert_eq!(rec.pto_count(), 1);
}

#[test]
fn while_the_link_is_down_a_timeout_still_probes_without_growing_the_count() {
    let mut rec = established();
    for pn in 1..=3 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn)).unwrap();
    }
    rec.set_link_down(true);
    let (_, to, log) = fire(&mut rec);
    assert!(to.ping, "the PING goes out");
    assert_eq!(
        log,
        [lost_ev(1)],
        "loss detection runs and the oldest packet is declared lost"
    );
    assert_eq!(rec.pto_count(), 0, "the count does not grow");
    let (_, to, log) = fire(&mut rec);
    assert!(to.ping);
    assert_eq!(log, [lost_ev(2)]);
    assert_eq!(rec.pto_count(), 0);
    rec.set_link_down(false);
    fire(&mut rec);
    assert_eq!(rec.pto_count(), 1);
}

/// Fire ten probe timeouts with enough packets in flight. Returns the time of the last.
fn ten_timeouts<const N: usize>(rec: &mut Recovery<N>, first_pn: u64, at: u64) -> u64 {
    for i in 0..14 {
        rec.on_packet_sent(sent(first_pn + i, at + i)).unwrap();
    }
    let mut t = 0;
    for _ in 0..10 {
        t = fire(rec).0;
    }
    assert_eq!(rec.pto_count(), 10);
    t
}

#[test]
fn giving_up_needs_ten_timeouts_and_eight_round_trips_of_silence() {
    let mut rec = Recovery::<64>::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)]);
    for i in 0..14 {
        rec.on_packet_sent(sent(1 + i, 200 * MS + i)).unwrap();
    }
    for n in 1..=9 {
        fire(&mut rec);
        assert_ne!(rec.health(1000 * SECOND), Health::Dead, "{n} timeouts");
    }
    let t = fire(&mut rec).0;
    assert_eq!(rec.pto_count(), 10);
    rec.note_peer_activity(t);
    // Not thin, not slow: silence of max(0, 8 x srtt) = 800 ms.
    assert_eq!(rec.health(t + 8 * 100 * MS - 1), Health::Degraded);
    assert_eq!(rec.health(t + 8 * 100 * MS), Health::Dead);
}

#[test]
fn giving_up_on_a_slow_path_needs_twenty_seconds_of_silence() {
    let mut rec = Recovery::<64>::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 300 * MS, &[(0, 0)]);
    let t = ten_timeouts(&mut rec, 1, SECOND);
    rec.note_peer_activity(t);
    assert_eq!(rec.health(t + 20 * SECOND - 1), Health::Degraded);
    assert_eq!(rec.health(t + 20 * SECOND), Health::Dead);
}

#[test]
fn giving_up_waits_eight_round_trips_when_that_is_longer_than_twenty_seconds() {
    let mut rec = Recovery::<64>::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 3 * SECOND, &[(0, 0)]);
    let t = ten_timeouts(&mut rec, 1, 4 * SECOND);
    rec.note_peer_activity(t);
    assert_eq!(rec.health(t + 24 * SECOND - 1), Health::Degraded);
    assert_eq!(rec.health(t + 24 * SECOND), Health::Dead);
}

#[test]
fn a_session_without_a_sample_counts_as_thin() {
    let mut rec = Recovery::<64>::new(MSS);
    let t = ten_timeouts(&mut rec, 0, 0);
    rec.note_peer_activity(t);
    assert_eq!(rec.health(t + 20 * SECOND - 1), Health::Degraded);
    assert_eq!(rec.health(t + 20 * SECOND), Health::Dead);
}

#[test]
fn a_thin_node_or_a_large_smoothed_round_trip_needs_twenty_seconds() {
    // The node's own round trip of 250 ms or more.
    let mut rec = Recovery::<64>::new(MSS);
    rec.set_handshake_rtt(250 * MS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)]);
    assert!(rec.is_thin());
    let t = ten_timeouts(&mut rec, 1, SECOND);
    rec.note_peer_activity(t);
    assert_eq!(rec.health(t + 20 * SECOND - 1), Health::Degraded);
    assert_eq!(rec.health(t + 20 * SECOND), Health::Dead);
    // 249 ms is not thin.
    let mut rec = Recovery::<64>::new(MSS);
    rec.set_handshake_rtt(249 * MS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)]);
    assert!(!rec.is_thin());
    // Half the smoothed round trip at 250 ms (srtt 500 ms) with a minimum below 250 ms.
    let mut rec = Recovery::<64>::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)]);
    rec.on_packet_sent(sent(1, SECOND)).unwrap();
    ack(&mut rec, SECOND + 4 * SECOND, &[(1, 1)]);
    assert_eq!(rec.rtt().smoothed(), (7 * 100 * MS + 4 * SECOND) / 8);
    assert!(rec.rtt().smoothed() >> 1 >= 250 * MS && rec.rtt().min_rtt() < Some(250 * MS));
    assert!(rec.is_thin());
}

#[test]
fn flushing_declares_everything_lost_without_a_response_and_resets_the_count() {
    let mut rec = established();
    for pn in 1..=3 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn)).unwrap();
    }
    fire(&mut rec);
    let cwnd = rec.cwnd();
    let mut log = Vec::new();
    let s = rec.flush_in_flight(SECOND, |e| log.push(describe(&e)));
    assert_eq!(log, [lost_ev(2), lost_ev(3)]);
    assert_eq!((s.lost_packets, s.lost_bytes), (2, 2400));
    assert_eq!(rec.pto_count(), 0);
    assert_eq!(rec.cwnd(), cwnd, "the window is untouched");
    assert_eq!(rec.bytes_in_flight(), 0);
    assert_eq!(rec.next_timeout(), None);
    assert_conserved(&rec);
}

// ---------------------------------------------------------------------------------------------------------------
// Ghosts and late acknowledgements
// ---------------------------------------------------------------------------------------------------------------

/// pn 1..=5 sent, pn 5 acknowledged at 210 ms: pn 1 and 2 are declared lost at that time.
fn with_two_losses() -> (Rec, u64) {
    let mut rec = established();
    for pn in 1..=5 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn)).unwrap();
    }
    let (s, _) = ack(&mut rec, 210 * MS, &[(5, 5)]);
    assert_eq!(s.lost_packets, 2);
    (rec, 210 * MS)
}

#[test]
fn a_late_ack_counts_as_acknowledged_and_reports_the_frames() {
    let mut rec = established();
    for pn in 1..=5 {
        rec.on_packet_sent(Sent {
            frames: stream_frame(pn),
            ..sent(pn, 200 * MS + pn)
        })
        .unwrap();
    }
    ack(&mut rec, 210 * MS, &[(5, 5)]);
    let lost_before = rec.bytes_lost();
    let mut late = Vec::new();
    let s = rec
        .on_ack_received(215 * MS, one(1, 2), |e| {
            if let Event::LateAcked { pn, frames } = e {
                late.push((pn, frames.as_slice().to_vec()));
            }
        })
        .unwrap();
    assert_eq!(s.late_acked_packets, 2);
    assert_eq!(
        s.acked_packets, 0,
        "a late acknowledgement is not a new acknowledgement"
    );
    assert_eq!(
        late,
        [
            (1, stream_frame(1).as_slice().to_vec()),
            (2, stream_frame(2).as_slice().to_vec())
        ]
    );
    assert_eq!(rec.bytes_lost(), lost_before - 2400);
    assert_conserved(&rec);
    // Acknowledged once: a second acknowledgement is ignored.
    let (s, log) = ack(&mut rec, 216 * MS, &[(1, 2)]);
    assert_eq!(s, Summary::default());
    assert_eq!(log, Vec::<String>::new());
}

#[test]
fn a_ghost_older_than_two_seconds_is_never_recognised() {
    // Expiry is checked at lookup: at exactly 2 s the ghosts still count, one nanosecond later they do not, whether
    // or not anything trimmed the ring in between.
    let (mut rec, lost_at) = with_two_losses();
    let (s, _) = ack(&mut rec, lost_at + 2 * SECOND, &[(1, 2)]);
    assert_eq!(s.late_acked_packets, 2);
    let (mut rec, lost_at) = with_two_losses();
    let (s, log) = ack(&mut rec, lost_at + 2 * SECOND + 1, &[(1, 2)]);
    assert_eq!(s.late_acked_packets, 0);
    assert_eq!(log, Vec::<String>::new());
}

#[test]
fn a_ghost_keeps_only_stream_data_frames() {
    // Rule: a lost packet leaves a ghost only if it carried stream bytes without a stream end; a late
    // acknowledgement then acts on those frames alone.
    let data = FrameRef::Stream {
        id: 4,
        offset: 0,
        len: 500,
        fin: false,
    };
    let fin_only = FrameRef::Stream {
        id: 4,
        offset: 500,
        len: 0,
        fin: true,
    };
    let data_fin = FrameRef::Stream {
        id: 8,
        offset: 0,
        len: 10,
        fin: true,
    };
    let ctl = FrameRef::Control { kind: 2, id: 9 };
    let packet = |pn: u64, frames: &[FrameRef]| {
        let mut f = FrameRefs::new();
        for x in frames {
            f.push(*x).unwrap();
        }
        Sent {
            frames: f,
            ..sent(pn, 200 * MS + pn)
        }
    };
    let mut rec = established();
    rec.on_packet_sent(packet(1, &[ctl, data, data_fin, fin_only])).unwrap();
    rec.on_packet_sent(packet(2, &[ctl])).unwrap();
    rec.on_packet_sent(packet(3, &[fin_only])).unwrap();
    rec.on_packet_sent(packet(4, &[data_fin])).unwrap();
    for pn in 5..=8 {
        rec.on_packet_sent(packet(pn, &[data])).unwrap();
    }
    ack(&mut rec, 210 * MS, &[(8, 8)]);
    let mut seen = Vec::new();
    rec.on_ack_received(220 * MS, std::iter::once(1..=4), |e| {
        if let Event::LateAcked { pn, frames } = e {
            seen.push((pn, frames.as_slice().to_vec()));
        }
    })
    .unwrap();
    assert_eq!(
        seen,
        [(1, vec![data])],
        "only pn 1 left a ghost, and it keeps just its data frame"
    );
}

#[test]
fn at_most_200_ghosts_are_kept_oldest_first_out() {
    let mut rec = Recovery::<512>::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)]);
    for pn in 1..=300 {
        rec.on_packet_sent(sent(pn, 200 * MS + pn * 1000)).unwrap();
    }
    let (s, _) = ack(&mut rec, 210 * MS, &[(300, 300)]);
    assert_eq!(s.lost_packets, 297, "every packet 3 or more behind pn 300");
    let (s, log) = ack(&mut rec, 211 * MS, &[(1, 97)]);
    assert_eq!(
        (s.late_acked_packets, log.len()),
        (0, 0),
        "the 97 oldest ghosts were forgotten"
    );
    // Ghosts are looked at once every 25 ms: the acknowledgement at 211 ms used this period's look.
    let (s, _) = ack(&mut rec, 212 * MS, &[(98, 297)]);
    assert_eq!(s.late_acked_packets, 0, "no second look within 25 ms of the first");
    let (s, _) = ack(&mut rec, 236 * MS, &[(98, 297)]);
    assert_eq!(s.late_acked_packets, 200);
    assert_conserved(&rec);
}

#[test]
fn a_late_ack_seeds_the_estimate_only_when_there_is_none() {
    // No sample yet: pn 0 sent at 0 and pn 1 at 10 ms; the timeout declares pn 0 lost at 1034 ms; pn 0 is
    // acknowledged at 2.5 s after all. Its own send time gives the sample, and the count restarts.
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    rec.on_packet_sent(sent(1, 10 * MS)).unwrap();
    let (t, to, log) = fire(&mut rec);
    assert_eq!(t, 10 * MS + 1024 * MS);
    assert_eq!((to.ping, log), (true, vec![lost_ev(0)]));
    assert_eq!(rec.pto_count(), 1);
    let (s, log) = ack(&mut rec, 2500 * MS, &[(0, 0)]);
    assert_eq!((s.late_acked_packets, log), (1, vec!["late 0".to_string()]));
    assert!(rec.rtt().has_sample());
    assert_eq!(rec.rtt().smoothed(), 2500 * MS);
    assert_eq!(rec.rtt().min_rtt(), Some(2500 * MS));
    assert_eq!(rec.pto_count(), 0);
    // With an estimate the late acknowledgement seeds nothing and resets nothing.
    let mut rec = established();
    rec.on_packet_sent(sent(1, 200 * MS)).unwrap();
    rec.on_packet_sent(sent(2, 210 * MS)).unwrap();
    fire(&mut rec);
    ack(&mut rec, 600 * MS, &[(1, 1)]);
    assert_eq!(rec.rtt().smoothed(), 100 * MS);
    assert_eq!(rec.rtt().latest(), Some(100 * MS));
    assert_eq!(rec.pto_count(), 1);
}

#[test]
fn a_late_sample_is_capped_at_four_seconds() {
    let mut rec = Rec::new(MSS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    // The timer is overdue by far (the host was suspended): the probe fires at 9.9 s and declares pn 0 lost.
    let to = rec.on_timeout(9900 * MS, |_| {});
    assert!(to.ping);
    ack(&mut rec, 10 * SECOND, &[(0, 0)]);
    assert_eq!(
        rec.rtt().smoothed(),
        4 * SECOND,
        "10 s since the send, but the sample is at most 4 s"
    );
}

#[test]
fn without_a_sample_the_timeout_is_seeded_from_the_node_round_trip() {
    // srtt = max(333 ms, 2 x max(peak, handshake round trip)), rttvar = srtt / 2.
    for (peak, hs, srtt) in [
        (0, 0, 333),
        (100, 0, 333),
        (200, 0, 400),
        (0, 300, 600),
        (150, 250, 500),
    ] {
        let mut rec = Rec::new(MSS);
        rec.set_node_rtt(peak * MS);
        rec.set_handshake_rtt(hs * MS);
        let want = srtt * MS + 4 * (srtt * MS / 2) + 25 * MS;
        assert_eq!(
            rec.pto_duration(),
            want.min(if srtt >= 1000 { want } else { 2 * SECOND }),
            "{peak} {hs}"
        );
    }
    // A very slow node: srtt 1.4 s takes the raised cap max(2 s, 2.8 s).
    let mut rec = Rec::new(MSS);
    rec.set_node_rtt(700 * MS);
    assert_eq!(rec.pto_duration(), 2800 * MS);
    // With a sample the seed is ignored.
    let mut rec = established();
    rec.set_node_rtt(700 * MS);
    assert_eq!(rec.pto_duration(), 325 * MS);
}

#[test]
fn the_peak_round_trip_follows_each_sample_and_decays_by_a_thirty_second() {
    // peak = max(srtt, peak - peak / 32) after every sample.
    let mut rec = Rec::new(MSS);
    assert_eq!(rec.peak_rtt(), 0);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, 100 * MS, &[(0, 0)]);
    assert_eq!(rec.peak_rtt(), 100 * MS);
    rec.on_packet_sent(sent(1, SECOND)).unwrap();
    ack(&mut rec, SECOND + 130 * MS, &[(1, 1)]);
    assert_eq!(
        rec.peak_rtt(),
        (7 * 100 * MS + 130 * MS) / 8,
        "srtt 103.75 ms is above 100 ms - 3.125 ms"
    );
    let mut peak = rec.peak_rtt();
    let mut t = 2 * SECOND;
    for pn in 2..40 {
        rec.on_packet_sent(sent(pn, t)).unwrap();
        ack(&mut rec, t + MS, &[(pn, pn)]);
        peak = rec.rtt().smoothed().max(peak - (peak >> 5));
        assert_eq!(rec.peak_rtt(), peak, "sample {pn}");
        t += SECOND;
    }
    // Seeded from outside, it decays the same way.
    let mut rec = Rec::new(MSS);
    rec.set_node_rtt(320 * MS);
    rec.on_packet_sent(sent(0, 0)).unwrap();
    ack(&mut rec, MS, &[(0, 0)]);
    assert_eq!(rec.peak_rtt(), 320 * MS - 10 * MS);
}
