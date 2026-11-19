//! Tests of the delivery-rate estimate, the rate gate and the pacer. Part of the `transport_cc` test target.
#![allow(clippy::unwrap_used, clippy::cast_possible_truncation)]

use pinc_transport::recovery::{
    AckInput, BURST_PACKETS, Cubic, GATE_SLACK_FAST, GATE_SLACK_MID, INITIAL_CWND, MS, Pacer, SECOND,
};

use crate::{MSS, ack};

// ---------------------------------------------------------------------------------------------------------------
// The delivery-rate estimate
// ---------------------------------------------------------------------------------------------------------------

/// A controller whose rate estimate comes from two acknowledgements `min_rtt` apart.
pub(crate) fn with_rate(min_rtt: u64, first: u64, second: u64) -> Cubic {
    let mut c = Cubic::new();
    for (t, b) in [(SECOND, first), (SECOND + min_rtt, second)] {
        c.on_acked(&AckInput {
            min_rtt: Some(min_rtt),
            ..ack(t, b)
        });
    }
    c
}

/// An acknowledgement of `acked` bytes just inside the current interval (no new rate sample).
fn big_ack(c: &mut Cubic, min_rtt: u64, srtt: u64, acked: u64) {
    c.on_acked(&AckInput {
        min_rtt: Some(min_rtt),
        srtt: Some(srtt),
        ..ack(SECOND + 2 * min_rtt - 1, acked)
    });
}

#[test]
fn the_rate_counts_the_bytes_of_the_first_acknowledgement() {
    // One interval of exactly min_rtt: (first + second) * 1e9 / min_rtt bytes per second.
    let c = with_rate(50 * MS, 30_000, 20_000);
    assert_eq!(c.delivery_rate(), 50_000 * 1_000_000_000 / (50 * MS));
}

#[test]
fn a_sample_needs_a_full_minimum_round_trip() {
    let mut c = Cubic::new();
    c.on_acked(&AckInput {
        min_rtt: Some(50 * MS),
        ..ack(SECOND, 10_000)
    });
    c.on_acked(&AckInput {
        min_rtt: Some(50 * MS),
        ..ack(SECOND + 50 * MS - 1, 10_000)
    });
    assert_eq!(c.delivery_rate(), 0, "49.999999 ms is short of the interval");
    c.on_acked(&AckInput {
        min_rtt: Some(50 * MS),
        ..ack(SECOND + 50 * MS, 10_000)
    });
    assert_eq!(c.delivery_rate(), 30_000 * 1_000_000_000 / (50 * MS));
}

#[test]
fn the_rate_is_a_maximum_that_decays_by_an_eighth_per_interval() {
    let m = 10 * MS;
    let mut c = with_rate(m, 100_000, 100_000);
    let mut btl = 200_000 * 1_000_000_000 / m;
    assert_eq!(c.delivery_rate(), btl);
    // Each following interval delivers nothing: btl = max(0, btl - btl / 8).
    let mut now = SECOND + m;
    for _ in 0..10 {
        now += m;
        c.on_acked(&AckInput {
            min_rtt: Some(m),
            ..ack(now, 0)
        });
        c.resume(Some(m));
        btl -= btl >> 3;
        assert_eq!(c.delivery_rate(), btl);
    }
    // A higher sample replaces the estimate at once.
    now += m;
    c.on_acked(&AckInput {
        min_rtt: Some(m),
        ..ack(now, 1_000_000)
    });
    assert_eq!(c.delivery_rate(), 1_000_000 * 1_000_000_000 / m);
}

// ---------------------------------------------------------------------------------------------------------------
// The rate gate
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn below_2_ms_the_gate_is_the_low_latency_cap() {
    // cap = 2 * (btl * min_rtt / 1e9) + 262144, also on the threshold.
    assert_eq!(GATE_SLACK_FAST, 262_144);
    for (min_rtt, first, second) in [
        (MS, 400_000, 600_000),
        (1_999_999, 5_000_000, 5_000_000),
        (500_000, 1000, 1000),
    ] {
        let mut c = with_rate(min_rtt, first, second);
        let btl = (first + second) * 1_000_000_000 / min_rtt;
        let cap = 2 * (btl * min_rtt / 1_000_000_000) + 262_144;
        assert_eq!(c.gate_cap(min_rtt), Some(cap));
        big_ack(&mut c, min_rtt, 50 * MS, 100_000_000);
        assert_eq!(c.cwnd(), cap, "min_rtt {min_rtt}");
        assert_eq!(c.ssthresh(), cap, "the threshold is clamped too");
    }
}

#[test]
fn from_250_ms_the_gate_is_twice_the_bandwidth_delay_product() {
    // cap = max(2 * (btl * min_rtt / 1e9), 2400); the queue-cut branch has the same factor, so a long queue changes
    // nothing.
    for (min_rtt, first, second) in [
        (250 * MS, 300_000, 200_000),
        (800 * MS, 1_000_000, 3_000_000),
        (2 * SECOND, 100, 100),
    ] {
        for srtt in [min_rtt, 10 * min_rtt] {
            let mut c = with_rate(min_rtt, first, second);
            let btl = (first + second) * 1_000_000_000 / min_rtt;
            let cap = (2 * (btl * min_rtt / 1_000_000_000)).max(2_400);
            assert_eq!(c.gate_cap(min_rtt), Some(cap), "min_rtt {min_rtt}");
            big_ack(&mut c, min_rtt, srtt, 100_000_000);
            assert_eq!(c.cwnd(), cap);
            assert_eq!(c.ssthresh(), cap);
        }
    }
}

#[test]
fn the_slow_path_gate_never_falls_below_2400() {
    // btl * min_rtt / 1e9 is tiny: the cap is the 2400-byte minimum window, not 2 x BDP.
    let c = with_rate(500 * MS, 10, 10);
    assert_eq!(c.gate_cap(500 * MS), Some(2_400));
}

#[test]
fn between_2_and_250_ms_the_slack_is_44000_and_configurable() {
    assert_eq!(GATE_SLACK_MID, 44_000);
    for min_rtt in [2 * MS, 20 * MS, 100 * MS, 250 * MS - 1] {
        let mut c = with_rate(min_rtt, 600_000, 400_000);
        let btl = 1_000_000 * 1_000_000_000 / min_rtt;
        let bdp2 = 2 * (btl * min_rtt / 1_000_000_000);
        assert_eq!(
            c.gate_cap(min_rtt),
            Some((bdp2 + GATE_SLACK_MID).max(44_000)),
            "min_rtt {min_rtt}"
        );
        c.set_gate_slack(7_000);
        assert_eq!(c.gate_cap(min_rtt), Some((bdp2 + 7_000).max(44_000)));
        c.set_gate_slack(0);
        assert_eq!(c.gate_cap(min_rtt), Some(bdp2.max(44_000)));
    }
    // The floor binds when the measured rate is tiny.
    let mut c = with_rate(50 * MS, 100, 100);
    let btl = 200 * 1_000_000_000 / (50 * MS);
    let bdp2 = 2 * (btl * 50 * MS / 1_000_000_000);
    assert_eq!(c.gate_cap(50 * MS), Some(44_000 + bdp2));
    c.set_gate_slack(0);
    assert_eq!(c.gate_cap(50 * MS), Some(44_000));
}

#[test]
fn there_is_no_gate_before_a_rate_is_measured() {
    let mut c = Cubic::new();
    assert_eq!(c.gate_cap(50 * MS), None);
    c.on_acked(&AckInput {
        min_rtt: Some(50 * MS),
        ..ack(SECOND, 10_000_000)
    });
    assert_eq!(
        c.gate_cap(50 * MS),
        None,
        "the first acknowledgement only opens the interval"
    );
    assert_eq!(c.cwnd(), INITIAL_CWND + 10_000_000);
}

#[test]
fn a_trickle_cannot_inflate_the_window_between_2_and_250_ms() {
    // One 1200-byte acknowledgement per 50 ms for 5 minutes in slow start would add 6000 x 1200 bytes without the
    // gate. The estimate starts at 2400 / 50 ms = 48,000 bytes/s, then settles at 1200 / 50 ms = 24,000 bytes/s, so
    // the gate falls from 2 x 2400 + 44,000 = 48,800 to 2 x 1200 + 44,000 = 46,400 bytes.
    let m = 50 * MS;
    let mut c = Cubic::new();
    let mut worst = 0;
    for i in 0..6000u64 {
        c.on_acked(&AckInput {
            min_rtt: Some(m),
            ..ack(SECOND + i * m, 1200)
        });
        c.resume(Some(m));
        if let Some(cap) = c.gate_cap(m) {
            assert!(c.cwnd() <= cap, "step {i}: {} above the gate {cap}", c.cwnd());
        }
        worst = worst.max(c.cwnd());
    }
    assert!(worst <= 48_800, "worst {worst}");
    assert_eq!(c.delivery_rate(), 24_000);
    assert_eq!(c.cwnd(), 46_400);
}

#[test]
fn between_2_and_250_ms_only_a_resuming_sender_is_capped() {
    // The same acknowledgement that caps the window below 2 ms and from 250 ms leaves it alone in between, and the
    // resume call applies the same gate; without a measured rate or a minimum round trip it does nothing.
    for min_rtt in [2 * MS, 20 * MS, 249 * MS] {
        let mut c = with_rate(min_rtt, 1_000, 1_000);
        let cap = c.gate_cap(min_rtt).unwrap();
        big_ack(&mut c, min_rtt, 50 * MS, 100_000_000);
        assert!(
            c.cwnd() > cap,
            "min_rtt {min_rtt}: slow start is not cut by an acknowledgement"
        );
        assert_eq!(c.ssthresh(), u64::MAX);
        c.resume(None);
        assert!(c.cwnd() > cap);
        c.resume(Some(min_rtt));
        assert_eq!((c.cwnd(), c.ssthresh()), (cap, cap), "min_rtt {min_rtt}");
        c.resume(Some(min_rtt));
        assert_eq!(c.cwnd(), cap, "a second resume changes nothing");
    }
    let mut c = Cubic::new();
    c.on_acked(&AckInput {
        min_rtt: Some(20 * MS),
        ..ack(SECOND, 1_000_000)
    });
    let w = c.cwnd();
    c.resume(Some(20 * MS));
    assert_eq!((c.cwnd(), c.ssthresh()), (w, u64::MAX), "no rate is known yet");
}

#[test]
fn after_a_busy_period_the_gate_falls_with_the_decaying_rate() {
    // A bulk phase raises the rate; then one empty acknowledgement per interval lets it decay by 1/8 each time and
    // the gate (so the largest burst after the idle stretch) follows it down.
    let m = 20 * MS;
    let mut c = with_rate(m, 1_000_000, 1_000_000);
    let mut btl = 2_000_000 * 1_000_000_000 / m;
    let busy_cap = c.gate_cap(m).unwrap();
    assert_eq!(c.cwnd(), INITIAL_CWND + 2_000_000, "the window grew in the busy phase");
    let mut now = SECOND + m;
    for _ in 0..40 {
        now += m;
        c.on_acked(&AckInput {
            min_rtt: Some(m),
            ..ack(now, 0)
        });
        c.resume(Some(m));
        btl -= btl >> 3;
        let cap = (2 * (btl * m / 1_000_000_000) + 44_000).max(44_000);
        assert_eq!(c.gate_cap(m), Some(cap));
        assert!(c.cwnd() <= cap);
    }
    assert!(
        c.cwnd() < busy_cap / 4,
        "the idle stretch shrank the largest possible burst"
    );
}

// ---------------------------------------------------------------------------------------------------------------
// The pacer
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn ten_packets_go_then_the_sender_waits_ten_gaps() {
    // gap = mtu * srtt * 4 / (5 * cwnd); after the 10th packet the next release is now + 10 * gap.
    let (mtu, srtt, cwnd) = (1452u64, 80 * MS, 90_000u64);
    let gap = mtu * srtt * 4 / (5 * cwnd);
    let mut p = Pacer::new();
    for i in 0..BURST_PACKETS {
        assert_eq!(p.next_release(1000), 1000, "packet {i} may leave at once");
        p.on_sent(1000, mtu, srtt, cwnd, true);
    }
    assert_eq!(p.next_release(1000), 1000 + 10 * gap);
    assert_eq!(p.next_release(1000 + 10 * gap - 1), 1000 + 10 * gap);
    assert_eq!(p.next_release(1000 + 10 * gap), 1000 + 10 * gap);
    assert_eq!(p.next_release(5 * SECOND), 5 * SECOND);
}

#[test]
fn the_burst_is_ten_packets_even_after_a_long_idle() {
    let mut p = Pacer::new();
    for _ in 0..10 {
        p.on_sent(0, MSS, 50 * MS, 50_000, true);
    }
    let gap = MSS * 50 * MS * 4 / (5 * 50_000);
    // A minute later the next ten leave, and the eleventh waits: tokens are not banked while idle.
    let t = 60 * SECOND;
    for i in 0..10 {
        assert_eq!(p.next_release(t), t, "packet {i}");
        p.on_sent(t, MSS, 50 * MS, 50_000, true);
    }
    assert_eq!(p.next_release(t), t + 10 * gap);
}

/// One small packet a round trip, as a request and reply flow sends, is far under the paced rate and its window does
/// not limit it: no packet waits. A packet right behind every tenth one waits one tick of the clock, not ten
/// packet-times.
#[test]
fn packets_that_leave_more_slowly_than_the_paced_rate_are_not_held() {
    let (srtt, cwnd) = (20 * MS, 40_000u64);
    let mut p = Pacer::new();
    for i in 0..100u64 {
        let t = i * srtt;
        assert_eq!(p.next_release(t), t, "packet {i} waits");
        p.on_sent(t, MSS, srtt, cwnd, false);
        assert!(p.next_release(t) <= t + 1, "a packet behind packet {i} would wait");
    }
}

/// Nine packets that trickled do not shorten the wait of a burst that follows: the one that completes the slow ten
/// leaves, the sender gives the driver a turn, a full burst of ten follows, and the next waits ten packet-times from
/// when that burst began.
#[test]
fn a_burst_after_a_trickle_is_paused_after_eleven_packets() {
    let (srtt, cwnd) = (50 * MS, 50_000u64);
    let gap = MSS * srtt * 4 / (5 * cwnd);
    let mut p = Pacer::new();
    for i in 0..9u64 {
        p.on_sent(i * SECOND, MSS, srtt, cwnd, false);
    }
    let t = 60 * SECOND;
    assert_eq!(p.next_release(t), t);
    p.on_sent(t, MSS, srtt, cwnd, false);
    assert_eq!(p.next_release(t), t + 1, "one tick after the tenth");
    for i in 0..10 {
        assert_eq!(p.next_release(t + 1), t + 1, "packet {i} of the burst");
        p.on_sent(t + 1, MSS, srtt, cwnd, false);
    }
    assert_eq!(p.next_release(t + 1), t + 1 + 10 * gap);
}

/// Ten packets of a sender its window does not limit that left faster than the paced rate, though not in one
/// instant, wait as ever: ten packet-times from the tenth.
#[test]
fn ten_packets_faster_than_the_paced_rate_wait_the_whole_ten_packet_times() {
    let (srtt, cwnd) = (50 * MS, 50_000u64);
    let gap = MSS * srtt * 4 / (5 * cwnd);
    let mut p = Pacer::new();
    for i in 0..10u64 {
        p.on_sent(1000 + i * gap / 2, MSS, srtt, cwnd, false);
    }
    let last = 1000 + 9 * gap / 2;
    assert_eq!(p.next_release(last), last + 10 * gap);
}

#[test]
fn the_pacing_rate_is_one_and_a_quarter_windows_per_round_trip() {
    // Ten packets of mtu bytes per 10 gaps is mtu / gap = 1.25 x cwnd / srtt bytes per second.
    let (mtu, srtt, cwnd) = (1200u64, 100 * MS, 120_000u64);
    let gap = mtu * srtt * 4 / (5 * cwnd);
    let rate = mtu * 1_000_000_000 / gap;
    let want = cwnd * 5 / 4 * 1_000_000_000 / srtt;
    assert!(rate.abs_diff(want) * 1000 < want, "rate {rate} vs {want}");
}

#[test]
fn the_pacer_handles_a_zero_window() {
    let mut p = Pacer::new();
    for _ in 0..10 {
        p.on_sent(0, MSS, SECOND, 0, true);
    }
    assert_eq!(p.next_release(0), MSS * SECOND * 4 / 5 * 10);
}

/// A sender its window limits is paced as before, whatever time its ten packets took: the pause is ten packet-times
/// from the tenth.
#[test]
fn a_sender_its_window_limits_pauses_after_every_tenth_packet_however_slowly_they_left() {
    let (srtt, cwnd) = (50 * MS, 50_000u64);
    let gap = MSS * srtt * 4 / (5 * cwnd);
    let mut p = Pacer::new();
    for i in 0..10u64 {
        p.on_sent(i * SECOND, MSS, srtt, cwnd, true);
    }
    assert_eq!(p.next_release(9 * SECOND), 9 * SECOND + 10 * gap);
}
