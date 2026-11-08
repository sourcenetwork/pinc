//! Tests of vinc-transport's congestion control and pacing: CUBIC against a floating-point reference, the two window
//! reductions, the loss filter, the slow-start exit, both caps, restart and the pacer.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::similar_names,
    clippy::too_many_lines
)]

use proptest::prelude::*;
use vinc_transport::recovery::{
    AckInput, BURST_PACKETS, CONGESTION_BETA_SMALL, Cubic, INITIAL_CWND, MAX_CWND, MIN_CWND, MS, Pacer, SECOND,
};

const MSS: u64 = 1200;

/// Grow a fresh controller in slow start to exactly `target` bytes (no round-trip samples, so no early exit).
fn grown_to(target: u64) -> Cubic {
    let mut c = Cubic::new(MSS);
    c.on_acked(&AckInput {
        growth_bytes: target - INITIAL_CWND,
        ..AckInput::default()
    });
    assert_eq!(c.cwnd(), target);
    c
}

// ---------------------------------------------------------------------------------------------------------------
// CUBIC against a floating-point reference
// ---------------------------------------------------------------------------------------------------------------

/// The same algorithm in `f64`, with exact cube roots and no truncation.
struct Reference {
    cwnd: f64,
    w_max: f64,
    w_est: f64,
    k: f64,
    epoch: Option<f64>,
    mss: f64,
}

impl Reference {
    fn on_ack(&mut self, t: f64, bytes: f64, rtt: f64) {
        let epoch = *self.epoch.get_or_insert_with(|| {
            self.k = if self.w_max > self.cwnd {
                ((self.w_max - self.cwnd) / self.mss / 0.4).cbrt()
            } else {
                self.w_max = self.cwnd;
                0.0
            };
            self.w_est = self.cwnd;
            t
        });
        self.w_est += 0.53 * self.mss * bytes / self.cwnd;
        let dt = (t - epoch) + rtt - self.k;
        let cubic = self.w_max + 0.4 * dt.powi(3) * self.mss;
        let target = cubic.max(self.w_est).min(1.5 * self.cwnd);
        if target > self.cwnd {
            self.cwnd += (target - self.cwnd) * bytes / self.cwnd;
        }
    }
}

fn drive_against_reference(loss_cwnd: u64, srtt: u64, rtt: u64, seconds: u64) {
    let mut c = grown_to(loss_cwnd);
    let min_rtt = Some(rtt);
    let loss_at = 5 * SECOND;
    assert!(c.on_congestion_event(loss_at, loss_at - 1, srtt, min_rtt));
    let after_loss = c.cwnd();
    let mut r = Reference {
        cwnd: after_loss as f64,
        w_max: loss_cwnd as f64,
        w_est: after_loss as f64,
        k: 0.0,
        epoch: None,
        mss: MSS as f64,
    };
    let step = MS;
    let mut now = loss_at;
    let mut worst = 0.0f64;
    for i in 1..=(seconds * 1000) {
        now += step;
        // One millisecond of acknowledgements at a rate of one window per round trip.
        let bytes = (c.cwnd() * step / rtt).max(1);
        c.on_acked(&AckInput {
            now,
            growth_bytes: bytes,
            acked_bytes: bytes,
            min_rtt,
            ..AckInput::default()
        });
        r.on_ack((now - loss_at) as f64 / 1e9, bytes as f64, rtt as f64 / 1e9);
        if i % 250 == 0 {
            let err = (c.cwnd() as f64 - r.cwnd).abs() / r.cwnd;
            worst = worst.max(err);
            assert!(
                err < 0.005,
                "t = {} ms: integer {} vs reference {:.0} ({:.3}%)",
                i,
                c.cwnd(),
                r.cwnd,
                err * 100.0
            );
        }
    }
    eprintln!("worst relative error {worst:.5}");
}

#[test]
fn cubic_window_matches_the_float_reference_over_time() {
    // Beta 0.7 (loss with queueing delay), 10 ms round trip, a 20 s regrowth through the plateau at W_max.
    drive_against_reference(600_000, 40 * MS, 10 * MS, 20);
}

#[test]
fn cubic_window_matches_the_reference_for_other_shapes() {
    drive_against_reference(5_000_000, 100 * MS, 50 * MS, 30);
    drive_against_reference(120_000, 30 * MS, 20 * MS, 20);
}

#[test]
fn cubic_grows_past_the_previous_maximum() {
    let mut c = grown_to(300_000);
    c.on_congestion_event(SECOND, SECOND - 1, 50 * MS, Some(10 * MS));
    let mut now = SECOND;
    for _ in 0..60_000 {
        now += MS;
        let bytes = c.cwnd() / 10;
        c.on_acked(&AckInput {
            now,
            growth_bytes: bytes,
            acked_bytes: bytes,
            min_rtt: Some(10 * MS),
            ..AckInput::default()
        });
    }
    assert!(c.cwnd() > 300_000, "convex growth beyond W_max, got {}", c.cwnd());
}

// ---------------------------------------------------------------------------------------------------------------
// Reductions
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn beta_is_0_7_and_0_85_below_48_kb() {
    // With queueing delay (srtt well above min rtt) the full reduction applies.
    let mut c = grown_to(100_000);
    assert!(c.on_congestion_event(SECOND, SECOND - 1, 50 * MS, Some(10 * MS)));
    assert_eq!(c.cwnd(), 70_000);
    assert_eq!(c.ssthresh(), 70_000);
    assert!(!c.in_slow_start());
    assert_eq!(c.recovery_start(), Some(SECOND));

    // The initial window is below 48 KB: 0.85.
    const { assert!(INITIAL_CWND < CONGESTION_BETA_SMALL) };
    let mut c = Cubic::new(MSS);
    c.on_congestion_event(SECOND, SECOND - 1, 50 * MS, Some(10 * MS));
    assert_eq!(c.cwnd(), 44_000 * 85 / 100);

    // Exactly 48 KB is not below it.
    let mut c = grown_to(CONGESTION_BETA_SMALL);
    c.on_congestion_event(SECOND, SECOND - 1, 50 * MS, Some(10 * MS));
    assert_eq!(c.cwnd(), 48_000 * 7 / 10);
    let mut c = grown_to(CONGESTION_BETA_SMALL - 1);
    c.on_congestion_event(SECOND, SECOND - 1, 50 * MS, Some(10 * MS));
    assert_eq!(c.cwnd(), (CONGESTION_BETA_SMALL - 1) * 85 / 100);
}

#[test]
fn the_window_never_falls_below_the_minimum() {
    let mut c = Cubic::new(MSS);
    let mut now = SECOND;
    for _ in 0..50 {
        c.on_congestion_event(now, now - 1, 50 * MS, Some(10 * MS));
        now += SECOND;
        assert!(c.cwnd() >= MIN_CWND);
    }
    assert_eq!(c.cwnd(), MIN_CWND);
}

#[test]
fn one_reduction_per_episode() {
    let mut c = grown_to(100_000);
    assert!(c.on_congestion_event(SECOND, SECOND - 1, 50 * MS, Some(10 * MS)));
    // A packet sent before the recovery began, or at the same instant, is the same episode.
    assert!(!c.on_congestion_event(SECOND + MS, SECOND - 5, 50 * MS, Some(10 * MS)));
    assert!(!c.on_congestion_event(SECOND + MS, SECOND, 50 * MS, Some(10 * MS)));
    assert_eq!(c.cwnd(), 70_000);
    // One sent after it is a new one.
    assert!(c.on_congestion_event(2 * SECOND, SECOND + 1, 50 * MS, Some(10 * MS)));
    assert_eq!(c.cwnd(), 49_000);
}

#[test]
fn acknowledgements_in_recovery_do_not_grow_the_window_through_growth_bytes() {
    let mut c = grown_to(100_000);
    c.on_congestion_event(SECOND, SECOND - 1, 50 * MS, Some(10 * MS));
    let cwnd = c.cwnd();
    c.on_acked(&AckInput {
        now: SECOND + MS,
        growth_bytes: 0,
        acked_bytes: 50_000,
        ..AckInput::default()
    });
    assert_eq!(c.cwnd(), cwnd);
}

#[test]
fn the_loss_filter_cuts_by_0_9_at_most_four_times_in_a_row() {
    let mut c = grown_to(1_000_000);
    let min_rtt = Some(10 * MS);
    let srtt = 11 * MS; // within 1/8 of the minimum: no queueing delay
    let mut now = SECOND;
    let mut want = 1_000_000u64;
    for _ in 0..4 {
        assert!(c.on_congestion_event(now, now - 1, srtt, min_rtt));
        want = want * 9 / 10;
        assert_eq!(c.cwnd(), want);
        now += SECOND;
    }
    // The 5th is a full reduction.
    assert!(c.on_congestion_event(now, now - 1, srtt, min_rtt));
    want = want * 7 / 10;
    assert_eq!(c.cwnd(), want);
    now += SECOND;
    // The streak starts over.
    assert!(c.on_congestion_event(now, now - 1, srtt, min_rtt));
    assert_eq!(c.cwnd(), want * 9 / 10);
}

#[test]
fn the_loss_filter_needs_no_queueing_delay_and_a_known_minimum() {
    // 11.25 ms is exactly 1/8 above 10 ms: filtered. One nanosecond more: not.
    let mut c = grown_to(1_000_000);
    c.on_congestion_event(SECOND, SECOND - 1, 10 * MS + 10 * MS / 8, Some(10 * MS));
    assert_eq!(c.cwnd(), 900_000);
    let mut c = grown_to(1_000_000);
    c.on_congestion_event(SECOND, SECOND - 1, 10 * MS + 10 * MS / 8 + 1, Some(10 * MS));
    assert_eq!(c.cwnd(), 700_000);
    let mut c = grown_to(1_000_000);
    c.on_congestion_event(SECOND, SECOND - 1, 10 * MS, None);
    assert_eq!(c.cwnd(), 700_000);
}

#[test]
fn undo_restores_the_window() {
    let mut c = grown_to(100_000);
    assert!(!c.can_undo());
    assert!(!c.undo());
    c.on_congestion_event(SECOND, SECOND - 1, 50 * MS, Some(10 * MS));
    assert!(c.can_undo());
    assert!(c.undo());
    assert_eq!(c.cwnd(), 100_000);
    assert!(!c.in_slow_start() || c.ssthresh() == u64::MAX);
    assert!(c.recovery_start().is_none());
    assert!(!c.undo(), "only once");
}

// ---------------------------------------------------------------------------------------------------------------
// HyStart++
// ---------------------------------------------------------------------------------------------------------------

/// One round of `n` acknowledgements with round trip `rtt`; the round ends at `end`. Returns whether slow start ended.
fn round(c: &mut Cubic, first: u64, n: u64, rtt: u64, largest_sent: u64) -> bool {
    for i in 0..n {
        c.on_acked(&AckInput {
            now: SECOND,
            largest_acked: first + i,
            largest_sent,
            rtt_sample: Some(rtt),
            ..AckInput::default()
        });
        if !c.in_slow_start() {
            return true;
        }
    }
    false
}

#[test]
fn hystart_leaves_slow_start_when_the_round_minimum_rises() {
    // Round 1: pn 1..=8 at 20 ms; the round ends once pn 10 is acknowledged.
    let mut c = Cubic::new(MSS);
    assert!(!round(&mut c, 1, 8, 20 * MS, 10));
    // Round 2 starts at pn 10; threshold max(4 ms, min(20/8, 16)) = 4 ms. A rise of exactly 4 ms is not enough.
    assert!(!round(&mut c, 10, 8, 24 * MS, 30));
    assert!(c.in_slow_start());
    // Round 3 (starts at pn 30): the previous minimum is 24 ms; 28 ms + 1 ns exceeds it by more than 4 ms.
    assert!(
        !round(&mut c, 30, 7, 28 * MS + 1, 50),
        "fewer than 8 samples never exit"
    );
    assert!(round(&mut c, 37, 1, 28 * MS + 1, 50));
    assert_eq!(c.ssthresh(), c.cwnd());
    assert!(!c.in_slow_start());
}

#[test]
fn hystart_threshold_scales_with_the_round_trip_up_to_16_ms() {
    let mut c = Cubic::new(MSS);
    assert!(!round(&mut c, 1, 8, 200 * MS, 10));
    // min(200/8 = 25, 16) = 16 ms: 216 ms is not enough, 216 ms + 1 ns is.
    assert!(!round(&mut c, 10, 8, 216 * MS, 30));
    let mut c = Cubic::new(MSS);
    assert!(!round(&mut c, 1, 8, 200 * MS, 10));
    assert!(round(&mut c, 10, 8, 216 * MS + 1, 30));
    // 80 ms: 80/8 = 10 ms.
    let mut c = Cubic::new(MSS);
    assert!(!round(&mut c, 1, 8, 80 * MS, 10));
    assert!(round(&mut c, 10, 8, 90 * MS + 1, 30));
}

#[test]
fn hystart_stays_in_slow_start_on_a_steady_round_trip() {
    let mut c = Cubic::new(MSS);
    let mut first = 1;
    for round_no in 0..20u64 {
        assert!(
            !round(&mut c, first, 10, 20 * MS, first + 10 + round_no),
            "round {round_no}"
        );
        first += 10;
    }
    assert!(c.in_slow_start());
}

#[test]
fn slow_start_doubles_per_acknowledged_window() {
    let mut c = Cubic::new(MSS);
    c.on_acked(&AckInput {
        growth_bytes: 44_000,
        ..AckInput::default()
    });
    assert_eq!(c.cwnd(), 88_000);
    assert!(c.in_slow_start());
}

// ---------------------------------------------------------------------------------------------------------------
// Caps and restart
// ---------------------------------------------------------------------------------------------------------------

fn ack_at(c: &mut Cubic, now: u64, acked: u64, growth: u64, min_rtt: u64) {
    c.on_acked(&AckInput {
        now,
        acked_bytes: acked,
        growth_bytes: growth,
        min_rtt: Some(min_rtt),
        ..AckInput::default()
    });
}

#[test]
fn low_latency_paths_are_capped_at_two_bdp_plus_256_kib() {
    let mut c = Cubic::new(MSS);
    // No rate sample yet: no cap.
    ack_at(&mut c, 0, 0, 10_000_000, MS);
    assert!(c.cwnd() > 10_000_000);
    let mut c = Cubic::new(MSS);
    ack_at(&mut c, 0, 0, 0, MS);
    // 100 000 bytes in 1 ms = 100 MB/s; BDP over the 1 ms minimum round trip = 100 000 bytes.
    ack_at(&mut c, MS, 100_000, 10_000_000, MS);
    assert_eq!(c.delivery_rate(), Some(100_000_000));
    assert_eq!(c.cwnd(), 2 * 100_000 + 256 * 1024);
}

#[test]
fn paths_from_2_ms_are_not_capped_at_the_low_latency_limit() {
    let mut c = Cubic::new(MSS);
    ack_at(&mut c, 0, 0, 0, 10 * MS);
    ack_at(&mut c, 10 * MS, 10_000, 5_000_000, 10 * MS);
    assert!(c.cwnd() > 2 * 10_000 + 256 * 1024);
    let mut c = Cubic::new(MSS);
    ack_at(&mut c, 0, 0, 0, 2 * MS);
    ack_at(&mut c, 2 * MS, 1000, 5_000_000, 2 * MS);
    assert!(c.cwnd() > 2 * 1000 + 256 * 1024, "2 ms is not under 2 ms");
}

#[test]
fn long_rtt_paths_are_capped_at_two_bdp() {
    let mut c = Cubic::new(MSS);
    ack_at(&mut c, 0, 0, 0, 300 * MS);
    // 3 MB over 300 ms = 10 MB/s; BDP over 300 ms = 3 MB; cap 6 MB.
    ack_at(&mut c, 300 * MS, 3_000_000, 100_000_000, 300 * MS);
    assert_eq!(c.delivery_rate(), Some(10_000_000));
    assert_eq!(c.cwnd(), 6_000_000);
    // 249 ms is not a long-RTT path.
    let mut c = Cubic::new(MSS);
    ack_at(&mut c, 0, 0, 0, 249 * MS);
    ack_at(&mut c, 249 * MS, 1_000_000, 100_000_000, 249 * MS);
    assert!(c.cwnd() > 20_000_000);
}

#[test]
fn a_cap_never_goes_below_the_minimum_window() {
    let mut c = Cubic::new(MSS);
    ack_at(&mut c, 0, 0, 0, 300 * MS);
    ack_at(&mut c, 300 * MS, 1, 100_000, 300 * MS);
    assert_eq!(c.cwnd(), MIN_CWND);
}

#[test]
fn restart_returns_to_the_initial_state() {
    let mut c = grown_to(500_000);
    c.on_congestion_event(SECOND, SECOND - 1, 50 * MS, Some(10 * MS));
    ack_at(&mut c, 0, 0, 0, 10 * MS);
    ack_at(&mut c, 20 * MS, 1000, 0, 10 * MS);
    assert!(c.delivery_rate().is_some());
    c.set_mss(1452);
    c.restart();
    assert_eq!(c.cwnd(), INITIAL_CWND);
    assert_eq!(c.ssthresh(), u64::MAX);
    assert!(c.in_slow_start());
    assert!(c.recovery_start().is_none());
    assert!(c.delivery_rate().is_none());
    assert!(!c.can_undo());
    assert_eq!(c.mss(), 1452, "the segment size is kept");
}

// ---------------------------------------------------------------------------------------------------------------
// The pacer
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn the_pacer_runs_at_1_25_cwnd_per_srtt() {
    let mut p = Pacer::new(MSS);
    p.set_rate(120_000, 100 * MS, MSS);
    assert_eq!(p.rate_bytes_per_sec(), 1_500_000);
    assert_eq!(p.burst(), 12_000);
    assert_eq!(BURST_PACKETS, 10);
    // Drain the bucket, then count what leaves in one second.
    let mut now = 0u64;
    let mut sent = 0u64;
    while p.next_release(now) <= now && sent < 12_000 {
        p.on_sent(now, MSS);
        sent += MSS;
    }
    assert_eq!(sent, 12_000, "the burst leaves at once");
    while now < SECOND {
        now = p.next_release(now).max(now);
        if now >= SECOND {
            break;
        }
        p.on_sent(now, MSS);
        sent += MSS;
    }
    let expect = 12_000.0 + 1_500_000.0;
    let err = (sent as f64 - expect).abs() / expect;
    assert!(err < 0.002, "sent {sent}, expected about {expect}");
}

#[test]
fn the_pacer_releases_the_next_packet_exactly_when_a_packet_of_tokens_exists() {
    let mut p = Pacer::new(MSS);
    p.set_rate(120_000, 100 * MS, MSS);
    for _ in 0..10 {
        assert_eq!(p.next_release(0), 0);
        p.on_sent(0, MSS);
    }
    // 1200 bytes at 1.5 MB/s = 800 us.
    assert_eq!(p.next_release(0), 800_000);
    assert_eq!(p.next_release(799_999), 800_000);
    assert_eq!(p.next_release(800_000), 800_000);
    p.on_sent(800_000, MSS);
    assert_eq!(p.next_release(800_000), 1_600_000);
}

#[test]
fn the_pacer_burst_is_ten_packets_even_after_a_long_idle() {
    let mut p = Pacer::new(MSS);
    p.set_rate(120_000, 100 * MS, MSS);
    let idle = 3600 * SECOND;
    for _ in 0..10 {
        assert_eq!(p.next_release(idle), idle);
        p.on_sent(idle, MSS);
    }
    assert!(p.next_release(idle) > idle, "the 11th packet waits");
}

#[test]
fn an_unconfigured_pacer_never_waits() {
    let p = Pacer::new(MSS);
    assert_eq!(p.rate_bytes_per_sec(), 0);
    assert_eq!(p.next_release(42), 42);
}

// ---------------------------------------------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum CcOp {
    Ack {
        now: u64,
        growth: u64,
        acked: u64,
        la: u64,
        ls: u64,
        rtt: Option<u64>,
        min_rtt: Option<u64>,
    },
    Loss {
        now: u64,
        sent: u64,
        srtt: u64,
        min_rtt: Option<u64>,
    },
    Undo,
    Restart,
    Mss(u64),
}

fn big() -> impl Strategy<Value = u64> {
    prop_oneof![
        Just(0u64),
        Just(1),
        Just(u64::MAX),
        Just(u64::MAX / 2),
        any::<u64>(),
        0u64..10_000_000_000
    ]
}

fn cc_op() -> impl Strategy<Value = CcOp> {
    prop_oneof![
        5 => (big(), big(), big(), big(), big(), proptest::option::of(big()), proptest::option::of(big())).prop_map(
            |(now, growth, acked, la, ls, rtt, min_rtt)| CcOp::Ack { now, growth, acked, la, ls, rtt, min_rtt }
        ),
        3 => (big(), big(), big(), proptest::option::of(big())).prop_map(|(now, sent, srtt, min_rtt)| CcOp::Loss { now, sent, srtt, min_rtt }),
        1 => Just(CcOp::Undo),
        1 => Just(CcOp::Restart),
        1 => big().prop_map(CcOp::Mss),
    ]
}

proptest! {
    /// The window stays within its bounds and nothing panics, for any inputs including `u64` extremes.
    #[test]
    fn the_window_stays_in_bounds(ops in proptest::collection::vec(cc_op(), 1..300)) {
        let mut c = Cubic::new(MSS);
        let mut p = Pacer::new(MSS);
        for op in ops {
            match op {
                CcOp::Ack { now, growth, acked, la, ls, rtt, min_rtt } => c.on_acked(&AckInput {
                    now, growth_bytes: growth, acked_bytes: acked, largest_acked: la, largest_sent: ls, rtt_sample: rtt, min_rtt,
                }),
                CcOp::Loss { now, sent, srtt, min_rtt } => { c.on_congestion_event(now, sent, srtt, min_rtt); }
                CcOp::Undo => { c.undo(); }
                CcOp::Restart => c.restart(),
                CcOp::Mss(m) => c.set_mss(m),
            }
            prop_assert!(c.cwnd() >= MIN_CWND, "cwnd {} below the minimum", c.cwnd());
            prop_assert!(c.cwnd() <= MAX_CWND);
            prop_assert!(c.ssthresh() >= MIN_CWND);
            p.set_rate(c.cwnd(), c.cwnd() ^ 0x5555, c.mss());
            let t = c.cwnd();
            let _ = p.next_release(t);
            p.on_sent(t, t);
        }
    }

    /// The pacer never panics and never waits less than zero, for any inputs.
    #[test]
    fn the_pacer_handles_any_inputs(
        cwnd in big(), srtt in big(), mss in big(),
        events in proptest::collection::vec((big(), big()), 1..60),
    ) {
        let mut p = Pacer::new(mss);
        p.set_rate(cwnd, srtt, mss);
        let _ = p.rate_bytes_per_sec();
        for (now, size) in events {
            let r = p.next_release(now);
            prop_assert!(r >= now);
            p.on_sent(now, size);
        }
    }
}
