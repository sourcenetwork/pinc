//! Tests of pinc-transport's congestion control and pacing: the cubic growth against an exact integer model and a
//! floating-point reference of the same update, the loss responses and the loss filter, the slow-start exit, the
//! delivery-rate estimate, the rate gate against the two caps it generalises, and the pacer.
//!
//! Every expected value is computed from the rule's own formula, written out in the test.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::similar_names,
    clippy::too_many_lines
)]

use proptest::prelude::*;
use pinc_transport::recovery::{
    AckInput, CONGESTION_BETA_SMALL, Cubic, INITIAL_CWND, MAX_CWND, MIN_CWND, MS, Pacer, SECOND,
};

pub(crate) const MSS: u64 = 1200;

mod cc_gate;

use cc_gate::with_rate;

pub(crate) fn ack(now: u64, acked: u64) -> AckInput {
    AckInput {
        now,
        acked,
        largest_acked: 0,
        next_pn: 0,
        srtt: Some(50 * MS),
        min_rtt: None,
        mss: MSS,
    }
}

/// Grow a fresh controller in slow start to exactly `target` bytes (no round-trip samples, so no early exit).
fn grown_to(target: u64) -> Cubic {
    let mut c = Cubic::new();
    c.on_acked(&ack(0, target - INITIAL_CWND));
    assert_eq!(c.cwnd(), target);
    c
}

// ---------------------------------------------------------------------------------------------------------------
// Slow start
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn the_initial_state_is_44000_in_slow_start() {
    let c = Cubic::new();
    assert_eq!((c.cwnd(), c.ssthresh(), c.w_max()), (44_000, u64::MAX, 0));
    assert!(c.in_slow_start());
    assert_eq!(c.delivery_rate(), 0);
    assert!(c.recovery_start().is_none());
}

#[test]
fn slow_start_adds_every_acknowledged_byte() {
    // cwnd += acked, per acknowledgement, whatever its size.
    let mut c = Cubic::new();
    let mut want = INITIAL_CWND;
    for acked in [1200, 1, 3600, 0, 65_000] {
        c.on_acked(&ack(0, acked));
        want += acked;
        assert_eq!(c.cwnd(), want);
    }
}

#[test]
fn the_window_grows_while_a_recovery_is_on() {
    // Growth is not conditioned on the recovery: after a filtered loss (which keeps slow start) the next
    // acknowledged bytes are added in full.
    let mut c = grown_to(100_000);
    assert!(c.on_loss(SECOND, SECOND - 1, Some(10 * MS), Some(10 * MS)));
    assert_eq!(c.cwnd(), 90_000);
    assert!(c.in_slow_start());
    assert!(c.recovery_start().is_some());
    c.on_acked(&ack(SECOND + MS, 5000));
    assert_eq!(c.cwnd(), 95_000);
    // And in congestion avoidance: acks of data sent before the recovery began still grow the window.
    let mut c = grown_to(100_000);
    assert!(c.on_loss(SECOND, SECOND - 1, None, None));
    let before = c.cwnd();
    c.on_acked(&ack(SECOND + MS, 12_000));
    assert!(c.cwnd() > before);
}

// ---------------------------------------------------------------------------------------------------------------
// The slow-start exit
// ---------------------------------------------------------------------------------------------------------------

/// One acknowledgement preceded by `samples` round-trip samples.
fn round(c: &mut Cubic, samples: &[u64], largest_acked: u64, next_pn: u64) {
    for &s in samples {
        c.on_rtt_sample(s);
    }
    c.on_acked(&AckInput {
        largest_acked,
        next_pn,
        ..ack(0, 0)
    });
}

/// A controller whose reference round (8 samples of `reference`) is complete and whose next round ends at packet 30.
fn with_reference_round(reference: u64) -> Cubic {
    let mut c = Cubic::new();
    round(&mut c, &[], 0, 10); // the first acknowledgement opens a round that ends at packet 10
    round(&mut c, &[reference; 8], 5, 11);
    round(&mut c, &[], 12, 30); // largest acked (12) >= 10: the round ends; 8 samples: the reference is set
    assert!(c.in_slow_start());
    c
}

#[test]
fn slow_start_ends_when_a_full_round_rises_above_the_threshold() {
    // threshold = max(4 ms, min(20 ms / 8, 16 ms)) = 4 ms: a round minimum above 24 ms ends slow start.
    let mut c = with_reference_round(20 * MS);
    round(&mut c, &[24 * MS; 8], 15, 31);
    assert!(c.in_slow_start(), "24 ms is at the threshold, not above it");
    let mut c = with_reference_round(20 * MS);
    round(&mut c, &[24 * MS + 1; 8], 15, 31);
    assert!(!c.in_slow_start(), "one nanosecond above the threshold ends slow start");
    assert_eq!(c.ssthresh(), c.cwnd(), "the exit sets only the threshold");
    assert_eq!(c.w_max(), 0, "the exit does not set w_max");
}

#[test]
fn round_exit_needs_eight_samples_in_the_round() {
    let mut c = with_reference_round(20 * MS);
    round(&mut c, &[100 * MS; 7], 15, 31);
    assert!(c.in_slow_start(), "7 samples never trigger an exit");
    round(&mut c, &[100 * MS], 16, 31);
    assert!(!c.in_slow_start(), "the 8th sample does");
}

#[test]
fn round_exit_keeps_the_old_reference_after_a_short_round() {
    let mut c = with_reference_round(20 * MS);
    // A round of 7 samples ends at packet 30: it does not replace the reference (20 ms)...
    round(&mut c, &[200 * MS; 7], 15, 31);
    round(&mut c, &[], 30, 60);
    assert!(c.in_slow_start());
    // ...so a following full round at 25 ms is above 20 ms + 4 ms and ends slow start.
    round(&mut c, &[25 * MS; 8], 40, 61);
    assert!(!c.in_slow_start());
}

#[test]
fn round_exit_threshold_is_an_eighth_of_the_reference_between_4_and_16_ms() {
    for (reference, extra) in [
        (20 * MS, 4 * MS),
        (80 * MS, 10 * MS),
        (200 * MS, 16 * MS),
        (400 * MS, 16 * MS),
    ] {
        let mut c = with_reference_round(reference);
        round(&mut c, &[reference + extra; 8], 15, 31);
        assert!(c.in_slow_start(), "reference {reference}: +{extra} is at the threshold");
        let mut c = with_reference_round(reference);
        round(&mut c, &[reference + extra + 1; 8], 15, 31);
        assert!(!c.in_slow_start(), "reference {reference}: +{extra} + 1 ns is above it");
    }
}

#[test]
fn round_exit_does_not_end_the_round_before_the_round_end_packet_is_acknowledged() {
    let mut c = Cubic::new();
    round(&mut c, &[], 0, 10);
    round(&mut c, &[20 * MS; 8], 5, 11);
    // Packet 9 is the largest acknowledged and the round ends at 10: not over yet, so there is no reference.
    round(&mut c, &[], 9, 30);
    round(&mut c, &[100 * MS; 8], 9, 30);
    assert!(c.in_slow_start(), "without a reference round nothing triggers");
}

#[test]
fn round_exit_needs_a_window_of_19200_bytes() {
    // Filtered losses (no queueing delay) keep slow start; each cut is x 0.9, four in a row, then the streak
    // decays after four smoothed round trips.
    let mut c = Cubic::new();
    let mut now = SECOND;
    while c.cwnd() >= 19_200 {
        for _ in 0..4 {
            c.on_loss(now, now - 1, Some(10 * MS), Some(10 * MS));
            now += 10 * MS;
        }
        now += SECOND;
        c.on_acked(&ack(now, 0));
        assert_eq!(c.filter_streak(), 0);
    }
    assert!(c.in_slow_start());
    round(&mut c, &[], 0, 10);
    round(&mut c, &[20 * MS; 8], 5, 11);
    round(&mut c, &[], 12, 30);
    round(&mut c, &[100 * MS; 8], 15, 31);
    assert!(c.in_slow_start(), "a window under 19200 bytes never exits");
}

// ---------------------------------------------------------------------------------------------------------------
// Loss responses
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn a_loss_with_queueing_delay_cuts_to_0_7_and_to_0_85_below_48_kb() {
    // cwnd = max(2400, cwnd * (85 if cwnd < 48000 else 70) / 100); ssthresh = cwnd; w_max = the old window.
    for (start, num) in [
        (300_000u64, 70u64),
        (CONGESTION_BETA_SMALL, 70),
        (CONGESTION_BETA_SMALL - 1, 85),
        (44_000, 85),
    ] {
        let mut c = grown_to(start);
        assert!(c.on_loss(SECOND, SECOND - 1, None, None));
        assert_eq!(c.cwnd(), (start * num / 100).max(MIN_CWND), "start {start}");
        assert_eq!(c.ssthresh(), c.cwnd());
        assert_eq!(c.w_max(), start);
        assert!(!c.in_slow_start());
    }
}

#[test]
fn the_window_never_falls_below_2400() {
    let mut c = Cubic::new();
    let mut now = SECOND;
    for _ in 0..40 {
        c.on_loss(now, now - 1, None, None);
        now += SECOND;
        assert!(c.cwnd() >= MIN_CWND);
    }
    assert_eq!(c.cwnd(), MIN_CWND);
}

#[test]
fn one_reduction_per_episode() {
    let mut c = grown_to(300_000);
    assert!(c.on_loss(SECOND, SECOND - 1, None, None));
    let cut = c.cwnd();
    // Anything sent at or before the recovery start belongs to the same episode.
    assert!(!c.on_loss(SECOND + 5, SECOND, None, None));
    assert!(!c.on_loss(SECOND + 5, SECOND - 10, None, None));
    assert_eq!(c.cwnd(), cut);
    // A packet sent after the recovery start starts a new one.
    assert!(c.on_loss(SECOND + 10, SECOND + 1, None, None));
    assert!(c.cwnd() < cut);
}

// ---------------------------------------------------------------------------------------------------------------
// The loss filter
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn the_loss_filter_tests_the_latest_round_trip_against_the_minimum_plus_the_larger_of_4_ms_and_an_eighth() {
    // latest <= min + max(4 ms, min / 8), evaluated for several minimums on both sides of the boundary.
    for min in [MS, 8 * MS, 32 * MS, 40 * MS, 100 * MS, 800 * MS] {
        let bound = min + (4 * MS).max(min / 8);
        let mut c = grown_to(200_000);
        assert!(c.on_loss(SECOND, SECOND - 1, Some(bound), Some(min)));
        assert_eq!(c.cwnd(), 180_000, "min {min}: latest at the bound is filtered");
        let mut c = grown_to(200_000);
        assert!(c.on_loss(SECOND, SECOND - 1, Some(bound + 1), Some(min)));
        assert_eq!(c.cwnd(), 140_000, "min {min}: one nanosecond above is a full response");
    }
    // Without a sample there is nothing to filter on.
    let mut c = grown_to(200_000);
    c.on_loss(SECOND, SECOND - 1, None, Some(10 * MS));
    assert_eq!(c.cwnd(), 140_000);
    let mut c = grown_to(200_000);
    c.on_loss(SECOND, SECOND - 1, Some(10 * MS), None);
    assert_eq!(c.cwnd(), 140_000);
}

#[test]
fn a_filtered_loss_does_not_leave_slow_start() {
    let mut c = grown_to(200_000);
    assert!(c.on_loss(SECOND, SECOND - 1, Some(10 * MS), Some(10 * MS)));
    assert_eq!(c.cwnd(), 180_000);
    assert_eq!(c.ssthresh(), u64::MAX, "an unset threshold stays unset");
    assert!(c.in_slow_start());
    assert_eq!(c.w_max(), 0, "w_max is untouched");
    assert_eq!(c.filter_streak(), 1);
}

#[test]
fn a_filtered_loss_lowers_a_threshold_that_is_set() {
    // After a full loss the threshold is set; a later filtered loss takes the minimum of both.
    let mut c = grown_to(400_000);
    c.on_loss(SECOND, SECOND - 1, None, None);
    assert_eq!(c.cwnd(), 280_000);
    c.on_acked(&ack(SECOND + MS, 0));
    let (w_max, cwnd) = (c.w_max(), c.cwnd());
    assert!(c.on_loss(2 * SECOND, 2 * SECOND - 1, Some(10 * MS), Some(10 * MS)));
    assert_eq!(c.cwnd(), cwnd * 9 / 10);
    assert_eq!(c.ssthresh(), c.cwnd(), "min(ssthresh, cwnd)");
    assert_eq!(c.w_max(), w_max, "w_max is kept");
}

#[test]
fn the_loss_filter_cuts_by_0_9_at_most_four_times_in_a_row() {
    let mut c = grown_to(1_000_000);
    let mut now = SECOND;
    let mut want = 1_000_000;
    for i in 1..=4 {
        assert!(c.on_loss(now, now - 1, Some(10 * MS), Some(10 * MS)));
        want = want * 9 / 10;
        assert_eq!(c.cwnd(), want, "cut {i}");
        now += 10 * MS;
    }
    assert_eq!(c.filter_streak(), 4);
    // The fifth is a full response: x 0.7, the threshold set, w_max recorded.
    assert!(c.on_loss(now, now - 1, Some(10 * MS), Some(10 * MS)));
    assert_eq!(c.cwnd(), want * 70 / 100);
    assert_eq!(c.w_max(), want);
    assert_eq!(c.filter_streak(), 0);
}

#[test]
fn the_filter_streak_decays_after_four_smoothed_round_trips() {
    let srtt = 50 * MS;
    let mut c = grown_to(1_000_000);
    let t0 = SECOND;
    for i in 0..3 {
        c.on_loss(t0 + i * MS, t0 + i * MS - 1, Some(10 * MS), Some(10 * MS));
    }
    assert_eq!(c.filter_streak(), 3);
    let recovery = t0 + 2 * MS;
    // At exactly 4 smoothed round trips after the last reduction the streak stays; one nanosecond later it resets.
    c.on_acked(&AckInput {
        srtt: Some(srtt),
        ..ack(recovery + 4 * srtt, 0)
    });
    assert_eq!(c.filter_streak(), 3);
    c.on_acked(&AckInput {
        srtt: Some(srtt),
        ..ack(recovery + 4 * srtt + 1, 0)
    });
    assert_eq!(c.filter_streak(), 0);
    // Without a sample the decay clock uses 333 ms.
    let mut c = grown_to(1_000_000);
    c.on_loss(t0, t0 - 1, Some(10 * MS), Some(10 * MS));
    c.on_acked(&AckInput {
        srtt: None,
        ..ack(t0 + 4 * 333 * MS, 0)
    });
    assert_eq!(c.filter_streak(), 1);
    c.on_acked(&AckInput {
        srtt: None,
        ..ack(t0 + 4 * 333 * MS + 1, 0)
    });
    assert_eq!(c.filter_streak(), 0);
}

// ---------------------------------------------------------------------------------------------------------------
// Cubic growth: an exact integer model, and a floating-point reference of the same update
// ---------------------------------------------------------------------------------------------------------------

/// The integer cube root by Newton's method with a final correction.
fn icbrt(n: i128) -> i128 {
    if n <= 0 {
        return 0;
    }
    let bits = 128 - i128::from(n.leading_zeros());
    let mut x = 1i128 << ((bits + 2) / 3);
    for _ in 0..64 {
        let y = (2 * x + n / (x * x)) / 3;
        if y >= x {
            break;
        }
        x = y;
    }
    while x * x * x > n {
        x -= 1;
    }
    x
}

/// The congestion-avoidance update written out in exact integer arithmetic:
/// - at the start of an epoch, `K = icbrt(((w_max - cwnd) * 1e9 // (mss * 4)) * 10)` ms when `cwnd < w_max`, else 0,
///   and `w_est = cwnd`;
/// - `t = (now - epoch + srtt) // 1 ms`, `target = w_max + (4 * mss * (t - K)^3) // (10 * 1e9)`;
/// - if `target > cwnd`: `cwnd += max(1, (target - cwnd) * mss // cwnd * acked // mss)`;
/// - `w_est += 53 * mss * acked // (100 * cwnd)`; if `w_est > cwnd`: `cwnd = w_est`.
struct Model {
    cwnd: i128,
    w_max: i128,
    w_est: i128,
    k_ms: i128,
    epoch: Option<u64>,
}

impl Model {
    fn after_loss(w_max: u64, cwnd: u64) -> Self {
        Self {
            cwnd: i128::from(cwnd),
            w_max: i128::from(w_max),
            w_est: 0,
            k_ms: 0,
            epoch: None,
        }
    }

    fn ack(&mut self, now: u64, acked: u64, srtt: u64, mss: u64) {
        let (mss, acked) = (i128::from(mss), i128::from(acked));
        let epoch = if let Some(e) = self.epoch {
            e
        } else {
            self.epoch = Some(now);
            self.k_ms = if self.cwnd < self.w_max {
                icbrt((self.w_max - self.cwnd) * 1_000_000_000 / (mss * 4) * 10)
            } else {
                0
            };
            self.w_est = self.cwnd;
            now
        };
        let t = i128::from((now - epoch + srtt) / MS);
        let d = t - self.k_ms;
        let target = self.w_max + (4 * mss * d * d * d).div_euclid(10 * 1_000_000_000);
        if target > self.cwnd {
            self.cwnd += ((target - self.cwnd) * mss / self.cwnd * acked / mss).max(1);
        }
        self.w_est += 53 * mss * acked / (100 * self.cwnd);
        if self.w_est > self.cwnd {
            self.cwnd = self.w_est;
        }
    }
}

/// Drive a controller and the model through the same acknowledgements and compare the windows exactly.
fn drive_against_model(c: &mut Cubic, m: &mut Model, start: u64, acks: &[(u64, u64)], srtt: u64, mss: u64) {
    let mut now = start;
    for (i, &(gap, acked)) in acks.iter().enumerate() {
        now += gap;
        c.on_acked(&AckInput {
            srtt: Some(srtt),
            mss,
            ..ack(now, acked)
        });
        m.ack(now, acked, srtt, mss);
        assert_eq!(i128::from(c.cwnd()), m.cwnd, "acknowledgement {i} at {now}");
    }
}

fn schedule(n: usize, gap: u64, sizes: &[u64]) -> Vec<(u64, u64)> {
    (0..n).map(|i| (gap, sizes[i % sizes.len()])).collect()
}

#[test]
fn cubic_equals_the_integer_formula_after_a_loss() {
    for (w_max, srtt, gap, mss) in [
        (600_000u64, 40 * MS, 7 * MS, 1200u64),
        (3_000_000, 100 * MS, 3 * MS, 1200),
        (90_000, 20 * MS, 11 * MS, 1200),
        (2_000_000, MS, 2 * MS, 8952),
    ] {
        let mut c = grown_to(w_max);
        c.on_loss(5 * SECOND, 5 * SECOND - 1, None, None);
        let mut m = Model::after_loss(w_max, c.cwnd());
        let acks = schedule(3000, gap, &[1200, 2400, 1, 36_000, 500, 12_000]);
        drive_against_model(&mut c, &mut m, 5 * SECOND, &acks, srtt, mss);
    }
}

#[test]
fn cubic_equals_the_integer_formula_across_an_idle_gap_with_no_cap_on_the_target() {
    let mut c = grown_to(100_000);
    c.on_loss(SECOND, SECOND - 1, None, None);
    let mut m = Model::after_loss(100_000, c.cwnd());
    let mut now = SECOND;
    let warm = schedule(200, 5 * MS, &[1200]);
    drive_against_model(&mut c, &mut m, now, &warm, 50 * MS, MSS);
    now += 200 * 5 * MS;
    // Five minutes of silence, then one acknowledgement: the cubic target is far above the window and the step is
    // ((target - cwnd) * mss // cwnd) * acked // mss, uncapped.
    let before = c.cwnd();
    drive_against_model(&mut c, &mut m, now, &[(300 * SECOND, 1200)], 50 * MS, MSS);
    assert!(
        c.cwnd() - before > 1200,
        "the step ({}) exceeds what a cap of 1.5 x the window allows (at most half an acknowledgement)",
        c.cwnd() - before
    );
    now += 300 * SECOND;
    drive_against_model(&mut c, &mut m, now, &schedule(300, 4 * MS, &[1200, 7200]), 50 * MS, MSS);
}

#[test]
fn a_step_grows_the_window_by_at_least_one_byte() {
    // While the target is above the window by less than cwnd / mss bytes, floor((target - cwnd) * mss / cwnd) is 0
    // yet the window moves by max(1, 0) = 1 byte (1 byte acknowledged, so the Reno estimate adds nothing).
    let mut c = grown_to(100_000);
    c.on_loss(SECOND, SECOND - 1, None, None);
    c.on_acked(&AckInput {
        srtt: Some(0),
        ..ack(2 * SECOND, 0)
    });
    let cwnd0 = i128::from(c.cwnd());
    let k = icbrt(i128::from(100_000 - c.cwnd()) * 1_000_000_000 / (4 * 1200) * 10);
    let t = (0..2 * k)
        .find(|t| {
            let d = *t - k;
            let target = 100_000 + (4 * 1200 * d * d * d).div_euclid(10_000_000_000);
            target > cwnd0 && (target - cwnd0) * 1200 < cwnd0
        })
        .expect("an instant with a target a few bytes above the window");
    let mut c2 = c;
    c2.on_acked(&AckInput {
        srtt: Some(0),
        ..ack(2 * SECOND + u64::try_from(t).unwrap() * MS, 1)
    });
    assert_eq!(i128::from(c2.cwnd()), cwnd0 + 1, "t = {t}");
}

#[test]
fn after_the_slow_start_exit_only_the_reno_term_grows_the_window() {
    // The exit sets only the threshold, so w_max stays 0: K = 0 and the cubic target starts from 0, below the
    // window. The window moves by w_est += 53 * mss * acked / (100 * cwnd), taking over when w_est > cwnd.
    let mut c = with_reference_round(20 * MS);
    round(&mut c, &[100 * MS; 8], 15, 31);
    assert!(!c.in_slow_start());
    assert_eq!(c.w_max(), 0);
    let start = c.cwnd();
    let mut m = Model::after_loss(0, start);
    let acks = schedule(2000, 3 * MS, &[1200, 2400, 600]);
    drive_against_model(&mut c, &mut m, SECOND, &acks, 50 * MS, MSS);
    // The cubic term alone starts at 0 and needs about 6 s to catch up with a 44 KB window (4 * 1200 * t^3 / 1e10).
    assert!(c.cwnd() > start);
}

#[test]
fn the_reno_estimate_takes_over_the_window_with_a_jump() {
    // At the start of an epoch the cubic target is the window itself (K is placed from the gap to w_max), so one
    // large acknowledgement with no look-ahead moves the cubic by one byte but w_est by 53 * mss * acked /
    // (100 * cwnd): the window jumps to w_est.
    let mut c = grown_to(1_000_000);
    c.on_loss(SECOND, SECOND - 1, None, None);
    let cwnd0 = c.cwnd();
    let mut m = Model::after_loss(1_000_000, cwnd0);
    c.on_acked(&AckInput {
        srtt: Some(0),
        ..ack(2 * SECOND, 10_000_000)
    });
    m.ack(2 * SECOND, 10_000_000, 0, MSS);
    assert_eq!(i128::from(c.cwnd()), m.cwnd);
    let reno = 53 * MSS * 10_000_000 / (100 * (cwnd0 + 1));
    assert!(reno > 9000);
    assert_eq!(
        c.cwnd(),
        cwnd0 + reno,
        "the window equals w_est = cwnd + 53 mss acked / (100 cwnd)"
    );
}

#[test]
fn the_cubic_look_ahead_is_the_smoothed_round_trip() {
    // Two controllers differing only in srtt: with the look-ahead, the larger srtt sits further along the curve.
    let run = |srtt: u64| {
        let mut c = grown_to(400_000);
        c.on_loss(SECOND, SECOND - 1, None, None);
        for i in 0..400 {
            c.on_acked(&AckInput {
                srtt: Some(srtt),
                ..ack(2 * SECOND + i * 10 * MS, 1200)
            });
        }
        c.cwnd()
    };
    assert!(run(200 * MS) > run(10 * MS));
}

#[test]
fn without_a_sample_the_look_ahead_is_333_ms() {
    let run = |srtt: Option<u64>| {
        let mut c = grown_to(400_000);
        c.on_loss(SECOND, SECOND - 1, None, None);
        for i in 0..200 {
            c.on_acked(&AckInput {
                srtt,
                ..ack(2 * SECOND + i * 10 * MS, 1200)
            });
        }
        c.cwnd()
    };
    assert_eq!(run(None), run(Some(333 * MS)));
}

/// The same update in `f64`, with the same floors: `K` from an exact cube root, then per acknowledgement
/// `x = floor((target - cwnd) * mss / cwnd)`, `cwnd += max(1, floor(x * acked / mss))`, `w_est += floor(0.53 mss
/// acked / cwnd)`, and `cwnd = w_est` when it is higher.
struct Reference {
    cwnd: f64,
    w_max: f64,
    w_est: f64,
    k_ms: f64,
    epoch: Option<f64>,
    mss: f64,
}

impl Reference {
    fn on_ack(&mut self, now_ms: f64, acked: f64, srtt_ms: f64) {
        let epoch = *self.epoch.get_or_insert_with(|| {
            self.k_ms = if self.w_max > self.cwnd {
                ((self.w_max - self.cwnd) * 1e9 / (self.mss * 4.0) * 10.0)
                    .cbrt()
                    .floor()
            } else {
                0.0
            };
            self.w_est = self.cwnd;
            now_ms
        });
        let t = ((now_ms - epoch) + srtt_ms).floor();
        let d = t - self.k_ms;
        let target = self.w_max + (4.0 * self.mss * d * d * d / 1e10).floor();
        if target > self.cwnd {
            let x = ((target - self.cwnd) * self.mss / self.cwnd).floor();
            self.cwnd += (x * acked / self.mss).floor().max(1.0);
        }
        self.w_est += (53.0 * self.mss * acked / (100.0 * self.cwnd)).floor();
        if self.w_est > self.cwnd {
            self.cwnd = self.w_est;
        }
    }
}

fn drive_against_reference(loss_cwnd: u64, srtt: u64, step: u64, acked: u64, seconds: u64, mss: u64) {
    let mut c = grown_to(loss_cwnd);
    let loss_at = 5 * SECOND;
    assert!(c.on_loss(loss_at, loss_at - 1, None, None));
    let mut r = Reference {
        cwnd: c.cwnd() as f64,
        w_max: loss_cwnd as f64,
        w_est: c.cwnd() as f64,
        k_ms: 0.0,
        epoch: None,
        mss: mss as f64,
    };
    let steps = seconds * SECOND / step;
    for i in 1..=steps {
        let now = loss_at + i * step;
        c.on_acked(&AckInput {
            srtt: Some(srtt),
            mss,
            ..ack(now, acked)
        });
        r.on_ack((now - loss_at) as f64 / 1e6, acked as f64, (srtt / MS) as f64);
        let err = (c.cwnd() as f64 - r.cwnd).abs() / r.cwnd;
        assert!(
            err < 0.005,
            "step {i}: integer {} vs reference {:.0} ({:.3}%)",
            c.cwnd(),
            r.cwnd,
            err * 100.0
        );
    }
}

#[test]
fn cubic_window_matches_the_float_reference_over_time() {
    // Beta 0.7, 40 ms smoothed round trip, a 20 s regrowth through the plateau at W_max.
    drive_against_reference(600_000, 40 * MS, 10 * MS, 12_000, 20, 1200);
}

#[test]
fn cubic_window_matches_the_reference_for_other_shapes() {
    drive_against_reference(5_000_000, 100 * MS, 10 * MS, 60_000, 30, 1200);
    drive_against_reference(120_000, 30 * MS, 5 * MS, 3_600, 20, 1200);
    // The segment size of a fast direct path (a jumbo datagram).
    drive_against_reference(2_000_000, MS, 2 * MS, 18_000, 10, 8952);
    // Beta 0.85 below 48,000 bytes.
    drive_against_reference(47_000, 20 * MS, 5 * MS, 2_400, 20, 1200);
}

#[test]
fn a_new_path_restarts_the_window_and_keeps_the_rate_and_w_max() {
    let mut c = grown_to(300_000);
    c.on_loss(SECOND, SECOND - 1, None, None);
    c.on_acked(&AckInput {
        min_rtt: Some(10 * MS),
        ..ack(2 * SECOND, 100_000)
    });
    c.on_acked(&AckInput {
        min_rtt: Some(10 * MS),
        ..ack(2 * SECOND + 10 * MS, 100_000)
    });
    let (rate, w_max) = (c.delivery_rate(), c.w_max());
    assert!(rate > 0 && w_max == 300_000);
    c.new_path(3 * SECOND, 77);
    assert_eq!((c.cwnd(), c.ssthresh()), (INITIAL_CWND, u64::MAX));
    assert_eq!(c.filter_streak(), 0);
    assert_eq!(c.delivery_rate(), rate);
    assert_eq!(c.w_max(), w_max);
    // The recovery mark is the switch time: a loss of anything sent before it cuts nothing.
    assert_eq!(c.recovery_start(), Some(3 * SECOND));
    assert!(!c.on_loss(3 * SECOND + 1, 3 * SECOND - 1, None, None));
    assert!(!c.on_loss(3 * SECOND + 1, 3 * SECOND, None, None));
    assert!(c.on_loss(3 * SECOND + 1, 3 * SECOND + 1, None, None));
    // A later recovery mark is never moved back.
    let mut c = grown_to(300_000);
    c.on_loss(5 * SECOND, 5 * SECOND - 1, None, None);
    c.new_path(3 * SECOND, 0);
    assert_eq!(c.recovery_start(), Some(5 * SECOND));
}

#[test]
fn restore_raises_the_window_the_threshold_and_the_reno_estimate() {
    let mut c = grown_to(300_000);
    c.on_loss(SECOND, SECOND - 1, None, None);
    let cut = c.cwnd();
    c.restore(300_000, 300_000);
    assert_eq!(c.cwnd(), 300_000);
    assert_eq!(c.ssthresh(), 300_000);
    // Nothing is restored when the window is already at least the saved one.
    c.restore(100_000, 100_000);
    assert_eq!(c.cwnd(), 300_000);
    assert!(cut < 300_000);
}

// ---------------------------------------------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum CcOp {
    Ack {
        now: u64,
        acked: u64,
        la: u64,
        next_pn: u64,
        srtt: Option<u64>,
        min_rtt: Option<u64>,
        mss: u64,
    },
    Sample(u64),
    Loss {
        now: u64,
        sent: u64,
        latest: Option<u64>,
        min_rtt: Option<u64>,
    },
    NewPath {
        now: u64,
        next_pn: u64,
    },
    Restore {
        cwnd: u64,
        ssthresh: u64,
    },
    Slack(u64),
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
        6 => (big(), big(), big(), big(), proptest::option::of(big()), proptest::option::of(big()), big()).prop_map(
            |(now, acked, la, next_pn, srtt, min_rtt, mss)| CcOp::Ack { now, acked, la, next_pn, srtt, min_rtt, mss }
        ),
        2 => big().prop_map(CcOp::Sample),
        3 => (big(), big(), proptest::option::of(big()), proptest::option::of(big())).prop_map(
            |(now, sent, latest, min_rtt)| CcOp::Loss { now, sent, latest, min_rtt }
        ),
        1 => (big(), big()).prop_map(|(now, next_pn)| CcOp::NewPath { now, next_pn }),
        1 => (big(), big()).prop_map(|(cwnd, ssthresh)| CcOp::Restore { cwnd, ssthresh }),
        1 => big().prop_map(CcOp::Slack),
    ]
}

proptest! {
    /// The window stays within its bounds and nothing panics, for any inputs including `u64` extremes.
    #[test]
    fn the_window_stays_in_bounds(ops in proptest::collection::vec(cc_op(), 1..300)) {
        let mut c = Cubic::new();
        let mut p = Pacer::new();
        for op in ops {
            match op {
                CcOp::Ack { now, acked, la, next_pn, srtt, min_rtt, mss } => c.on_acked(&AckInput {
                    now, acked, largest_acked: la, next_pn, srtt, min_rtt, mss,
                }),
                CcOp::Sample(s) => c.on_rtt_sample(s),
                CcOp::Loss { now, sent, latest, min_rtt } => { c.on_loss(now, sent, latest, min_rtt); }
                CcOp::NewPath { now, next_pn } => c.new_path(now, next_pn),
                CcOp::Restore { cwnd, ssthresh } => c.restore(cwnd, ssthresh),
                CcOp::Slack(s) => c.set_gate_slack(s),
            }
            prop_assert!(c.cwnd() >= MIN_CWND, "cwnd {} below the minimum", c.cwnd());
            prop_assert!(c.cwnd() <= MAX_CWND);
            let _ = c.gate_cap(c.cwnd() ^ 0x5555);
            let t = c.cwnd();
            let r = p.next_release(t);
            prop_assert!(r >= t);
            p.on_sent(t, t, t ^ 0xAAAA, t, t & 1 == 0);
        }
    }

    /// The pacer never panics and never waits less than zero, for any inputs.
    #[test]
    fn the_pacer_handles_any_inputs(
        events in proptest::collection::vec((big(), big(), big(), big(), any::<bool>()), 1..60),
    ) {
        let mut p = Pacer::new();
        for (now, mtu, srtt, cwnd, limited) in events {
            let r = p.next_release(now);
            prop_assert!(r >= now);
            p.on_sent(now, mtu, srtt, cwnd, limited);
        }
    }

    /// The gate is never below its floor and never above the window limit.
    #[test]
    fn the_gate_is_between_its_floor_and_the_window_limit(
        min_rtt in big(), first in 0u64..1_000_000_000, second in 0u64..1_000_000_000, mid in big(),
    ) {
        let m = min_rtt.clamp(1, 10 * SECOND);
        let mut c = with_rate(m, first, second);
        c.set_gate_slack(mid);
        if let Some(cap) = c.gate_cap(min_rtt) {
            let floor = if min_rtt >= 250 * MS { MIN_CWND } else { 44_000 };
            prop_assert!(cap >= floor && cap <= MAX_CWND);
        }
    }
}
