//! The congestion controller of one connection: slow start with a round-based exit, a cubic growth curve in
//! congestion avoidance, the loss filter, the loss responses and the rate gate.
//!
//! Slow start adds every acknowledged byte to the window. Congestion avoidance follows
//! `W(t) = W_max + 0.4 (t - K)^3` in segments, with `t` looking one smoothed round trip ahead, and a Reno-style
//! estimate that grows by 53/100 of a segment per window and takes over the window whenever it is higher. The window
//! grows on every acknowledged byte, in or out of a recovery, and nothing paces it down when the sender runs dry: the
//! [rate gate](Cubic::gate_cap) bounds it by what the path was measured to deliver. Below 2 ms and from 250 ms of
//! minimum round trip the gate caps the window on every acknowledgement. In between it caps it only when the sender
//! resumes after an idle or application-limited stretch ([`Cubic::resume`]), so slow start on a busy path is not cut
//! short by a rate sample that is one interval behind it.
//!
//! A loss multiplies the window by 0.7 (0.85 below 48,000 bytes) and ends slow start. A loss that shows no queueing
//! delay (the latest round trip within `min_rtt + max(4 ms, min_rtt / 8)`) is filtered: the window is multiplied by
//! 0.9, slow start is not left, and the streak is capped at 4 in a row until 4 smoothed round trips pass after the last
//! reduction. One reduction per episode: a loss of a packet sent before the last reduction changes nothing.
//!
//! Invariants: `MIN_CWND <= cwnd <= MAX_CWND` after every call; `ssthresh` is `u64::MAX` until first set. Overflow
//! bounds, all in `u128` or `i128` unless noted: the window is at most `MAX_CWND` (2^40) and the segment size at most
//! `MAX_MSS` (2^16).
//! - `K` in milliseconds is `icbrt((w_max - cwnd) * 1e9 / (4 mss) * 10)`: the radicand is below 2^(40 + 30 + 4) so the
//!   root is below 2^25.
//! - The cubic term is `4 mss d^3 / 1e10` with `|d|` at most 2^31 ms (the clock term is clamped to 2^30 ms): the
//!   product is below 2^(2 + 16 + 93) = 2^111 in `i128`, floored toward negative infinity.
//! - The target is capped at `MAX_CWND`. A growth step is `((target - cwnd) * mss / cwnd) * acked / mss`: the first
//!   product is below 2^(40 + 16), the
//!   quotient below 2^45 (the window is at least 2400), and times `acked` (below 2^64) below 2^109.
//! - The Reno estimate adds `53 mss acked / (100 cwnd)`: the numerator is below 2^(6 + 16 + 64) = 2^86.
//! - A reduction multiplies a window below 2^40 by at most 100: below 2^47, inside `u64`.

use super::MS;
use super::delivery::RateProbe;
use super::math::{icbrt, sat};
use super::round_exit::RoundExit;

/// The initial congestion window in bytes.
pub const INITIAL_CWND: u64 = 44_000;
/// The smallest congestion window in bytes.
pub const MIN_CWND: u64 = 2_400;
/// The largest congestion window in bytes (1 TiB); the bound that makes every product below fit.
pub const MAX_CWND: u64 = 1 << 40;
/// A window under this many bytes is cut by 0.85 instead of 0.7.
pub const CONGESTION_BETA_SMALL: u64 = 48_000;
/// The smallest segment size, and the one used on every path except a fast direct one (1200).
pub const MIN_MSS: u64 = 1_200;
/// The largest segment size the controller accepts (the largest UDP payload).
pub const MAX_MSS: u64 = 65_535;
/// The rate gate's slack below a minimum round trip of 2 ms: 256 KiB.
pub const GATE_SLACK_FAST: u64 = 256 * 1024;
/// The rate gate's default slack between 2 ms and 250 ms: 44,000 bytes.
pub const GATE_SLACK_MID: u64 = 44_000;

const BETA_NUM: u64 = 7;
const BETA_DEN: u64 = 10;
const BETA_SMALL_NUM: u64 = 85;
const BETA_SMALL_DEN: u64 = 100;
const FILTER_NUM: u64 = 9;
const FILTER_DEN: u64 = 10;
const FILTER_MAX_STREAK: u8 = 4;
const FILTER_FLOOR: u64 = 4 * MS;
/// The streak resets once the last reduction is older than this many smoothed round trips.
const FILTER_DECAY_RTTS: u64 = 4;
const RENO_NUM: u128 = 53;
const RENO_DEN: u128 = 100;
const FAST_RTT: u64 = 2 * MS;
const SLOW_RTT: u64 = super::LONG_RTT;
/// The clock term of the cubic is clamped to 2^30 ms (12 days), the bound behind the cube above.
const MAX_T_MS: u64 = 1 << 30;

/// What one acknowledgement tells the controller.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct AckInput {
    /// The current time in nanoseconds.
    pub now: u64,
    /// Bytes newly acknowledged by this acknowledgement.
    pub acked: u64,
    /// The largest packet number the peer has acknowledged so far.
    pub largest_acked: u64,
    /// The packet number the next sent packet will have.
    pub next_pn: u64,
    /// The smoothed round trip, if a sample exists.
    pub srtt: Option<u64>,
    /// The minimum round trip, if known.
    pub min_rtt: Option<u64>,
    /// The segment size for the growth steps (1200, or the path datagram size on a fast direct path).
    pub mss: u64,
}

/// The congestion controller.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cubic {
    cwnd: u64,
    ssthresh: u64,
    w_max: u64,
    w_est: u64,
    k_ms: u64,
    epoch: Option<u64>,
    recovery: Option<u64>,
    streak: u8,
    round_exit: RoundExit,
    probe: RateProbe,
    gate_slack_mid: u64,
}

impl Default for Cubic {
    fn default() -> Self {
        Self::new()
    }
}

impl Cubic {
    /// A controller in slow start with the initial window.
    pub const fn new() -> Self {
        Self {
            cwnd: INITIAL_CWND,
            ssthresh: u64::MAX,
            w_max: 0,
            w_est: 0,
            k_ms: 0,
            epoch: None,
            recovery: None,
            streak: 0,
            round_exit: RoundExit::new(),
            probe: RateProbe::new(),
            gate_slack_mid: GATE_SLACK_MID,
        }
    }

    /// The congestion window in bytes.
    pub const fn cwnd(&self) -> u64 {
        self.cwnd
    }

    /// The slow-start threshold in bytes (`u64::MAX` until it is first set).
    pub const fn ssthresh(&self) -> u64 {
        self.ssthresh
    }

    /// The window the last reduction started from.
    pub const fn w_max(&self) -> u64 {
        self.w_max
    }

    /// Whether the controller is in slow start.
    pub const fn in_slow_start(&self) -> bool {
        self.cwnd < self.ssthresh
    }

    /// When the last reduction happened, if any.
    pub const fn recovery_start(&self) -> Option<u64> {
        self.recovery
    }

    /// Consecutive filtered (0.9) reductions so far.
    pub const fn filter_streak(&self) -> u8 {
        self.streak
    }

    /// The delivery-rate estimate in bytes per second; 0 before the first interval ends.
    pub const fn delivery_rate(&self) -> u64 {
        self.probe.rate()
    }

    /// Set the rate gate's slack for paths whose minimum round trip is between 2 ms and 250 ms (44,000 by default).
    pub fn set_gate_slack(&mut self, bytes: u64) {
        self.gate_slack_mid = bytes.min(MAX_CWND);
    }

    /// The rate gate for a path with minimum round trip `min_rtt`: `max(floor, 2 * rate * min_rtt + slack)` bytes,
    /// or `None` while no delivery rate is known.
    ///
    /// - Below 2 ms the slack is 256 KiB and the floor 44,000.
    /// - At 250 ms or more the slack is 0 and the floor is [`MIN_CWND`], so the gate is exactly twice the
    ///   bandwidth-delay product.
    /// - In between the slack is the configured value (44,000 by default) and the floor 44,000.
    ///
    /// The product `rate * min_rtt` is formed in `u128`; the result is clamped to [`MAX_CWND`].
    pub fn gate_cap(&self, min_rtt: u64) -> Option<u64> {
        let rate = self.probe.rate();
        if rate == 0 {
            return None;
        }
        let bdp = sat(u128::from(rate) * u128::from(min_rtt) / 1_000_000_000);
        let (slack, floor) = if min_rtt < FAST_RTT {
            (GATE_SLACK_FAST, INITIAL_CWND)
        } else if min_rtt >= SLOW_RTT {
            (0, MIN_CWND)
        } else {
            (self.gate_slack_mid, INITIAL_CWND)
        };
        Some(bdp.saturating_mul(2).saturating_add(slack).max(floor).min(MAX_CWND))
    }

    /// Fold in one round-trip sample (feeds the slow-start exit).
    pub fn on_rtt_sample(&mut self, sample: u64) {
        self.round_exit.on_sample(sample);
    }

    /// Account for newly acknowledged data: update the delivery rate, let the filter streak decay, grow the window
    /// and apply the rate gate.
    pub fn on_acked(&mut self, a: &AckInput) {
        if let Some(m) = a.min_rtt.filter(|m| *m > 0) {
            self.probe.on_acked(a.now, a.acked, m);
        }
        let srtt = a.srtt.unwrap_or(super::INITIAL_RTT);
        if self.streak != 0
            && self
                .recovery
                .is_some_and(|r| a.now.saturating_sub(r) > FILTER_DECAY_RTTS.saturating_mul(srtt))
        {
            self.streak = 0;
        }
        self.grow(a, srtt);
        if let Some(m) = a.min_rtt.filter(|m| !(FAST_RTT..SLOW_RTT).contains(m)) {
            self.apply_gate(m);
        }
    }

    /// The sender resumes after a stretch in which the window did not limit it: cap the window, and the threshold,
    /// at the rate gate for a path with minimum round trip `min_rtt`, so a window that grew while the sender was idle
    /// or application-limited cannot leave as one burst. A no-op without a known minimum or a measured rate.
    pub fn resume(&mut self, min_rtt: Option<u64>) {
        if let Some(m) = min_rtt {
            self.apply_gate(m);
        }
    }

    fn apply_gate(&mut self, min_rtt: u64) {
        if let Some(cap) = self.gate_cap(min_rtt)
            && self.cwnd > cap
        {
            self.cwnd = cap;
            self.ssthresh = self.ssthresh.min(cap);
        }
    }

    fn grow(&mut self, a: &AckInput, srtt: u64) {
        if self.in_slow_start() {
            self.cwnd = self.cwnd.saturating_add(a.acked).min(MAX_CWND);
            if self.round_exit.on_ack(a.largest_acked, a.next_pn, self.cwnd) {
                self.ssthresh = self.cwnd;
            }
            return;
        }
        let mss = a.mss.clamp(MIN_MSS, MAX_MSS);
        let epoch = if let Some(e) = self.epoch {
            e
        } else {
            self.epoch = Some(a.now);
            self.k_ms = if self.cwnd < self.w_max {
                let d = u128::from(self.w_max - self.cwnd);
                icbrt(d * 1_000_000_000 / (u128::from(mss) * 4) * 10)
            } else {
                0
            };
            self.w_est = self.cwnd;
            a.now
        };
        let t_ms = (a.now.saturating_sub(epoch).saturating_add(srtt) / MS).min(MAX_T_MS);
        let target = cubic_target(self.w_max, self.k_ms, mss, t_ms);
        let cwnd = u128::from(self.cwnd);
        if target > i128::from(self.cwnd) {
            let gap = u128::try_from(target).unwrap_or(0) - cwnd;
            let step = (gap * u128::from(mss) / cwnd * u128::from(a.acked) / u128::from(mss)).max(1);
            self.cwnd = self.cwnd.saturating_add(sat(step)).min(MAX_CWND);
        }
        let reno = RENO_NUM * u128::from(mss) * u128::from(a.acked) / (RENO_DEN * u128::from(self.cwnd));
        self.w_est = self.w_est.saturating_add(sat(reno)).min(MAX_CWND);
        if self.w_est > self.cwnd {
            self.cwnd = self.w_est;
        }
    }

    /// React to the loss of packets whose newest was sent at `newest_lost_sent`. Returns whether the window was
    /// reduced: a loss of packets sent before the last reduction is part of that episode and changes nothing.
    ///
    /// `latest_rtt` and `min_rtt` are the newest and the smallest round trip, if sampled.
    pub fn on_loss(&mut self, now: u64, newest_lost_sent: u64, latest_rtt: Option<u64>, min_rtt: Option<u64>) -> bool {
        if self.recovery.is_some_and(|r| newest_lost_sent <= r) {
            return false;
        }
        self.recovery = Some(now);
        if let (Some(latest), Some(min)) = (latest_rtt, min_rtt)
            && latest <= min.saturating_add(FILTER_FLOOR.max(min / 8))
            && self.streak < FILTER_MAX_STREAK
        {
            self.streak += 1;
            self.cwnd = (self.cwnd * FILTER_NUM / FILTER_DEN).max(MIN_CWND);
            if self.ssthresh != u64::MAX {
                self.ssthresh = self.ssthresh.min(self.cwnd);
                self.w_est = self.w_est.min(self.cwnd);
            }
            return true;
        }
        self.streak = 0;
        self.w_max = self.cwnd;
        let (num, den) = if self.cwnd < CONGESTION_BETA_SMALL {
            (BETA_SMALL_NUM, BETA_SMALL_DEN)
        } else {
            (BETA_NUM, BETA_DEN)
        };
        self.cwnd = (self.cwnd * num / den).max(MIN_CWND);
        self.ssthresh = self.cwnd;
        self.epoch = None;
        self.w_est = self.cwnd;
        true
    }

    /// A new path: initial window, slow start, a fresh slow-start exit detector and filter streak, and the last
    /// reduction marked at `now` so a loss of anything sent before the switch cuts nothing. The delivery rate,
    /// `w_max` and the Reno estimate are kept.
    pub fn new_path(&mut self, now: u64, next_pn: u64) {
        self.cwnd = INITIAL_CWND;
        self.ssthresh = u64::MAX;
        self.epoch = None;
        self.round_exit.restart(next_pn);
        self.streak = 0;
        if self.recovery.is_none_or(|r| r < now) {
            self.recovery = Some(now);
        }
    }

    /// Restore a window saved before a probe that turned out to be spurious: the window rises to `cwnd` if it is
    /// lower, and the threshold and the Reno estimate rise to match.
    pub fn restore(&mut self, cwnd: u64, ssthresh: u64) {
        if self.cwnd < cwnd {
            self.cwnd = cwnd.min(MAX_CWND);
            self.ssthresh = self.ssthresh.max(ssthresh);
            self.w_est = self.w_est.max(self.cwnd);
        }
    }
}

/// `W_max + 4 mss d^3 / 1e10` with `d = t_ms - k_ms`, the floor of the quotient taken toward negative infinity,
/// capped at `MAX_CWND` (the window cannot pass it, and the cap keeps the growth step inside `u128`).
fn cubic_target(w_max: u64, k_ms: u64, mss: u64, t_ms: u64) -> i128 {
    let d = i128::from(t_ms) - i128::from(k_ms.min(MAX_T_MS));
    let delta = (4 * i128::from(mss) * d * d * d).div_euclid(10_000_000_000);
    (i128::from(w_max) + delta).min(i128::from(MAX_CWND))
}

#[cfg(feature = "trace")]
impl Cubic {
    /// The state of the controller, for trace validation.
    pub const fn trace_view(&self) -> super::trace::CcView {
        let (round_end, reference, round_min, samples) = self.round_exit.trace_view();
        let (probe_start, probe_bytes, rate) = self.probe.trace_view();
        super::trace::CcView {
            cwnd: self.cwnd,
            ssthresh: self.ssthresh,
            w_max: self.w_max,
            w_est: self.w_est,
            k_ms: self.k_ms,
            epoch: self.epoch,
            recovery: self.recovery,
            streak: self.streak,
            round_end,
            reference,
            round_min,
            samples,
            probe_start,
            probe_bytes,
            rate,
            slack: self.gate_slack_mid,
        }
    }
}
