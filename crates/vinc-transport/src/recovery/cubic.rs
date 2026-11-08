//! CUBIC congestion control (RFC 9438) in integer arithmetic, with `HyStart++` slow-start exit, a loss filter, a
//! low-latency cap and a long-RTT cap.
//!
//! Window growth in congestion avoidance follows `W(t) = W_max + C (t - K)^3` with `C = 0.4`, where `K` comes from
//! an integer cube root, floored by a Reno-friendly estimate that grows at 53/100 of a segment per window. Reductions
//! multiply by 0.7 (0.85 below 48 KB), or by 0.9 when the loss shows no queueing delay (at most 4 in a row).
//!
//! Invariants: `MIN_CWND <= cwnd <= MAX_CWND` after every call; `ssthresh >= MIN_CWND`. Overflow bounds, all in
//! `u128` unless noted: windows are at most `MAX_CWND` (2^40) and the segment size is clamped to `[1200, 65535]`.
//! - `K` in milliseconds is `icbrt(d * 2.5e9 / mss)` with `d <= 2^40`: the radicand is below 2^72, the root below 2^24.
//! - The cubic term is `dt^3 * 4 * mss / 1e10` with `|dt|` clamped to 2^30 ms: the product is below 2^(90+18) = 2^108.
//! - A growth step accumulates `(target - cwnd) * acked` with both factors below 2^64 (product below 2^128) and
//!   divides by `cwnd >= 2400`; the remainder is kept so no growth is lost to rounding.
//! - A reduction multiplies a window below 2^40 by at most 100: below 2^47, inside `u64`.

use super::MS;
use super::delivery::DeliveryRate;
use super::hystart::HyStart;
use super::math::{icbrt, sat};

/// The initial congestion window in bytes.
pub const INITIAL_CWND: u64 = 44_000;
/// The smallest congestion window in bytes.
pub const MIN_CWND: u64 = 2_400;
/// The largest congestion window in bytes (1 TiB); the bound that makes every product below fit.
pub const MAX_CWND: u64 = 1 << 40;
/// A window under this many bytes is cut by [`CONGESTION_BETA_SMALL`] (0.85) instead of 0.7.
pub const CONGESTION_BETA_SMALL: u64 = 48_000;
/// The smallest segment size the controller accepts.
pub const MIN_MSS: u64 = 1_200;
/// The largest segment size the controller accepts (the largest UDP payload).
pub const MAX_MSS: u64 = 65_535;

const BETA_NUM: u64 = 7;
const BETA_DEN: u64 = 10;
const BETA_SMALL_NUM: u64 = 85;
const BETA_SMALL_DEN: u64 = 100;
const FILTER_NUM: u64 = 9;
const FILTER_DEN: u64 = 10;
const FILTER_MAX_STREAK: u8 = 4;
const RENO_NUM: u128 = 53;
const RENO_DEN: u128 = 100;
const DC_RTT: u64 = 2 * MS;
const DC_SLACK: u64 = 256 * 1024;
const MAX_DT_MS: u64 = 1 << 30;
/// Growth in one step is at most half the window (target is capped at 1.5 x cwnd).
const TARGET_NUM: u64 = 3;
const TARGET_DEN: u64 = 2;

/// What one acknowledgement tells the controller.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct AckInput {
    /// The current time.
    pub now: u64,
    /// Bytes acknowledged that may grow the window (packets sent after the current recovery began).
    pub growth_bytes: u64,
    /// All bytes newly acknowledged, for the delivery-rate estimate.
    pub acked_bytes: u64,
    /// The largest newly acknowledged packet number.
    pub largest_acked: u64,
    /// The largest packet number sent so far.
    pub largest_sent: u64,
    /// The newest round-trip sample from this acknowledgement, if it produced one.
    pub rtt_sample: Option<u64>,
    /// The minimum round trip, if known.
    pub min_rtt: Option<u64>,
}

/// The window state that a spurious-loss undo restores.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Window {
    cwnd: u64,
    ssthresh: u64,
    w_max: u64,
    w_est: u64,
    epoch_start: Option<u64>,
    k_ms: u64,
    growth_rem: u128,
    reno_rem: u128,
    recovery_start: Option<u64>,
    filter_streak: u8,
}

impl Window {
    const fn initial() -> Self {
        Self {
            cwnd: INITIAL_CWND,
            ssthresh: u64::MAX,
            w_max: 0,
            w_est: INITIAL_CWND,
            epoch_start: None,
            k_ms: 0,
            growth_rem: 0,
            reno_rem: 0,
            recovery_start: None,
            filter_streak: 0,
        }
    }
}

/// The congestion controller of one path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cubic {
    w: Window,
    mss: u64,
    hystart: HyStart,
    delivery: DeliveryRate,
    snapshot: Option<Window>,
}

impl Cubic {
    /// A controller in slow start with the initial window and segment size `mss` (clamped to 1200..=65535).
    pub fn new(mss: u64) -> Self {
        Self {
            w: Window::initial(),
            mss: mss.clamp(MIN_MSS, MAX_MSS),
            hystart: HyStart::new(),
            delivery: DeliveryRate::new(),
            snapshot: None,
        }
    }

    /// The congestion window in bytes.
    pub const fn cwnd(&self) -> u64 {
        self.w.cwnd
    }

    /// The slow-start threshold in bytes (`u64::MAX` before the first exit from slow start).
    pub const fn ssthresh(&self) -> u64 {
        self.w.ssthresh
    }

    /// The segment size in bytes.
    pub const fn mss(&self) -> u64 {
        self.mss
    }

    /// Whether the controller is in slow start.
    pub const fn in_slow_start(&self) -> bool {
        self.w.cwnd < self.w.ssthresh
    }

    /// When the current recovery began, if one is on.
    pub const fn recovery_start(&self) -> Option<u64> {
        self.w.recovery_start
    }

    /// The delivery rate estimate in bytes per second, once sampled.
    pub fn delivery_rate(&self) -> Option<u64> {
        self.delivery.rate()
    }

    /// Change the segment size (clamped to 1200..=65535), for example after a path MTU change.
    pub fn set_mss(&mut self, mss: u64) {
        self.mss = mss.clamp(MIN_MSS, MAX_MSS);
    }

    /// Start over on a new path: initial window, slow start, no history. The segment size is kept.
    pub fn restart(&mut self) {
        *self = Self::new(self.mss);
    }

    /// Whether a congestion response was saved and can still be undone.
    pub const fn can_undo(&self) -> bool {
        self.snapshot.is_some()
    }

    /// Undo the last congestion response (every loss of its episode turned out spurious). The window never ends up
    /// smaller than it is now. Returns whether anything was restored.
    pub fn undo(&mut self) -> bool {
        let Some(saved) = self.snapshot.take() else {
            return false;
        };
        let cwnd = self.w.cwnd.max(saved.cwnd);
        self.w = saved;
        self.w.cwnd = cwnd;
        true
    }

    /// React to a loss of a packet sent at `sent_time`. Returns whether the window was reduced: a loss of a packet
    /// sent before the current recovery began is part of that recovery and changes nothing.
    pub fn on_congestion_event(&mut self, now: u64, sent_time: u64, srtt: u64, min_rtt: Option<u64>) -> bool {
        if self.w.recovery_start.is_some_and(|start| sent_time <= start) {
            return false;
        }
        self.snapshot = Some(self.w);
        let no_queue = min_rtt.is_some_and(|m| srtt <= m.saturating_add(m / 8));
        let filtered = no_queue && self.w.filter_streak < FILTER_MAX_STREAK;
        let (num, den) = if filtered {
            (FILTER_NUM, FILTER_DEN)
        } else if self.w.cwnd < CONGESTION_BETA_SMALL {
            (BETA_SMALL_NUM, BETA_SMALL_DEN)
        } else {
            (BETA_NUM, BETA_DEN)
        };
        self.w.filter_streak = if filtered { self.w.filter_streak + 1 } else { 0 };
        self.w.w_max = self.w.cwnd;
        self.w.cwnd = (self.w.cwnd * num / den).max(MIN_CWND);
        self.w.ssthresh = self.w.cwnd;
        self.w.w_est = self.w.cwnd;
        self.w.epoch_start = None;
        self.w.growth_rem = 0;
        self.w.reno_rem = 0;
        self.w.recovery_start = Some(now);
        true
    }

    /// Account for newly acknowledged data: grow the window, watch for the end of slow start and apply the caps.
    pub fn on_acked(&mut self, ack: &AckInput) {
        if let Some(min_rtt) = ack.min_rtt {
            self.delivery.on_acked(ack.now, ack.acked_bytes, min_rtt);
        }
        if self.in_slow_start()
            && self
                .hystart
                .on_ack(ack.largest_acked, ack.largest_sent, ack.rtt_sample, self.w.cwnd)
        {
            self.w.ssthresh = self.w.cwnd;
            self.w.w_max = self.w.cwnd;
        }
        if ack.growth_bytes > 0 {
            if self.in_slow_start() {
                self.w.cwnd = self.w.cwnd.saturating_add(ack.growth_bytes).min(MAX_CWND);
            } else {
                self.grow_cubic(ack);
            }
        }
        self.apply_caps(ack.min_rtt);
    }

    fn grow_cubic(&mut self, ack: &AckInput) {
        let mss = self.mss;
        let w = &mut self.w;
        let epoch = if let Some(epoch) = w.epoch_start {
            epoch
        } else {
            // First step of an epoch: place K from the gap to the previous maximum.
            w.epoch_start = Some(ack.now);
            if w.w_max > w.cwnd {
                let d = u128::from(w.w_max - w.cwnd);
                w.k_ms = icbrt(d * 2_500_000_000 / u128::from(mss));
            } else {
                w.k_ms = 0;
                w.w_max = w.cwnd;
            }
            w.w_est = w.cwnd;
            ack.now
        };
        let cwnd128 = u128::from(w.cwnd);
        // Reno-friendly estimate: 53/100 segment per window acknowledged.
        let reno = u128::from(mss) * RENO_NUM * u128::from(ack.growth_bytes) + w.reno_rem;
        w.w_est = w.w_est.saturating_add(sat(reno / (RENO_DEN * cwnd128)));
        w.reno_rem = reno % (RENO_DEN * cwnd128);
        let elapsed = ack.now.saturating_sub(epoch);
        let cubic = cubic_target(w.w_max, w.k_ms, mss, elapsed, ack.min_rtt.unwrap_or(0));
        let target = cubic.max(w.w_est).min(w.cwnd.saturating_mul(TARGET_NUM) / TARGET_DEN);
        if target > w.cwnd {
            let num = u128::from(target - w.cwnd) * u128::from(ack.growth_bytes) + w.growth_rem;
            w.cwnd = w.cwnd.saturating_add(sat(num / cwnd128)).min(MAX_CWND);
            w.growth_rem = num % cwnd128;
        }
    }

    /// Cap the window at 2 x BDP + 256 KiB on low-latency paths and at 2 x BDP on long-RTT paths.
    fn apply_caps(&mut self, min_rtt: Option<u64>) {
        let Some(min_rtt) = min_rtt else { return };
        let Some(bdp) = self.delivery.bdp(min_rtt) else { return };
        let cap = if min_rtt < DC_RTT {
            bdp.saturating_mul(2).saturating_add(DC_SLACK)
        } else if min_rtt >= super::LONG_RTT {
            bdp.saturating_mul(2)
        } else {
            return;
        };
        self.w.cwnd = self.w.cwnd.min(cap.max(MIN_CWND));
    }
}

/// The cubic window `elapsed_ns` after the epoch began, looking one `rtt` ahead.
fn cubic_target(w_max: u64, k_ms: u64, mss: u64, elapsed_ns: u64, rtt: u64) -> u64 {
    let t_ms = (elapsed_ns / MS).saturating_add(rtt / MS).min(MAX_DT_MS);
    let dt = i128::from(t_ms) - i128::from(k_ms.min(MAX_DT_MS));
    let cube = dt.unsigned_abs().pow(3);
    let delta = sat(cube * 4 * u128::from(mss) / 10_000_000_000);
    if dt >= 0 {
        w_max.saturating_add(delta).min(MAX_CWND)
    } else {
        w_max.saturating_sub(delta)
    }
}
