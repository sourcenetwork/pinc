//! Round-trip estimation: the smoothed round trip, its variation and its minimum.
//!
//! Every sample is used as measured: acknowledgements carry no delay field, because the receiver's delay is bounded by
//! a fixed policy ([`max_ack_delay`]) that the sender already allows for in its probe timeout.
//!
//! Invariants: `smoothed`, `rttvar` and `latest` are nanoseconds; the minimum is the smallest sample ever measured. The
//! first sample sets `smoothed = sample` and `rttvar = sample / 2`; later ones set `rttvar = (3 rttvar + |smoothed -
//! sample|) / 4` and `smoothed = (7 smoothed + sample) / 8`. The handshake round trip ([`RttEstimator::seed`]) sets
//! only the smoothed value and the variation, so the first measured sample is smoothed into it, and the latest and
//! minimum stay unknown until a sample is measured. All updates use `u128` intermediates and saturate, so no input
//! can overflow.

use super::math::sat;
use super::{LONG_RTT, MS, is_long_rtt};

/// The round trip assumed before the first sample (333 ms).
pub const INITIAL_RTT: u64 = 333 * MS;
const BASE_MAX_ACK_DELAY: u64 = 25 * MS;
const LONG_RTT_MAX_ACK_DELAY: u64 = 250 * MS;
/// On a long-RTT path the receiver holds an acknowledgement for `min_rtt / ACK_DELAY_DIVISOR` (8).
const ACK_DELAY_DIVISOR: u64 = 8;

/// The longest the receiver holds an acknowledgement: 25 ms, or on a long-RTT path (minimum round trip of 250 ms or
/// more) `min(250 ms, max(25 ms, min_rtt / 8))`.
///
/// The receiver delays by this much and the sender allows for 25 ms in its probe timeout: a fixed
/// policy, never reported on the wire.
pub fn max_ack_delay(min_rtt: Option<u64>) -> u64 {
    match min_rtt {
        Some(m) if m >= LONG_RTT => (m / ACK_DELAY_DIVISOR).clamp(BASE_MAX_ACK_DELAY, LONG_RTT_MAX_ACK_DELAY),
        _ => BASE_MAX_ACK_DELAY,
    }
}

/// The smoothed round trip, its variation and its minimum.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RttEstimator {
    latest: u64,
    smoothed: u64,
    rttvar: u64,
    min: u64,
    /// The smoothed value is known: seeded or measured.
    has_sample: bool,
    /// A sample was measured, so `latest` and `min` are known.
    measured: bool,
}

impl Default for RttEstimator {
    fn default() -> Self {
        Self::new()
    }
}

impl RttEstimator {
    /// An estimator with no sample, reporting [`INITIAL_RTT`].
    pub const fn new() -> Self {
        Self {
            latest: 0,
            smoothed: INITIAL_RTT,
            rttvar: INITIAL_RTT / 2,
            min: u64::MAX,
            has_sample: false,
            measured: false,
        }
    }

    /// Seed the smoothed value with the handshake round trip, at least 1 ms, and the variation with half of it. The
    /// latest and minimum stay unknown, and the first measured sample is smoothed into the seed. Does nothing once
    /// the smoothed value is known.
    pub fn seed(&mut self, rtt: u64) {
        if !self.has_sample {
            self.has_sample = true;
            self.smoothed = rtt.max(MS);
            self.rttvar = self.smoothed / 2;
        }
    }

    /// Fold in one sample, used as measured.
    pub fn update(&mut self, sample: u64) {
        self.latest = sample;
        self.min = self.min.min(sample);
        self.measured = true;
        if !self.has_sample {
            self.has_sample = true;
            self.smoothed = sample;
            self.rttvar = sample / 2;
            return;
        }
        let diff = u128::from(self.smoothed.abs_diff(sample));
        self.rttvar = sat((3 * u128::from(self.rttvar) + diff) / 4);
        self.smoothed = sat((7 * u128::from(self.smoothed) + u128::from(sample)) / 8);
    }

    /// The latest measured sample, or `None` before the first.
    pub const fn latest(&self) -> Option<u64> {
        if self.measured { Some(self.latest) } else { None }
    }

    /// The smoothed round trip; [`INITIAL_RTT`] before the first sample.
    pub const fn smoothed(&self) -> u64 {
        self.smoothed
    }

    /// The round-trip variation.
    pub const fn rttvar(&self) -> u64 {
        self.rttvar
    }

    /// The smallest measured sample, or `None` before the first.
    pub const fn min_rtt(&self) -> Option<u64> {
        if self.measured { Some(self.min) } else { None }
    }

    /// Whether the smoothed value is known: a sample was measured or the handshake round trip seeded it.
    pub const fn has_sample(&self) -> bool {
        self.has_sample
    }

    /// Whether the minimum marks a long-RTT path.
    pub fn is_long_rtt(&self) -> bool {
        is_long_rtt(self.min_rtt())
    }
}
