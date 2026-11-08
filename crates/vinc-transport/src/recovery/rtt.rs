//! Round-trip estimation (RFC 9002 section 5) with acknowledgement-delay capping.
//!
//! Invariants: `smoothed`, `rttvar` and `latest` are nanoseconds; the minimum is the smallest sample ever seen since
//! the last reset. All updates use `u128` intermediates and saturate, so no input can overflow.

use super::math::sat;
use super::{LONG_RTT, MS, is_long_rtt};

/// The round trip assumed before the first sample (333 ms).
pub const INITIAL_RTT: u64 = 333 * MS;
const BASE_MAX_ACK_DELAY: u64 = 25 * MS;
const LONG_RTT_MAX_ACK_DELAY: u64 = 250 * MS;

/// The longest the peer may hold an acknowledgement: 25 ms, or on a long-RTT path min(250 ms, `min_rtt` / 8).
///
/// The receiver delays by this much and the sender caps the reported delay by it: both call this one function.
pub fn max_ack_delay(min_rtt: Option<u64>) -> u64 {
    match min_rtt {
        Some(m) if m >= LONG_RTT => (m / 8).min(LONG_RTT_MAX_ACK_DELAY),
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
    has_sample: bool,
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
        }
    }

    /// Fold in one sample: `latest` is the measured round trip, `ack_delay` what the peer reported holding the ack.
    pub fn update(&mut self, latest: u64, ack_delay: u64) {
        self.latest = latest;
        self.min = self.min.min(latest);
        if !self.has_sample {
            self.has_sample = true;
            self.smoothed = latest;
            self.rttvar = latest / 2;
            return;
        }
        let delay = ack_delay.min(max_ack_delay(self.min_rtt()));
        let adjusted = if latest >= self.min.saturating_add(delay) {
            latest - delay
        } else {
            latest
        };
        let diff = u128::from(self.smoothed.abs_diff(adjusted));
        self.rttvar = sat((3 * u128::from(self.rttvar) + diff) / 4);
        self.smoothed = sat((7 * u128::from(self.smoothed) + u128::from(adjusted)) / 8);
    }

    /// Forget every sample (a new path).
    pub fn reset(&mut self) {
        *self = Self::new();
    }

    /// The latest raw sample, or 0 before the first.
    pub const fn latest(&self) -> u64 {
        self.latest
    }

    /// The smoothed round trip; [`INITIAL_RTT`] before the first sample.
    pub const fn smoothed(&self) -> u64 {
        self.smoothed
    }

    /// The round-trip variation.
    pub const fn rttvar(&self) -> u64 {
        self.rttvar
    }

    /// The smallest sample, or `None` before the first.
    pub const fn min_rtt(&self) -> Option<u64> {
        if self.has_sample { Some(self.min) } else { None }
    }

    /// Whether at least one sample was taken.
    pub const fn has_sample(&self) -> bool {
        self.has_sample
    }

    /// Whether the minimum marks a long-RTT path.
    pub fn is_long_rtt(&self) -> bool {
        is_long_rtt(self.min_rtt())
    }
}
