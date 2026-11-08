//! The delivery-rate probe: acknowledged bytes per minimum-round-trip interval, kept as a maximum that decays.
//!
//! Each acknowledgement adds its bytes. Once an interval of at least the minimum round trip has passed, the interval
//! yields one rate sample `bytes * 1e9 / elapsed` (bytes per second), and the estimate becomes
//! `max(sample, estimate - estimate / 8)`: it jumps to a higher sample at once and falls by 1/8 per interval when the
//! sender delivers less. The first acknowledgement only opens the first interval, and its bytes count in it.
//!
//! Overflow bounds: `bytes` saturates in `u64`; the sample product is below 2^64 * 2^30 = 2^94 in `u128` and saturates
//! at `u64::MAX`.

use super::SECOND;
use super::math::sat;

/// The decaying-maximum delivery-rate estimate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RateProbe {
    start: Option<u64>,
    bytes: u64,
    rate: u64,
}

impl RateProbe {
    pub(crate) const fn new() -> Self {
        Self {
            start: None,
            bytes: 0,
            rate: 0,
        }
    }

    /// Count `bytes` acknowledged at `now`; an interval ends once `min_rtt` (nonzero) has elapsed since it began.
    pub(crate) fn on_acked(&mut self, now: u64, bytes: u64, min_rtt: u64) {
        let start = *self.start.get_or_insert(now);
        self.bytes = self.bytes.saturating_add(bytes);
        let elapsed = now.saturating_sub(start);
        if elapsed == 0 || elapsed < min_rtt {
            return;
        }
        let sample = sat(u128::from(self.bytes) * u128::from(SECOND) / u128::from(elapsed));
        self.rate = sample.max(self.rate - (self.rate >> 3));
        self.start = Some(now);
        self.bytes = 0;
    }

    /// The estimate in bytes per second; 0 before the first sample.
    pub(crate) const fn rate(&self) -> u64 {
        self.rate
    }
}
