//! Delivery-rate estimation: bytes acknowledged over a sampling interval, keeping the best of the last 8 samples.
//!
//! The rate is in bytes per second. Overflow bounds: a sample is `bytes * 1e9 / elapsed` in `u128` (bytes < 2^64 and
//! 1e9 < 2^30 give < 2^94) and saturates at `u64`; the bandwidth-delay product is `rate * min_rtt / 1e9` in `u128`
//! (< 2^128) and is clamped to [`MAX_CWND`].

use super::math::sat;
use super::{MAX_CWND, MS, SECOND};

const SAMPLES: usize = 8;

/// Sliding best-of-8 delivery rate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct DeliveryRate {
    start: Option<u64>,
    bytes: u64,
    samples: [u64; SAMPLES],
    next: usize,
    filled: usize,
}

impl DeliveryRate {
    pub(crate) const fn new() -> Self {
        Self {
            start: None,
            bytes: 0,
            samples: [0; SAMPLES],
            next: 0,
            filled: 0,
        }
    }

    /// Count `bytes` acknowledged at `now`; a sample is taken once a `min_rtt` (at least 1 ms) has elapsed.
    pub(crate) fn on_acked(&mut self, now: u64, bytes: u64, min_rtt: u64) {
        let Some(start) = self.start else {
            self.start = Some(now);
            return;
        };
        self.bytes = self.bytes.saturating_add(bytes);
        let elapsed = now.saturating_sub(start);
        if elapsed < min_rtt.max(MS) {
            return;
        }
        let rate = sat(u128::from(self.bytes) * u128::from(SECOND) / u128::from(elapsed));
        if let Some(slot) = self.samples.get_mut(self.next) {
            *slot = rate;
        }
        self.next = (self.next + 1) % SAMPLES;
        self.filled = (self.filled + 1).min(SAMPLES);
        self.start = Some(now);
        self.bytes = 0;
    }

    /// The best rate of the last samples in bytes per second, or `None` before the first sample.
    pub(crate) fn rate(&self) -> Option<u64> {
        if self.filled == 0 {
            return None;
        }
        self.samples.iter().copied().max()
    }

    /// The bandwidth-delay product in bytes for `min_rtt`, or `None` before the first rate sample.
    pub(crate) fn bdp(&self, min_rtt: u64) -> Option<u64> {
        let rate = self.rate()?;
        let bdp = u128::from(rate) * u128::from(min_rtt) / u128::from(SECOND);
        Some(sat(bdp).min(MAX_CWND))
    }
}
