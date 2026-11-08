//! The node-wide loss estimate and the tail-repair decision.
//!
//! The estimate is an exponentially weighted average in units of 1/65536 with gain 1/32, kept in one atomic so every
//! connection of an endpoint shares it by reference without a lock. Invariant: the value is always in `0..=65536`.

use core::sync::atomic::{AtomicU32, Ordering};

use super::SECOND;

/// The scale of the estimate: 65536 means every packet was lost.
pub const SCALE: u32 = 65_536;
/// Tail repair needs an estimate above this (1%, 655/65536).
pub const REPAIR_THRESHOLD: u32 = 655;
/// A connection must be older than this (2 s) before it repairs its tail.
pub const REPAIR_MIN_AGE: u64 = 2 * SECOND;
/// The averaging gain is 1/`GAIN_DIVISOR`.
const GAIN_DIVISOR: u32 = 32;

/// The shared loss average of an endpoint.
#[derive(Debug, Default)]
pub struct LossEstimate {
    value: AtomicU32,
}

impl LossEstimate {
    /// An estimate of zero loss.
    pub const fn new() -> Self {
        Self {
            value: AtomicU32::new(0),
        }
    }

    /// The current estimate in units of 1/65536.
    pub fn get(&self) -> u32 {
        self.value.load(Ordering::Relaxed)
    }

    /// Fold in one batch: `lost` packets declared lost and `delivered` packets acknowledged. An empty batch is ignored.
    ///
    /// The sample is `lost * 65536 / (lost + delivered)`; the sum is at most 2^33 and the product 2^49, so `u64`
    /// cannot overflow.
    pub fn record(&self, lost: u32, delivered: u32) {
        let total = u64::from(lost) + u64::from(delivered);
        if total == 0 {
            return;
        }
        let sample = u64::from(lost) * u64::from(SCALE) / total;
        let sample = u32::try_from(sample).unwrap_or(SCALE);
        // The closure always returns `Some`, so the update cannot fail; ignoring the result is safe.
        let _ = self
            .value
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |old| Some(step(old, sample)));
    }

    /// Whether to send one repair packet re-carrying the tail of the last packet: the connection is older than 2 s,
    /// its send queue just drained, the path is UDP and the estimate is above 1%.
    pub fn should_send_repair(&self, conn_age: u64, queue_drained: bool, on_udp_path: bool) -> bool {
        queue_drained && on_udp_path && conn_age > REPAIR_MIN_AGE && self.get() > REPAIR_THRESHOLD
    }
}

/// One averaging step toward `sample`, rounding the move up so the average reaches the target.
fn step(old: u32, sample: u32) -> u32 {
    if sample >= old {
        old + (sample - old).div_ceil(GAIN_DIVISOR)
    } else {
        old - (old - sample).div_ceil(GAIN_DIVISOR)
    }
}
