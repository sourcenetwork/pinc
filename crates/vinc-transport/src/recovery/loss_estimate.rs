//! The node-wide loss estimate and the tail-repair decision.
//!
//! The estimate is an exponentially weighted average in units of 1/65536 with gain 1/32, stepped once per packet: an
//! acknowledged packet does `v -= v >> 5`, a lost one does `v += (65536 - v) >> 5`. It is kept in one atomic so every
//! connection of an endpoint shares it by reference without a lock. Only packets that need an acknowledgement count,
//! and repair packets and path MTU probes are left out (the caller passes only the packets that count).
//!
//! Invariant: the value is always in `0..=65536`. Both steps have a fixed point (below 32 for the decay, above 65504
//! for the growth), so a batch of any size costs at most a few hundred steps.

use core::sync::atomic::{AtomicU32, Ordering};

use super::SECOND;

/// The scale of the estimate: 65536 means every packet was lost.
pub const SCALE: u32 = 65_536;
/// Tail repair needs an estimate of at least this (328/65536, about 0.5 %).
pub const REPAIR_THRESHOLD: u32 = 328;
/// A connection must be at least this old (2 s) before it repairs its tail.
pub const REPAIR_MIN_AGE: u64 = 2 * SECOND;
/// The averaging gain is 1/2^`GAIN_SHIFT` (1/32).
const GAIN_SHIFT: u32 = 5;

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

    /// Fold in a batch: `acked` acknowledged packets, then `lost` lost ones, each as its own step.
    pub fn record(&self, lost: u32, acked: u32) {
        if lost == 0 && acked == 0 {
            return;
        }
        // The closure always returns `Some`, so the update cannot fail; ignoring the result is safe.
        let _ = self.value.try_update(Ordering::Relaxed, Ordering::Relaxed, |old| {
            let mut v = old;
            for _ in 0..acked {
                let next = v - (v >> GAIN_SHIFT);
                if next == v {
                    break;
                }
                v = next;
            }
            for _ in 0..lost {
                let next = v + ((SCALE - v) >> GAIN_SHIFT);
                if next == v {
                    break;
                }
                v = next;
            }
            Some(v)
        });
    }

    /// Whether to repair the tail: the connection is at least 2 s old, its send queue just drained, the path is a
    /// direct one and the estimate is at least 328/65536.
    pub fn should_send_repair(&self, conn_age: u64, queue_drained: bool, on_direct_path: bool) -> bool {
        queue_drained && on_direct_path && conn_age >= REPAIR_MIN_AGE && self.get() >= REPAIR_THRESHOLD
    }
}
