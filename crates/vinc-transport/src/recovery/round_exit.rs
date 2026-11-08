//! Slow-start exit detection by the per-round minimum round trip.
//!
//! A round ends when the largest acknowledged packet number reaches the next packet number to be sent at the round's
//! start. At that boundary the finished round's minimum becomes the reference only if the round had at least 8
//! samples; otherwise the earlier reference is kept. Slow start ends when a round with at least 8 samples has a
//! minimum above `reference + max(4 ms, min(reference / 8, 16 ms))` while the window is at least 19,200 bytes.

use super::MS;

/// Round-trip samples needed in a round before it may trigger an exit or become the reference.
pub(crate) const MIN_SAMPLES: u32 = 8;
/// The window must be at least this many bytes (16 segments of 1200) before an exit.
pub(crate) const MIN_CWND: u64 = 19_200;
const MIN_THRESH: u64 = 4 * MS;
const MAX_THRESH: u64 = 16 * MS;

/// Per-round minimum round-trip tracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RoundExit {
    round_end: u64,
    reference: Option<u64>,
    round_min: Option<u64>,
    samples: u32,
}

impl RoundExit {
    pub(crate) const fn new() -> Self {
        Self {
            round_end: 0,
            reference: None,
            round_min: None,
            samples: 0,
        }
    }

    /// Forget the old path's rounds; the next round ends at `next_pn`.
    pub(crate) fn restart(&mut self, next_pn: u64) {
        *self = Self {
            round_end: next_pn,
            ..Self::new()
        };
    }

    /// Fold in one round-trip sample.
    pub(crate) fn on_sample(&mut self, rtt: u64) {
        self.round_min = Some(self.round_min.map_or(rtt, |m| m.min(rtt)));
        self.samples = self.samples.saturating_add(1);
    }

    /// Feed one acknowledgement in slow start; true when slow start should end.
    pub(crate) fn on_ack(&mut self, largest_acked: u64, next_pn: u64, cwnd: u64) -> bool {
        if largest_acked >= self.round_end {
            if self.samples >= MIN_SAMPLES {
                self.reference = self.round_min.or(self.reference);
            }
            self.round_min = None;
            self.samples = 0;
            self.round_end = next_pn;
        }
        let (Some(reference), Some(min)) = (self.reference, self.round_min) else {
            return false;
        };
        let thresh = (reference / 8).clamp(MIN_THRESH, MAX_THRESH);
        self.samples >= MIN_SAMPLES && cwnd >= MIN_CWND && min > reference.saturating_add(thresh)
    }
}
