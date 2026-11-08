//! `HyStart++` slow-start exit detection (RFC 9406), with rounds measured by packet number.
//!
//! A round ends when a packet sent after the round began is acknowledged. The detector leaves slow start when the
//! minimum round trip of the current round, over at least 8 samples, exceeds the previous round's minimum by more than
//! max(4 ms, min(previous / 8, 16 ms)) while the window is at least 19.2 KB.

use super::MS;

/// Round-trip samples needed in a round before it may trigger an exit.
pub(crate) const MIN_SAMPLES: u32 = 8;
/// The window must be at least this many bytes before an exit.
pub(crate) const MIN_CWND: u64 = 19_200;
const MIN_THRESH: u64 = 4 * MS;
const MAX_THRESH: u64 = 16 * MS;

/// Per-round minimum round-trip tracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct HyStart {
    round_end: Option<u64>,
    current_min: u64,
    previous_min: u64,
    samples: u32,
}

impl HyStart {
    pub(crate) const fn new() -> Self {
        Self {
            round_end: None,
            current_min: u64::MAX,
            previous_min: u64::MAX,
            samples: 0,
        }
    }

    /// Feed one acknowledgement; returns true when slow start should end.
    pub(crate) fn on_ack(&mut self, largest_acked: u64, largest_sent: u64, rtt: Option<u64>, cwnd: u64) -> bool {
        if self.round_end.is_none_or(|end| largest_acked >= end) {
            if self.samples > 0 {
                self.previous_min = self.current_min;
            }
            self.current_min = u64::MAX;
            self.samples = 0;
            self.round_end = Some(largest_sent);
        }
        if let Some(rtt) = rtt {
            self.current_min = self.current_min.min(rtt);
            self.samples = self.samples.saturating_add(1);
        }
        if self.samples < MIN_SAMPLES || self.previous_min == u64::MAX || cwnd < MIN_CWND {
            return false;
        }
        let thresh = (self.previous_min / 8).clamp(MIN_THRESH, MAX_THRESH);
        self.current_min > self.previous_min.saturating_add(thresh)
    }
}
