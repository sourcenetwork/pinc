//! The pacer: a token bucket refilling at 1.25 x cwnd / srtt with bursts of 10 packets, on nanosecond time.
//!
//! Invariants: `tokens <= burst`; `last` never moves past the time of the latest refill. Overflow bounds: cwnd is
//! clamped to [`MAX_CWND`] (2^40) and srtt to 2^40 ns, so `5 * cwnd < 2^43` and `4 * srtt < 2^42`; an elapsed time or
//! token count below 2^64 times either stays below 2^107 inside `u128`.

use super::MAX_CWND;
use super::math::{mul_div, mul_div_ceil};

/// The token bucket holds this many packets.
pub const BURST_PACKETS: u64 = 10;
const MAX_SRTT: u64 = 1 << 40;
/// The pacing rate is `RATE_NUM / RATE_DEN` (5/4) of cwnd per srtt.
const RATE_NUM: u64 = 5;
const RATE_DEN: u64 = 4;

/// Spaces packet departures so a window is spread over a round trip instead of sent as one burst.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pacer {
    tokens: u64,
    last: u64,
    cwnd: u64,
    srtt: u64,
    mss: u64,
}

impl Pacer {
    /// A pacer with a full bucket and no rate yet (everything may leave at once until [`Self::set_rate`]).
    pub const fn new(mss: u64) -> Self {
        Self {
            tokens: BURST_PACKETS.saturating_mul(mss),
            last: 0,
            cwnd: 0,
            srtt: 0,
            mss,
        }
    }

    /// Set the pacing inputs: the congestion window, the smoothed round trip and the packet size in bytes.
    pub fn set_rate(&mut self, cwnd: u64, srtt: u64, mss: u64) {
        self.cwnd = cwnd.min(MAX_CWND);
        self.srtt = srtt.clamp(1, MAX_SRTT);
        self.mss = mss;
        self.tokens = self.tokens.min(self.burst());
    }

    /// The bucket size in bytes: 10 packets.
    pub const fn burst(&self) -> u64 {
        BURST_PACKETS.saturating_mul(self.mss)
    }

    /// The pacing rate in bytes per second, or 0 while no rate is set.
    pub fn rate_bytes_per_sec(&self) -> u64 {
        if self.cwnd == 0 {
            return 0;
        }
        mul_div(RATE_NUM * self.cwnd, 1_000_000_000, RATE_DEN * self.srtt)
    }

    fn unlimited(&self) -> bool {
        self.cwnd == 0
    }

    /// Tokens and refill time as of `now`, without changing the pacer.
    fn refilled(&self, now: u64) -> (u64, u64) {
        if self.unlimited() {
            return (self.burst(), now);
        }
        let elapsed = now.saturating_sub(self.last);
        let add = mul_div(elapsed, RATE_NUM * self.cwnd, RATE_DEN * self.srtt);
        if add == 0 {
            return (self.tokens, self.last);
        }
        let total = self.tokens.saturating_add(add);
        if total >= self.burst() {
            return (self.burst(), now);
        }
        // Advance only by the time the added tokens took, so a fraction of a byte is not lost.
        let used = mul_div(add, RATE_DEN * self.srtt, RATE_NUM * self.cwnd).min(elapsed);
        (total, self.last.saturating_add(used))
    }

    /// The earliest time at or after `now` when one packet of the current size may leave; `now` when it may leave
    /// at once. Feed this to the connection's timeout.
    pub fn next_release(&self, now: u64) -> u64 {
        let (tokens, last) = self.refilled(now);
        if tokens >= self.mss {
            return now;
        }
        let wait = mul_div_ceil(self.mss - tokens, RATE_DEN * self.srtt, RATE_NUM * self.cwnd);
        last.saturating_add(wait).max(now)
    }

    /// Record a departure of `size` bytes at `now`.
    pub fn on_sent(&mut self, now: u64, size: u64) {
        let (tokens, last) = self.refilled(now);
        self.tokens = tokens.saturating_sub(size);
        self.last = last;
    }
}
