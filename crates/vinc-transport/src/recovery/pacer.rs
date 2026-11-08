//! The pacer: ten packets go out, then the sender waits ten packet-times at 1.25 x cwnd per smoothed round trip.
//!
//! Pacing starts only once a round-trip sample exists (the owner calls [`Pacer::on_sent`] only then). After each
//! packet the token count drops by one; when it reaches zero the next release is `now + 10 * gap`, with
//! `gap = mtu * srtt * 4 / (5 * max(cwnd, 1))`, and the tokens refill to ten. Acknowledgements never wait for the
//! pacer: only data consults [`Pacer::next_release`].
//!
//! Invariants: `1 <= tokens <= 10`; `next` only moves forward in time of use. Overflow bound: the gap is computed in
//! `u128` from factors below 2^16 (the datagram size, clamped to 65535), 2^64 (srtt) and 4, so below 2^82, and
//! saturates in `u64`.

use super::cubic::MAX_MSS;
use super::math::sat;

/// The packets sent back to back before the sender pauses.
pub const BURST_PACKETS: u32 = 10;

/// Spaces packet departures so a window is spread over a round trip.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pacer {
    tokens: u32,
    next: u64,
}

impl Default for Pacer {
    fn default() -> Self {
        Self::new()
    }
}

impl Pacer {
    /// A pacer with a full burst and no pause.
    pub const fn new() -> Self {
        Self {
            tokens: BURST_PACKETS,
            next: 0,
        }
    }

    /// The earliest time at or after `now` when data may leave; `now` when it may leave at once.
    pub const fn next_release(&self, now: u64) -> u64 {
        if self.next > now { self.next } else { now }
    }

    /// Record one packet sent at `now` on a path with datagram size `mtu`, with the connection's smoothed round trip
    /// and window.
    pub fn on_sent(&mut self, now: u64, mtu: u64, srtt: u64, cwnd: u64) {
        if self.tokens > 1 {
            self.tokens -= 1;
            return;
        }
        let gap = sat(u128::from(mtu.min(MAX_MSS)) * u128::from(srtt) * 4 / (5 * u128::from(cwnd.max(1))));
        self.next = now.saturating_add(gap.saturating_mul(u64::from(BURST_PACKETS)));
        self.tokens = BURST_PACKETS;
    }
}
