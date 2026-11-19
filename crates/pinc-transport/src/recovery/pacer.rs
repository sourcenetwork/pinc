//! The pacer: ten packets go out, then the sender waits ten packet-times at 1.25 x cwnd per smoothed round trip,
//! unless its window does not limit it and the ten already took that long.
//!
//! Pacing starts only once a round-trip sample exists (the owner calls [`Pacer::on_sent`] only then). After each
//! packet the token count drops by one; when it reaches zero the tokens refill to ten and the next release is set,
//! with a packet-time of `gap = mtu * srtt * 4 / (5 * max(cwnd, 1))`: `10 * gap` after the tenth packet. One case
//! is different: a sender its window does not limit (less than half of it in flight) whose ten packets took at
//! least `10 * gap` from the first to the tenth has sent more slowly than the paced rate and waited already; it is
//! released one tick of the clock after the tenth. A request and reply flow of one small packet a round trip is so
//! never held, where it used to pay ten packet-times (about a quarter of a round trip) at every tenth packet. A
//! sender the window limits, and any ten packets that left faster than the paced rate, wait as before.
//!
//! The tick keeps one thing as it was: after ten packets the sender gives the driver a turn before it sends more.
//! Acknowledgements never wait for the pacer: only data consults [`Pacer::next_release`].
//!
//! Invariants: `1 <= tokens <= 10`; `next` only moves forward. Overflow bound: the gap is computed in `u128` from
//! factors below 2^16 (the datagram size, clamped to 65535), 2^64 (srtt) and 4, so below 2^82, and saturates in
//! `u64`.

use super::cubic::MAX_MSS;
use super::math::sat;

/// The packets sent back to back before the sender pauses.
pub const BURST_PACKETS: u32 = 10;

/// Spaces packet departures so a window is spread over a round trip.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pacer {
    tokens: u32,
    next: u64,
    /// When the first packet of the burst being counted left.
    start: u64,
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
            start: 0,
        }
    }

    /// The earliest time at or after `now` when data may leave; `now` when it may leave at once.
    pub const fn next_release(&self, now: u64) -> u64 {
        if self.next > now { self.next } else { now }
    }

    /// Record one packet sent at `now` on a path with datagram size `mtu`, with the connection's smoothed round trip
    /// and window; `limited` says whether the window limits the sender now.
    pub fn on_sent(&mut self, now: u64, mtu: u64, srtt: u64, cwnd: u64, limited: bool) {
        if self.tokens == BURST_PACKETS {
            self.start = now;
        }
        if self.tokens > 1 {
            self.tokens -= 1;
            return;
        }
        let gap = sat(u128::from(mtu.min(MAX_MSS)) * u128::from(srtt) * 4 / (5 * u128::from(cwnd.max(1))));
        let span = gap.saturating_mul(u64::from(BURST_PACKETS));
        let slow = !limited && now.saturating_sub(self.start) >= span;
        let release = now.saturating_add(if slow { 1 } else { span });
        self.next = self.next.max(release);
        self.tokens = BURST_PACKETS;
    }
}

#[cfg(feature = "trace")]
impl Pacer {
    /// The tokens left, the next release and the start of the burst being counted, for trace validation.
    pub const fn trace_view(&self) -> (u32, u64, u64) {
        (self.tokens, self.next, self.start)
    }
}
