//! The pacer: a burst of ten datagrams' worth of bytes goes out, then the sender waits as long as those bytes take at
//! 1.25 x cwnd per smoothed round trip, unless its window does not limit it and the burst already took that long.
//!
//! Pacing starts only once a round-trip sample exists (the owner calls [`Pacer::on_sent`] only then). Each packet is
//! charged its own size. A burst's budget is ten of the path's datagrams ([`burst_budget`], the datagram size clamped
//! to `1..=65535`); the packet that brings the bytes charged to the budget or past it ends the burst and sets the
//! release a span after it: `spent` bytes, every byte of the burst with that packet's whole size, at
//! `gap = mtu * srtt * 4 / (5 * max(cwnd, 1))` a datagram, so a gap for each whole datagram and the remainder by its
//! bytes. One case is different: a sender its window does not limit (less than half of it in
//! flight) whose burst took at least `span` from its first packet to its last has sent more slowly than the paced rate
//! and waited already; it is released one tick of the clock after its last packet. A sender the window limits, and any
//! burst that left faster than the paced rate, waits the span.
//!
//! The reference model's pacer counts packets instead: each costs one of ten tokens whatever it weighs, and only a
//! packet larger than the path's datagram size costs as many as the datagrams it is worth. Full-size packets end a
//! burst at the same packet under both rules and wait the same ten gaps; a smaller packet is no longer charged a whole
//! datagram, so a sender of small packets leaves at the documented rate instead of below it.
//!
//! The tick keeps one thing as it was: after a burst the sender gives the driver a turn before it sends more.
//! Acknowledgements never wait for the pacer: only data consults [`Pacer::next_release`].
//!
//! Invariants: `spent < burst_budget(mtu)` for the datagram size of the last call; `next` only moves forward.
//! Overflow bound: `spent` stays below `10 * 65535 + 2^32`; each product of the span has a factor below `2^33`, `srtt`
//! below `2^64` and 4, so stays below `2^99` in `u128`, and the span saturates in `u64`.

use super::cubic::MAX_MSS;
use super::math::sat;

/// The path datagrams a burst may carry back to back before the sender pauses.
pub const BURST_PACKETS: u32 = 10;

/// The path's datagram size as the pacer charges it, clamped to `1..=65535`.
const fn datagram(mtu: u64) -> u64 {
    if mtu > MAX_MSS {
        MAX_MSS
    } else if mtu == 0 {
        1
    } else {
        mtu
    }
}

/// The bytes a burst may carry back to back on a path with datagram size `mtu`.
pub const fn burst_budget(mtu: u64) -> u64 {
    datagram(mtu) * BURST_PACKETS as u64
}

/// The pause after a burst of `spent` bytes: a gap of `mtu * srtt * 4 / (5 * cwnd)` for each whole datagram, as the
/// packet count charged a full-size packet, and the remainder at the same rate by its bytes.
fn span(spent: u64, mtu: u64, srtt: u64, cwnd: u64) -> u64 {
    let m = datagram(mtu);
    let per = |bytes: u64| sat(u128::from(bytes) * u128::from(srtt) * 4 / (5 * u128::from(cwnd.max(1))));
    per(m).saturating_mul(spent / m).saturating_add(per(spent % m))
}

/// Spaces packet departures so a window is spread over a round trip.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pacer {
    /// Bytes charged to the burst being counted.
    spent: u64,
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
            spent: 0,
            next: 0,
            start: 0,
        }
    }

    /// The earliest time at or after `now` when data may leave; `now` when it may leave at once.
    pub const fn next_release(&self, now: u64) -> u64 {
        if self.next > now { self.next } else { now }
    }

    /// Record one packet of `size` bytes sent at `now` on a path with datagram size `mtu`, with the connection's
    /// smoothed round trip and window; `limited` says whether the window limits the sender now.
    pub fn on_sent(&mut self, now: u64, size: u32, mtu: u64, srtt: u64, cwnd: u64, limited: bool) {
        if self.spent == 0 {
            self.start = now;
        }
        self.spent += u64::from(size.max(1));
        if self.spent < burst_budget(mtu) {
            return;
        }
        let span = span(self.spent, mtu, srtt, cwnd);
        let slow = !limited && now.saturating_sub(self.start) >= span;
        let release = now.saturating_add(if slow { 1 } else { span });
        self.next = self.next.max(release);
        self.spent = 0;
    }
}

#[cfg(feature = "trace")]
impl Pacer {
    /// The bytes charged to the burst being counted, the next release and the start of that burst, for trace
    /// validation.
    pub const fn trace_view(&self) -> (u64, u64, u64) {
        (self.spent, self.next, self.start)
    }
}
