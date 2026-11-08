//! Received-packet tracking of one packet space: a bounded range set, duplicate detection, the acknowledgement
//! decision and the ranges to report.
//!
//! Received packet numbers live in at most `RANGES` disjoint, sorted, merged `[start, end)` intervals. When a new
//! interval does not fit, the lowest one is forgotten and `floor` rises past it: everything below `floor` is treated
//! as already received, so a forgotten packet is dropped as a duplicate rather than processed twice.
//!
//! The acknowledgement policy:
//! - every 2nd ack-eliciting packet, every 3rd when the packet is bulk (at least 1000 stream bytes, number above 2),
//!   and on a long-RTT path at least every 4th;
//! - at once when the packet leaves a gap or fills one;
//! - otherwise after [`max_ack_delay`] (25 ms, or min(250 ms, `min_rtt` / 8) on a long-RTT path).
//!
//! Reported ranges are largest first, at most [`MAX_ACK_RANGES`], and exclude what the peer confirmed having seen our
//! acknowledgement of more than 2 s ago.

use core::ops::RangeInclusive;

use super::rtt::max_ack_delay;
use super::{MAX_PACKET_NUMBER, RecoveryError, SECOND, is_long_rtt};

/// The most ranges one acknowledgement reports.
pub const MAX_ACK_RANGES: usize = 32;
/// Stream bytes at which a packet counts as bulk.
const BULK_BYTES: u32 = 1000;
/// Packet numbers up to this are never bulk.
const BULK_MIN_PN: u64 = 2;
const EVERY_DEFAULT: u32 = 2;
const EVERY_BULK: u32 = 3;
const EVERY_LONG_RTT: u32 = 4;
/// How long a confirmed range stays reported after the peer confirmed it (2 s).
const CONFIRM_HOLD: u64 = 2 * SECOND;
const SENT_ACKS: usize = 8;

/// One received packet, as the policy needs to see it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RxPacket {
    /// The packet number.
    pub pn: u64,
    /// The receive time.
    pub now: u64,
    /// Whether the packet carries frames that need an acknowledgement.
    pub ack_eliciting: bool,
    /// Bytes of stream data the packet carried.
    pub stream_bytes: u32,
}

/// What recording a packet found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RxOutcome {
    /// A packet number not seen before: process the packet.
    New,
    /// Already received, or older than anything still tracked: drop the packet.
    Duplicate,
}

#[derive(Debug, Clone, Copy)]
struct AckSent {
    pn: u64,
    largest: u64,
    confirmed_at: Option<u64>,
}

/// Received packet numbers and acknowledgement state of one packet space, with room for `RANGES` ranges.
#[derive(Debug, Clone)]
pub struct ReceivedPackets<const RANGES: usize> {
    items: [(u64, u64); RANGES],
    len: usize,
    floor: u64,
    largest_time: u64,
    pending: u32,
    first_pending: u64,
    immediate_at: Option<u64>,
    min_rtt: Option<u64>,
    sent: [Option<AckSent>; SENT_ACKS],
    next_sent: usize,
    pruned: Option<u64>,
}

impl<const RANGES: usize> Default for ReceivedPackets<RANGES> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const RANGES: usize> ReceivedPackets<RANGES> {
    /// An empty tracker.
    pub const fn new() -> Self {
        const { assert!(RANGES >= 1) };
        Self {
            items: [(0, 0); RANGES],
            len: 0,
            floor: 0,
            largest_time: 0,
            pending: 0,
            first_pending: 0,
            immediate_at: None,
            min_rtt: None,
            sent: [None; SENT_ACKS],
            next_sent: 0,
            pruned: None,
        }
    }

    fn live(&self) -> &[(u64, u64)] {
        self.items.get(..self.len).unwrap_or(&[])
    }

    /// The path's minimum round trip, which selects the long-RTT acknowledgement policy.
    pub fn set_min_rtt(&mut self, min_rtt: Option<u64>) {
        self.min_rtt = min_rtt;
    }

    /// The largest packet number received.
    pub fn largest(&self) -> Option<u64> {
        self.live().last().map(|iv| iv.1 - 1)
    }

    /// Whether `pn` was received (or is too old to tell).
    pub fn contains(&self, pn: u64) -> bool {
        pn < self.floor || self.live().iter().any(|iv| iv.0 <= pn && pn < iv.1)
    }

    /// The number of tracked ranges.
    pub const fn range_count(&self) -> usize {
        self.len
    }

    /// Record a received packet and update the acknowledgement decision.
    ///
    /// # Errors
    /// [`RecoveryError::PacketNumberOutOfRange`] if the packet number exceeds 2^62 - 1.
    pub fn on_packet_received(&mut self, p: RxPacket) -> Result<RxOutcome, RecoveryError> {
        if p.pn > MAX_PACKET_NUMBER {
            return Err(RecoveryError::PacketNumberOutOfRange);
        }
        let prev_largest = self.largest();
        if !self.insert(p.pn) {
            return Ok(RxOutcome::Duplicate);
        }
        if prev_largest.is_none_or(|l| p.pn > l) {
            self.largest_time = p.now;
        }
        if p.ack_eliciting {
            let gap = prev_largest.is_some_and(|l| p.pn > l + 1 || p.pn < l);
            if self.pending == 0 {
                self.first_pending = p.now;
            }
            self.pending = self.pending.saturating_add(1);
            let bulk = p.stream_bytes >= BULK_BYTES && p.pn > BULK_MIN_PN;
            let mut every = if bulk { EVERY_BULK } else { EVERY_DEFAULT };
            if is_long_rtt(self.min_rtt) {
                every = every.max(EVERY_LONG_RTT);
            }
            if (gap || self.pending >= every) && self.immediate_at.is_none() {
                self.immediate_at = Some(p.now);
            }
        }
        Ok(RxOutcome::New)
    }

    /// Insert `pn`; false if it is a duplicate or too old to track.
    fn insert(&mut self, pn: u64) -> bool {
        if pn < self.floor {
            return false;
        }
        let at = self.live().partition_point(|iv| iv.1 < pn);
        let Some(&(start, end)) = self.items.get(at).filter(|_| at < self.len) else {
            return self.push_new(at, pn);
        };
        if start <= pn && pn < end {
            return false;
        }
        if end == pn {
            // Extends the interval upward; it may now touch the next one.
            let next = self.items.get(at + 1).copied().filter(|_| at + 1 < self.len);
            if let Some((_, next_end)) = next.filter(|n| n.0 == pn + 1) {
                self.replace(at, (start, next_end));
                self.remove(at + 1);
            } else {
                self.replace(at, (start, pn + 1));
            }
            return true;
        }
        if start == pn + 1 {
            self.replace(at, (pn, end));
            return true;
        }
        self.push_new(at, pn)
    }

    fn replace(&mut self, at: usize, iv: (u64, u64)) {
        if let Some(slot) = self.items.get_mut(at) {
            *slot = iv;
        }
    }

    fn remove(&mut self, at: usize) {
        if at < self.len {
            self.items.copy_within(at + 1..self.len, at);
            self.len -= 1;
        }
    }

    /// Insert a fresh single-packet interval at sorted position `at`, forgetting the lowest interval when full.
    fn push_new(&mut self, at: usize, pn: u64) -> bool {
        let mut at = at;
        if self.len == RANGES {
            let Some(&(low_start, low_end)) = self.items.first() else {
                return false;
            };
            if at == 0 {
                // Below everything tracked and no room: too old to keep.
                self.floor = self.floor.max(low_start);
                return false;
            }
            self.floor = self.floor.max(low_end);
            self.remove(0);
            at -= 1;
        }
        self.items.copy_within(at..self.len, at + 1);
        self.replace(at, (pn, pn + 1));
        self.len += 1;
        true
    }

    /// Whether any ack-eliciting packet awaits an acknowledgement.
    pub const fn ack_pending(&self) -> bool {
        self.pending > 0
    }

    /// When the acknowledgement must go out: the time of the packet that made it urgent, or the first unacknowledged
    /// ack-eliciting packet plus the maximum ack delay. `None` when nothing awaits acknowledgement.
    pub fn ack_deadline(&self) -> Option<u64> {
        if self.pending == 0 {
            return None;
        }
        Some(
            self.immediate_at
                .unwrap_or_else(|| self.first_pending.saturating_add(max_ack_delay(self.min_rtt))),
        )
    }

    /// Whether the acknowledgement is due at `now`.
    pub fn ack_due(&self, now: u64) -> bool {
        self.ack_deadline().is_some_and(|d| d <= now)
    }

    /// The delay to report: time since the largest packet arrived, in nanoseconds.
    pub fn ack_delay(&self, now: u64) -> u64 {
        now.saturating_sub(self.largest_time)
    }

    /// The received ranges to report, largest first, at most [`MAX_ACK_RANGES`], without what the peer confirmed
    /// more than 2 s before `now`.
    pub fn ack_ranges(&self, now: u64) -> impl Iterator<Item = RangeInclusive<u64>> + '_ {
        let pruned = self.prune_floor(now);
        self.live()
            .iter()
            .rev()
            .take(MAX_ACK_RANGES)
            .map_while(move |&(start, end)| {
                let last = end - 1;
                let first = pruned.map_or(start, |p| start.max(p.saturating_add(1)));
                (first <= last).then_some(first..=last)
            })
    }

    /// Everything at or below the returned packet number is no longer reported.
    fn prune_floor(&self, now: u64) -> Option<u64> {
        self.sent
            .iter()
            .flatten()
            .filter(|s| s.confirmed_at.is_some_and(|at| at.saturating_add(CONFIRM_HOLD) <= now))
            .map(|s| s.largest)
            .chain(self.pruned)
            .max()
    }

    /// Record that an acknowledgement of everything received so far went out in our packet `ack_pn` at `now`; the
    /// pending state clears.
    pub fn on_ack_sent(&mut self, ack_pn: u64, now: u64) {
        let Some(largest) = self.largest() else { return };
        self.pending = 0;
        self.immediate_at = None;
        if let Some(old) = self.sent.get(self.next_sent).copied().flatten()
            && old
                .confirmed_at
                .is_some_and(|at| at.saturating_add(CONFIRM_HOLD) <= now)
        {
            self.pruned = self.pruned.max(Some(old.largest));
        }
        if let Some(slot) = self.sent.get_mut(self.next_sent) {
            *slot = Some(AckSent {
                pn: ack_pn,
                largest,
                confirmed_at: None,
            });
        }
        self.next_sent = (self.next_sent + 1) % SENT_ACKS;
    }

    /// Record that the peer acknowledged our packet `ack_pn`, which carried an acknowledgement: the ranges it
    /// reported stop being repeated 2 s after `now`.
    pub fn on_ack_confirmed(&mut self, ack_pn: u64, now: u64) {
        if let Some(rec) = self.sent.iter_mut().flatten().find(|s| s.pn == ack_pn) {
            rec.confirmed_at.get_or_insert(now);
        }
    }
}
