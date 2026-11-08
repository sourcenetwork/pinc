//! Received-packet tracking of one packet space: a bounded range set, duplicate detection, the acknowledgement
//! decision and the ranges to report.
//!
//! Received packet numbers live in at most `RANGES` disjoint, sorted, merged `[start, end)` intervals. When a new
//! interval does not fit, the lowest one is forgotten and `floor` rises past it: everything below `floor` is treated
//! as already received, so a forgotten packet is dropped as a duplicate rather than processed twice.
//!
//! The acknowledgement policy, applied to each ack-eliciting packet:
//! - every 2nd packet; every 3rd when the packet is bulk (at least 1000 stream bytes and the largest received number
//!   is at least 2); every 4th when the owner marked this a member's hub session ([`ReceivedPackets::set_every`]);
//!   on a long-RTT path (minimum round trip of 250 ms or more) at least every 4th;
//! - at once when the packet number is not the one after the largest received (a gap, or an older packet);
//! - otherwise after [`max_ack_delay`] (25 ms, or `min(250 ms, max(25 ms, min_rtt / 8))` on a long-RTT path), counted
//!   from the packet that found no acknowledgement due.
//!
//! Reported ranges are largest first and at most [`MAX_ACK_RANGES`]. Older ranges are left out once the peer
//! confirmed an acknowledgement of ours: ours is recorded per packet number (the last 48 acknowledgement-carrying
//! packets); when the peer acknowledges one, the largest number it reported is queued (up to 32 entries) and, 2 s
//! later, becomes the floor. If the second-newest range ends below the floor, only the newest range is reported.
//!
//! Invariants: the set never holds more than `RANGES` ranges; every table is a fixed array.

use core::ops::RangeInclusive;

use super::rtt::max_ack_delay;
use super::{MAX_PACKET_NUMBER, RecoveryError, SECOND, is_long_rtt};

/// The most ranges one acknowledgement reports.
pub const MAX_ACK_RANGES: usize = 32;
/// Stream bytes at which a packet counts as bulk.
const BULK_BYTES: u32 = 1000;
/// A packet is bulk only once the largest received number is at least this.
const BULK_MIN_LARGEST: u64 = 2;
const EVERY_DEFAULT: u32 = 2;
const EVERY_BULK: u32 = 3;
const EVERY_LONG_RTT: u32 = 4;
/// How long a confirmed number waits before it becomes the floor (2 s).
const CONFIRM_HOLD: u64 = 2 * SECOND;
/// Acknowledgement-carrying packets remembered, oldest forgotten first.
const SENT_ACKS: usize = 48;
/// Confirmations queued before the floor takes them.
const CONFIRMS: usize = 32;

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

/// Received packet numbers and acknowledgement state of one packet space, with room for `RANGES` ranges.
#[derive(Debug, Clone)]
pub struct ReceivedPackets<const RANGES: usize> {
    items: [(u64, u64); RANGES],
    len: usize,
    floor: u64,
    pending: u32,
    due: Option<u64>,
    every: Option<u32>,
    min_rtt: Option<u64>,
    /// Our packets that carried an acknowledgement: (packet number, largest number it reported), oldest first.
    sent: [(u64, u64); SENT_ACKS],
    sent_len: usize,
    /// Confirmations waiting for the floor: (time the peer confirmed, largest number confirmed), oldest first.
    confirms: [(u64, u64); CONFIRMS],
    confirms_len: usize,
    confirmed_floor: Option<u64>,
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
            pending: 0,
            due: None,
            every: None,
            min_rtt: None,
            sent: [(0, 0); SENT_ACKS],
            sent_len: 0,
            confirms: [(0, 0); CONFIRMS],
            confirms_len: 0,
            confirmed_floor: None,
        }
    }

    fn live(&self) -> &[(u64, u64)] {
        self.items.get(..self.len).unwrap_or(&[])
    }

    /// The path's minimum round trip, which selects the long-RTT acknowledgement policy.
    pub fn set_min_rtt(&mut self, min_rtt: Option<u64>) {
        self.min_rtt = min_rtt;
    }

    /// Acknowledge every `every`-th ack-eliciting packet instead of every 2nd (or 3rd for bulk): 4 for a member's
    /// session with a hub. `None` restores the default policy. A value below 1 counts as 1.
    pub fn set_every(&mut self, every: Option<u32>) {
        self.every = every.map(|e| e.max(1));
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
        let expected = self.largest().map_or(0, |l| l + 1);
        if !self.insert(p.pn) {
            return Ok(RxOutcome::Duplicate);
        }
        if p.ack_eliciting {
            let gap = p.pn != expected;
            self.pending = self.pending.saturating_add(1);
            let bulk = p.stream_bytes >= BULK_BYTES && self.largest().is_some_and(|l| l >= BULK_MIN_LARGEST);
            let mut every = self.every.unwrap_or(if bulk { EVERY_BULK } else { EVERY_DEFAULT });
            if is_long_rtt(self.min_rtt) {
                every = every.max(EVERY_LONG_RTT);
            }
            let delay = max_ack_delay(self.min_rtt);
            if self.pending >= every || gap {
                self.due = Some(p.now);
            } else if self.due.is_none_or(|d| d > p.now.saturating_add(delay)) {
                self.due = Some(p.now.saturating_add(delay));
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

    /// When the acknowledgement must go out. `None` when nothing awaits acknowledgement.
    pub const fn ack_deadline(&self) -> Option<u64> {
        if self.pending == 0 { None } else { self.due }
    }

    /// Whether the acknowledgement is due at `now`.
    pub fn ack_due(&self, now: u64) -> bool {
        self.ack_deadline().is_some_and(|d| d <= now)
    }

    /// The floor at `now`: the largest confirmed number whose confirmation is at least 2 s old.
    fn floor_at(&self, now: u64) -> Option<u64> {
        self.confirms
            .iter()
            .take(self.confirms_len)
            .take_while(|(at, _)| at.saturating_add(CONFIRM_HOLD) <= now)
            .map(|c| c.1)
            .chain(self.confirmed_floor)
            .max()
    }

    /// The received ranges to report at `now`, largest first, at most [`MAX_ACK_RANGES`]. Only the newest range if
    /// the second-newest ends below the confirmed floor.
    pub fn ack_ranges(&self, now: u64) -> impl Iterator<Item = RangeInclusive<u64>> + '_ {
        let live = self.live();
        let only_newest = self.floor_at(now).is_some_and(|f| {
            live.len() > 1
                && live
                    .len()
                    .checked_sub(2)
                    .and_then(|i| live.get(i))
                    .is_some_and(|iv| iv.1 - 1 < f)
        });
        let take = if only_newest { 1 } else { MAX_ACK_RANGES };
        live.iter().rev().take(take).map(|&(start, end)| start..=end - 1)
    }

    /// Record that an acknowledgement of everything received so far went out in our packet `ack_pn` at `now`; the
    /// pending state clears and confirmations older than 2 s take effect.
    pub fn on_ack_sent(&mut self, ack_pn: u64, now: u64) {
        let Some(largest) = self.largest() else { return };
        self.pending = 0;
        self.due = None;
        while self
            .confirms
            .first()
            .filter(|_| self.confirms_len > 0)
            .is_some_and(|(at, _)| at.saturating_add(CONFIRM_HOLD) <= now)
        {
            if let Some(&(_, n)) = self.confirms.first() {
                self.confirmed_floor = self.confirmed_floor.max(Some(n));
            }
            self.confirms.copy_within(1..self.confirms_len, 0);
            self.confirms_len -= 1;
        }
        if self.sent_len == SENT_ACKS {
            self.sent.copy_within(1.., 0);
            self.sent_len -= 1;
        }
        if let Some(slot) = self.sent.get_mut(self.sent_len) {
            *slot = (ack_pn, largest);
            self.sent_len += 1;
        }
    }

    /// The peer sent an acknowledgement with `ranges`. If it acknowledges any of our recorded acknowledgement
    /// packets at or below its largest number, the largest number those reported is queued for the floor, and every
    /// recorded packet at or below that largest number is forgotten.
    pub fn on_peer_ack<I>(&mut self, now: u64, ranges: &I)
    where
        I: IntoIterator<Item = RangeInclusive<u64>> + Clone,
    {
        let Some(largest) = ranges.clone().into_iter().map(|r| *r.end()).max() else {
            return;
        };
        let best = self
            .sent
            .iter()
            .take(self.sent_len)
            .filter(|(pn, _)| *pn <= largest && ranges.clone().into_iter().any(|r| r.contains(pn)))
            .map(|(_, reported)| *reported)
            .max();
        let Some(best) = best else { return };
        let mut kept = 0;
        for i in 0..self.sent_len {
            if let Some(&e) = self.sent.get(i).filter(|e| e.0 > largest) {
                if let Some(slot) = self.sent.get_mut(kept) {
                    *slot = e;
                }
                kept += 1;
            }
        }
        self.sent_len = kept;
        if self.confirms_len < CONFIRMS
            && let Some(slot) = self.confirms.get_mut(self.confirms_len)
        {
            *slot = (now, best);
            self.confirms_len += 1;
        }
    }
}
