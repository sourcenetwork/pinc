//! Loss detection for [`Recovery`]: which in-flight packets are declared lost and what that does to the window.
//!
//! A packet below the largest acknowledged one is judged by the path it left on, with
//! `rtt = max(latest, smoothed)` (333 ms before a sample) and `delay = max(rtt * 9 / 8, 1 ms)`:
//! - a packet sent on a path that is no longer active is lost once it is `max(rtt, that path's round trip) * 4 +
//!   50 ms` old; if that path is a relay, at least `max(4 * max(rtt, path rtt), 1.5 s)`;
//! - a relay packet sent on the active path before the latest path switch is lost once `max(rtt * 4 + 50 ms,
//!   1.5 s)` old;
//! - a packet on the active relay path is lost once `max(2 * rtt, delay) + 50 ms` old (time only, no packet count);
//! - any other packet is lost when three packets above it are acknowledged or it is `delay` old; while the path shows
//!   reordering (the reorder lens, below) only the time rule applies, with `min(max(delay, rtt + 2 * extent), 4 *
//!   rtt)`.
//!
//! The reorder lens: a packet of the active direct path that is acknowledged, or acknowledged late after being declared
//! lost, at least three numbers below the largest packet acknowledged before was overtaken. The path's reorder extent
//! becomes the send-time spread between the two (the widest seen while the evidence stays fresh), and the path keeps
//! the time rule for `max(2 s, 16 smoothed round trips)` after the last such packet. A path that never shows it keeps
//! the count rule, so nothing changes there.
//!
//! The loss timer is the earliest time at which a packet still in flight would cross its threshold. A lost repair
//! packet or path MTU probe is dropped without a retransmission, a ghost or a congestion signal. Any other loss
//! leaves a ghost (so a late acknowledgement is recognised), remembers its send time (so a late acknowledgement can
//! seed an empty estimate), and, if its send time is after the last window reduction, reduces the window once for the
//! whole batch.

use super::engine::{Event, PathKind, Recovery, Summary};
use super::math::sat;
use super::rtt::INITIAL_RTT;
use super::sent::{State, is_ghost_data};
use super::{MS, SECOND};

/// Packets above a lost one that must be acknowledged for the count rule.
const PACKET_THRESHOLD: u64 = 3;
/// The factor on the round trip for a packet of a path that is no longer active.
const OLD_PATH_RTT_FACTOR: u64 = 4;
/// Twice the receiver's 25 ms delay, added to the old-path and relay thresholds.
const OLD_PATH_EXTRA: u64 = 50 * MS;
/// The shortest wait before a relay packet is presumed lost (1.5 s).
const RELAY_MIN_DELAY: u64 = 3 * SECOND / 2;
/// The multiple of the round trip for the active relay path.
const ACTIVE_RELAY_RTT_FACTOR: u64 = 2;
/// The reorder lens: the time rule waits `rtt + REORDER_EXTENT_FACTOR * extent` ...
const REORDER_EXTENT_FACTOR: u64 = 2;
/// ... at most `REORDER_CAP_RTTS * rtt`.
const REORDER_CAP_RTTS: u64 = 4;
/// The reorder lens holds a path on the time rule this long after the last overtaken packet (at least 2 s) ...
const REORDER_HOLD_MIN: u64 = 2 * SECOND;
/// ... or this many smoothed round trips, whichever is longer.
const REORDER_HOLD_RTTS: u64 = 16;

impl<const N: usize> Recovery<N> {
    fn kind_of(&self, path: u8) -> PathKind {
        self.paths.get(usize::from(path)).copied().unwrap_or(PathKind::Direct)
    }

    /// Declare lost every packet in flight at or below `largest` that crossed its threshold, arm the loss timer for
    /// the next one to cross, and reduce the window once if any loss counts.
    ///
    /// vertexia: scans from the oldest packet in flight to `largest` on every acknowledgement, O(packets in flight
    /// below `largest`, acknowledged ones among them); an index of the packets in flight would make it O(losses) if
    /// profiles show it.
    pub(super) fn detect_lost<F: FnMut(Event<'_>)>(
        &mut self,
        now: u64,
        largest: u64,
        s: &mut Summary,
        on_event: &mut F,
    ) {
        let rtt = if self.rtt.has_sample() {
            self.rtt.latest().unwrap_or(0).max(self.rtt.smoothed())
        } else {
            INITIAL_RTT
        };
        let delay = sat(u128::from(rtt) * 9 / 8).max(MS);
        self.loss_time = None;
        let mut newest_lost: Option<u64> = None;
        let mut i = self.ring.lead();
        while let Some(slot) = self.ring.get(i) {
            if slot.sent.pn > largest {
                break;
            }
            i += 1;
            if slot.state != State::InFlight {
                continue;
            }
            let sent = slot.sent;
            let kind = self.kind_of(sent.path);
            let (lost, threshold) = if sent.path != self.active {
                let old_rtt = self.path_rtt.get(usize::from(sent.path)).copied().unwrap_or(0);
                let widest = rtt.max(old_rtt);
                let mut d2 = widest
                    .saturating_mul(OLD_PATH_RTT_FACTOR)
                    .saturating_add(OLD_PATH_EXTRA);
                if kind == PathKind::Relay {
                    d2 = d2.max(RELAY_MIN_DELAY);
                }
                (false, d2)
            } else if kind == PathKind::Relay && self.flip_at.is_some_and(|f| sent.time <= f) {
                let d2 = rtt
                    .saturating_mul(OLD_PATH_RTT_FACTOR)
                    .saturating_add(OLD_PATH_EXTRA)
                    .max(RELAY_MIN_DELAY);
                (false, d2)
            } else if kind == PathKind::Relay {
                let d2 = rtt
                    .saturating_mul(ACTIVE_RELAY_RTT_FACTOR)
                    .max(delay)
                    .saturating_add(OLD_PATH_EXTRA);
                (false, d2)
            } else if let Some(extent) = self.reorder_extent(sent.path, now) {
                let wait = rtt.saturating_add(extent.saturating_mul(REORDER_EXTENT_FACTOR));
                (false, delay.max(wait).min(rtt.saturating_mul(REORDER_CAP_RTTS)))
            } else {
                (largest >= sent.pn.saturating_add(PACKET_THRESHOLD), delay)
            };
            let due = sent.time.saturating_add(threshold);
            if !(lost || now >= due) {
                self.loss_time = Some(self.loss_time.map_or(due, |t| t.min(due)));
                continue;
            }
            let idx = i - 1;
            newest_lost = newest_lost.max(self.lose_at(idx, now, s, on_event));
        }
        self.settle_losses(now, newest_lost, s);
    }

    /// The reorder extent of `path` while its evidence is fresh (the reorder lens); `None` keeps the count rule.
    fn reorder_extent(&self, path: u8, now: u64) -> Option<u64> {
        let hold = REORDER_HOLD_MIN.max(self.rtt.smoothed().saturating_mul(REORDER_HOLD_RTTS));
        let r = self.reorder.get(usize::from(path))?;
        r.seen.filter(|t| now.saturating_sub(*t) < hold).map(|_| r.extent)
    }

    /// The reorder lens: packet `pn`, sent at `time` on `path`, was just acknowledged (or acknowledged late). If it is
    /// at least three below the largest packet acknowledged before, on the active direct path, it was overtaken: widen the
    /// path's extent to the send-time spread and refresh the evidence.
    pub(super) fn note_overtaken(&mut self, now: u64, pn: u64, time: u64, path: u8) {
        let Some(prev) = self.largest_acked else { return };
        if pn.saturating_add(PACKET_THRESHOLD) > prev || path != self.active || self.kind_of(path) != PathKind::Direct {
            return;
        }
        let spread = self.largest_acked_time.saturating_sub(time);
        let kept = self.reorder_extent(path, now).unwrap_or(0);
        if let Some(r) = self.reorder.get_mut(usize::from(path)) {
            r.extent = kept.max(spread);
            r.seen = Some(now);
        }
    }

    /// Declare the packet at ring index `idx` lost. Returns its send time if it counts as a congestion signal.
    pub(super) fn lose_at<F: FnMut(Event<'_>)>(
        &mut self,
        idx: usize,
        now: u64,
        s: &mut Summary,
        on_event: &mut F,
    ) -> Option<u64> {
        let slot = self.ring.get_mut(idx)?;
        let sent = slot.sent;
        let counts = !sent.is_repair && !sent.is_mtu_probe;
        let ghost = counts && sent.frames.iter().any(is_ghost_data);
        slot.state = if ghost { State::Lost(now) } else { State::Done };
        let size = u64::from(sent.size);
        s.lost_packets += 1;
        s.lost_bytes += size;
        self.acct.in_flight -= size;
        self.acct.lost += u128::from(size);
        self.in_flight_packets -= 1;
        if counts {
            self.late_sends.insert(sent.pn, sent.time);
        }
        on_event(Event::Lost {
            pn: sent.pn,
            size: sent.size,
            frames: &sent.frames,
            requeue: counts,
            mtu_probe: sent.is_mtu_probe,
            path: sent.path,
            flushed: false,
        });
        counts.then_some(sent.time)
    }

    /// After a batch of losses: reduce the window once for the newest counted loss and bound the ghosts.
    pub(super) fn settle_losses(&mut self, now: u64, newest_lost: Option<u64>, s: &Summary) {
        if let Some(t) = newest_lost {
            self.cc.on_loss(now, t, self.rtt.latest(), self.rtt.min_rtt());
        }
        if s.lost_packets > 0 {
            self.ring.limit_ghosts();
        }
    }
}
