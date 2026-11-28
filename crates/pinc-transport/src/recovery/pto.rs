//! The probe timer of [`Recovery`]: when it fires, what a firing does, and the loss timer it shares a deadline with.
//!
//! The probe timeout is `srtt + max(4 * rttvar, 1 ms) + 25 ms` (333 ms and 166.5 ms before a sample), shifted left
//! by the number of consecutive timeouts (at most 6) and capped at `max(2 s, 2 * srtt) * 4`. It never exceeds 2 s,
//! except when the minimum round trip is 250 ms or more or the smoothed round trip is 1 s or more, where the cap is
//! `max(2 s, 2 * srtt)`. The deadline counts from the later of the newest packet in flight and the last timeout.
//!
//! A firing timer:
//! - grows the count (not while the peer sleeps, and not while the link is down), and records the firing time;
//! - on the first timeout, saves the window so that, if the packet it declares lost is acknowledged later, the
//!   window is restored;
//! - declares the oldest packet in flight lost (it is requeued and, once per episode, reduces the window);
//! - asks for one PING, which is not recorded as in flight.
//!
//! While the peer sleeps a firing only moves the anchor forward: nothing is declared lost, nothing is sent and the
//! count stays. The give-up decision is [`Recovery::health`].

use super::engine::{Event, Recovery, SavedWindow, Summary, Timeout};
use super::{MS, SECOND};

/// The largest shift of the timeout by the timeout count.
const PTO_MAX_SHIFT: u32 = 6;
/// The ordinary cap of the probe timeout (2 s).
const PTO_CAP: u64 = 2 * SECOND;
/// The receiver's delay allowed for in the timeout (25 ms).
const PTO_MAX_ACK_DELAY: u64 = 25 * MS;
/// The floor of four times the variation.
const PTO_FLOOR_VAR: u64 = MS;
/// The shifted timeout never exceeds the wide cap times this.
const PTO_SHIFTED_CAP_FACTOR: u64 = 4;
/// A smoothed round trip of this much or more raises the cap (1 s, four times the slow-path threshold of 250 ms).
const SLOW_SRTT: u64 = 4 * super::LONG_RTT;

impl<const N: usize> Recovery<N> {
    /// The probe timeout duration for the current count (see the module documentation).
    pub fn pto_duration(&self) -> u64 {
        // Without a sample the smoothed round trip is seeded from the node: max(333 ms, 2 x node round trip).
        let (srtt, var) = if self.rtt.has_sample() {
            (self.rtt.smoothed(), self.rtt.rttvar())
        } else {
            let seed = super::INITIAL_RTT.max(self.node_rtt().saturating_mul(2));
            (seed, seed / 2)
        };
        let base = srtt
            .saturating_add(var.saturating_mul(4).max(PTO_FLOOR_VAR))
            .saturating_add(PTO_MAX_ACK_DELAY);
        let wide = PTO_CAP.max(srtt.saturating_mul(2));
        let shifted = base
            .saturating_mul(1u64 << self.pto_count.min(PTO_MAX_SHIFT))
            .min(wide.saturating_mul(PTO_SHIFTED_CAP_FACTOR));
        let slow = self.rtt.min_rtt().is_some_and(|m| m >= super::LONG_RTT) || srtt >= SLOW_SRTT;
        shifted.min(if slow { wide } else { PTO_CAP })
    }

    fn pto_deadline(&self) -> Option<u64> {
        let newest = self.ring.newest_in_flight_time()?;
        super::deadline_after(newest.max(self.last_pto), self.pto_duration())
    }

    /// The next time [`Self::on_timeout`] must run: the earlier of the loss timer and the probe timer.
    pub fn next_timeout(&self) -> Option<u64> {
        match (self.loss_time, self.pto_deadline()) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        }
    }

    /// Run the expired timers: loss detection if its time came, then the probe timer if its deadline came.
    pub fn on_timeout<F: FnMut(Event<'_>)>(&mut self, now: u64, mut on_event: F) -> Timeout {
        self.clock = self.clock.max(now);
        let mut out = Timeout::default();
        if self.loss_time.is_some_and(|t| now >= t) {
            let largest = self.largest_acked.unwrap_or(0);
            if self.largest_acked.is_some() {
                self.detect_lost(now, largest, &mut out.summary, &mut on_event);
            }
        }
        if self.pto_deadline().is_none_or(|d| now < d) {
            return out;
        }
        if self.asleep {
            self.last_pto = now;
            return out;
        }
        if !self.link_down {
            self.pto_count = self.pto_count.saturating_add(1);
        }
        self.last_pto = now;
        if matches!(self.health(now), super::Health::Dead) {
            return out;
        }
        self.declare_oldest_lost(now, &mut out.summary, &mut on_event);
        out.ping = true;
        out
    }

    fn declare_oldest_lost<F: FnMut(Event<'_>)>(&mut self, now: u64, s: &mut Summary, on_event: &mut F) {
        let Some(idx) = self.ring.first_in_flight() else { return };
        let Some(pn) = self.ring.get(idx).map(|slot| slot.sent.pn) else {
            return;
        };
        if self.pto_count == 1 {
            self.saved_window = Some(SavedWindow {
                pn,
                cwnd: self.cc.cwnd(),
                ssthresh: self.cc.ssthresh(),
            });
        }
        let newest = self.lose_at(idx, now, s, on_event);
        self.settle_losses(now, newest, s);
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::super::{FrameRef, FrameRefs, Sent};
    use super::*;

    /// The deadline is `None` (never), not `u64::MAX`, when the probe timeout passes the end of the clock, so a
    /// timer that fired is not due again at once.
    #[test]
    fn the_probe_timer_never_saturates_at_the_end_of_the_clock() {
        let mut rec = Recovery::<48>::new(1200);
        let start = u64::MAX - SECOND / 2;
        for _ in 0..3 {
            let pn = rec.next_pn();
            let mut frames = FrameRefs::new();
            frames
                .push(FrameRef::Stream {
                    id: 0,
                    offset: pn * 100,
                    len: 100,
                    fin: false,
                })
                .unwrap();
            rec.on_packet_sent(Sent {
                pn,
                time: start,
                size: 100,
                path: 0,
                is_repair: false,
                is_mtu_probe: false,
                frames,
            })
            .unwrap();
        }
        assert_eq!(rec.next_timeout(), None, "the deadline passes the end of the clock");
        // A probe timer that is due before the end still fires, and the next one is later or never.
        let before = start - SECOND;
        let mut rec2 = Recovery::<48>::new(1200);
        let pn = rec2.next_pn();
        let mut frames = FrameRefs::new();
        frames
            .push(FrameRef::Stream {
                id: 0,
                offset: 0,
                len: 100,
                fin: false,
            })
            .unwrap();
        rec2.on_packet_sent(Sent {
            pn,
            time: before,
            size: 100,
            path: 0,
            is_repair: false,
            is_mtu_probe: false,
            frames,
        })
        .unwrap();
        let t = rec2.next_timeout().unwrap();
        assert!(t > before && t < u64::MAX);
    }
}
