//! Time: the stall wait and its adjustments, retries, the steal re-check, the head timer and the deadline.
//!
//! STALL_REDIAL: a fetch that was receiving and then got no verified granule (and no stream bytes) for the stall wait
//! drops its sessions and dials afresh, doubling the wait up to 16 s. The wait grows with the transfer's own pace
//! (ARK_PACE), the gaps between stream bytes (BYTE_LIVE, in `recv`), four session round trips (STALL_RTT) and, for
//! slow sessions that are still receiving, STALL_LIVE.

use super::{Env, Fetch, State};
use crate::knobs::{ASSUMED_RTT, HOLD_MAX, LIVE_CAP, NS, SLOW_RTT, STALL_CAP, STALL_RTT, STALL_RTT_CAP, STALL_WAIT};
use crate::session::Outbound;
use crate::trace::{Event, FailReason, Out, Trace};

impl Fetch {
    /// The next time [`Fetch::on_timeout`] has something to do, if any.
    pub fn poll_timeout(&self) -> Option<u64> {
        if self.state != State::Running {
            return None;
        }
        let stall = (self.lastp != 0).then(|| self.lastp.max(self.lastb).saturating_add(self.sw));
        let head = self.head.map(|h| h.t0.saturating_add(HOLD_MAX));
        let steal = (self.tw != 0).then_some(self.tw);
        stall
            .into_iter()
            .chain(head)
            .chain(steal)
            .chain(self.deadline.map(|d| d.saturating_add(1)))
            .chain(self.provs.iter().filter_map(|p| p.retry))
            .min()
    }

    /// Run whatever is due at `now`.
    pub fn on_timeout<E: Env>(&mut self, io: &mut E, now: u64) {
        if self.state != State::Running {
            return;
        }
        if STALL_WAIT != 0 && self.lastp != 0 && now >= self.lastp.max(self.lastb).saturating_add(self.sw) {
            let w = self.stall_rtt(io);
            let lv = self.stall_live(io, now);
            if w > self.sw && self.lastp.saturating_add(w) > now {
                self.sw = w;
            } else if lv != 0 {
                self.sw = now.saturating_sub(self.lastp).saturating_add(lv);
            } else {
                self.stall_redial(io, now);
            }
        }
        if self.head.is_some() {
            self.hold_check(io, now, None);
            self.check_done(io, now);
            if self.state != State::Running {
                return;
            }
        }
        if self.striped && self.tw != 0 && now >= self.tw {
            self.tw = 0;
            for pi in 0..self.nprov {
                if self.provs.get(pi).is_some_and(|p| p.in_assign) {
                    self.top_up(io, now, pi);
                }
            }
            if self.state != State::Running {
                return;
            }
        }
        if self.deadline.is_some_and(|d| now > d) {
            self.state = State::Done;
            self.drop_all_streams(io);
            io.split().2.event(now, Event::Failed(FailReason::Deadline));
            return;
        }
        for pi in 0..self.nprov {
            let due = self
                .provs
                .get_mut(pi)
                .is_some_and(|p| p.retry.is_some_and(|t| t <= now) && p.retry.take().is_some());
            if due && (self.rx.iter().all(Option::is_none) || !self.provs.get(pi).is_some_and(|p| p.conn)) {
                self.request(io, now, pi, None);
            }
        }
    }

    /// STALL_RTT: at least four of the slowest session's round trips.
    fn stall_rtt<E: Env>(&self, io: &mut E) -> u64 {
        let (se, _, _) = io.split();
        let r = self
            .provs
            .iter()
            .filter(|p| p.in_assign)
            .filter_map(|p| se.peer_info(p.id).and_then(|i| i.rtt_ns))
            .filter(|&r| r != 0)
            .max()
            .unwrap_or(0);
        STALL_RTT.saturating_mul(r).min(STALL_RTT_CAP)
    }

    /// STALL_LIVE: every assigned session is slow (250 ms or more) and still receiving without a probe timeout.
    fn stall_live<E: Env>(&self, io: &mut E, now: u64) -> u64 {
        let (se, _, _) = io.split();
        let mut d = 0;
        for p in self.provs.iter().filter(|p| p.in_assign) {
            let info = if p.conn { se.peer_info(p.id) } else { None };
            let Some(info) = info else { return 0 };
            let r = info.rtt_ns.filter(|&r| r != 0).unwrap_or(ASSUMED_RTT);
            if r < SLOW_RTT
                || info.pto
                || now.saturating_sub(info.last_rx) > (2 * NS).max(r.saturating_mul(2))
                || now.saturating_sub(self.lastp) > LIVE_CAP
            {
                return 0;
            }
            d = d.max(r.saturating_mul(2)).max(STALL_WAIT);
        }
        d
    }

    /// STALL_REDIAL: drop every assigned session and dial afresh from the current addresses.
    fn stall_redial<E: Env>(&mut self, io: &mut E, now: u64) {
        let prev = self.sw;
        self.lastp = now;
        self.sw = self.sw.saturating_mul(2).min(STALL_CAP);
        io.split().2.trace(
            now,
            Trace::StallRedial {
                wait: prev,
                next: self.sw,
            },
        );
        for pi in 0..self.nprov {
            let Some(p) = self.provs.get_mut(pi).filter(|p| p.in_assign && p.conn) else {
                continue;
            };
            p.conn = false;
            let id = p.id;
            self.drop_streams(pi);
            io.split().0.hangup(id);
        }
        for pi in 0..self.nprov {
            if self.provs.get(pi).is_some_and(|p| p.in_assign) {
                self.request(io, now, pi, None);
            }
        }
    }
}
