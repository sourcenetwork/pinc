//! Timers and the per-session bookkeeping that follows every input.
//!
//! After any call that touches a session the endpoint settles it: it reads the session's events, hands it the node
//! round trips if they changed, applies the keepalive plan, registers new connection ids, and recomputes the one
//! deadline the session contributes to the heap. The deadline is the earliest of the connection's own timer, the
//! keepalive review, the next ping of a standby path, the end of an unauthenticated session's 30 s, and the moment a
//! cached access answer has 5 s left. [`Endpoint::poll_timeout`](crate::Endpoint::poll_timeout) is a peek at the
//! heap; [`Endpoint::handle_timeout`](crate::Endpoint::handle_timeout) pops the sessions that are due, each at most
//! once per call.
//!
//! Invariants: a session has at most one entry in the heap; a settled session that has ended is freed; a deadline
//! after a timer is strictly later than the time of the call, so a timer cannot spin.

use vinc_transport::conn::Config;

use crate::endpoint::{CLOSE_GRACE, env, ep_impl};
use crate::keepalive::{Inputs, standby_due};
use crate::rx::HALF_OPEN_LIFE;
use crate::trace::trace;

ep_impl! {
    /// The configuration of a new connection: the base configuration with the node round trips filled in. For a
    /// dial, `peer` selects the remembered round trip.
    pub(crate) fn conn_config(&self, peer: Option<&vinc_crypto::NodeId>) -> Config {
        let mut c = self.cfg.conn;
        c.thin = self.rtt.thin_node();
        c.node_rtt = Some(self.rtt.lrtt()).filter(|r| *r > 0);
        c.node_peak_rtt = Some(self.rtt.tgr()).filter(|r| *r > 0);
        c.remembered_rtt = peer.and_then(|p| self.rtt.remembered_for(p));
        c
    }

    /// Bring session `i` up to date after an input, recompute its deadline and queue it for sending.
    pub(crate) fn settle(&mut self, i: usize, now: u64) {
        self.settle_core(i, now, true);
    }

    /// As [`settle`](Self::settle); `queue` says whether to put the session on the send queue.
    pub(crate) fn settle_core(&mut self, i: usize, now: u64, queue: bool) {
        self.drain(i, now);
        let Some(slot) = self.slots.get_mut(i) else { return };
        if !slot.m.in_use {
            return;
        }
        let Some(conn) = slot.conn.as_mut() else { return };
        if conn.poll_timeout().is_none() {
            self.free_slot(i, now);
            return;
        }
        let closing = conn.is_closed();
        let peak = conn.recovery().peak_rtt();
        if peak != slot.m.seen_peak {
            slot.m.seen_peak = peak;
            self.rtt.note_peak(peak);
            self.rtt.note_sample();
            self.node_ver += 1;
            trace!(self, now, Rtt {
                lrtt: self.rtt.lrtt(),
                tgr: self.rtt.tgr(),
                hs_floor: self.rtt.hs_floor(),
            });
        }
        if slot.m.node_ver != self.node_ver {
            slot.m.node_ver = self.node_ver;
            conn.set_node_rtt(self.rtt.tgr(), self.rtt.lrtt(), self.rtt.thin_node());
        }
        let mut deadline = if closing {
            Some(now.saturating_add(CLOSE_GRACE))
        } else {
            conn.poll_timeout()
        };
        let mut note = |d: Option<u64>| {
            if let Some(d) = d {
                deadline = Some(deadline.map_or(d, |c| c.min(d)));
            }
        };
        if !closing && conn.is_connected() {
            let plan = Inputs {
                role: slot.m.role,
                dialer: slot.m.client,
                direct: !conn.active_is_relay(),
                now,
                last_tx: slot.m.last_tx,
                last_rx: slot.m.last_rx,
                last_app: slot.m.last_app,
                quiet_until: self.quiet_until,
                in_flight: conn.recovery().packets_in_flight() > 0,
            }
            .plan();
            if plan != slot.m.plan {
                slot.m.plan = plan;
                let interval = plan.ping_at.map(|p| p.saturating_sub(slot.m.last_tx));
                conn.set_keepalive(if slot.m.pulse { None } else { interval });
                trace!(self, now, Keepalive {
                    slot: i as u64,
                    ping_at: plan.ping_at.unwrap_or(u64::MAX),
                    review_at: plan.review_at.unwrap_or(u64::MAX),
                });
            }
            note(plan.review_at);
            slot.m.pulse_due = slot.m.pulse && plan.ping_at.is_some_and(|p| p <= now);
            if slot.m.pulse {
                note(plan.ping_at);
            }
            let active = conn.active_path();
            for p in slot.m.paths.iter().flatten() {
                if Some(p.id) != active && conn.path_validated(p.id) {
                    note(standby_due(now, p.tx, slot.m.last_app));
                }
            }
            note(slot.m.acp_recheck);
        }
        if slot.m.unauth {
            note(Some(slot.m.created.saturating_add(HALF_OPEN_LIFE)));
        }
        self.heap.set(i, deadline);
        self.sync_cids(i, false);
        if queue {
            self.mark_dirty(i);
        }
    }

    /// The next time [`handle_timeout`](Self::handle_timeout) must run, or `None` when no session has a timer.
    /// While the event queue is near full no timer is due: read events with `poll_event` first.
    pub fn poll_timeout(&self) -> Option<u64> {
        self.heap.peek().map(|(t, _)| t).filter(|_| !self.events.stalled())
    }

    /// Run every timer that is due at `now`.
    pub fn handle_timeout(&mut self, now: u64) {
        self.last_now = now;
        for _ in 0..K {
            if self.events.stalled() {
                return;
            }
            let Some((t, i)) = self.heap.peek() else { return };
            if t > now {
                return;
            }
            self.heap.set(i, None);
            self.run_timer(i, now);
            if self.heap.deadline(i).is_some_and(|d| d <= now) {
                self.heap.set(i, Some(now.saturating_add(1)));
            }
        }
    }

    fn run_timer(&mut self, i: usize, now: u64) {
        let Some(slot) = self.slots.get_mut(i) else { return };
        if !slot.m.in_use {
            return;
        }
        if slot.m.unauth && now >= slot.m.created.saturating_add(HALF_OPEN_LIFE) {
            trace!(self, now, HalfOpenExpired { slot: i as u64 });
            self.free_slot(i, now);
            return;
        }
        if slot.m.acp_recheck.is_some_and(|t| t <= now) {
            slot.m.acp_recheck = None;
            self.ask_acp(i, now, true);
        }
        let Some(slot) = self.slots.get_mut(i) else { return };
        let Some(conn) = slot.conn.as_mut() else { return };
        // A standby path that carried nothing for 5 s while data moves is challenged to keep its mapping open.
        let active = conn.active_path();
        let mut probe: [Option<vinc_transport::conn::PathId>; NP] = [None; NP];
        let mut n = 0;
        for p in slot.m.paths.iter().flatten() {
            if Some(p.id) != active
                && conn.path_validated(p.id)
                && standby_due(now, p.tx, slot.m.last_app).is_some_and(|d| d <= now)
                && let Some(s) = probe.get_mut(n)
            {
                *s = Some(p.id);
                n += 1;
            }
        }
        let mut env = env!(self, now);
        for id in probe.iter().flatten() {
            let _ = conn.probe(&mut env, *id);
            if let Some(p) = slot.m.stamp(*id) {
                p.tx = now;
            }
        }
        conn.handle_timeout(&mut env);
        self.settle(i, now);
    }
}
