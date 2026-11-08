//! Timers: when the connection next needs attention, and what to do when that time comes.
//!
//! Invariants: a timer is reported only while it can still act (a stale deadline would make a driver spin); while the
//! peer sleeps or the link is down the probe and loss timers are not reported and do not run; closing and draining
//! end exactly at their deadline.

use vinc_crypto::Provider;
use vinc_security::Env;

use super::config::MIN_MTU;
use super::ctl::{Outcome, apply};
use super::event::{CloseReason, Ev};
use super::life::LINK_DOWN_MAX;
use super::{Connection, Phase};
use crate::recovery::{Health, PathKind};
use crate::stream::StreamSource;

conn_impl! {
    /// The next time [`handle_timeout`](Self::handle_timeout) must run, in the clock of the `Env`; `None` when the
    /// connection has ended.
    pub fn poll_timeout(&self) -> Option<u64> {
        match self.phase {
            Phase::Closed => return None,
            Phase::Closing | Phase::Draining => return Some(self.life.close_until),
            Phase::Handshaking | Phase::Connected => {}
        }
        let mut t = self.idle_deadline();
        let mut add = |x: Option<u64>| {
            if let Some(x) = x {
                t = t.min(x);
            }
        };
        // While nothing can leave (the link is down, or this endpoint sleeps), only the clocks that end that state
        // and the idle timeout run; the others would come due and have nothing to do.
        if self.life.link_down.is_some() || (self.life.local_asleep.is_some() && self.life.sleep_tx == 0) {
            add(self.life.link_down.map(|s| s.saturating_add(LINK_DOWN_MAX)));
            add(self.life.wake_deadline);
            return Some(t);
        }
        if !self.client || !self.confirmed {
            add(self.hs.retransmit_at());
        }
        if !self.suspended() {
            add(self.rec.next_timeout());
        }
        if self.amp_room(self.paths.active) >= 64 {
            add(self.rx.ack_deadline());
        }
        add(self.paced_until);
        add(self.path_deadline());
        add(self.life.wake_deadline);
        add(self.life.repair_at);
        add(self.life.link_down.map(|s| s.saturating_add(LINK_DOWN_MAX)));
        if self.phase == Phase::Connected {
            add(self.life.keepalive.map(|k| self.life.last_sent.saturating_add(k)));
            if let Some(p) = self.paths.active().filter(|p| p.mtu.next_at > 0 && p.mtu.inflight.is_none()) {
                add(self.mtu_target(self.paths.active).map(|_| p.mtu.next_at));
            }
        }
        Some(t)
    }

    /// Run whatever timer expired: the handshake retransmit, loss detection and probes, path challenges, the wake
    /// wait, the tail repair, the idle timeout, and the end of closing or draining.
    pub fn handle_timeout(&mut self, env: &mut Env<'_, P>) {
        let now = env.now;
        match self.phase {
            Phase::Closed => return,
            Phase::Closing | Phase::Draining => {
                if now >= self.life.close_until {
                    self.phase = Phase::Closed;
                }
                return;
            }
            Phase::Handshaking | Phase::Connected => {}
        }
        if now >= self.idle_deadline() {
            self.silent_close(CloseReason::IdleTimeout);
            return;
        }
        if self.hs.on_timer(now) {
            self.stats.handshake_retransmits += 1;
            self.pump(env);
        }
        if self.life.link_down.is_some_and(|s| s.saturating_add(LINK_DOWN_MAX) <= now) {
            self.life.link_down = None;
            self.suspend_probes();
        }
        if !self.suspended() {
            self.run_recovery_timer(now);
        }
        self.on_path_timers(env);
        // A probe retry that came due is not a timer any more: the next transmit attempt takes it when it may.
        for p in self.paths.slots.iter_mut().flatten() {
            if p.mtu.next_at <= now {
                p.mtu.next_at = 0;
            }
        }
        if self.life.wake_deadline.is_some_and(|d| d <= now) {
            self.life.wake_deadline = None;
            self.push(Ev::WakeUnanswered);
        }
        if self.life.repair_at.is_some_and(|t| t <= now) {
            self.life.repair_at = None;
            let direct = self.paths.active().is_some_and(|p| p.info.kind == PathKind::Direct);
            let age = now.saturating_sub(self.started);
            self.life.repair_due = self.rec.bytes_in_flight() > 0 && self.loss.should_send_repair(age, true, direct);
        }
    }

    fn run_recovery_timer(&mut self, now: u64) {
        let mut out = Outcome::default();
        let (streams, pool, ctl, cids, rx) = (&mut *self.streams, &mut self.pool, &mut self.ctl, &mut self.cids, &mut self.rx);
        let to = self.rec.on_timeout(now, |ev| apply(&ev, now, streams, pool, ctl, cids, rx, &mut out));
        self.after_feedback(out, now);
        if to.probes > 0 {
            self.life.probes = to.probes;
            self.stats.ptos += 1;
            self.mtu_black_hole_check();
        }
        match self.rec.health(now) {
            Health::Dead => self.silent_close(CloseReason::PathDead),
            Health::Degraded if !self.degraded_told => {
                self.degraded_told = true;
                if let Some(id) = self.paths.active().map(|p| p.id) {
                    self.push(Ev::PathFailed(id));
                }
                if self.client {
                    self.evaluate_paths();
                }
            }
            _ => {}
        }
        let _ = MIN_MTU;
    }
}
