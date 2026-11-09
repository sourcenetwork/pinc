//! Timers: when the connection next needs attention, and what to do when that time comes.
//!
//! Invariants: a timer is reported only while it can still act (a stale deadline would make a driver spin); the
//! recovery timer keeps running while the peer sleeps or the link is down (it declares the oldest packet lost and
//! pings, without growing the count); a connection that is closing ends at its next timer.

use vinc_crypto::Provider;
use vinc_security::Env;

use super::ctl::{Outcome, apply};
use super::event::{CloseReason, Ev};
use super::life::LINK_DOWN_MAX;
use super::path::PTO_FALLBACK;
use super::{Connection, Phase};
use crate::recovery::Health;
use crate::stream::StreamSource;

conn_impl! {
    /// The next time [`handle_timeout`](Self::handle_timeout) must run, in the clock of the `Env`; `None` when the
    /// connection has ended.
    pub fn poll_timeout(&self) -> Option<u64> {
        match self.phase {
            Phase::Closed => return None,
            Phase::Closing => return Some(0),
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
            if self.life.link_down.is_some() {
                add(self.rec.next_timeout());
            }
            return Some(t);
        }
        if !self.confirmed {
            add(self.hs.retransmit_at());
        }
        add(self.rekey_deadline());
        add(self.rec.next_timeout());
        if self.amp_room(self.paths.active) >= 64 {
            add(self.rx.ack_deadline());
        }
        add(self.paced_until);
        add(self.path_deadline());
        add(self.life.wake_deadline);
        add(self.life.link_down.map(|s| s.saturating_add(LINK_DOWN_MAX)));
        if self.phase == Phase::Connected {
            add(self.life.keepalive.map(|k| self.life.last_sent.saturating_add(k)));
            add(self.mtu_deadline());
        }
        Some(t)
    }

    /// Run whatever timer expired: the handshake retransmit, loss detection and probes, path challenges, the wake
    /// wait, the idle timeout and the end of a close.
    pub fn handle_timeout(&mut self, env: &mut Env<'_, P>) {
        let now = env.now;
        match self.phase {
            Phase::Closed => return,
            Phase::Closing => {
                self.phase = Phase::Closed;
                return;
            }
            Phase::Handshaking | Phase::Connected => {}
        }
        if now >= self.idle_deadline() {
            self.silent_close(CloseReason::IdleTimeout);
            return;
        }
        if self.hs.on_timer(env, now) {
            self.stats.handshake_retransmits += 1;
            self.pump(env);
        }
        if self.life.link_down.is_some_and(|s| s.saturating_add(LINK_DOWN_MAX) <= now) {
            self.life.link_down = None;
            self.suspend_probes();
        }
        self.apply_app_writes(now);
        self.run_recovery_timer(env);
        self.on_path_timers(env);
        // A lost probe has waited long enough: the path is probed again.
        for i in 0..NP {
            if self.paths.get(i).is_some_and(|p| p.mtu.retry_at != 0 && p.mtu.retry_at <= now) {
                self.mtu_event(i);
            }
        }
        if self.life.wake_deadline.is_some_and(|d| d <= now) {
            self.life.wake_deadline = None;
            self.push(Ev::WakeUnanswered);
        }
    }

    fn run_recovery_timer(&mut self, env: &mut Env<'_, P>) {
        let now = env.now;
        let mut out = Outcome::default();
        let (streams, pool, ctl) = (&mut *self.streams, &mut self.pool, &mut self.ctl);
        let to = self.rec.on_timeout(now, |ev| apply(&ev, streams, pool, ctl, &mut out));
        self.after_feedback(out, now);
        if to.ping {
            self.life.probes = 1;
            self.stats.ptos += 1;
        }
        match self.rec.health(now) {
            Health::Dead => self.silent_close(CloseReason::PathDead),
            Health::Degraded if !self.degraded_told => {
                self.degraded_told = true;
                if let Some(id) = self.paths.active().map(|p| p.id) {
                    self.push(Ev::PathFailed(id));
                }
            }
            _ => {}
        }
        // The endpoint was told about the failing path above; now the connection leaves it.
        if self.rec.pto_count() >= PTO_FALLBACK {
            self.fail_over(env);
        }
    }
}
