//! Timers: when the connection next needs attention, and what to do when that time comes.
//!
//! Invariants: a timer is reported only while it can still act (a stale deadline would make a driver spin); the
//! recovery timer keeps running while the peer sleeps or the link is down (it declares the oldest packet lost and
//! pings, without growing the count); a connection that is closing ends at its next timer. A session on a relay path
//! is closed, with a CLOSE, at a probe timeout once 4 have fired in a row, it heard nothing for 4 round trips and the
//! relay's carrier was heard within 6 s: the carrier works, so the peer no longer holds the session, and the layers
//! above dial again instead of waiting for the probes to give up.

use pinc_crypto::Provider;
use pinc_security::Env;

use super::ctl::{Outcome, apply};
use super::event::{CloseReason, Ev};
use super::life::LINK_DOWN_MAX;
use super::path::PTO_FALLBACK;
use super::{Connection, Phase};
use crate::recovery::{Health, INITIAL_RTT, PathKind, SECOND, deadline_after};
use crate::stream::StreamSource;

/// Probe timeouts in a row on a relay path whose carrier answers after which the session is closed.
const CLOSE_AFTER_PTOS: u32 = 4;
/// A carrier heard within this long answers.
const CARRIER_FRESH: u64 = 6 * SECOND;
/// The session must also have heard nothing for this many round trips.
const SILENT_RTTS: u64 = 4;

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
        // The request is a control frame: with no room to write one, its deadline would stay due and wake the host
        // for nothing. An acknowledgement that frees a slot wakes it, and the deadline, by then past, is offered again.
        if self.rekey_room(self.paths.active) {
            add(self.rekey_deadline());
        }
        add(self.rec.next_timeout());
        if self.ack_room(self.paths.active) {
            add(self.rx.ack_deadline());
        }
        add(self.paced_until);
        add(self.path_deadline());
        add(self.life.wake_deadline);
        add(self.life.link_down.map(|s| s.saturating_add(LINK_DOWN_MAX)));
        if self.phase == Phase::Connected {
            // The PING is a forced packet, written only with room in the ring like any control frame.
            if self.keepalive_room(self.paths.active) {
                add(self.life.keepalive.and_then(|k| deadline_after(self.life.last_sent, k)));
            }
            add(self.mtu_deadline());
        }
        Some(t)
    }

    /// Run whatever timer expired: the handshake retransmit, loss detection and probes, path challenges, the wake
    /// wait, the idle timeout and the end of a close.
    pub fn handle_timeout(&mut self, env: &mut Env<'_, P>, lent: &mut super::Lent<'_, 'a>) {
        self.with_lent(lent, |c| c.handle_timeout_inner(env));
    }

    fn handle_timeout_inner(&mut self, env: &mut Env<'_, P>) {
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
            // The one resend of a resume Hello takes the early data in flight with it: what left with the first
            // flight goes again behind it, not a round trip after the handshake, when loss detection would find it.
            // The send after it is a full handshake, which has no early data.
            if self.stats.handshake_retransmits == 1 && self.early_client() {
                self.flush_in_flight(now);
            }
            self.pump(env);
        }
        if self.life.link_down.is_some_and(|s| s.saturating_add(LINK_DOWN_MAX) <= now) {
            self.life.link_down = None;
            self.suspend_probes();
        }
        self.apply_app_writes(now);
        self.run_recovery_timer(env);
        self.mtu_black_hole_check(now);
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
        #[cfg(feature = "trace")]
        {
            self.life.carrier_probe = Some(self.trace_carrier(now, to.ping));
        }
        match self.rec.health(now) {
            Health::Dead => self.silent_close(CloseReason::PathDead),
            _ if to.ping && self.dead_behind_live_carrier(now) => {
                self.begin_close(now, 0, CloseReason::PathDead);
                return;
            }
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

    /// Probe timeouts keep firing on a relay path whose carrier answers: 4 in a row, nothing heard for 4 round trips
    /// (before a sample, of `max(333 ms, 2 x the node's longest round trip)`), and the carrier heard within 6 s.
    fn dead_behind_live_carrier(&self, now: u64) -> bool {
        let relay = self.paths.active().is_some_and(|p| p.info.kind == PathKind::Relay);
        let alive = self.life.carrier_heard.is_some_and(|h| now.saturating_sub(h) < CARRIER_FRESH);
        let rtt = if self.rec.rtt().has_sample() {
            self.rec.rtt().smoothed()
        } else {
            let node = self.cfg.node_rtt.unwrap_or(0).max(self.cfg.node_peak_rtt.unwrap_or(0));
            INITIAL_RTT.max(node.saturating_mul(2))
        };
        relay
            && alive
            && self.rec.pto_count() >= CLOSE_AFTER_PTOS
            && now.saturating_sub(self.rec.last_heard()) >= rtt.saturating_mul(SILENT_RTTS)
    }
}

/// Test-only view of the timers and the closing state, for trace validation (cargo feature `trace`, off by default).
#[cfg(feature = "trace")]
pub(super) mod trace {
    use pinc_crypto::Provider;

    use super::super::{Connection, Phase};
    use crate::recovery::{Health, PathKind};
    use crate::stream::StreamSource;

    /// The lifecycle state of a connection and every deadline [`Connection::poll_timeout`] combines, as it reads them.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[allow(clippy::struct_excessive_bools, reason = "independent flags of the view")]
    pub struct TimerView {
        /// 0 handshaking, 1 connected, 2 closing (the CLOSE still to leave), 3 closed.
        pub phase: u8,
        /// The code of the CLOSE to send, until it left.
        pub close: Option<u64>,
        /// Whether the 1-RTT sending keys are installed.
        pub send_keys: bool,
        /// When the peer was last heard (or the connection last resumed).
        pub last_activity: u64,
        /// When a datagram last left.
        pub last_sent: u64,
        /// The keepalive interval.
        pub keepalive: Option<u64>,
        /// Since when the peer announced it sleeps.
        pub peer_asleep: Option<u64>,
        /// Whether this endpoint sleeps.
        pub local_asleep: bool,
        /// SLEEP frames still to send.
        pub sleep_tx: u8,
        /// When an unanswered WAKE is reported.
        pub wake_deadline: Option<u64>,
        /// Since when the link is down.
        pub link_down: Option<u64>,
        /// The deadline after which silence closes the connection.
        pub idle: u64,
        /// Whether the handshake is confirmed (its retransmit timer is then not read).
        pub confirmed: bool,
        /// The handshake retransmit (or give-up) deadline.
        pub hs: Option<u64>,
        /// When the pending REKEY request is sent again.
        pub rekey: Option<u64>,
        /// Loss recovery: the loss time or the probe timeout.
        pub rec: Option<u64>,
        /// When the acknowledgement is due.
        pub ack: Option<u64>,
        /// Whether the acknowledgement due can leave on the active path (the acknowledgement deadline is read only then).
        pub amp_ok: bool,
        /// Whether the REKEY resend may be offered: a REKEY datagram can leave on the active path.
        pub rr: bool,
        /// Whether the keepalive may be offered: a PING datagram can leave on the active path.
        pub kr: bool,
        /// When the pacer releases the data that waits.
        pub paced: Option<u64>,
        /// The earliest path deadline: a probe of an unvalidated path, the idle-out of a validated direct one.
        pub path: Option<u64>,
        /// The earliest path MTU deadline: a probe retry or a black-hole suspicion.
        pub mtu: Option<u64>,
    }

    /// What the recovery timer reads at a call of `handle_timeout` to decide a close behind a live carrier, as it reads
    /// it: the probe timeout that fired, whether the path is dead, the active path is a relay path, when its carrier
    /// was heard, the probe timeouts in a row, when the peer was last heard, whether the round trip has a sample and
    /// its smoothed value, and the node's longest round trip.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[allow(clippy::struct_excessive_bools, reason = "independent flags of the view")]
    pub struct CarrierView {
        /// A probe timeout fired in this call.
        pub ping: bool,
        /// The path is dead (the connection ends silently).
        pub dead: bool,
        /// The active path is a relay path.
        pub relay: bool,
        /// When the relay's carrier last heard anything.
        pub carrier: Option<u64>,
        /// Probe timeouts in a row.
        pub ptos: u32,
        /// When the peer was last heard.
        pub heard: u64,
        /// The round trip has a sample.
        pub sampled: bool,
        /// The smoothed round trip.
        pub srtt: u64,
        /// The node's longest round trip (the larger of the two the endpoint reports, 0 for none).
        pub node: u64,
    }

    /// The Finish resend state of a dialing handshake (cargo feature `trace`).
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct FinishView {
        /// The handshake is a dialer's in its Finish stage.
        pub finish: bool,
        /// The flights sent so far, the Finish's resends included.
        pub sends: u32,
        /// The first wait before the Finish is resent (ns).
        pub first: u64,
        /// The next resend (ns).
        pub retx_at: Option<u64>,
        /// The node is thin.
        pub thin: bool,
        /// The round trip a thin node waits on (ns).
        pub rtt: u64,
        /// The probe timeout `finish_sent` was given (ns), 0 before.
        pub pto: u64,
    }

    conn_impl! {
        /// The Finish resend state of the handshake.
        pub fn trace_finish(&self) -> FinishView {
            self.hs.finish_view()
        }

        /// What the last recovery timer read for the carrier rule, taken: `None` when no recovery timer ran since.
        pub fn trace_carrier_take(&mut self) -> Option<CarrierView> {
            self.life.carrier_probe.take()
        }

        pub(super) fn trace_carrier(&self, now: u64, ping: bool) -> CarrierView {
            CarrierView {
                ping,
                dead: matches!(self.rec.health(now), Health::Dead),
                relay: self.paths.active().is_some_and(|p| p.info.kind == PathKind::Relay),
                carrier: self.life.carrier_heard,
                ptos: self.rec.pto_count(),
                heard: self.rec.last_heard(),
                sampled: self.rec.rtt().has_sample(),
                srtt: self.rec.rtt().smoothed(),
                node: self.cfg.node_rtt.unwrap_or(0).max(self.cfg.node_peak_rtt.unwrap_or(0)),
            }
        }

        /// The timers and the closing state as [`poll_timeout`](Self::poll_timeout) reads them.
        pub fn trace_timers(&self) -> TimerView {
            TimerView {
                phase: match self.phase {
                    Phase::Handshaking => 0,
                    Phase::Connected => 1,
                    Phase::Closing => 2,
                    Phase::Closed => 3,
                },
                close: self.life.close,
                send_keys: self.keys.send.is_some(),
                last_activity: self.life.last_activity,
                last_sent: self.life.last_sent,
                keepalive: self.life.keepalive,
                peer_asleep: self.life.peer_asleep,
                local_asleep: self.life.local_asleep.is_some(),
                sleep_tx: self.life.sleep_tx,
                wake_deadline: self.life.wake_deadline,
                link_down: self.life.link_down,
                idle: self.idle_deadline(),
                confirmed: self.confirmed,
                hs: self.hs.retransmit_at(),
                rekey: self.rekey_deadline(),
                rec: self.rec.next_timeout(),
                ack: self.rx.ack_deadline(),
                amp_ok: self.ack_room(self.paths.active),
                rr: self.rekey_room(self.paths.active),
                kr: self.keepalive_room(self.paths.active),
                paced: self.paced_until,
                path: self.path_deadline(),
                mtu: self.mtu_deadline(),
            }
        }
    }
}
