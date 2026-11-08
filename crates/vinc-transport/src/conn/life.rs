//! The lifecycle: idle timeout, keepalive, close and drain, sleep and wake, and link outages.
//!
//! Invariants: a connection ends exactly once and reports it with one [`Event::Closed`]; after a local close or a
//! violation it answers packets with CLOSE for three probe timeouts, after a peer's CLOSE it only waits (draining);
//! a silent end (idle, stateless reset, dead path) sends nothing. While the peer sleeps or the link is down the probe
//! backoff does not grow and the connection does not give up: a sleeping peer is held for 120 s, a down link for 30 s.

use vinc_crypto::Provider;
use vinc_security::Env;

use super::config::DRAIN_PTOS;
use super::event::{CloseReason, Ev};
use super::{Connection, Phase};
use crate::recovery::{MS, SECOND};
use crate::stream::StreamSource;

/// How long the context of a sleeping peer is held.
pub(crate) const SLEEP_HOLD: u64 = 120 * SECOND;
/// How long a WAKE waits for any answer.
pub(crate) const WAKE_WAIT: u64 = 800 * MS;
/// How long a link outage freezes the probe backoff.
pub(crate) const LINK_DOWN_MAX: u64 = 30 * SECOND;
/// CLOSE replies sent to a peer that keeps talking after we closed.
const CLOSE_REPLIES: u8 = 8;

/// The frame a closing connection sends.
#[derive(Debug, Clone, Copy)]
pub(crate) struct CloseFrame {
    pub(crate) app: bool,
    pub(crate) error: u64,
    pub(crate) reason: &'static str,
}

/// Timers and flags of the lifecycle.
#[derive(Debug)]
#[allow(clippy::struct_excessive_bools, reason = "independent one-shot flags")]
pub(crate) struct Life {
    pub(crate) last_activity: u64,
    pub(crate) last_sent: u64,
    pub(crate) keepalive: Option<u64>,
    pub(crate) close: Option<CloseFrame>,
    pub(crate) close_until: u64,
    pub(crate) close_owed: bool,
    pub(crate) close_replies: u8,
    pub(crate) peer_asleep: Option<u64>,
    pub(crate) local_asleep: Option<u64>,
    pub(crate) sleep_tx: u8,
    pub(crate) wake_tx: bool,
    pub(crate) wake_deadline: Option<u64>,
    pub(crate) link_down: Option<u64>,
    pub(crate) probes: u8,
    pub(crate) ping_owed: bool,
    pub(crate) repair_at: Option<u64>,
    pub(crate) repair_due: bool,
    pub(crate) last_stream_tx: u64,
    pub(crate) ack_only_run: u8,
    pub(crate) tail: [Option<(u64, u64, u32, bool)>; 4],
}

impl Life {
    pub(crate) const fn new(now: u64) -> Self {
        Self {
            last_activity: now,
            last_sent: now,
            keepalive: None,
            close: None,
            close_until: 0,
            close_owed: false,
            close_replies: 0,
            peer_asleep: None,
            local_asleep: None,
            sleep_tx: 0,
            wake_tx: false,
            wake_deadline: None,
            link_down: None,
            probes: 0,
            ping_owed: false,
            repair_at: None,
            repair_due: false,
            last_stream_tx: 0,
            ack_only_run: 0,
            tail: [None; 4],
        }
    }
}

conn_impl! {
    /// Close the connection with an application error code and a short reason. A CLOSE goes out and the connection
    /// drains for three probe timeouts.
    pub fn close(&mut self, env: &mut Env<'_, P>, error: u64, reason: &'static str) {
        self.begin_close(env.now, CloseFrame { app: true, error, reason }, CloseReason::Local { error });
    }

    /// Set (or turn off) the keepalive interval: a PING goes out after this long without sending anything.
    pub fn set_keepalive(&mut self, interval: Option<u64>) {
        self.life.keepalive = interval;
        self.cfg.keepalive = interval;
    }

    /// Tell the peer this endpoint is about to sleep (SLEEP is sent twice). Until [`wake`](Self::wake) the
    /// connection stays open without probing, for up to 120 s.
    pub fn sleep(&mut self, env: &mut Env<'_, P>) {
        if self.phase != Phase::Connected || self.life.local_asleep.is_some() {
            return;
        }
        self.life.local_asleep = Some(env.now);
        self.life.sleep_tx = 2;
        self.suspend_probes();
    }

    /// Wake up: WAKE and a PING go out, everything in flight is declared lost without a congestion response and
    /// sent again. If nothing is heard within 800 ms, [`Event::WakeUnanswered`](super::Event::WakeUnanswered) is reported.
    pub fn wake(&mut self, env: &mut Env<'_, P>) {
        if self.phase != Phase::Connected || self.life.local_asleep.take().is_none() {
            return;
        }
        self.life.wake_tx = true;
        self.life.ping_owed = true;
        self.life.wake_deadline = Some(env.now.saturating_add(WAKE_WAIT));
        self.life.last_activity = env.now;
        self.suspend_probes();
        self.flush_in_flight(env.now);
    }

    /// The endpoint saw the network link go down (`true`) or come back (`false`). While it is down for up to 30 s the
    /// probe backoff does not grow and the connection does not give up; when it returns, everything in flight is
    /// sent again without a congestion response.
    pub fn set_link_down(&mut self, env: &mut Env<'_, P>, down: bool) {
        if self.phase != Phase::Connected {
            return;
        }
        if down {
            self.life.link_down.get_or_insert(env.now);
        } else if self.life.link_down.take().is_some() {
            self.life.last_activity = env.now;
            self.flush_in_flight(env.now);
        }
        self.suspend_probes();
    }

    /// Whether the peer announced it sleeps.
    pub const fn peer_asleep(&self) -> bool {
        self.life.peer_asleep.is_some()
    }

    /// Whether this endpoint called [`sleep`](Self::sleep) and has not woken.
    pub const fn asleep(&self) -> bool {
        self.life.local_asleep.is_some()
    }

    /// Whether probe timeouts are frozen: the peer or this endpoint sleeps, or the link is down.
    pub(super) const fn suspended(&self) -> bool {
        self.life.peer_asleep.is_some() || self.life.local_asleep.is_some() || self.life.link_down.is_some()
    }

    pub(super) fn suspend_probes(&mut self) {
        self.rec.set_peer_asleep(self.suspended());
    }

    /// Declare everything in flight lost with no congestion response and requeue it.
    pub(super) fn flush_in_flight(&mut self, now: u64) {
        let mut out = super::ctl::Outcome::default();
        let (streams, pool, ctl, cids, rx) = (&mut *self.streams, &mut self.pool, &mut self.ctl, &mut self.cids, &mut self.rx);
        self.rec.flush_in_flight(now, |ev| super::ctl::apply(&ev, now, streams, pool, ctl, cids, rx, &mut out));
        self.life.probes = 0;
        self.degraded_told = false;
        self.after_feedback(out, now);
    }

    /// Start closing with `frame`: a CLOSE goes out, then three probe timeouts of waiting.
    pub(super) fn begin_close(&mut self, now: u64, frame: CloseFrame, reason: CloseReason) {
        if matches!(self.phase, Phase::Closing | Phase::Draining | Phase::Closed) {
            return;
        }
        let established = self.phase == Phase::Connected;
        self.release_buffers();
        self.life.close = Some(frame);
        self.life.close_owed = true;
        self.life.close_until = now.saturating_add(self.rec.pto_duration().saturating_mul(DRAIN_PTOS));
        self.phase = if established && self.keys.send.is_some() { Phase::Closing } else { Phase::Closed };
        self.push(Ev::Closed(reason));
    }

    /// Close because a rule was broken.
    pub(super) fn violation(&mut self, now: u64, error: u64, reason: &'static str) {
        self.begin_close(now, CloseFrame { app: false, error, reason }, CloseReason::Violation { error });
    }

    /// The peer sent CLOSE: drain without sending.
    pub(super) fn on_peer_close(&mut self, now: u64, app: bool, error: u64) {
        if matches!(self.phase, Phase::Draining | Phase::Closed) {
            return;
        }
        self.release_buffers();
        self.life.close_until = now.saturating_add(self.rec.pto_duration().saturating_mul(DRAIN_PTOS));
        self.life.close_owed = false;
        self.phase = Phase::Draining;
        let reason = if app { CloseReason::PeerApplication { error } } else { CloseReason::PeerTransport { error } };
        self.push(Ev::Closed(reason));
    }

    /// End without a CLOSE packet.
    pub(super) fn silent_close(&mut self, reason: CloseReason) {
        if matches!(self.phase, Phase::Closed) {
            return;
        }
        self.release_buffers();
        self.phase = Phase::Closed;
        self.push(Ev::Closed(reason));
    }

    fn release_buffers(&mut self) {
        self.streams.close_all(&mut self.pool);
        self.dgrams.clear(&mut self.pool);
        self.ext.clear(&mut self.pool);
        self.early.clear(&mut self.pool);
    }

    /// A packet arrived while closing: owe another CLOSE, within a bound.
    pub(super) fn on_packet_while_closing(&mut self) {
        if self.life.close_replies < CLOSE_REPLIES {
            self.life.close_replies += 1;
            self.life.close_owed = true;
        }
    }

    /// The peer is heard: clear the wake wait, and its sleep if it was only that.
    pub(super) fn note_heard(&mut self, now: u64) {
        self.life.last_activity = now;
        self.life.wake_deadline = None;
    }

    /// The deadline after which silence closes the connection.
    pub(super) fn idle_deadline(&self) -> u64 {
        let base = self.life.last_activity.saturating_add(self.cfg.idle_timeout);
        match self.life.peer_asleep.into_iter().chain(self.life.local_asleep).chain(self.life.link_down).min() {
            Some(since) => base.max(since.saturating_add(SLEEP_HOLD)),
            None => base,
        }
    }

}
