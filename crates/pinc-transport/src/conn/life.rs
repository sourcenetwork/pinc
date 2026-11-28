//! The lifecycle: idle timeout, keepalive, close, sleep and wake, and link outages.
//!
//! Invariants: a connection ends exactly once and reports it with one [`Event::Closed`]; a local close or a violation
//! queues one CLOSE, which leaves with the next `poll_transmit`, and the state is freed (there is no closing or
//! draining wait); a `handle_timeout` that runs before that `poll_transmit` ends the connection without the CLOSE, so
//! at most one CLOSE is ever sent; a peer's CLOSE and every silent end (idle, dead path) send nothing. Any
//! authenticated packet from the peer that it has not received before ends its sleep; only a peer that announced
//! its sleep is held past the idle timeout, for 120 s, and the probe backoff does not grow while the peer sleeps or
//! the link is down.

use pinc_crypto::Provider;
use pinc_security::Env;

use super::config::IDLE_TIMEOUT;
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
/// For this long after a wake or a link return the probes carry WAKE too.
pub(crate) const WAKE_SPAN: u64 = 3 * SECOND;
/// For this long after a wake or a link return no path MTU probe is sent.
pub(crate) const QUIET_RESUME: u64 = 10 * SECOND;
/// A second WAKE within this long (or the smoothed round trip, if larger) of the last one is not acted on again.
const WAKE_DEDUP: u64 = 333 * MS;

/// Timers and flags of the lifecycle.
#[derive(Debug)]
#[allow(clippy::struct_excessive_bools, reason = "independent one-shot flags")]
pub(crate) struct Life {
    pub(crate) last_activity: u64,
    pub(crate) last_sent: u64,
    pub(crate) keepalive: Option<u64>,
    /// The code of the CLOSE to send, until it left.
    pub(crate) close: Option<u64>,
    pub(crate) peer_asleep: Option<u64>,
    pub(crate) local_asleep: Option<u64>,
    pub(crate) sleep_tx: u8,
    pub(crate) wake_tx: bool,
    pub(crate) wake_deadline: Option<u64>,
    /// Probes carry WAKE until this time.
    pub(crate) wake_until: u64,
    /// When the last received WAKE was acted on.
    pub(crate) wake_rx: Option<u64>,
    pub(crate) link_down: Option<u64>,
    /// No path MTU probe is sent before this time.
    pub(crate) qr_until: u64,
    pub(crate) probes: u8,
    /// A path that was abandoned validated again: its id and round trip, until the endpoint takes them.
    pub(crate) rejoined: Option<(super::PathId, u64)>,
    /// The last datagram only added a part to a handshake message and finished none.
    pub(crate) hs_part: bool,
    /// The last datagram was a part of the first message a responder already holds, again, or added no byte to the
    /// one it is still assembling.
    pub(crate) hs_repeat: bool,
    pub(crate) ping_owed: bool,
    /// An acknowledgement must leave in the next packet.
    pub(crate) ack_now: bool,
    /// The packet number of the last probe-timeout PING, while a black-hole check waits for its acknowledgement.
    pub(crate) small_ping: Option<u64>,
    /// The session counts as carrying application data until this time (the endpoint's last application activity,
    /// either way, plus 20 s); always, until the endpoint says ([`Connection::set_app_until`](super::Connection)).
    pub(crate) app_until: u64,
    /// When the application last wrote anything, and when it last wrote more than a control message.
    pub(crate) last_app: u64,
    pub(crate) last_data: u64,
    pub(crate) app_written: bool,
    pub(crate) data_written: bool,
    /// The packet the next tail repair re-carries.
    pub(crate) repair_pn: Option<u64>,
    /// The latest time any call carried; the path rules read it.
    pub(crate) clock: u64,
    /// When the carrier of the active relay path last heard anything, as the endpoint reports it.
    pub(crate) carrier_heard: Option<u64>,
    /// What the last recovery timer read to decide whether the session is closed behind a live carrier (trace only).
    #[cfg(feature = "trace")]
    pub(crate) carrier_probe: Option<super::timer::trace::CarrierView>,
}

impl Life {
    pub(crate) const fn new(now: u64) -> Self {
        Self {
            last_activity: now,
            last_sent: now,
            keepalive: None,
            close: None,
            peer_asleep: None,
            local_asleep: None,
            sleep_tx: 0,
            wake_tx: false,
            wake_deadline: None,
            wake_until: 0,
            wake_rx: None,
            link_down: None,
            qr_until: 0,
            probes: 0,
            rejoined: None,
            hs_part: false,
            hs_repeat: false,
            ping_owed: false,
            ack_now: false,
            small_ping: None,
            app_until: u64::MAX,
            last_app: 0,
            last_data: 0,
            app_written: false,
            data_written: false,
            repair_pn: None,
            clock: now,
            carrier_heard: None,
            #[cfg(feature = "trace")]
            carrier_probe: None,
        }
    }
}

conn_impl! {
    /// Close the connection with `error`. One CLOSE goes out with the next `poll_transmit` and the connection is
    /// over; nothing waits afterwards. Call `poll_transmit` before `handle_timeout`: the timer ends a closing
    /// connection, and a CLOSE that has not left by then is not sent.
    pub fn close(&mut self, env: &mut Env<'_, P>, lent: &mut super::Lent<'_, 'a>, error: u64) {
        self.with_lent(lent, |c| c.begin_close(env.now, error, CloseReason::Local { error }));
    }

    /// Set (or turn off) the keepalive interval: a PING goes out after this long without sending anything.
    pub fn set_keepalive(&mut self, interval: Option<u64>) {
        self.life.keepalive = interval;
        self.cfg.keepalive = interval;
    }

    /// Tell the peer this endpoint is about to sleep (SLEEP is sent twice). Until [`wake`](Self::wake) the
    /// connection stays open without probing.
    pub fn sleep(&mut self, env: &mut Env<'_, P>) {
        if self.phase != Phase::Connected || self.life.local_asleep.is_some() {
            return;
        }
        self.life.local_asleep = Some(env.now);
        self.life.sleep_tx = 2;
        self.suspend_probes();
    }

    /// Wake up: WAKE, a PING and an acknowledgement go out, everything in flight is declared lost without a
    /// congestion response and sent again, and the probes carry WAKE for 3 s. If nothing is heard within 800 ms,
    /// [`Event::WakeUnanswered`](super::Event::WakeUnanswered) is reported.
    pub fn wake(&mut self, env: &mut Env<'_, P>) {
        if self.phase != Phase::Connected || self.life.local_asleep.take().is_none() {
            return;
        }
        self.resume(env.now, true);
    }

    /// Send one acknowledgement-eliciting PING on the active path with the next packet.
    pub fn ping(&mut self) {
        if self.phase == Phase::Connected {
            self.life.ping_owed = true;
        }
    }

    /// The endpoint saw the network link go down (`true`) or come back (`false`). While it is down for up to 30 s the
    /// probe backoff does not grow and the connection does not give up; when it returns the connection resumes as
    /// after [`wake`](Self::wake), except that it does not report an unanswered wake after 800 ms.
    pub fn set_link_down(&mut self, env: &mut Env<'_, P>, down: bool) {
        if self.phase == Phase::Handshaking && !down {
            self.hs.link_return(env.now);
            return;
        }
        if self.phase != Phase::Connected {
            return;
        }
        if down {
            self.life.link_down.get_or_insert(env.now);
        } else if self.life.link_down.take().is_some() {
            self.resume(env.now, false);
        }
        self.suspend_probes();
    }

    /// The common part of a local wake and a link return. Only a wake from a suspension starts the wait for the peer's
    /// answer (800 ms): after a link return or an address change the answer may legitimately take longer than that,
    /// and a wait already running is left as it is.
    fn resume(&mut self, now: u64, suspended: bool) {
        self.life.wake_tx = true;
        self.life.ping_owed = true;
        self.life.ack_now = self.rx.ack_pending();
        if suspended {
            self.life.wake_deadline = Some(now.saturating_add(WAKE_WAIT));
        }
        self.life.wake_until = now.saturating_add(WAKE_SPAN);
        self.life.qr_until = now.saturating_add(QUIET_RESUME);
        self.life.last_activity = now;
        self.suspend_probes();
        self.flush_in_flight(now);
        self.mtu_event_all();
    }

    /// Whether the peer announced it sleeps.
    pub const fn peer_asleep(&self) -> bool {
        self.life.peer_asleep.is_some()
    }

    /// Whether this endpoint called [`sleep`](Self::sleep) and has not woken.
    pub const fn asleep(&self) -> bool {
        self.life.local_asleep.is_some()
    }

    pub(super) fn suspend_probes(&mut self) {
        self.rec.set_peer_asleep(self.life.peer_asleep.is_some() || self.life.local_asleep.is_some());
        self.rec.set_link_down(self.life.link_down.is_some());
    }

    /// Declare everything in flight lost with no congestion response and requeue it.
    pub(super) fn flush_in_flight(&mut self, now: u64) {
        let mut out = super::ctl::Outcome::default();
        let (streams, pool, ctl) = (&mut *self.streams, &mut self.pool, &mut self.ctl);
        self.rec.flush_in_flight(now, |ev| super::ctl::apply(&ev, streams, pool, ctl, &mut out));
        self.life.probes = 0;
        self.degraded_told = false;
        self.after_feedback(out, now);
    }

    /// Start closing with `error`: one CLOSE goes out when the next datagram is built, and the state is then freed.
    pub(super) fn begin_close(&mut self, now: u64, error: u64, reason: CloseReason) {
        let _ = now;
        if matches!(self.phase, Phase::Closing | Phase::Closed) {
            return;
        }
        let established = self.phase == Phase::Connected;
        self.release_buffers();
        self.life.close = Some(error);
        self.phase = if established && self.keys.send.is_some() { Phase::Closing } else { Phase::Closed };
        self.push(Ev::Closed(reason));
    }

    /// Close because a rule was broken.
    pub(super) fn violation(&mut self, now: u64, error: u64) {
        self.begin_close(now, error, CloseReason::Violation { error });
    }

    /// The peer sent CLOSE: the connection is over and nothing is sent.
    pub(super) fn on_peer_close(&mut self, error: u64) {
        if matches!(self.phase, Phase::Closed) {
            return;
        }
        self.release_buffers();
        self.life.close = None;
        self.phase = Phase::Closed;
        self.push(Ev::Closed(CloseReason::Peer { error }));
    }

    /// End without a CLOSE packet.
    pub(super) fn silent_close(&mut self, reason: CloseReason) {
        if matches!(self.phase, Phase::Closed) {
            return;
        }
        self.release_buffers();
        self.life.close = None;
        self.phase = Phase::Closed;
        self.push(Ev::Closed(reason));
    }

    fn release_buffers(&mut self) {
        self.streams.close_all(&mut self.pool);
        self.dgrams.clear(&mut self.pool);
        self.ext.clear(&mut self.pool);
        self.ctl.release_ext(&mut self.pool);
        self.early.clear(&mut self.pool);
    }

    /// The peer is heard: clear the wake wait.
    pub(super) fn note_heard(&mut self, now: u64) {
        self.life.last_activity = now;
        self.life.wake_deadline = None;
    }

    /// A WAKE arrived: act on it unless one was acted on within the last round trip. Returns whether it was acted on.
    pub(super) fn on_wake(&mut self, now: u64) -> bool {
        let gap = if self.rec.rtt().has_sample() { self.rec.rtt().smoothed() } else { WAKE_DEDUP };
        if self.life.wake_rx.is_some_and(|t| now.saturating_sub(t) <= gap) {
            return false;
        }
        self.life.wake_rx = Some(now);
        self.life.ack_now = true;
        self.flush_in_flight(now);
        true
    }

    /// The deadline after which silence closes the connection: 75 s after the last packet, or 120 s after the peer
    /// announced its sleep.
    pub(super) fn idle_deadline(&self) -> u64 {
        let base = self.life.last_activity.saturating_add(IDLE_TIMEOUT);
        match self.life.peer_asleep {
            Some(since) => base.max(since.saturating_add(SLEEP_HOLD)),
            None => base,
        }
    }

    /// Fold the application's writes since the last clock reading into the activity times: data above a control
    /// message after an idle spell re-challenges the paths that wait on the slow back-off.
    pub(super) fn apply_app_writes(&mut self, now: u64) {
        if self.life.app_written {
            self.life.app_written = false;
            self.life.last_app = now;
        }
        if self.life.data_written {
            self.life.data_written = false;
            self.data_seen(now);
        }
    }
}
