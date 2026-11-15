//! Connection events to endpoint events: establishment, closing and the application gate.
//!
//! The endpoint reads every event of a connection right after it changed. Transport events become [`Event`]s; the
//! ones that report application data (streams, datagrams) pass the access gate: they are emitted only once the peer's
//! access check allowed the session (and, on a client that waits for READY, once READY arrived), and are held in order
//! until then, 64 at most. A held read or write notification, which the application can recover by reading state, is
//! the only thing a full hold gives up. A hold full of anything else stalls the session: its events wait in the
//! connection and the packets that would raise more events are refused (acknowledgements and a close still get
//! through) until the answer comes. Establishment starts the access check and, on the
//! dialing side, the round trip notes; a close tells the application, orphans the unheard sub-sessions of the session
//! and, for a dial that timed out, raises the handshake floor.
//!
//! Extension frames: a `SUB_SESSION_OPEN` goes to the sub-session layer and a `REACH_OUT` to the reach ring whatever
//! the session's access state (neither carries application data; a sub-session's own data passes its own gate); any
//! other type goes to the application ring if the session may release. An empty `SUB_SESSION_OPEN` or `REACH_OUT`, a
//! `REACH_OUT` longer than the reach body limit, an empty body of any other type and any other type on a session that
//! may not release are dropped, and the connection stays open.
//!
//! Invariants: no application event (a stream, a datagram, an extension frame for the application ring) leaves
//! before the session is allowed or after a deny or a lapsed answer (one predicate, `may_release`, decides every
//! release); a denied session holds and delivers nothing; a session the
//! application never heard of produces no `Closed`; a dial the application asked for ends with `Connected` or `ConnectFailed` (or `Closed` after
//! an early `Connected`), never silently; a session is orphaned at most once; an event the application cannot recover
//! (a stream opened or reset, a datagram) is never dropped from the hold.

use vinc_security::TicketBatch;
use vinc_transport::conn::{CloseReason, Event as ConnEvent, PathId, code};
use vinc_transport::frame::ext;

use crate::acp::Release;
use crate::api::{ConnectFailure, EndReason, Event, PathState};
use crate::endpoint::{env, ep_impl};
use crate::slot::{HeldEvent, State};
use crate::trace::trace;

/// The largest extension body kept for the endpoint to parse.
const EXT_KEEP: usize = crate::ext_in::EXT_BODY_MAX;
/// The round trip below which a client waits for READY before it reports the session (20 ms).
const READY_RTT: u64 = 20_000_000;

/// A connection event with its borrowed data copied out.
#[derive(Clone, Copy)]
enum Co {
    KeyRequest,
    Connected(bool),
    Opened(u64),
    Readable(u64),
    Writable(u64),
    OpenReady,
    Reset(u64, u64),
    Stopped(u64, u64),
    Datagram,
    Extension { ty: u64, len: usize, body: [u8; EXT_KEEP] },
    Undeliverable(u64),
    Path(PathId, PathState),
    Asleep,
    Awake,
    WakeUnanswered,
    Tickets(TicketBatch),
    Ready,
    Closed(CloseReason),
}

ep_impl! {
    /// Read and handle every event session `i` has.
    pub(crate) fn drain(&mut self, i: usize, now: u64) {
        loop {
            // Back-pressure: leave the events in the connection until the host reads events (queue near full; the
            // session is parked and `resume_parked` takes it up again) or the session's held events drain.
            if self.events.stalled() {
                self.park(i);
                return;
            }
            let Some(slot) = self.slots.get_mut(i) else { return };
            if !slot.m.in_use {
                return;
            }
            // A session the application never heard of that ended needs its events read to be freed: its held ones go.
            let dead = !slot.m.allowed && slot.conn.as_ref().is_some_and(vinc_transport::conn::Connection::is_closed);
            if slot.m.held.stalled() && !dead {
                return;
            }
            let Some(conn) = slot.conn.as_mut() else { return };
            let Some(ev) = conn.poll_event() else { return };
            let co = match ev {
                ConnEvent::KeyRequest(_) => Co::KeyRequest,
                ConnEvent::Connected { resumed } => Co::Connected(resumed),
                ConnEvent::StreamOpened(id) => Co::Opened(id),
                ConnEvent::StreamReadable(id) => Co::Readable(id),
                ConnEvent::StreamWritable(id) => Co::Writable(id),
                ConnEvent::OpenReady => Co::OpenReady,
                ConnEvent::StreamReset { id, error } => Co::Reset(id, error),
                ConnEvent::StreamStopped { id, error } => Co::Stopped(id, error),
                ConnEvent::DatagramReceived => Co::Datagram,
                ConnEvent::Extension { ty, body } => {
                    let mut buf = [0u8; EXT_KEEP];
                    let len = body.len().min(EXT_KEEP);
                    if let (Some(d), Some(s)) = (buf.get_mut(..len), body.get(..len)) {
                        d.copy_from_slice(s);
                    }
                    Co::Extension { ty, len: if body.len() > EXT_KEEP { 0 } else { len }, body: buf }
                }
                ConnEvent::ExtensionUndeliverable { ty, .. } => Co::Undeliverable(ty),
                ConnEvent::PathValidated(p) => Co::Path(p, PathState::Validated),
                ConnEvent::PathFailed(p) => Co::Path(p, PathState::Failed),
                ConnEvent::PeerAsleep => Co::Asleep,
                ConnEvent::PeerAwake => Co::Awake,
                ConnEvent::WakeUnanswered => Co::WakeUnanswered,
                ConnEvent::TicketsReceived(b) => Co::Tickets(b),
                ConnEvent::Ready => Co::Ready,
                ConnEvent::Closed(r) => Co::Closed(r),
            };
            self.on_conn_event(i, now, co);
        }
    }

    #[allow(
        clippy::large_types_passed_by_value,
        reason = "the event carries a frame body inline so that nothing is allocated; it is moved once"
    )]
    fn on_conn_event(&mut self, i: usize, now: u64, co: Co) {
        let session = self.session_id(i);
        match co {
            Co::KeyRequest => self.emit(Event::KeyRequest { session }),
            Co::Connected(resumed) => self.on_established(i, now, resumed),
            Co::Opened(stream) => self.app_event(i, now, Event::StreamOpened { session, stream }),
            Co::Readable(stream) => {
                self.note_app_data(i, now);
                self.app_event(i, now, Event::StreamReadable { session, stream });
            }
            Co::Writable(stream) => self.app_event(i, now, Event::StreamWritable { session, stream }),
            Co::OpenReady => self.app_event(i, now, Event::OpenReady { session }),
            Co::Reset(stream, error) => self.app_event(i, now, Event::StreamReset { session, stream, error }),
            Co::Stopped(stream, error) => self.app_event(i, now, Event::StreamStopped { session, stream, error }),
            Co::Datagram => self.app_event(i, now, Event::DatagramReceived { session }),
            Co::Extension { ty, len, body } => {
                let body = body.get(..len).unwrap_or_default();
                if ty == ext::SUB_SESSION_OPEN && len > 0 {
                    self.sub_accept(i, now, body);
                } else if ty == ext::REACH_OUT && len > 0 && len <= crate::reach::REACH_BODY_MAX {
                    self.counters.reach_dropped += self.reach_in.put(session, body);
                    self.emit(Event::ReachOut { session });
                } else if ty == ext::REACH_OUT {
                    // A body that is empty or too long to keep is lost.
                    self.counters.reach_dropped += 1;
                } else if ty != ext::SUB_SESSION_OPEN
                    && ty != ext::REACH_OUT
                    && len > 0
                    && self.may_release(i, now)
                {
                    // A frame of a session the access check has not allowed is dropped (the branch above); the
                    // application protocols carry hints in extension frames and ask again. A body too long to keep
                    // is dropped too.
                    self.counters.ext_dropped += self.ext_in.put(session, ty, body).unwrap_or(1);
                }
            }
            Co::Undeliverable(ty) => {
                // A sub-session open that cannot be sent leaves its children unaccepted.
                if ty == ext::SUB_SESSION_OPEN {
                    self.orphan_children(i, now);
                }
            }
            Co::Path(path, state) => self.emit(Event::PathChanged { session, path, state }),
            Co::Asleep => self.emit(Event::PeerAsleep { session }),
            Co::Awake => self.emit(Event::PeerAwake { session }),
            Co::WakeUnanswered => self.redial(i, now),
            Co::Tickets(batch) => {
                if let Some(conn) = self.slots.get(i).and_then(|s| s.conn.as_ref()) {
                    conn.store_tickets(&mut self.tickets, &batch, now);
                }
                self.emit(Event::TicketsReceived { session, count: batch.entries().len() });
            }
            Co::Ready => self.on_ready(i, now),
            Co::Closed(reason) => self.on_closed(i, now, reason),
        }
    }

    /// Application data arrived: it counts as activity on a session that is not quiet. On a quiet session received
    /// data never arms the active keepalive: only the dialing side's own writes do.
    fn note_app_data(&mut self, i: usize, now: u64) {
        let Some(slot) = self.slots.get_mut(i) else { return };
        if !slot.m.role.quiet() {
            slot.m.last_app = now;
        }
    }

    /// An application event: emitted if the session is allowed and not waiting for READY, held otherwise.
    fn app_event(&mut self, i: usize, now: u64, ev: Event) {
        let Some(denied) = self.slots.get(i).map(|s| s.m.denied) else { return };
        // A denied session is closing: its data never reaches the application and is not held.
        if denied {
            return;
        }
        // An allowed session whose peer's answer lapsed holds its events and asks again: nothing leaves on an answer
        // that no longer stands. The cached answer is looked up once for both questions; after asking, the predicate
        // is asked afresh.
        let open = match self.release_state(i, now) {
            Release::Open => true,
            Release::Shut => false,
            Release::Lapsed => {
                self.ask_acp(i, now, true);
                self.may_release(i, now)
            }
        };
        let Some(slot) = self.slots.get_mut(i) else { return };
        // Behind earlier held events the new one waits too, so the order holds.
        if open && slot.m.hold != 2 && slot.m.held.len() == 0 {
            self.emit(ev);
            return;
        }
        if let Some(h) = HeldEvent::of(&ev) {
            slot.m.held.push(h);
            trace!(self, now, Gate { slot: i as u64, release: 0, held: slot.m.held.len() as u64 });
        }
    }

    /// Emit the held events of session `i` in the order they arrived.
    pub(crate) fn release_held(&mut self, i: usize, now: u64) {
        if !self.may_release(i, now) {
            return;
        }
        let session = self.session_id(i);
        trace!(self, now, Gate { slot: i as u64, release: 1, held: self.slots.get(i).map_or(0, |s| s.m.held.len()) as u64 });
        while !self.events.stalled() {
            let Some(h) = self.slots.get_mut(i).and_then(|s| s.m.held.pop()) else { return };
            self.emit(h.event(session));
        }
        if self.slots.get(i).is_some_and(|s| s.m.held.len() > 0) {
            self.park(i);
        }
    }

    /// Mark session `i` as having work left for [`resume_parked`](Self::resume_parked).
    fn park(&mut self, i: usize) {
        let Ok(id) = u32::try_from(i) else { return };
        if let (Some(flag), Some(cell)) = (self.is_parked.get_mut(i), self.parked.get_mut(self.parked_len))
            && !*flag
        {
            *flag = true;
            *cell = id;
            self.parked_len += 1;
        }
    }

    /// The host read events and the queue has room again: finish the work of the parked sessions, the held events
    /// of an allowed session first, until the queue is near full again. Costs one step per parked session.
    pub(crate) fn resume_parked(&mut self, now: u64) {
        while self.parked_len > 0 && !self.events.stalled() {
            self.parked_len -= 1;
            let i = self.parked.get(self.parked_len).map_or(0, |v| *v as usize);
            if let Some(flag) = self.is_parked.get_mut(i) {
                *flag = false;
            }
            if self.slots.get(i).is_some_and(|s| s.m.hold != 2) {
                self.release_held(i, now);
            }
            self.settle(i, now);
        }
    }

    /// The handshake completed.
    fn on_established(&mut self, i: usize, now: u64, resumed: bool) {
        let Some(slot) = self.slots.get_mut(i) else { return };
        let Some(conn) = slot.conn.as_mut() else { return };
        let Some((peer, alpn)) = conn.session().map(|e| (e.peer, e.alpn)) else { return };
        let stats = conn.stats();
        slot.m.peer = Some(peer);
        slot.m.alpn = Some(alpn);
        slot.m.state = State::Established;
        slot.m.resumed = resumed;
        let answered_now = slot.m.announced && !slot.m.answered;
        slot.m.answered |= answered_now;
        slot.m.last_app = now;
        if slot.m.unauth {
            slot.m.unauth = false;
            if slot.m.half_open {
                slot.m.half_open = false;
                self.half_open = self.half_open.saturating_sub(1);
            }
        }
        let client = slot.m.client;
        let sub = slot.m.sub;
        self.link_peer(peer, u32::try_from(i).unwrap_or(0));
        trace!(self, now, Session { slot: i as u64, step: 1, dialer: u64::from(client) });
        if answered_now {
            let session = self.session_id(i);
            self.emit(Event::Answered { session });
        }
        if sub {
            // A sub-session takes the access state of the peer; there was no handshake to measure.
            self.start_acp(i, now);
            return;
        }
        if client {
            if stats.handshake_retransmits == 0 && stats.srtt > 0 {
                self.rtt.note_handshake(peer, stats.srtt);
                self.node_ver += 1;
                trace!(self, now, Rtt {
                    lrtt: self.rtt.lrtt(),
                    tgr: self.rtt.tgr(),
                    hs_floor: self.rtt.hs_floor(),
                });
            }
            if !resumed && let Some(pk) = self.prekey.as_ref() {
                self.ekk.insert(peer, *pk.hash());
            }
            if let Some(slot) = self.slots.get_mut(i) {
                if stats.srtt > 0 && stats.srtt < READY_RTT {
                    slot.m.hold = 1;
                }
                if let Some(conn) = slot.conn.as_mut() {
                    let mut env = env!(self, now);
                    // The responder keeps one ticket of ours so it can dial back with a resumption.
                    let _ = conn.issue_tickets(&mut env, &mut self.stores.tickets, 1, self.cfg.ticket_lifetime_s);
                }
            }
        }
        self.start_acp(i, now);
    }

    /// The peer sent READY: the server's access answer is in.
    fn on_ready(&mut self, i: usize, now: u64) {
        let Some(slot) = self.slots.get_mut(i) else { return };
        if !slot.m.client {
            return;
        }
        match slot.m.hold {
            2 => {
                slot.m.hold = 0;
                let report = !slot.m.optimistic && slot.m.state == State::Established;
                trace!(self, now, Early { slot: i as u64, rule: 2 });
                if report {
                    self.announce(i);
                }
                self.release_held(i, now);
            }
            1 => slot.m.hold = 3,
            _ => {}
        }
    }

    /// Tell the application a dialed session is open.
    pub(crate) fn announce(&mut self, i: usize) {
        let session = self.session_id(i);
        let Some(slot) = self.slots.get_mut(i) else { return };
        let (Some(node), Some(alpn)) = (slot.m.peer, slot.m.alpn) else { return };
        slot.m.announced = true;
        // A dial reported after its handshake heard the peer; an optimistic one and a sub-session have not yet.
        slot.m.answered =
            (!slot.m.optimistic && !slot.m.sub) || slot.conn.as_ref().is_some_and(|c| c.recovery().last_heard() > 0);
        let resumed = slot.m.resumed;
        self.emit(Event::Connected { session, node, alpn, resumed });
    }

    /// A connection ended.
    fn on_closed(&mut self, i: usize, now: u64, reason: CloseReason) {
        let session = self.session_id(i);
        let Some(slot) = self.slots.get_mut(i) else { return };
        // Closed follows a Connected or Incoming; a dial that ended before it was reported fails instead. A session
        // allowed while it waited for its peer's READY was not reported yet.
        let was_visible = slot.m.announced;
        let (client, denied, orphaned, redial) = (slot.m.client, slot.m.denied, slot.m.orphaned, slot.m.redial);
        let (node, alpn) = (slot.m.peer, slot.m.alpn);
        let has_sub = slot.m.has_sub;
        slot.m.state = State::Closing;
        slot.m.held.clear();
        slot.m.acp_recheck = None;
        if was_visible {
            let why = if denied {
                EndReason::Denied
            } else if orphaned {
                EndReason::Orphaned
            } else if redial {
                EndReason::Redial
            } else {
                EndReason::Transport(reason)
            };
            self.emit(Event::Closed { session, reason: why });
        } else if client && !denied && let (Some(node), Some(alpn)) = (node, alpn) {
            self.emit(Event::ConnectFailed {
                session: Some(session),
                node,
                alpn,
                reason: failure_of(reason),
            });
        }
        if client && matches!(reason, CloseReason::HandshakeTimeout) {
            self.rtt.note_timeout();
            self.node_ver += 1;
        }
        if has_sub {
            self.orphan_children(i, now);
        }
    }

    /// Close the sessions opened over session `i` that never heard their peer.
    fn orphan_children(&mut self, parent: usize, now: u64) {
        let Some(peer) = self.slots.get(parent).and_then(|s| s.m.peer) else { return };
        let pid = self.session_id(parent);
        while let Some(c) = self.peer_find(&peer, |e, c| {
            e.slots.get(c).is_some_and(|s| {
                s.m.parent == Some(pid)
                    && !s.m.orphaned
                    && (s.m.waiting
                        || (s.m.state == State::Established
                            && s.conn.as_ref().is_some_and(|k| k.stats().packets_received == 0)))
            })
        }) {
            trace!(self, now, Sub { step: 2, parent: parent as u64, child: c as u64 });
            if let Some(s) = self.slots.get_mut(c) {
                s.m.orphaned = true;
                if let Some(conn) = s.conn.as_mut() {
                    let mut env = env!(self, now);
                    conn.close(&mut env, code::NO_ERROR);
                }
            }
            self.settle(c, now);
        }
    }

    /// Close session `i` so the application dials again at once.
    pub(crate) fn redial(&mut self, i: usize, now: u64) {
        if let Some(s) = self.slots.get_mut(i) {
            s.m.redial = true;
            if let Some(conn) = s.conn.as_mut() {
                let mut env = env!(self, now);
                conn.close(&mut env, code::NO_ERROR);
            }
        }
        self.settle(i, now);
    }
}

/// How a dial that never opened is reported.
const fn failure_of(reason: CloseReason) -> ConnectFailure {
    match reason {
        CloseReason::HandshakeTimeout | CloseReason::Unanswered | CloseReason::Unconfirmed => ConnectFailure::Timeout,
        CloseReason::Handshake(f) => ConnectFailure::Handshake(f),
        _ => ConnectFailure::Closed,
    }
}
