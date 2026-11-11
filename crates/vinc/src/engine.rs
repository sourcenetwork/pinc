//! The core: the SANS-IO endpoint plus everything a host does for it, with no socket, no clock and no thread of its own.
//!
//! The futures of the facade lock the core for short, non-waiting sections: they feed it datagrams and the time, run
//! commands for the handles, read stream bytes straight out of the endpoint into the caller's buffer, and send what it
//! wants to send. The core answers key requests and access checks, keeps the session table, the accept queues, the
//! dials and the lists of futures waiting on a stream, a session or a queue, and wakes exactly those when an event
//! changes what they wait for. There are no channels and no copies of stream bytes beyond the one into the caller's
//! buffer.
//!
//! Invariants: a lock is never held across an await; a pending dial is answered at most once; a session leaves the
//! table exactly when the endpoint reports it closed, and every future waiting on it is woken with its reason; a table
//! holds an entry only while its session or stream lives, so nothing grows with history; per-poll work is proportional
//! to what changed, never to a table's capacity.

use std::cell::OnceCell;
use std::collections::VecDeque;
use std::net::SocketAddr;
use std::rc::Rc;

use rapidhash::RapidHashMap;
use vinc_core::{Answer, Command, CommandError, Event, IfaceId, Query, SessionId, Value};
use vinc_crypto::NodeId;
use vinc_keystore::KeyStore;
use vinc_node::NodeEvent;
use vinc_security::{Alpn, KeyRequest, KeyResponse};
use vinc_transport::stream::{NoSource, RecvStatus, StreamId, is_uni};

use crate::error::{Error, ErrorKind, Result};
use crate::keys::{Identity, Prekeys, is_identity};
use crate::mem::Limits;
use crate::node::FacadeNode;
use crate::standby::{Standby, Ticket};

mod gate;
mod ops;

pub use gate::AllowAll;
pub(crate) use gate::Gate;
pub use gate::{Admit, DENIED, Direction, REVOKED_MAX};

/// The close code sent for a session or stream refused because a queue was full.
pub const BUSY: u64 = 0x42;
/// How long a shutdown waits for the CLOSE packets to leave.
const SHUTDOWN_GRACE: u64 = 1_000_000_000;
/// The most events one [`Core::service`] call handles before it returns, so transmit and receive are not starved.
const BUDGET: usize = 4096;
/// The most stopped streams of a session remembered for their writers, and discarded streams tracked.
const TRACKED: usize = 128;

/// What a core is built from.
pub(crate) struct CoreConfig<S, A> {
    /// The node's identity.
    pub identity: Identity<S>,
    /// The protocols served; at most [`MAX_ALPNS`] with those added later.
    pub alpns: Vec<Vec<u8>>,
    /// The sizes.
    pub limits: Limits,
    /// The access hook.
    pub admit: A,
    /// The most same-size datagrams one transmit batches (1 turns batching off).
    pub max_gso: usize,
    /// The largest datagram the host's socket can send.
    pub mtu: u16,
    /// The local addresses datagrams are sent from and received on.
    pub locals: Vec<SocketAddr>,
}

/// What both the core and the handles of a session read.
#[derive(Debug)]
pub(crate) struct SessInfo {
    pub id: SessionId,
    pub node: NodeId,
    pub alpn: Alpn,
    pub dialer: bool,
    /// Why the session ended, set once when it leaves the table.
    pub ended: OnceCell<Error>,
}

impl SessInfo {
    /// The error an operation on an ended session returns.
    pub(crate) fn gone(&self) -> Error {
        self.ended.get().copied().unwrap_or_else(Error::shutdown)
    }
}

/// What a future waits for on a session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SKey {
    AcceptBi,
    AcceptUni,
    Datagram,
    Closed,
    Open,
    Read(StreamId),
    Write(StreamId),
}

/// What a future waits for outside any session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GKey {
    Dial(SessionId),
    Route(usize),
    Shutdown,
    Idle,
}

/// A wait a future registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Wait {
    S(SessionId, SKey),
    G(GKey),
}

/// The outcome of one attempt at an operation.
pub(crate) enum Try<T> {
    Done(T),
    Wait(Wait),
}

struct Sess {
    info: Rc<SessInfo>,
    accept_bi: VecDeque<StreamId>,
    accept_uni: VecDeque<StreamId>,
    waits: Vec<(SKey, Ticket)>,
    /// Streams the peer stopped or this side reset: the error their writer sees.
    send_fail: Vec<(StreamId, Error)>,
    /// Streams the application dropped or refused: what arrives on them is thrown away until they end.
    discard: Vec<StreamId>,
}

struct Dial {
    node: NodeId,
    alpn: Alpn,
    result: Option<Result<Rc<SessInfo>>>,
}

struct Route {
    alpn: Vec<u8>,
    queue: VecDeque<Rc<SessInfo>>,
}

/// The core; see the module docs.
pub(crate) struct Core<S, A> {
    pub(crate) node: Box<FacadeNode>,
    identity: Identity<S>,
    prekeys: Prekeys,
    /// The access hook, shared with the endpoint's handles so they can ask it without borrowing the core.
    admit: Rc<Gate<A>>,
    pub(crate) limits: Limits,
    sessions: RapidHashMap<SessionId, Sess>,
    dials: RapidHashMap<SessionId, Dial>,
    dial_by_peer: RapidHashMap<(NodeId, Alpn), SessionId>,
    /// The accept queues: the first takes every protocol no registered one claims.
    routes: Vec<Route>,
    book: RapidHashMap<NodeId, Vec<SocketAddr>>,
    ifaces: Vec<IfaceId>,
    shutdown: Option<u64>,
    stopped: Option<Error>,
    last_dropped: u64,
    draining: bool,
    /// A command ran that may have queued something to send.
    dirty: bool,
    gwaits: Vec<(GKey, Ticket)>,
    pub(crate) standby: Standby,
    /// The ticket of the future that drives, and the deadline it sleeps for.
    pub(crate) driver: Option<Ticket>,
    pub(crate) armed: u64,
}

impl<S: KeyStore, A: Admit> Core<S, A> {
    /// A core over `node`, whose endpoint already holds the prekey, the protocols and the interfaces `ifaces`.
    pub(crate) fn new(node: Box<FacadeNode>, cfg: CoreConfig<S, A>, prekeys: Prekeys, ifaces: Vec<IfaceId>) -> Self {
        Self {
            node,
            identity: cfg.identity,
            prekeys,
            admit: Rc::new(Gate::new(cfg.admit)),
            limits: cfg.limits,
            sessions: RapidHashMap::default(),
            dials: RapidHashMap::default(),
            dial_by_peer: RapidHashMap::default(),
            routes: vec![Route {
                alpn: Vec::new(),
                queue: VecDeque::new(),
            }],
            book: RapidHashMap::default(),
            ifaces,
            shutdown: None,
            stopped: None,
            last_dropped: 0,
            draining: false,
            dirty: false,
            gwaits: Vec::new(),
            standby: Standby::default(),
            driver: None,
            armed: u64::MAX,
        }
    }

    /// Whether the endpoint has stopped, and why.
    pub(crate) const fn stopped(&self) -> Option<Error> {
        self.stopped
    }

    /// The next time the endpoint needs to run, in the clock the host feeds it; `None` if only an input can wake it.
    pub(crate) fn deadline(&self) -> Option<u64> {
        match (self.node.poll_timeout(), self.shutdown) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        }
    }

    /// Wake the driving future if the endpoint now needs to run sooner than it sleeps.
    pub(crate) fn kick(&mut self) {
        if let Some(t) = self.driver
            && self.deadline().is_some_and(|d| d < self.armed)
        {
            self.standby.notify(t);
        }
    }

    /// Handle everything waiting: due timers, events and the answers they need, until none is left or the budget runs
    /// out. Returns how many items it handled; the caller goes on until it returns 0.
    pub(crate) fn service(&mut self, now: u64) -> usize {
        if self.prekeys.due(now)
            && let Ok(p) = self.prekeys.rotate(now)
        {
            self.node.endpoint_mut().set_prekey(p);
        }
        let mut n = 0;
        if self.node.poll_timeout().is_some_and(|d| d <= now) {
            self.node.handle_timeout(now);
            n += 1;
        }
        n += self.answer_signatures(now);
        n += self.drain(now);
        if n > 0 {
            let dropped = self.node.endpoint().node_stats().events_dropped;
            if dropped != self.last_dropped {
                // A dropped event may have been for any waiter: they all look again.
                self.last_dropped = dropped;
                self.standby.notify_all();
            }
        }
        if self.shutdown.is_some() {
            self.check_finished(now);
        }
        n
    }

    fn drain(&mut self, now: u64) -> usize {
        if self.draining {
            return 0;
        }
        self.draining = true;
        let mut n = 0;
        while n < BUDGET {
            let Some(ev) = self.node.poll_event() else {
                break;
            };
            self.on_node_event(now, &ev);
            n += 1;
        }
        self.draining = false;
        n
    }

    /// Run the command `make` builds. While the host has left too many events unread the endpoint holds a command back:
    /// read them and try again, so a caller never sees an error for the endpoint's own back-pressure.
    fn cmd<'c>(
        &mut self,
        now: u64,
        make: impl Fn() -> Command<'c, NoSource>,
    ) -> core::result::Result<Value, CommandError> {
        let mut r = self.cmd_once(now, make());
        if matches!(r, Err(CommandError::EventsPending)) && !self.draining {
            self.drain(now);
            r = self.cmd_once(now, make());
        }
        r
    }

    fn cmd_once(&mut self, now: u64, c: Command<'_, NoSource>) -> core::result::Result<Value, CommandError> {
        let quiet = matches!(c, Command::Consume { n: 0, .. } | Command::OpenStream { .. });
        let r = self.node.command(now, c);
        if let Ok(v) = &r {
            // A write that took nothing queued nothing: sending again would only loop.
            self.dirty |= !quiet && !matches!(v, Value::Written(0));
        }
        r
    }

    /// Whether a command ran since the last call that may have queued packets; the caller then sends them.
    pub(crate) fn take_dirty(&mut self) -> bool {
        std::mem::take(&mut self.dirty)
    }

    // ---- waiting ----

    /// Register `t` as waiting for `w`.
    pub(crate) fn add_wait(&mut self, w: Wait, t: Ticket) {
        match w {
            Wait::S(sid, key) => {
                if let Some(s) = self.sessions.get_mut(&sid)
                    && !s.waits.contains(&(key, t))
                {
                    s.waits.push((key, t));
                }
            }
            Wait::G(key) => {
                if !self.gwaits.contains(&(key, t)) {
                    self.gwaits.push((key, t));
                }
            }
        }
    }

    /// Remove `t`'s registration for `w` (its future ended).
    pub(crate) fn forget(&mut self, w: Wait, t: Ticket) {
        match w {
            Wait::S(sid, key) => {
                if let Some(s) = self.sessions.get_mut(&sid) {
                    s.waits.retain(|e| *e != (key, t));
                }
            }
            Wait::G(key) => self.gwaits.retain(|e| *e != (key, t)),
        }
    }

    fn wake_s(&mut self, sid: SessionId, key: SKey) {
        let Some(s) = self.sessions.get_mut(&sid) else { return };
        let standby = &mut self.standby;
        s.waits.retain(|(k, t)| {
            let hit = *k == key;
            if hit {
                standby.notify(*t);
            }
            !hit
        });
    }

    fn wake_g(&mut self, key: GKey) {
        let standby = &mut self.standby;
        self.gwaits.retain(|(k, t)| {
            let hit = *k == key;
            if hit {
                standby.notify(*t);
            }
            !hit
        });
    }

    // ---- events ----

    /// One event of the node. The endpoint's events are the sessions and streams of the handles; the node's own
    /// (membership, broadcast, connectivity) are surfaced by the calls that use them.
    fn on_node_event(&mut self, now: u64, ev: &NodeEvent) {
        if let NodeEvent::Endpoint(ev) = ev {
            self.on_event(now, *ev);
        }
    }

    /// Answer the signatures the connectivity layer waits for (its record, a sleep notice, a beacon).
    fn answer_signatures(&mut self, now: u64) -> usize {
        let Some(KeyRequest::Sign { message, .. }) = self.node.sign_request() else {
            return 0;
        };
        let message = message.to_vec();
        match self.identity.sign(&message) {
            Ok(sig) => self.node.sign_response(now, KeyResponse::Signature(&sig)),
            Err(_) => self.node.sign_response(now, KeyResponse::Failed),
        }
        1
    }

    fn on_event(&mut self, now: u64, ev: Event) {
        match ev {
            Event::Connected {
                session, node, alpn, ..
            } => self.session_up(now, session, node, alpn, true),
            Event::Incoming { session, node, alpn } => self.session_up(now, session, node, alpn, false),
            Event::ConnectFailed { node, alpn, reason } => {
                if let Some(sid) = self.dial_by_peer.remove(&(node, alpn)) {
                    self.dial_done(sid, Err(Error::dial(reason)));
                }
            }
            Event::Closed { session, reason } => self.session_down(session, Error::ended(reason)),
            Event::StreamOpened { session, stream } => self.stream_opened(now, session, stream),
            Event::StreamReadable { session, stream } | Event::StreamReset { session, stream, .. } => {
                self.discard_if_dropped(now, session, stream);
                self.wake_s(session, SKey::Read(stream));
            }
            Event::StreamWritable { session, stream } => {
                self.wake_s(session, SKey::Write(stream));
                self.wake_s(session, SKey::Open);
            }
            Event::OpenReady { session } => self.wake_s(session, SKey::Open),
            Event::AcpCheck { check, node, alpn } => {
                let dir = if self.dial_by_peer.contains_key(&(node, alpn)) {
                    Direction::Outbound
                } else {
                    Direction::Inbound
                };
                let allow = self.admit.admit(&node, alpn.as_bytes(), dir);
                let _ = self.cmd_once(now, Command::AcpAnswer { check, allow });
            }
            Event::StreamStopped { session, stream, error } => {
                self.send_failed(
                    session,
                    stream,
                    Error::new(ErrorKind::Stopped(error), "the peer stopped the stream"),
                );
                self.wake_s(session, SKey::Write(stream));
            }
            Event::KeyRequest { session } => self.answer_key(now, session),
            Event::DatagramReceived { session } => self.wake_s(session, SKey::Datagram),
            Event::PathChanged { .. }
            | Event::PeerAsleep { .. }
            | Event::PeerAwake { .. }
            | Event::ReachOut { .. }
            | Event::TicketsReceived { .. } => {}
        }
    }

    fn answer_key(&mut self, now: u64, session: SessionId) {
        enum Owned {
            Sign(vinc_security::KeyHandle, Vec<u8>),
            Decap(vinc_security::KeyHandle, Vec<u8>),
        }
        let req = match self.node.endpoint().query(Query::KeyRequest(session)) {
            Answer::KeyRequest(KeyRequest::Sign { key, message, .. }) => Owned::Sign(key, message.to_vec()),
            Answer::KeyRequest(KeyRequest::Decapsulate { key, ct }) => Owned::Decap(key, ct.to_vec()),
            _ => return,
        };
        let sig;
        let response = match req {
            Owned::Sign(key, msg) => match is_identity(key).then(|| self.identity.sign(&msg).ok()).flatten() {
                Some(s) => {
                    sig = s;
                    KeyResponse::Signature(&sig)
                }
                None => KeyResponse::Failed,
            },
            Owned::Decap(key, ct) => match self.prekeys.decapsulate(key, &ct) {
                Some(s) => KeyResponse::SharedSecret(s),
                None => KeyResponse::Failed,
            },
        };
        let _ = self.cmd_once(now, Command::KeyResponse { session, response });
    }

    fn route_of(&self, alpn: &Alpn) -> usize {
        self.routes
            .iter()
            .position(|r| !r.alpn.is_empty() && r.alpn == alpn.as_bytes())
            .unwrap_or(0)
    }

    fn session_up(&mut self, now: u64, session: SessionId, node: NodeId, alpn: Alpn, dialer: bool) {
        let info = Rc::new(SessInfo {
            id: session,
            node,
            alpn,
            dialer,
            ended: OnceCell::new(),
        });
        if self.admit.is_revoked(&node) {
            let _ = self.cmd(now, || Command::Close { session, error: DENIED });
            return;
        }
        let route = self.route_of(&alpn);
        if !dialer {
            let full = self
                .routes
                .get(route)
                .is_none_or(|r| r.queue.len() >= self.limits.accept_sessions);
            if self.sessions.len() >= self.limits.connections || full {
                let _ = self.cmd(now, || Command::Close { session, error: BUSY });
                return;
            }
        } else if !self.dials.contains_key(&session) {
            // The dial was dropped before the session came up: close it, no one holds it.
            let _ = self.cmd(now, || Command::Close { session, error: 0 });
            return;
        }
        self.sessions.insert(
            session,
            Sess {
                info: Rc::clone(&info),
                accept_bi: VecDeque::new(),
                accept_uni: VecDeque::new(),
                waits: Vec::new(),
                send_fail: Vec::new(),
                discard: Vec::new(),
            },
        );
        if dialer {
            self.dial_by_peer.remove(&(node, alpn));
            self.dial_done(session, Ok(info));
        } else if let Some(r) = self.routes.get_mut(route) {
            r.queue.push_back(info);
            self.wake_g(GKey::Route(route));
        }
    }

    fn dial_done(&mut self, session: SessionId, result: Result<Rc<SessInfo>>) {
        if let Some(d) = self.dials.get_mut(&session)
            && d.result.is_none()
        {
            d.result = Some(result);
            self.wake_g(GKey::Dial(session));
        }
    }

    fn session_down(&mut self, session: SessionId, err: Error) {
        if let Some(d) = self.dials.get(&session)
            && d.result.is_none()
        {
            self.dial_by_peer.remove(&(d.node, d.alpn));
            self.dial_done(session, Err(err));
        }
        if let Some(rec) = self.sessions.remove(&session) {
            end_session(&mut self.standby, rec, err);
        }
    }

    /// Everything stops for `err`: every session ends and every waiting future is woken.
    fn stop(&mut self, err: Error) {
        self.stopped = Some(err);
        self.shutdown = None;
        for (_, rec) in self.sessions.drain() {
            end_session(&mut self.standby, rec, err);
        }
        for d in self.dials.values_mut() {
            if d.result.is_none() {
                d.result = Some(Err(err));
            }
        }
        for (_, t) in self.gwaits.drain(..) {
            self.standby.notify(t);
        }
    }

    /// The host's socket failed for good: end everything with the reason.
    pub(crate) fn fail(&mut self, err: Error) {
        if self.stopped.is_none() {
            self.stop(err);
        }
    }

    fn stream_opened(&mut self, now: u64, session: SessionId, id: StreamId) {
        let uni = is_uni(id);
        let cap = self.limits.accept_streams;
        let Some(s) = self.sessions.get_mut(&session) else {
            return;
        };
        let q = if uni { &mut s.accept_uni } else { &mut s.accept_bi };
        if q.len() < cap {
            q.push_back(id);
            self.wake_s(session, if uni { SKey::AcceptUni } else { SKey::AcceptBi });
            return;
        }
        // Refuse: tell the peer to stop, and drop what it sends.
        if s.discard.len() < TRACKED {
            s.discard.push(id);
        }
        if !uni {
            let _ = self.cmd(now, || Command::Reset {
                session,
                stream: id,
                error: BUSY,
            });
            self.send_failed(
                session,
                id,
                Error::new(ErrorKind::Stopped(BUSY), "the stream was refused"),
            );
        }
        let _ = self.cmd(now, || Command::StopSending {
            session,
            stream: id,
            error: BUSY,
        });
        self.discard_if_dropped(now, session, id);
    }

    fn send_failed(&mut self, session: SessionId, id: StreamId, err: Error) {
        if let Some(s) = self.sessions.get_mut(&session) {
            s.send_fail.retain(|(i, _)| *i != id);
            if s.send_fail.len() >= TRACKED {
                s.send_fail.remove(0);
            }
            s.send_fail.push((id, err));
        }
    }

    fn send_failure(&self, session: SessionId, id: StreamId) -> Option<Error> {
        let s = self.sessions.get(&session)?;
        s.send_fail.iter().find(|(i, _)| *i == id).map(|(_, e)| *e)
    }

    /// Throw away what the endpoint holds on a stream the application dropped, until the stream ends.
    fn discard_if_dropped(&mut self, now: u64, session: SessionId, id: StreamId) {
        if !self.sessions.get(&session).is_some_and(|s| s.discard.contains(&id)) {
            return;
        }
        loop {
            let n = match self.node.endpoint().query(Query::Read { session, stream: id }) {
                Answer::Chunk(c) => c.len(),
                _ => 0,
            };
            let status = match self.cmd(now, || Command::Consume { session, stream: id, n }) {
                Ok(Value::Recv(st)) => st,
                Ok(_) => RecvStatus::Open,
                Err(_) => RecvStatus::Finished,
            };
            if status != RecvStatus::Open {
                if let Some(s) = self.sessions.get_mut(&session) {
                    s.discard.retain(|i| *i != id);
                }
                return;
            }
            if n == 0 {
                return;
            }
        }
    }
}

/// End a session record for `err`: the reason is set before every waiting future is woken.
fn end_session(standby: &mut Standby, rec: Sess, err: Error) {
    let _ = rec.info.ended.set(err);
    for (_, t) in rec.waits {
        standby.notify(t);
    }
}
