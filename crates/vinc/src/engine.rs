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

use std::cell::{OnceCell, RefCell};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::net::SocketAddr;
use std::rc::Rc;

use rapidhash::RapidHashMap;
use vinc_core::{Answer, Command, CommandError, Event, IfaceId, Query, SessionId, Value};
use vinc_crypto::{NodeId, Secret};
use vinc_keystore::KeyStore;
use vinc_node::HUB_ALPN;
use vinc_security::{Alpn, KeyRequest, KeyResponse};
use vinc_transport::stream::{RecvStatus, StreamId, is_uni};

use crate::carriers::Relay;
use crate::error::{Error, ErrorKind, Result};
use crate::event::Event as TopicEvent;
use crate::keys::{Identity, Prekeys, is_identity};
use crate::mem::Limits;
use crate::node::{FacadeNode, RELAYS};
use crate::standby::{Standby, Ticket};

mod gate;
mod ops;
mod state;
mod topics;
pub use state::Restored;

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
/// The most events of hub sessions kept for the relay role between two of its turns; the rest are dropped.
const RELAY_EVENTS: usize = 1024;

/// A key answer that owns its bytes, so the request it answers can be dropped first.
enum Answered {
    Signature(Vec<u8>),
    Secret(Secret<32>),
    Failed,
}

impl Answered {
    fn with<T>(self, f: impl FnOnce(KeyResponse<'_>) -> T) -> T {
        match self {
            Self::Signature(sig) => f(KeyResponse::Signature(&sig)),
            Self::Secret(s) => f(KeyResponse::SharedSecret(s)),
            Self::Failed => f(KeyResponse::Failed),
        }
    }
}

/// Answer a key operation from the identity key or the prekeys.
fn answer<S: KeyStore>(identity: &RefCell<Identity<S>>, prekeys: &mut Prekeys, req: KeyRequest<'_>) -> Answered {
    match req {
        KeyRequest::Sign { key, message, .. } => {
            let signed = is_identity(key)
                .then(|| identity.try_borrow_mut().ok().and_then(|mut i| i.sign(message).ok()))
                .flatten();
            match signed {
                Some(sig) => Answered::Signature(sig),
                None => Answered::Failed,
            }
        }
        KeyRequest::Decapsulate { key, ct } => match prekeys.decapsulate(key, ct) {
            Some(s) => Answered::Secret(s),
            None => Answered::Failed,
        },
    }
}

/// What a core is built from.
pub(crate) struct CoreConfig<S, A> {
    /// The node's identity.
    pub identity: Identity<S>,
    /// The protocols served; at most [`MAX_PROTOCOLS`](crate::MAX_PROTOCOLS) with those added later.
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
    /// The relays, in the order the node numbers them.
    pub relays: Vec<Relay>,
    /// The endpoint is a hub of membership and broadcast.
    pub hub: bool,
    /// The endpoint runs the relay role: the events of its members' sessions are kept for it.
    pub relaying: bool,
    /// How long a dial may take, in nanoseconds.
    pub connect_timeout: u64,
}

/// What both the core and the handles of a session read.
#[derive(Debug)]
pub(crate) struct SessInfo {
    pub id: SessionId,
    pub node: NodeId,
    pub alpn: Alpn,
    pub dialer: bool,
    /// The session resumed an earlier one with a ticket (known on the dialing side).
    pub resumed: bool,
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
    /// A place for a stream, bidirectional or not. Its waiters are served in the order they asked.
    Open(bool),
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
    /// A topic event was queued.
    Events,
    /// A relay answered a lookup.
    Lookup,
    /// The neighbours of a topic changed, or a deadline passed.
    Topic,
    /// A publish was acknowledged or given up, or a hub's log has room again: the node may take another.
    Publish,
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

/// The oldest ticket in `waits` that waits for `key`.
fn first_wait(waits: &[(SKey, Ticket)], key: SKey) -> Option<Ticket> {
    waits.iter().find(|(k, _)| *k == key).map(|&(_, t)| t)
}

struct Dial {
    node: NodeId,
    alpn: Alpn,
    result: Option<Result<Rc<SessInfo>>>,
    /// When the dial gives up, in the endpoint's clock.
    deadline: u64,
}

struct Route {
    alpn: Vec<u8>,
    queue: VecDeque<Rc<SessInfo>>,
}

/// The core; see the module docs.
pub(crate) struct Core<S, A> {
    pub(crate) node: Box<FacadeNode>,
    /// The identity, shared with the relay role when the endpoint has one; borrowed only inside a call.
    identity: Rc<RefCell<Identity<S>>>,
    prekeys: Prekeys,
    /// The access hook, shared with the endpoint's handles so they can ask it without borrowing the core.
    admit: Rc<Gate<A>>,
    pub(crate) limits: Limits,
    sessions: RapidHashMap<SessionId, Sess>,
    dials: RapidHashMap<SessionId, Dial>,
    /// The accept queues: the first takes every protocol no registered one claims.
    routes: Vec<Route>,
    /// The protocols served for the application: those the builder listed and those registered since.
    user_alpns: usize,
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
    /// The ticket of the future whose attempt runs, `None` before it first waited.
    pub(crate) caller: Option<Ticket>,
    pub(crate) armed: u64,
    /// The events for the host, oldest first, and how many were dropped since the host last read.
    events: VecDeque<TopicEvent>,
    lost: u32,
    /// The topics joined, with the neighbours last reported for each.
    topics: BTreeMap<Vec<u8>, Vec<NodeId>>,
    /// The sessions of the hub protocol, by session, with their peer.
    hub_sessions: RapidHashMap<SessionId, NodeId>,
    /// How long a dial may take, in nanoseconds.
    connect_timeout: u64,
    /// The peers a relay had no record for or sent a bad one for, oldest first.
    lookup_failed: VecDeque<NodeId>,
    neighbors_dirty: bool,
    look_at: u64,
    /// The instants futures wait for: a deadline passing wakes them to look again.
    deadlines: BTreeSet<u64>,
    /// With the relay role, the relays this endpoint itself names as its hubs (their sessions are not the role's
    /// members); `None` without the role. With it, the events of hub sessions go to `relay_events`.
    relay_hubs: Option<Vec<NodeId>>,
    /// Events of hub sessions the relay role has not heard yet, oldest first; bounded by [`RELAY_EVENTS`].
    relay_events: Vec<Event>,
}

impl<S: KeyStore, A: Admit> Core<S, A> {
    /// A core over `node`, whose endpoint already holds the prekey, the protocols and the interfaces `ifaces`.
    pub(crate) fn new(node: Box<FacadeNode>, cfg: CoreConfig<S, A>, prekeys: Prekeys, ifaces: Vec<IfaceId>) -> Self {
        Self {
            node,
            identity: Rc::new(RefCell::new(cfg.identity)),
            prekeys,
            admit: Rc::new(Gate::new(cfg.admit)),
            limits: cfg.limits,
            sessions: RapidHashMap::default(),
            dials: RapidHashMap::default(),
            user_alpns: cfg.alpns.len(),
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
            caller: None,
            armed: u64::MAX,
            events: VecDeque::new(),
            lost: 0,
            topics: BTreeMap::new(),
            hub_sessions: RapidHashMap::default(),
            connect_timeout: cfg.connect_timeout,
            lookup_failed: VecDeque::new(),
            neighbors_dirty: false,
            look_at: 0,
            deadlines: BTreeSet::new(),
            relay_hubs: cfg.relaying.then(|| cfg.relays.iter().map(|r| r.id).collect()),
            relay_events: Vec::new(),
        }
    }

    /// Whether the endpoint has stopped, and why.
    pub(crate) const fn stopped(&self) -> Option<Error> {
        self.stopped
    }

    /// The identity the core signs with, for the relay role to share.
    pub(crate) fn identity(&self) -> Rc<RefCell<Identity<S>>> {
        Rc::clone(&self.identity)
    }

    /// Run `f` on the identity.
    pub(crate) fn with_identity<T>(&self, f: impl FnOnce(&mut Identity<S>) -> Result<T>) -> Result<T> {
        let mut id = self
            .identity
            .try_borrow_mut()
            .map_err(|_| Error::new(ErrorKind::Busy, "the identity key is in use, try again"))?;
        f(&mut id)
    }

    /// The next time the endpoint needs to run, in the clock the host feeds it; `None` if only an input can wake it.
    pub(crate) fn deadline(&self) -> Option<u64> {
        [
            self.node.poll_timeout(),
            self.shutdown,
            self.look_deadline(),
            self.deadlines.first().copied(),
        ]
        .into_iter()
        .flatten()
        .min()
    }

    /// Have the driving future wake at `at` as well: the relay role's next deadline.
    pub(crate) fn add_deadline(&mut self, at: u64) {
        self.deadlines.insert(at);
    }

    /// Keep an event of a session the relay role may own: a member's hub session coming up, going down or waking.
    /// Sessions of the other protocols, and of the relays this endpoint itself uses as hubs, are not the role's.
    pub(super) fn tap(&mut self, ev: &Event) {
        let Some(hubs) = &self.relay_hubs else { return };
        let mine = match ev {
            Event::Incoming { node, alpn, .. } => alpn.as_bytes() == HUB_ALPN && !hubs.contains(node),
            Event::Closed { .. } | Event::PeerAwake { .. } => true,
            _ => false,
        };
        if mine && self.relay_events.len() < RELAY_EVENTS {
            self.relay_events.push(*ev);
            self.wake_driver();
        }
    }

    /// The events kept for the relay role; the caller gives the vector back through [`Core::return_relay_events`].
    pub(crate) fn take_relay_events(&mut self) -> Vec<Event> {
        std::mem::take(&mut self.relay_events)
    }

    /// Give back the vector [`Core::take_relay_events`] lent, emptied, so its memory is reused.
    pub(crate) fn return_relay_events(&mut self, mut v: Vec<Event>) {
        v.clear();
        v.append(&mut self.relay_events);
        self.relay_events = v;
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
            self.node.endpoint_mut().set_prekey(p.clone());
            self.node.set_prekey(p);
        }
        let mut n = 0;
        if self.node.poll_timeout().is_some_and(|d| d <= now) {
            self.node.handle_timeout(now);
            n += 1;
        }
        n += self.answer_signatures(now);
        n += self.answer_relay_keys(now);
        n += self.drain(now);
        if n > 0 {
            let dropped = self.node.endpoint().node_stats().events_dropped;
            if dropped != self.last_dropped {
                // A dropped event may have been for any waiter: they all look again.
                self.last_dropped = dropped;
                self.standby.notify_all();
            }
        }
        self.look(now);
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
            self.on_node_event(now, ev);
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
        make: impl Fn() -> Command<'c, crate::Body>,
    ) -> core::result::Result<Value, CommandError> {
        let mut r = self.cmd_once(now, make());
        if matches!(r, Err(CommandError::EventsPending)) && !self.draining {
            self.drain(now);
            r = self.cmd_once(now, make());
        }
        r
    }

    fn cmd_once(&mut self, now: u64, c: Command<'_, crate::Body>) -> core::result::Result<Value, CommandError> {
        let quiet = matches!(c, Command::Consume { n: 0, .. } | Command::OpenStream { .. });
        // A command that only moves the application's data leaves the node's layers nothing to do unless it raised
        // an event; the others always get their round.
        let data = matches!(
            c,
            Command::Write { .. }
                | Command::Consume { .. }
                | Command::OpenStream { .. }
                | Command::Finish { .. }
                | Command::SetUrgency { .. }
                | Command::SendDatagram { .. }
        );
        let r = if data {
            self.node.data_command(now, c)
        } else {
            self.node.command(now, c)
        };
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

    /// Remove `t`'s registration for `w` (its future ended). The oldest open that leaves hands the turn to the next.
    pub(crate) fn forget(&mut self, w: Wait, t: Ticket) {
        match w {
            Wait::S(sid, key) => {
                if let Some(s) = self.sessions.get_mut(&sid) {
                    let first = matches!(key, SKey::Open(_)) && first_wait(&s.waits, key) == Some(t);
                    s.waits.retain(|e| *e != (key, t));
                    if first && let Some(next) = first_wait(&s.waits, key) {
                        self.standby.notify(next);
                    }
                }
            }
            Wait::G(key) => self.gwaits.retain(|e| *e != (key, t)),
        }
    }

    /// The oldest open that waits on `sid` for a stream of the kind `key` names, unless it is the caller's own: an
    /// open that finds one queues behind it, so a newcomer never takes a place an older open was woken for.
    pub(crate) fn open_ahead(&self, sid: SessionId, key: SKey) -> bool {
        self.sessions
            .get(&sid)
            .and_then(|s| first_wait(&s.waits, key))
            .is_some_and(|t| Some(t) != self.caller)
    }

    /// Wake the oldest open of each kind on `sid`: there may be a place for it now.
    pub(crate) fn wake_open(&mut self, sid: SessionId) {
        self.wake_s(sid, SKey::Open(true));
        self.wake_s(sid, SKey::Open(false));
    }

    fn wake_s(&mut self, sid: SessionId, key: SKey) {
        let Some(s) = self.sessions.get_mut(&sid) else { return };
        let standby = &mut self.standby;
        if matches!(key, SKey::Open(_)) {
            // Only the oldest, which keeps its place; it wakes the next when it leaves (see `forget`).
            if let Some(t) = first_wait(&s.waits, key) {
                standby.notify(t);
            }
            return;
        }
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

    /// Answer the signatures the connectivity layer waits for (its record, a sleep notice, a beacon).
    fn answer_signatures(&mut self, now: u64) -> usize {
        let Some(KeyRequest::Sign { message, .. }) = self.node.sign_request() else {
            return 0;
        };
        let message = message.to_vec();
        match self.with_identity(|i| i.sign(&message)) {
            Ok(sig) => self.node.sign_response(now, KeyResponse::Signature(&sig)),
            Err(_) => self.node.sign_response(now, KeyResponse::Failed),
        }
        1
    }

    fn on_event(&mut self, now: u64, ev: Event) {
        match ev {
            Event::Connected {
                session,
                node,
                alpn,
                resumed,
                ..
            } => self.session_up(now, session, node, alpn, true, resumed),
            Event::Incoming { session, node, alpn } => self.session_up(now, session, node, alpn, false, false),
            Event::ConnectFailed { session, reason, .. } => {
                if let Some(session) = session {
                    self.dial_done(session, Err(Error::dial(reason)));
                }
            }
            Event::Closed { session, reason } => {
                self.hub_session_down(session);
                self.session_down(session, Error::ended(reason));
            }
            Event::StreamOpened { session, stream } => self.stream_opened(now, session, stream),
            Event::StreamReadable { session, stream } | Event::StreamReset { session, stream, .. } => {
                self.discard_if_dropped(now, session, stream);
                self.wake_s(session, SKey::Read(stream));
            }
            Event::StreamWritable { session, stream } => {
                self.wake_s(session, SKey::Write(stream));
                self.wake_open(session);
            }
            Event::OpenReady { session } => self.wake_open(session),
            Event::AcpCheck { check, node, alpn } => {
                let dir = if alpn.as_bytes() == HUB_ALPN {
                    Direction::Gossip
                } else if self.dialing(&node, alpn) {
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
        let answered = match self.node.endpoint().query(Query::KeyRequest(session)) {
            Answer::KeyRequest(req) => answer(&self.identity, &mut self.prekeys, req),
            _ => return,
        };
        answered.with(|response| {
            let _ = self.cmd_once(now, Command::KeyResponse { session, response });
        });
    }

    /// Answer the key operations the carrier handshakes of the relays wait for.
    fn answer_relay_keys(&mut self, now: u64) -> usize {
        let mut n = 0;
        for relay in 0..RELAYS {
            let Some(req) = self.node.key_request(relay) else {
                continue;
            };
            let answered = answer(&self.identity, &mut self.prekeys, req);
            answered.with(|resp| self.node.key_response(now, relay, resp));
            n += 1;
        }
        n
    }

    fn route_of(&self, alpn: &Alpn) -> usize {
        self.routes
            .iter()
            .position(|r| !r.alpn.is_empty() && r.alpn == alpn.as_bytes())
            .unwrap_or(0)
    }

    fn session_up(&mut self, now: u64, session: SessionId, node: NodeId, alpn: Alpn, dialer: bool, resumed: bool) {
        if alpn.as_bytes() == HUB_ALPN {
            self.hub_session_up(session, node);
            return;
        }
        let info = Rc::new(SessInfo {
            id: session,
            node,
            alpn,
            dialer,
            resumed,
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
            self.dial_done(session, Ok(info));
        } else if let Some(r) = self.routes.get_mut(route) {
            r.queue.push_back(info);
            self.wake_g(GKey::Route(route));
        }
    }

    /// Whether a dial to `node` for `alpn` still waits for its answer. The dials are bounded by the connection table.
    fn dialing(&self, node: &NodeId, alpn: Alpn) -> bool {
        self.dials
            .values()
            .any(|d| d.result.is_none() && d.node == *node && d.alpn == alpn)
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
