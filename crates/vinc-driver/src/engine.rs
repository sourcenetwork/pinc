//! The engine: the SANS-IO endpoint plus everything a host does for it, with no socket and no clock of its own.
//!
//! A driver feeds it datagrams and the time and reads datagrams and a deadline back; the engine answers key requests
//! and access checks, moves stream bytes between the endpoint and the handles' channels, opens and accepts streams,
//! dials, and applies the requests of [`Remote`](crate::Remote) handles. After any input the driver calls
//! [`Engine::service`] and then drains [`Engine::poll_transmit`] until it returns `None`; there are no hidden wakeups.
//!
//! Invariants: every wait a handle can drop sits in a channel, never in the engine; a pending dial is answered exactly
//! once; a session leaves the table exactly when the endpoint reports it closed, and every stream of it ends with a
//! reason set first; a request with no one waiting for its answer leaves nothing open.

use std::collections::{HashMap, VecDeque};
use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::Ordering;

use kovan_channel::bounded::{Receiver, Sender};
use vinc_core::{
    Answer, Command, CommandError, Event, IfaceEvent, IfaceId, MAX_ALPNS, NodeStats, Query, Reply, Role, SessionId,
    Transmit, Value,
};
use vinc_crypto::NodeId;
use vinc_security::{Alpn, KeyRequest, KeyResponse};
use vinc_transport::stream::{NoSource, RecvStatus, StreamError, StreamId, is_uni};

use crate::error::{Error, ErrorKind, Result};
use crate::keys::{Identity, Prekeys, is_identity};
use crate::link::{BLOCK, Item, NewStream, SessionShared, StreamShared, chan};
use crate::mem::Limits;
use crate::node::Node;
use crate::plane::{Ctl, Plane, Request};

/// The close code sent for a session or stream refused because a queue was full.
pub const BUSY: u64 = 0x42;
/// How long a shutdown waits for the CLOSE packets to leave.
const SHUTDOWN_GRACE: u64 = 1_000_000_000;
/// The most items one [`Engine::service`] call handles before it returns, so transmit and receive are not starved.
const BUDGET: usize = 4096;
/// How often the engine looks for sessions no one holds: 1 s.
const GC_PERIOD: u64 = 1_000_000_000;

/// Which way a connection was made, as the access hook is told.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// A peer dialed this node.
    Inbound,
    /// This node dialed the peer.
    Outbound,
    /// A broadcast layer asks to take the peer as a neighbour or to reach it.
    Gossip,
}

/// The access hook: whether a peer may connect or be a neighbour. It runs on the engine thread and must not block.
pub trait Admit: Send + Sync + 'static {
    /// Whether `peer` may use `alpn` in `dir`.
    fn admit(&self, peer: &NodeId, alpn: &[u8], dir: Direction) -> bool;
}

/// What an engine is built from.
pub struct EngineConfig {
    /// The node's identity.
    pub identity: Identity,
    /// The protocols served; at most [`MAX_ALPNS`] with those added later.
    pub alpns: Vec<Vec<u8>>,
    /// The sizes.
    pub limits: Limits,
    /// The access hook, if any.
    pub admit: Option<Arc<dyn Admit>>,
    /// The most same-size datagrams one transmit batches (1 turns batching off).
    pub max_gso: usize,
    /// The local addresses datagrams are sent from and received on.
    pub locals: Vec<SocketAddr>,
}

struct StreamRec {
    shared: Arc<StreamShared>,
    tx_rx: Option<Receiver<Item>>,
    cur: Option<(Vec<u8>, usize)>,
    rx_tx: Option<Sender<Vec<u8>>>,
    send_done: bool,
    recv_done: bool,
}

struct SessionRec {
    shared: Arc<SessionShared>,
    streams: HashMap<StreamId, StreamRec>,
    accept_bi: Sender<NewStream>,
    accept_uni: Sender<NewStream>,
    datagrams: Sender<Vec<u8>>,
    // Dropped with the record: closing the channel is the "session ended" signal.
    _gone: Sender<()>,
}

struct Dial {
    session: SessionId,
    node: NodeId,
    alpn: Vec<u8>,
    reply: Sender<Result<Arc<SessionShared>>>,
}

/// The engine; see the module docs. Build it with [`crate::run`].
pub struct Engine<'s, 'a> {
    pub(crate) ep: Box<dyn Node + 's>,
    pub(crate) _memory: std::marker::PhantomData<&'s &'a ()>,
    identity: Identity,
    prekeys: Prekeys,
    plane: Plane,
    limits: Limits,
    admit: Option<Arc<dyn Admit>>,
    default_queue: Sender<Arc<SessionShared>>,
    routes: Vec<(Vec<u8>, Sender<Arc<SessionShared>>)>,
    sessions: HashMap<SessionId, SessionRec>,
    dials: Vec<Dial>,
    book: HashMap<NodeId, Vec<SocketAddr>>,
    backlog: VecDeque<Event>,
    dgram_buf: Vec<u8>,
    ifaces: Vec<IfaceId>,
    shutdown: Option<(u64, Vec<Sender<()>>)>,
    last_dropped: u64,
    /// Set while `sweep` runs: the events a refused write waits for may have been dropped.
    sweeping: bool,
    next_gc: u64,
}

impl<'s> Engine<'s, '_> {
    /// An engine over `ep`, which already holds the prekey, the protocols and the interfaces `ifaces`.
    pub(crate) fn new(
        ep: Box<dyn Node + 's>,
        cfg: EngineConfig,
        prekeys: Prekeys,
        plane: Plane,
        default_queue: Sender<Arc<SessionShared>>,
        ifaces: Vec<IfaceId>,
        now: u64,
    ) -> Self {
        Self {
            ep,
            _memory: std::marker::PhantomData,
            identity: cfg.identity,
            prekeys,
            plane,
            limits: cfg.limits,
            admit: cfg.admit,
            default_queue,
            routes: Vec::new(),
            sessions: HashMap::new(),
            dials: Vec::new(),
            book: HashMap::new(),
            backlog: VecDeque::new(),
            dgram_buf: vec![0; vinc_core::MAX_DATAGRAM],
            ifaces,
            shutdown: None,
            last_dropped: 0,
            sweeping: false,
            next_gc: now,
        }
    }
}

impl Drop for Engine<'_, '_> {
    fn drop(&mut self) {
        // Mark the plane stopped, then answer what is still queued: a caller never waits on an engine that is gone.
        self.plane.stopped.store(true, Ordering::SeqCst);
        while let Some(r) = self.plane.req.try_recv() {
            Self::refuse(r);
        }
    }
}

impl Engine<'_, '_> {
    /// This node's id.
    pub const fn node_id(&self) -> NodeId {
        self.identity.node_id()
    }

    /// Feed a datagram received on `local` from `remote`.
    pub fn handle_datagram(&mut self, now: u64, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        self.ep.handle_datagram(now, local, remote, data);
    }

    /// Run the timers due at `now`.
    pub fn handle_timeout(&mut self, now: u64) {
        self.ep.handle_timeout(now);
    }

    /// The next datagram, or batch of equal-size datagrams, to send.
    pub fn poll_transmit(&mut self, now: u64, out: &mut [u8]) -> Option<Transmit> {
        self.ep.poll_transmit(now, out)
    }

    /// The next time the engine needs to run, in the clock the driver feeds it; `None` if only an input can wake it.
    pub fn poll_timeout(&self) -> Option<u64> {
        let shutdown = self.shutdown.as_ref().map(|(at, _)| *at);
        match (self.ep.poll_timeout(), shutdown) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        }
    }

    /// The node-wide counters of the endpoint.
    pub fn node_stats(&self) -> NodeStats {
        self.ep.node_stats()
    }

    /// Whether a shutdown was asked for and has finished: the sessions are gone or the grace ran out. Answers the
    /// callers waiting for it; the driver then stops.
    pub fn finished(&mut self, now: u64) -> bool {
        let Some((at, _)) = &self.shutdown else { return false };
        if self.ep.node_stats().sessions > 0 && now < *at {
            return false;
        }
        for r in self.shutdown.take().map(|(_, r)| r).unwrap_or_default() {
            r.send(());
        }
        true
    }

    /// Handle everything waiting: events, control messages, requests and the stream bytes they move, until none is
    /// left or the budget runs out. Returns how many items it handled; the driver calls it again until it returns 0,
    /// and the budget keeps one call from starving the socket.
    pub fn service(&mut self, now: u64) -> usize {
        if now >= self.prekeys.rotate_at
            && let Ok(p) = self.prekeys.rotate(now)
        {
            self.ep.set_prekey(p);
        }
        let mut budget = BUDGET;
        while budget > 0 {
            if let Some(ev) = self.backlog.pop_front().or_else(|| self.ep.poll_event()) {
                self.on_event(now, ev);
            } else if let Some(c) = self.plane.ctl.try_recv() {
                self.on_ctl(now, c);
            } else if let Some(r) = self.plane.req.try_recv() {
                self.on_request(now, r);
            } else {
                break;
            }
            budget -= 1;
        }
        if now >= self.next_gc {
            self.next_gc = now.saturating_add(GC_PERIOD);
            self.collect(now);
        }
        let dropped = self.ep.node_stats().events_dropped;
        if dropped != self.last_dropped {
            self.last_dropped = dropped;
            self.sweep(now);
        }
        BUDGET - budget
    }

    /// Close the sessions no one holds: a dial or an accept whose answer was dropped before it was read.
    fn collect(&mut self, now: u64) {
        let orphans: Vec<SessionId> = self
            .sessions
            .iter()
            .filter(|(_, r)| Arc::strong_count(&r.shared) == 1)
            .map(|(s, _)| *s)
            .collect();
        for session in orphans {
            let _ = self.cmd(now, Command::Close { session, error: 0 });
        }
    }

    fn cmd(&mut self, now: u64, c: Command<'_, NoSource>) -> core::result::Result<Reply, CommandError> {
        let r = self.ep.command(now, c);
        if let Ok(rep) = &r {
            self.backlog.extend(rep.events.iter().copied());
        }
        r
    }

    /// The endpoint dropped events it said the host can recover by reading state: read all of it.
    fn sweep(&mut self, now: u64) {
        let all: Vec<(SessionId, Vec<StreamId>)> = self
            .sessions
            .iter()
            .map(|(s, r)| (*s, r.streams.keys().copied().collect()))
            .collect();
        self.sweeping = true;
        for (s, streams) in all {
            for id in streams {
                self.pump_send(now, s, id);
                self.pump_recv(now, s, id);
            }
        }
        self.sweeping = false;
    }

    fn on_event(&mut self, now: u64, ev: Event) {
        match ev {
            Event::Connected {
                session, node, alpn, ..
            } => self.session_up(now, session, node, alpn, true),
            Event::Incoming { session, node, alpn } => self.session_up(now, session, node, alpn, false),
            Event::ConnectFailed { node, alpn, reason } => {
                if let Some(i) = self
                    .dials
                    .iter()
                    .position(|d| d.node == node && d.alpn == alpn.as_bytes())
                {
                    self.dials.remove(i).reply.send(Err(Error::dial(reason)));
                }
            }
            Event::Closed { session, reason } => self.session_down(session, Error::ended(reason)),
            Event::StreamOpened { session, stream } => self.stream_opened(now, session, stream),
            Event::StreamReadable { session, stream } | Event::StreamReset { session, stream, .. } => {
                self.pump_recv(now, session, stream);
            }
            Event::StreamWritable { session, stream } => self.pump_send(now, session, stream),
            Event::AcpCheck { check, node, alpn } => {
                let dir = if self.dials.iter().any(|d| d.node == node && d.alpn == alpn.as_bytes()) {
                    Direction::Outbound
                } else {
                    Direction::Inbound
                };
                let allow = self.admit.as_ref().is_none_or(|a| a.admit(&node, alpn.as_bytes(), dir));
                let _ = self.cmd(now, Command::AcpAnswer { check, allow });
            }
            Event::StreamStopped { session, stream, error } => self.send_fail(
                session,
                stream,
                Error::new(ErrorKind::Stopped(error), "the peer stopped the stream"),
            ),
            Event::KeyRequest { session } => self.answer_key(now, session),
            Event::DatagramReceived { session } => self.pump_datagrams(session),
            Event::PathChanged { .. }
            | Event::PeerAsleep { .. }
            | Event::PeerAwake { .. }
            | Event::ReachOut { .. }
            | Event::TicketsReceived { .. } => {}
        }
    }

    /// Move the session's received datagrams from the endpoint into the read channel, as far as it has room. What the
    /// endpoint holds meanwhile is bounded by its own queue, which drops the oldest and counts it.
    fn pump_datagrams(&mut self, session: SessionId) {
        let Some(rec) = self.sessions.get(&session) else { return };
        let (tx, shared) = (rec.datagrams.clone(), Arc::clone(&rec.shared));
        let discard = tx.is_disconnected();
        loop {
            if !discard && tx.is_full() {
                // Set before the last look: a reader that drains in between sees the flag and wakes the engine.
                shared.datagrams_starved.store(true, Ordering::SeqCst);
                if tx.is_full() {
                    return;
                }
            }
            match self.ep.read_datagram(session, &mut self.dgram_buf) {
                Ok(Some(n)) => {
                    if !discard && let Some(d) = self.dgram_buf.get(..n) {
                        tx.send(d.to_vec());
                    }
                }
                Err(CommandError::BufferTooSmall { len }) => self.dgram_buf.resize(len, 0),
                Ok(None) | Err(_) => return,
            }
        }
    }

    fn answer_key(&mut self, now: u64, session: SessionId) {
        enum Owned {
            Sign(vinc_security::KeyHandle, Vec<u8>),
            Decap(vinc_security::KeyHandle, Vec<u8>),
        }
        let req = match self.ep.query(Query::KeyRequest(session)) {
            Answer::KeyRequest(KeyRequest::Sign { key, message, .. }) => Owned::Sign(key, message.to_vec()),
            Answer::KeyRequest(KeyRequest::Decapsulate { key, ct }) => Owned::Decap(key, ct.to_vec()),
            _ => return,
        };
        let _ = match req {
            Owned::Sign(key, msg) => match is_identity(key).then(|| self.identity.sign(&msg).ok()).flatten() {
                Some(sig) => self.cmd(
                    now,
                    Command::KeyResponse {
                        session,
                        response: KeyResponse::Signature(&sig),
                    },
                ),
                None => self.cmd(
                    now,
                    Command::KeyResponse {
                        session,
                        response: KeyResponse::Failed,
                    },
                ),
            },
            Owned::Decap(key, ct) => match self.prekeys.decapsulate(key, &ct) {
                Some(s) => self.cmd(
                    now,
                    Command::KeyResponse {
                        session,
                        response: KeyResponse::SharedSecret(s),
                    },
                ),
                None => self.cmd(
                    now,
                    Command::KeyResponse {
                        session,
                        response: KeyResponse::Failed,
                    },
                ),
            },
        };
    }

    fn route(&self, alpn: &Alpn) -> &Sender<Arc<SessionShared>> {
        self.routes
            .iter()
            .find(|(a, _)| a == alpn.as_bytes())
            .map_or(&self.default_queue, |(_, q)| q)
    }

    fn session_up(&mut self, now: u64, session: SessionId, node: NodeId, alpn: Alpn, dialer: bool) {
        let (bi_tx, bi_rx) = chan(self.limits.accept_streams);
        let (uni_tx, uni_rx) = chan(self.limits.accept_streams);
        let (gone_tx, gone_rx) = chan(1);
        let (dg_tx, dg_rx) = chan(self.limits.datagrams);
        let shared = Arc::new(SessionShared {
            id: session,
            node,
            alpn,
            dialer,
            ended: std::sync::OnceLock::new(),
            accept_bi: bi_rx,
            accept_uni: uni_rx,
            gone: gone_rx,
            datagrams: dg_rx,
            datagrams_starved: std::sync::atomic::AtomicBool::new(false),
        });
        if !dialer {
            let q = self.route(&alpn);
            if self.sessions.len() >= self.limits.connections || q.is_full() || q.is_disconnected() {
                let _ = self.cmd(now, Command::Close { session, error: BUSY });
                return;
            }
            q.send(Arc::clone(&shared));
        }
        self.sessions.insert(
            session,
            SessionRec {
                shared: Arc::clone(&shared),
                streams: HashMap::new(),
                accept_bi: bi_tx,
                accept_uni: uni_tx,
                datagrams: dg_tx,
                _gone: gone_tx,
            },
        );
        if dialer && let Some(i) = self.dials.iter().position(|d| d.session == session) {
            let d = self.dials.remove(i);
            if d.reply.is_disconnected() {
                let _ = self.cmd(now, Command::Close { session, error: 0 });
            } else {
                d.reply.send(Ok(shared));
            }
        }
    }

    fn session_down(&mut self, session: SessionId, err: Error) {
        if let Some(i) = self.dials.iter().position(|d| d.session == session) {
            self.dials.remove(i).reply.send(Err(err));
        }
        let Some(mut rec) = self.sessions.remove(&session) else {
            return;
        };
        let _ = rec.shared.ended.set(err);
        for s in rec.streams.values_mut() {
            let _ = s.shared.rx_end.set(Err(err));
            let _ = s.shared.tx_err.set(err);
        }
    }

    /// The engine's record of a stream and the ends its handles take.
    fn make_stream(&self, session: SessionId, id: StreamId, can_send: bool, can_recv: bool) -> (StreamRec, NewStream) {
        let shared = Arc::new(StreamShared::new(session, id));
        let blocks = self.limits.stream_blocks;
        let (tx, tx_rx) = if can_send {
            let (t, r) = chan::<Item>(blocks);
            (Some(t), Some(r))
        } else {
            (None, None)
        };
        let (rx_tx, rx) = if can_recv {
            let (t, r) = chan::<Vec<u8>>(blocks);
            (Some(t), Some(r))
        } else {
            (None, None)
        };
        let rec = StreamRec {
            shared: Arc::clone(&shared),
            tx_rx,
            cur: None,
            rx_tx,
            send_done: !can_send,
            recv_done: !can_recv,
        };
        (rec, NewStream { shared, tx, rx })
    }

    /// The peer opened a stream: hand it to the session's accept queue, or refuse it if the queue is full. The
    /// transport reports every stream the peer opens exactly once, before any other event of it.
    fn stream_opened(&mut self, now: u64, session: SessionId, id: StreamId) {
        if self.stream_mut(session, id).is_some() {
            return;
        }
        let uni = is_uni(id);
        let (mut rec, new) = self.make_stream(session, id, !uni, true);
        let Some(s) = self.sessions.get_mut(&session) else {
            return;
        };
        let q = if uni { &s.accept_uni } else { &s.accept_bi };
        if q.is_full() || q.is_disconnected() {
            // Refuse: drop what the peer sends, and tell it to stop on a stream it can read.
            rec.rx_tx = None;
            drop(new);
            s.streams.insert(id, rec);
            if !uni {
                let _ = self.cmd(
                    now,
                    Command::Reset {
                        session,
                        stream: id,
                        error: BUSY,
                    },
                );
                self.send_fail(
                    session,
                    id,
                    Error::new(ErrorKind::Stopped(BUSY), "the stream was refused"),
                );
            }
        } else {
            q.send(new);
            s.streams.insert(id, rec);
        }
        self.pump_recv(now, session, id);
    }

    fn stream_mut(&mut self, session: SessionId, id: StreamId) -> Option<&mut StreamRec> {
        self.sessions.get_mut(&session)?.streams.get_mut(&id)
    }

    /// Forget a stream that is finished in both directions.
    fn reap(&mut self, session: SessionId, id: StreamId) {
        if let Some(s) = self.sessions.get_mut(&session)
            && s.streams.get(&id).is_some_and(|r| r.send_done && r.recv_done)
        {
            s.streams.remove(&id);
        }
    }

    /// The receive side of a stream ended for `end`: set why, then close the channel.
    fn recv_end(&mut self, session: SessionId, id: StreamId, end: Result<()>) {
        let Some(r) = self.stream_mut(session, id) else { return };
        let _ = r.shared.rx_end.set(end);
        r.rx_tx = None;
        r.recv_done = true;
        self.reap(session, id);
    }

    /// The send side of a stream can take no more, for `err`.
    fn send_fail(&mut self, session: SessionId, id: StreamId, err: Error) {
        let Some(r) = self.stream_mut(session, id) else { return };
        let _ = r.shared.tx_err.set(err);
        r.tx_rx = None;
        r.cur = None;
        r.send_done = true;
        self.reap(session, id);
    }

    /// Move the stream's received bytes from the endpoint into the read channel, as far as it has room.
    fn pump_recv(&mut self, now: u64, session: SessionId, id: StreamId) {
        loop {
            let Some(r) = self.stream_mut(session, id).filter(|r| !r.recv_done) else {
                return;
            };
            let tx = r.rx_tx.clone();
            let shared = Arc::clone(&r.shared);
            let discard = tx.as_ref().is_none_or(Sender::is_disconnected);
            if !discard
                && let Some(t) = &tx
                && t.is_full()
            {
                shared.starved.store(true, Ordering::SeqCst);
                if t.is_full() {
                    return;
                }
            }
            // Gather up to one block from the endpoint's chunks.
            let mut block = Vec::new();
            let mut status = RecvStatus::Open;
            let mut more = false;
            while block.len() < BLOCK {
                let n = match self.ep.query(Query::Read { session, stream: id }) {
                    Answer::Chunk(c) if !c.is_empty() => {
                        let n = c.len().min(BLOCK - block.len());
                        if !discard {
                            block.extend_from_slice(c.get(..n).unwrap_or_default());
                        }
                        n
                    }
                    _ => 0,
                };
                match self.cmd(now, Command::Consume { session, stream: id, n }) {
                    Ok(Reply {
                        value: Value::Recv(st), ..
                    }) => status = st,
                    Ok(_) => {}
                    Err(e) => {
                        self.recv_end(session, id, Err(Error::command(e)));
                        return;
                    }
                }
                if n == 0 || status != RecvStatus::Open {
                    break;
                }
                more = true;
            }
            if let Some(t) = tx.as_ref().filter(|_| !block.is_empty()) {
                t.send(block);
            }
            match status {
                RecvStatus::Finished => return self.recv_end(session, id, Ok(())),
                RecvStatus::Reset(e) => {
                    return self.recv_end(
                        session,
                        id,
                        Err(Error::new(ErrorKind::Reset(e), "the peer reset the stream")),
                    );
                }
                RecvStatus::Open if !more => return,
                RecvStatus::Open => {}
            }
        }
    }

    /// The application stopped reading: tell the peer to stop sending, fail later reads with `error`, and discard
    /// what is still on its way until the peer's reset ends the stream.
    fn stop_recv(&mut self, now: u64, session: SessionId, id: StreamId, error: u64) {
        let Some(r) = self.stream_mut(session, id).filter(|r| !r.recv_done) else {
            return;
        };
        let _ = r
            .shared
            .rx_end
            .set(Err(Error::new(ErrorKind::Stopped(error), "the stream was stopped")));
        r.rx_tx = None;
        let _ = self.cmd(
            now,
            Command::StopSending {
                session,
                stream: id,
                error,
            },
        );
        self.pump_recv(now, session, id);
    }

    /// Move bytes from the write channel into the endpoint, as far as it takes them.
    fn pump_send(&mut self, now: u64, session: SessionId, id: StreamId) {
        loop {
            let Some(r) = self.stream_mut(session, id).filter(|r| !r.send_done) else {
                return;
            };
            let (block, off) = if let Some(cur) = r.cur.take() {
                cur
            } else {
                let Some(rx) = r.tx_rx.as_ref() else { return };
                match rx.try_recv() {
                    Some(Item::Data(v)) if v.is_empty() => continue,
                    Some(Item::Data(v)) => (v, 0),
                    // The writer finished, or dropped the stream, which finishes it.
                    Some(Item::Fin) => return self.finish(now, session, id),
                    None if rx.is_disconnected() => return self.finish(now, session, id),
                    None => return,
                }
            };
            match self.cmd(
                now,
                Command::Write {
                    session,
                    stream: id,
                    data: block.get(off..).unwrap_or_default(),
                },
            ) {
                Ok(Reply {
                    value: Value::Written(n),
                    ..
                }) => {
                    if off + n < block.len() {
                        if let Some(r) = self.stream_mut(session, id) {
                            r.cur = Some((block, off + n));
                        }
                        return;
                    }
                }
                Ok(_) => {}
                Err(e) => return self.send_refused(session, id, e),
            }
        }
    }

    /// A write or finish the endpoint refused. A send half the peer stopped refuses as finished before the stop event
    /// behind it is handled; that event carries the code the writer must see, so it is left to fail the stream.
    fn send_refused(&mut self, session: SessionId, id: StreamId, e: CommandError) {
        if !self.sweeping && matches!(e, CommandError::Stream(StreamError::Finished)) {
            return;
        }
        self.send_fail(session, id, Error::command(e));
    }

    fn finish(&mut self, now: u64, session: SessionId, id: StreamId) {
        match self.cmd(now, Command::Finish { session, stream: id }) {
            Ok(_) => {
                if let Some(r) = self.stream_mut(session, id) {
                    r.send_done = true;
                    r.tx_rx = None;
                }
                self.reap(session, id);
            }
            Err(e) => self.send_refused(session, id, e),
        }
    }

    fn on_ctl(&mut self, now: u64, c: Ctl) {
        match c {
            Ctl::Nudge(session, id) => {
                if let Some(r) = self.stream_mut(session, id) {
                    r.shared.pump.store(false, Ordering::Release);
                }
                self.pump_send(now, session, id);
                self.pump_recv(now, session, id);
            }
            Ctl::Datagrams(session) => self.pump_datagrams(session),
            Ctl::Stop(session, id, error) => self.stop_recv(now, session, id, error),
            Ctl::Reset(session, id, error) => {
                let _ = self.cmd(
                    now,
                    Command::Reset {
                        session,
                        stream: id,
                        error,
                    },
                );
                self.send_fail(
                    session,
                    id,
                    Error::new(ErrorKind::Stopped(error), "the stream was reset"),
                );
            }
            Ctl::Close(session, error) => {
                let _ = self.cmd(now, Command::Close { session, error });
            }
            Ctl::ClosePeer(node) => {
                let all: Vec<SessionId> = self
                    .sessions
                    .iter()
                    .filter(|(_, r)| r.shared.node == node)
                    .map(|(s, _)| *s)
                    .collect();
                for session in all {
                    let _ = self.cmd(now, Command::Close { session, error: 0 });
                }
            }
            Ctl::AddAddr(node, addr) => {
                let v = self.book.entry(node).or_default();
                if !v.contains(&addr) && v.len() < 8 {
                    v.push(addr);
                }
            }
            Ctl::NetworkChange => {
                for id in self.ifaces.clone() {
                    self.ep.iface_event(now, id, IfaceEvent::Down);
                    self.ep.iface_event(now, id, IfaceEvent::Up);
                }
            }
            Ctl::Suspend => {
                let _ = self.cmd(now, Command::Suspend);
            }
            Ctl::Resume(moved) => {
                let _ = self.cmd(now, Command::Resume { moved });
            }
            Ctl::Dropped => self.begin_shutdown(now, None),
        }
    }

    fn begin_shutdown(&mut self, now: u64, reply: Option<Sender<()>>) {
        let first = self.shutdown.is_none();
        let (_, waiting) = self
            .shutdown
            .get_or_insert_with(|| (now.saturating_add(SHUTDOWN_GRACE), Vec::new()));
        waiting.extend(reply);
        if first {
            let _ = self.cmd(now, Command::Shutdown);
        }
    }

    fn on_request(&mut self, now: u64, r: Request) {
        if self.shutdown.is_some() {
            return match r {
                Request::Shutdown { reply } => self.begin_shutdown(now, Some(reply)),
                r => Self::refuse(r),
            };
        }
        match r {
            Request::Connect {
                node,
                alpn,
                mut addrs,
                reply,
            } => {
                if self.sessions.len() >= self.limits.connections {
                    return reply.send(Err(Error::new(ErrorKind::Busy, "the connection table is full")));
                }
                for a in self.book.get(&node).into_iter().flatten() {
                    if !addrs.contains(a) {
                        addrs.push(*a);
                    }
                }
                match self.connect(now, node, &alpn, &addrs) {
                    Ok(Reply {
                        value: Value::Session(session),
                        ..
                    }) => {
                        self.dials.push(Dial {
                            session,
                            node,
                            alpn,
                            reply,
                        });
                    }
                    Ok(_) => reply.send(Err(Error::new(ErrorKind::Unreachable, "the dial did not start"))),
                    Err(e) => reply.send(Err(Error::command(e))),
                }
            }
            Request::Open { session, bidi, reply } => {
                let r = self.open(now, session, bidi);
                reply.send(r);
            }
            Request::Datagram { session, data, reply } => {
                reply.send(
                    self.cmd(now, Command::SendDatagram { session, data: &data })
                        .map(|_| ())
                        .map_err(Error::command),
                );
            }
            Request::Stats { session, reply } => {
                reply.send(match self.ep.query(Query::Stats(session)) {
                    Answer::Stats(s) => Ok(s),
                    _ => Err(Error::command(CommandError::NoSession)),
                });
            }
            Request::Peers { reply } => {
                let mut v: Vec<NodeId> = self.sessions.values().map(|s| s.shared.node).collect();
                v.sort_by_key(|n| n.bytes);
                v.dedup();
                reply.send(v);
            }
            Request::Node { reply } => reply.send(self.ep.node_stats()),
            Request::Listen { alpn, reply } => reply.send(self.listen(&alpn)),
            Request::Shutdown { reply } => self.begin_shutdown(now, Some(reply)),
        }
    }

    /// Answer a request that arrives while the engine is stopping.
    fn refuse(r: Request) {
        match r {
            Request::Connect { reply, .. } => reply.send(Err(Error::shutdown())),
            Request::Open { reply, .. } => reply.send(Err(Error::shutdown())),
            Request::Datagram { reply, .. } => reply.send(Err(Error::shutdown())),
            Request::Stats { reply, .. } => reply.send(Err(Error::shutdown())),
            Request::Listen { reply, .. } => reply.send(Err(Error::shutdown())),
            Request::Shutdown { reply } => reply.send(()),
            Request::Peers { .. } | Request::Node { .. } => {}
        }
    }

    fn listen(&mut self, alpn: &[u8]) -> Result<Receiver<Arc<SessionShared>>> {
        if self.routes.iter().any(|(a, _)| a == alpn) || self.routes.len() >= MAX_ALPNS {
            return Err(Error::config("the protocol is already registered or too many are"));
        }
        if !self.ep.register_alpn(alpn) {
            return Err(Error::config("the protocol name is empty, too long or one too many"));
        }
        let (tx, rx) = chan(self.limits.accept_sessions);
        self.routes.push((alpn.to_vec(), tx));
        Ok(rx)
    }

    /// Dial. While the application has left too many events unread the endpoint holds a dial back: read them and try
    /// again, so the caller never sees an error for the endpoint's own back-pressure.
    fn connect(
        &mut self,
        now: u64,
        node: NodeId,
        alpn: &[u8],
        addrs: &[SocketAddr],
    ) -> core::result::Result<Reply, CommandError> {
        for _ in 0..2 {
            let r = self.cmd(
                now,
                Command::Connect {
                    node,
                    alpn,
                    addrs,
                    role: Role::Other,
                },
            );
            if !matches!(r, Err(CommandError::EventsPending)) {
                return r;
            }
            while let Some(ev) = self.backlog.pop_front().or_else(|| self.ep.poll_event()) {
                self.on_event(now, ev);
            }
        }
        self.cmd(
            now,
            Command::Connect {
                node,
                alpn,
                addrs,
                role: Role::Other,
            },
        )
    }

    fn open(&mut self, now: u64, session: SessionId, bidi: bool) -> Result<NewStream> {
        let Value::Stream(id) = self
            .cmd(now, Command::OpenStream { session, bidi })
            .map_err(Error::command)?
            .value
        else {
            return Err(Error::new(ErrorKind::Busy, "the stream did not open"));
        };
        let (rec, new) = self.make_stream(session, id, true, bidi);
        self.sessions
            .get_mut(&session)
            .ok_or_else(|| Error::command(CommandError::NoSession))?
            .streams
            .insert(id, rec);
        Ok(new)
    }
}
