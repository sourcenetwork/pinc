//! An in-memory network for the protocol tests: a [`Host`] per node, byte pipes with arbitrary chunking and
//! backpressure, and a driver that moves actions, bytes and events until nothing is left to do.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::rc::Rc;

use vinc_core::SessionId;
use vinc_sim::suite::crypto::Registry;
use vinc_sim::suite::grade::fixture::blank_world;
use vinc_sim::suite::proto::host::{Host, LayerEvent, Layers};
use vinc_sim::suite::proto::{Durable, MsgIntents, Stack};
use vinc_sim::suite::rec::{NS, Rec};
use vinc_sim::suite::world::model::{Intent, IntentKind, Must, World};

pub enum Action {
    Connect { peer: usize, alpn: &'static [u8] },
    Open { session: SessionId, stream: u64 },
    Close { session: SessionId },
    Reset { session: SessionId, stream: u64 },
}

#[derive(Default)]
pub struct Pipe {
    pub buf: VecDeque<u8>,
    pub fin: bool,
    pub fin_sent: bool,
    pub blocked: bool,
}

pub struct TestHost {
    pub idx: usize,
    pub reg: &'static Registry,
    pub cap: usize,
    pub actions: Vec<Action>,
    pub peers: BTreeMap<SessionId, usize>,
    pub next_stream: BTreeMap<SessionId, u64>,
    pub pipes: BTreeMap<(SessionId, u64), Pipe>,
    pub written: u64,
    pub resets: Vec<(SessionId, u64, u64)>,
    pub connects: Vec<(usize, Vec<u8>)>,
    pub open_ok: bool,
    pub subscribed: Vec<Vec<u8>>,
    pub published: Vec<(Vec<u8>, Vec<u8>)>,
}

impl TestHost {
    pub fn new(idx: usize, reg: &'static Registry, cap: usize) -> Self {
        Self {
            idx,
            reg,
            cap,
            actions: Vec::new(),
            peers: BTreeMap::new(),
            next_stream: BTreeMap::new(),
            pipes: BTreeMap::new(),
            written: 0,
            resets: Vec::new(),
            connects: Vec::new(),
            open_ok: true,
            subscribed: Vec::new(),
            published: Vec::new(),
        }
    }

    /// Everything written to a stream that has not been moved yet, as bytes.
    pub fn pending_bytes(&self) -> Vec<u8> {
        self.pipes.values().flat_map(|p| p.buf.iter().copied()).collect()
    }
}

impl Host for TestHost {
    fn idx(&self) -> usize {
        self.idx
    }
    fn registry(&self) -> &'static Registry {
        self.reg
    }
    fn connect(&mut self, peer: usize, alpn: &'static [u8]) -> bool {
        self.connects.push((peer, alpn.to_vec()));
        self.actions.push(Action::Connect { peer, alpn });
        true
    }
    fn open_stream(&mut self, session: SessionId) -> Option<u64> {
        if !self.open_ok {
            return None;
        }
        let n = self.next_stream.entry(session).or_insert(0);
        let stream = *n * 2 + (self.idx as u64 & 1);
        *n += 1;
        self.actions.push(Action::Open { session, stream });
        Some(stream)
    }
    fn write(&mut self, session: SessionId, stream: u64, data: &[u8]) -> usize {
        let cap = self.cap;
        let p = self.pipes.entry((session, stream)).or_default();
        let n = cap.saturating_sub(p.buf.len()).min(data.len());
        p.buf.extend(&data[..n]);
        p.blocked = n < data.len();
        self.written += n as u64;
        n
    }
    fn finish(&mut self, session: SessionId, stream: u64) {
        self.pipes.entry((session, stream)).or_default().fin = true;
    }
    fn reset(&mut self, session: SessionId, stream: u64, code: u64) {
        self.resets.push((session, stream, code));
        self.actions.push(Action::Reset { session, stream });
    }
    fn close(&mut self, session: SessionId, _code: u64) {
        self.actions.push(Action::Close { session });
    }
    fn peer_of(&self, session: SessionId) -> Option<usize> {
        self.peers.get(&session).copied()
    }
    fn subscribe(&mut self, topic: &[u8]) -> bool {
        self.subscribed.push(topic.to_vec());
        true
    }
    fn publish(&mut self, topic: &[u8], msg: &[u8]) -> bool {
        self.published.push((topic.to_vec(), msg.to_vec()));
        true
    }
}

/// An owned event.
pub enum Ev {
    Incoming {
        session: SessionId,
        peer: usize,
        alpn: &'static [u8],
    },
    Connected {
        session: SessionId,
        peer: usize,
        alpn: &'static [u8],
    },
    ConnectFailed {
        peer: usize,
        alpn: &'static [u8],
    },
    Closed {
        session: SessionId,
    },
    Opened {
        session: SessionId,
        stream: u64,
    },
    Data {
        session: SessionId,
        stream: u64,
        data: Vec<u8>,
        fin: bool,
    },
    Reset {
        session: SessionId,
        stream: u64,
    },
    Writable {
        session: SessionId,
        stream: u64,
    },
}

impl Ev {
    pub fn layer(&self) -> LayerEvent<'_> {
        match self {
            Self::Incoming { session, peer, alpn } => LayerEvent::Incoming {
                session: *session,
                peer: *peer,
                alpn,
            },
            Self::Connected { session, peer, alpn } => LayerEvent::Connected {
                session: *session,
                peer: *peer,
                alpn,
            },
            Self::ConnectFailed { peer, alpn } => LayerEvent::ConnectFailed { peer: *peer, alpn },
            Self::Closed { session } => LayerEvent::Closed { session: *session },
            Self::Opened { session, stream } => LayerEvent::StreamOpened {
                session: *session,
                stream: *stream,
            },
            Self::Data {
                session,
                stream,
                data,
                fin,
            } => LayerEvent::StreamData {
                session: *session,
                stream: *stream,
                data,
                fin: *fin,
            },
            Self::Reset { session, stream } => LayerEvent::StreamReset {
                session: *session,
                stream: *stream,
            },
            Self::Writable { session, stream } => LayerEvent::StreamWritable {
                session: *session,
                stream: *stream,
            },
        }
    }
}

pub struct Node {
    pub stack: Stack,
    pub host: TestHost,
    pub durable: Rc<RefCell<Durable>>,
}

pub struct Net {
    pub now: u64,
    pub world: Rc<World>,
    pub rec: Rc<RefCell<Rec>>,
    pub reg: &'static Registry,
    pub nodes: Vec<Node>,
    pub chunk: usize,
    pub cap: usize,
    /// Nodes whose bytes are lost in transit.
    pub lose: BTreeSet<usize>,
    pub shared: MsgIntents,
    /// Every dial made, with the time it was carried out.
    pub dials: Vec<(usize, u64)>,
    next_session: u64,
}

pub fn base_intent(node: usize, kind: IntentKind) -> Intent {
    Intent {
        t: 0,
        node,
        kind,
        to: None,
        topic: None,
        size: None,
        req: None,
        resp: None,
        deadline_ns: 60 * NS,
        receivers: Vec::new(),
        must: Must::Flag(true),
        value: None,
        providers: Vec::new(),
        ranges: Vec::new(),
        stream_rate: None,
        probe: false,
        under_bulk: false,
        set_ref: None,
    }
}

pub fn new_world(nodes: usize) -> World {
    blank_world("S2", nodes, 1000 * NS)
}

/// Lets `node` ask the oracle about `principal`, so a delivery from it is allowed.
pub fn allow(rec: &Rc<RefCell<Rec>>, node: usize, principal: usize) {
    rec.borrow_mut().acp_decide(0, node, Some(principal));
}

impl Net {
    pub fn new(nodes: usize, chunk: usize, cap: usize) -> Self {
        Self::with_world(new_world(nodes), chunk, cap)
    }

    pub fn with_world(world: World, chunk: usize, cap: usize) -> Self {
        let n = world.nodes.len();
        let world = Rc::new(world);
        let rec = Rc::new(RefCell::new(Rec::new(world.clone())));
        let reg: &'static Registry = Registry::leak(7);
        let shared = MsgIntents::default();
        let mut net = Self {
            now: 0,
            world,
            rec,
            reg,
            nodes: Vec::new(),
            chunk,
            cap,
            lose: BTreeSet::new(),
            shared,
            dials: Vec::new(),
            next_session: 1,
        };
        for idx in 0..n {
            let durable = Rc::new(RefCell::new(Durable::sharing(net.shared.clone())));
            let stack = Stack::new(idx, net.world.clone(), net.rec.clone(), durable.clone());
            let host = TestHost::new(idx, reg, cap);
            net.nodes.push(Node { stack, host, durable });
        }
        net
    }

    pub fn boot(&mut self) {
        for n in &mut self.nodes {
            n.stack.boot(self.now, &mut n.host);
        }
        self.run();
    }

    pub fn intent(&mut self, node: usize, d: &Intent) {
        let n = &mut self.nodes[node];
        n.stack.intent(self.now, &mut n.host, d);
    }

    /// Ends every session at once (a lost connection); both ends get `Closed`.
    pub fn kill_sessions(&mut self) {
        let ids: BTreeSet<SessionId> = self.nodes.iter().flat_map(|n| n.host.peers.keys().copied()).collect();
        for s in ids {
            for (i, ev) in self.close_events(s) {
                self.deliver(i, &ev);
            }
        }
    }

    /// Stops node `idx` and starts a new stack on the same durable state.
    pub fn restart(&mut self, idx: usize) {
        let sessions: Vec<SessionId> = self.nodes[idx].host.peers.keys().copied().collect();
        self.nodes[idx].stack.stop();
        for s in sessions {
            self.nodes[idx].host.peers.remove(&s);
            self.nodes[idx].host.pipes.retain(|k, _| k.0 != s);
            let peer = (0..self.nodes.len()).find(|&p| p != idx && self.nodes[p].host.peers.contains_key(&s));
            if let Some(p) = peer {
                self.nodes[p].host.peers.remove(&s);
                self.nodes[p].host.pipes.retain(|k, _| k.0 != s);
                self.deliver(p, &Ev::Closed { session: s });
            }
        }
        let durable = self.nodes[idx].durable.clone();
        let stack = Stack::new(idx, self.world.clone(), self.rec.clone(), durable);
        self.nodes[idx].stack = stack;
        self.nodes[idx].host = TestHost::new(idx, self.reg, self.cap);
        let n = &mut self.nodes[idx];
        n.stack.boot(self.now, &mut n.host);
    }

    fn deliver(&mut self, node: usize, ev: &Ev) {
        let n = &mut self.nodes[node];
        n.stack.event(self.now, &mut n.host, ev.layer());
    }

    /// One round: carry out the actions, move up to `chunk` bytes per pipe, deliver the events. Returns whether
    /// anything happened.
    fn step(&mut self) -> bool {
        let mut events: Vec<(usize, Ev)> = Vec::new();
        for i in 0..self.nodes.len() {
            let actions = std::mem::take(&mut self.nodes[i].host.actions);
            for a in actions {
                match a {
                    Action::Connect { peer, alpn } => {
                        self.dials.push((peer, self.now));
                        if peer == i || peer >= self.nodes.len() {
                            events.push((i, Ev::ConnectFailed { peer, alpn }));
                            continue;
                        }
                        let session = SessionId(self.next_session);
                        self.next_session += 1;
                        self.nodes[i].host.peers.insert(session, peer);
                        self.nodes[peer].host.peers.insert(session, i);
                        events.push((peer, Ev::Incoming { session, peer: i, alpn }));
                        events.push((i, Ev::Connected { session, peer, alpn }));
                    }
                    Action::Open { session, stream } => {
                        if let Some(&p) = self.nodes[i].host.peers.get(&session) {
                            events.push((p, Ev::Opened { session, stream }));
                        }
                    }
                    Action::Close { session } => {
                        events.extend(self.close_events(session));
                    }
                    Action::Reset { session, stream } => {
                        if let Some(&p) = self.nodes[i].host.peers.get(&session) {
                            self.nodes[i].host.pipes.remove(&(session, stream));
                            events.push((p, Ev::Reset { session, stream }));
                        }
                    }
                }
            }
        }
        for i in 0..self.nodes.len() {
            let keys: Vec<(SessionId, u64)> = self.nodes[i].host.pipes.keys().copied().collect();
            for key in keys {
                let Some(&peer) = self.nodes[i].host.peers.get(&key.0) else {
                    self.nodes[i].host.pipes.remove(&key);
                    continue;
                };
                let lose = self.lose.contains(&i);
                let chunk = self.chunk;
                let cap = self.cap;
                let Some(p) = self.nodes[i].host.pipes.get_mut(&key) else {
                    continue;
                };
                let take = chunk.min(p.buf.len());
                let data: Vec<u8> = p.buf.drain(..take).collect();
                let fin = p.fin && !p.fin_sent && p.buf.is_empty();
                if fin {
                    p.fin_sent = true;
                }
                let unblock = p.blocked && p.buf.len() < cap;
                if unblock {
                    p.blocked = false;
                }
                if !data.is_empty() || fin {
                    if !lose {
                        events.push((
                            peer,
                            Ev::Data {
                                session: key.0,
                                stream: key.1,
                                data,
                                fin,
                            },
                        ));
                    }
                }
                if unblock {
                    events.push((
                        i,
                        Ev::Writable {
                            session: key.0,
                            stream: key.1,
                        },
                    ));
                }
            }
        }
        let progressed = !events.is_empty();
        for (node, ev) in events {
            // an event for a session that has since ended is dropped, as the endpoint would
            let live = match &ev {
                Ev::Incoming { .. } | Ev::Connected { .. } | Ev::ConnectFailed { .. } | Ev::Closed { .. } => true,
                Ev::Opened { session, .. }
                | Ev::Data { session, .. }
                | Ev::Reset { session, .. }
                | Ev::Writable { session, .. } => self.nodes[node].host.peers.contains_key(session),
            };
            if live {
                self.deliver(node, &ev);
            }
        }
        progressed
    }

    fn close_events(&mut self, session: SessionId) -> Vec<(usize, Ev)> {
        let mut out = Vec::new();
        for (i, n) in self.nodes.iter_mut().enumerate() {
            if n.host.peers.remove(&session).is_some() {
                n.host.pipes.retain(|k, _| k.0 != session);
                out.push((i, Ev::Closed { session }));
            }
        }
        out
    }

    /// Rounds of 1 ms until no action, byte or event is left.
    pub fn settle(&mut self) {
        for _ in 0..2_000_000 {
            self.now += 1_000_000;
            if !self.step() {
                return;
            }
        }
        panic!("the network did not settle");
    }

    fn fire_due(&mut self) {
        for n in &mut self.nodes {
            if n.stack.poll_timeout().is_some_and(|t| t <= self.now) {
                n.stack.timeout(self.now, &mut n.host);
            }
        }
    }

    /// Runs exactly `n` rounds of 1 ms.
    pub fn rounds(&mut self, n: usize) {
        for _ in 0..n {
            self.now += 1_000_000;
            self.step();
        }
    }

    /// Settles; while only timers remain, time jumps to the next one.
    pub fn run(&mut self) {
        loop {
            self.settle();
            let Some(t) = self.nodes.iter().filter_map(|n| n.stack.poll_timeout()).min() else {
                return;
            };
            self.now = self.now.max(t);
            self.fire_due();
        }
    }

    /// Moves time forward by `ns`: timers due on the way fire and the network settles after each.
    pub fn advance(&mut self, ns: u64) {
        let until = self.now + ns;
        self.settle();
        while let Some(t) = self.nodes.iter().filter_map(|n| n.stack.poll_timeout()).min() {
            if t > until {
                break;
            }
            self.now = self.now.max(t);
            self.fire_due();
            self.settle();
        }
        self.now = self.now.max(until);
    }
}
