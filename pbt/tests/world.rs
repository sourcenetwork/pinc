//! `pinc-sim` suite nodes (real `pinc-node` nodes: the endpoint, the connectivity client with its relays, membership,
//! broadcast) in small generated networks of the three shapes the project requires, under a generated application
//! script.
//!
//! The shapes. A relay is a node like every other node that carries the relay role; in the suite a node carries the
//! relay and hub roles when it is a bootstrap node ("A bootstrap node is a hub: it also runs the relay for its
//! members", suite/node/mod.rs).
//! - Ordinary: every node runs the application; one or two of them (public ones) also carry the relay and hub roles.
//! - Dedicated: the relay and hub roles are carried only by nodes that do nothing else (no application work), the
//!   nodes the relay binary deploys; the application nodes carry no relay role.
//! - Mixed: one application node carries the roles and one or two dedicated nodes carry them too.
//!
//! Where the expected behaviour comes from:
//! - Reachability: the application dials by node id alone ("The application dials by node id alone: the
//!   connectivity layer finds the way", suite/node/events.rs `connect`), and a node with no public address is found
//!   through a hub (the existing test `a_dial_of_a_node_with_no_public_address_is_carried_by_the_connectivity_layer`,
//!   tests/scenario_node.rs). So every pair of application nodes reaches each other once the faults have stopped
//!   (partitions healed, the restarted relay-role node up again), whatever the NATs: within `FINAL_BOUND` of virtual
//!   time each node delivers a message to each other node.
//! - Streams: bytes read equal bytes written, in order, and a stream's end comes once (universal: no data loss, no
//!   duplication; `pinc_transport::stream`). Every message is self-describing, so the receiver checks it alone.
//! - Broadcast: "delivers each message at most once (ids are remembered for 600 s)" (pinc-broadcast lib.rs), and
//!   "A broadcast message, delivered once; its signature over this exact body verified" (pinc-node event.rs).
//! - The shapes agree: a network of ordinary nodes only reaches the same end state (which pairs reached each other
//!   in the final phase, and whether every final message came intact) as the same world with a dedicated relay-role
//!   node added.
//! - No panic, no failed debug assertion, no overflow (the crates' rule), and no timer the node had to be woken for
//!   late (`SuiteNode::timer_violations`, held at 0 by tests/scenario_node.rs).
//!
//! Every case runs on one long-lived thread, as the suite's own runner does, so the connection tables of finished
//! runs are reused by later ones (`pinc-sim` suite/node/mem.rs). The comparison of two runs compares only outcomes the
//! oracles hold absolute (every final pair delivered, every byte intact), never traces or timings: the simulator is
//! not deterministic across runs of one process (`repro_sim.rs`, and `repro_slots.rs` for the slot leak behind it).
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::net::SocketAddr;
use std::rc::Rc;

use ephyra::{check_generator, gens};
use pinc_core::SessionId;
use pinc_sim::suite::crypto::Registry;
use pinc_sim::suite::grade::fixture::blank_world;
use pinc_sim::suite::node::{Cmd, NodeEvent, Shared, SuiteCost, SuiteNode, iface_ip};
use pinc_sim::suite::proto::host::{Host, LayerEvent, Layers};
use pinc_sim::suite::rec::Rec;
use pinc_sim::suite::world::model::{Addr, IfaceSpec, Intent, IntentKind, Must, World};
use pinc_sim::{LinkConfig, Loss, NatConfig, NatKind, NodeId, PortPolicy, Sim, SimConfig, StreamKind};
use pinc_transport::stream::StreamId;

const NS: u64 = 1_000_000_000;
const MS: u64 = 1_000_000;
const ALPN: &[u8] = b"pbt/world";
const TOPIC: &[u8] = b"pbt-topic";
/// When the final round starts: every fault is over by then.
const FINAL: u64 = 32 * NS;
/// How long after `FINAL` every pair must have delivered its final message.
const FINAL_BOUND: u64 = 40 * NS;
const RETRY: u64 = NS;
const MAX_RETRIES: u32 = 30;

// ---------------------------------------------------------------- the generated world

#[derive(Clone, Copy, Debug, PartialEq, Eq, ephyra::Arbitrary)]
enum Shape {
    Ordinary,
    Dedicated,
    Mixed,
}

#[derive(Clone, Copy, Debug, ephyra::Arbitrary)]
struct AppNode {
    public: bool,
    /// The NAT in front of a private node: FullCone, AddressRestricted, PortRestricted, Symmetric, DependentOpen,
    /// DependentAddress.
    #[ephyra(gen = gens::int(0u8..=5))]
    nat: u8,
}

#[derive(Clone, Copy, Debug, ephyra::Arbitrary)]
enum AppOp {
    Dial(u8),
    Send(u8, #[ephyra(gen = gens::int(10u32..=40_000))] u32),
    Close(u8),
    Publish(#[ephyra(gen = gens::int(10u16..=1500))] u16),
}

#[derive(Clone, Copy, Debug, ephyra::Arbitrary)]
struct Step {
    #[ephyra(gen = gens::int(3_000u32..=30_000))]
    t_ms: u32,
    node: u8,
    op: AppOp,
}

#[derive(Clone, Copy, Debug, ephyra::Arbitrary)]
struct Part {
    #[ephyra(gen = gens::int(3u8..=18))]
    at_s: u8,
    #[ephyra(gen = gens::int(1u8..=10))]
    len_s: u8,
    /// Bit `i` puts node `i` on the first side.
    mask: u8,
}

#[derive(Clone, Copy, Debug, ephyra::Arbitrary)]
struct Restart {
    #[ephyra(gen = gens::int(5u8..=24))]
    at_s: u8,
    #[ephyra(gen = gens::int(1u8..=4))]
    down_s: u8,
    /// Which relay-role node.
    hub: u8,
    /// Persist its state just before it goes down.
    persist: bool,
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Spec {
    shape: Shape,
    #[ephyra(gen = gens::vec(ephyra::any::<AppNode>()).len(2..=6))]
    apps: Vec<AppNode>,
    #[ephyra(gen = gens::int(1u8..=2))]
    dedicated: u8,
    /// Loss per mille on every link, all the time.
    #[ephyra(gen = gens::frequency(vec![(2, gens::constant(0u16).boxed()), (1, gens::int(1u16..=30).boxed())]))]
    loss_pm: u16,
    reorder: bool,
    partition: Option<Part>,
    restart: Option<Restart>,
    #[ephyra(gen = gens::vec(ephyra::any::<Step>()).len(0..=16))]
    script: Vec<Step>,
    seed: u64,
}

/// The layout a spec gives: node indices of the application nodes, the dedicated nodes, the relay-role nodes.
struct Layout {
    apps: usize,
    dedicated: usize,
    hubs: Vec<usize>,
    public: Vec<bool>,
}

fn layout(s: &Spec, extra_dedicated: usize) -> Layout {
    let apps = s.apps.len();
    let base = if s.shape == Shape::Ordinary { 0 } else { usize::from(s.dedicated) };
    let dedicated = base + extra_dedicated;
    let mut public: Vec<bool> = s.apps.iter().map(|a| a.public).collect();
    if s.shape != Shape::Dedicated {
        // An application node carries the relay role: it needs a public address.
        public[0] = true;
    }
    public.extend(std::iter::repeat_n(true, dedicated));
    let mut hubs: Vec<usize> = match s.shape {
        Shape::Ordinary => (0..apps).filter(|&i| public[i]).take(2).collect(),
        Shape::Dedicated => Vec::new(),
        Shape::Mixed => vec![0],
    };
    hubs.extend(apps..apps + dedicated);
    Layout {
        apps,
        dedicated,
        hubs,
        public,
    }
}

fn iface(name: &str, kind: &str, akind: &str, host: u64, port: u16, public: bool) -> IfaceSpec {
    IfaceSpec {
        name: name.to_owned(),
        kind: kind.to_owned(),
        addr: Addr {
            kind: akind.to_owned(),
            host,
            port,
        },
        mtu: if kind == "udp4" { 1472 } else { 1 << 20 },
        public,
        v6: false,
    }
}

fn host_of(i: usize, public: bool) -> u64 {
    if public { 1_000_000 + i as u64 } else { 3_000_000 + i as u64 * 256 }
}

fn make_world(s: &Spec, l: &Layout) -> World {
    let n = l.apps + l.dedicated;
    let mut w = blank_world("S1", n, FINAL + FINAL_BOUND + 10 * NS);
    w.seed = s.seed | 1;
    for i in 0..n {
        let p = l.public[i];
        let h = host_of(i, p);
        let (tp, wp) = if p { (443, 8443) } else { (50_000, 50_001) };
        w.nodes[i].ifaces = vec![
            iface("u4", "udp4", "udp4", h, 4433, p),
            iface("t", "tcp", "tcp4", h, tp, p),
            iface("w", "ws", "tcp4", h, wp, p),
        ];
        if p {
            "cloud".clone_into(&mut w.nodes[i].device);
            "cloud".clone_into(&mut w.nodes[i].kind);
            w.clouds.push(i);
        } else {
            w.homes.push(i);
        }
    }
    w.bootstrap.clone_from(&l.hubs);
    w
}

const NATS: [NatKind; 6] = [
    NatKind::FullCone,
    NatKind::AddressRestricted,
    NatKind::PortRestricted,
    NatKind::Symmetric,
    NatKind::DependentOpen,
    NatKind::DependentAddress,
];

// ---------------------------------------------------------------- the application

/// What every node of a run reports to the oracles.
#[derive(Default)]
struct Ledger {
    /// (from, seq) to (to, length, final).
    sent: BTreeMap<(usize, u32), (usize, u32, bool)>,
    /// (from, seq) to how many times a whole, intact message reached its receiver.
    delivered: BTreeMap<(usize, u32), u32>,
    /// (from, to) of the final messages delivered whole and intact.
    final_ok: BTreeSet<(usize, usize)>,
    /// (from, seq, receiver) of broadcast messages to their deliveries.
    bcast: BTreeMap<(usize, u32, usize), u32>,
    bad: Vec<(&'static str, String)>,
}

impl Ledger {
    fn bad(&mut self, sig: &'static str, detail: String) {
        if self.bad.len() < 16 {
            self.bad.push((sig, detail));
        }
    }
}

const HDR: usize = 10;

fn byte_at(from: usize, seq: u32, p: usize) -> u8 {
    (from as u32).wrapping_mul(31).wrapping_add(seq.wrapping_mul(7)).wrapping_add(p as u32) as u8
}

/// A self-describing message: magic, sender, sequence number, total length, then bytes the receiver can recompute.
fn message(magic: u8, from: usize, seq: u32, len: u32) -> Vec<u8> {
    let len = (len as usize).max(HDR);
    let mut m = Vec::with_capacity(len);
    m.push(magic);
    m.push(from as u8);
    m.extend_from_slice(&seq.to_le_bytes());
    m.extend_from_slice(&(len as u32).to_le_bytes());
    m.extend((HDR..len).map(|p| byte_at(from, seq, p)));
    m
}

/// The header of a message, if `b` holds it and its magic is `magic`: (from, seq, len).
fn header(magic: u8, b: &[u8]) -> Option<(usize, u32, u32)> {
    if b.len() < HDR || b[0] != magic {
        return None;
    }
    let seq = u32::from_le_bytes(b[2..6].try_into().ok()?);
    let len = u32::from_le_bytes(b[6..10].try_into().ok()?);
    Some((usize::from(b[1]), seq, len))
}

/// The first position at which `b` is not a prefix of the message its header names.
fn first_wrong(b: &[u8], from: usize, seq: u32) -> Option<usize> {
    (HDR..b.len()).find(|&p| b[p] != byte_at(from, seq, p))
}

struct Out {
    data: Vec<u8>,
    off: usize,
    to: usize,
    final_: bool,
}

struct Pending {
    len: u32,
    final_: bool,
}

struct In {
    got: Vec<u8>,
    done: bool,
    /// (time, bytes, fin) of every data event, for the failure message.
    log: Vec<(u64, usize, bool)>,
}

struct App {
    idx: usize,
    apps: usize,
    script: Vec<(u64, AppOp)>,
    next: usize,
    led: Rc<RefCell<Ledger>>,
    seq: u32,
    open: BTreeMap<usize, SessionId>,
    ours: BTreeSet<SessionId>,
    waiting: BTreeMap<usize, Vec<Pending>>,
    retry_at: BTreeMap<usize, u64>,
    retries: BTreeMap<usize, u32>,
    final_sent: bool,
    out: BTreeMap<(SessionId, StreamId), Out>,
    inbox: BTreeMap<(SessionId, StreamId), In>,
}

impl App {
    fn new(idx: usize, apps: usize, mut script: Vec<(u64, AppOp)>, led: Rc<RefCell<Ledger>>) -> Self {
        script.sort_by_key(|(t, _)| *t);
        Self {
            idx,
            apps,
            script,
            next: 0,
            led,
            seq: 0,
            open: BTreeMap::new(),
            ours: BTreeSet::new(),
            waiting: BTreeMap::new(),
            retry_at: BTreeMap::new(),
            retries: BTreeMap::new(),
            final_sent: false,
            out: BTreeMap::new(),
            inbox: BTreeMap::new(),
        }
    }

    fn peer(&self, x: u8) -> Option<usize> {
        if self.apps < 2 {
            return None;
        }
        let p = usize::from(x) % self.apps;
        Some(if p == self.idx { (p + 1) % self.apps } else { p })
    }

    fn dial(&mut self, now: u64, host: &mut dyn Host, to: usize) {
        if self.open.contains_key(&to) {
            return;
        }
        if !host.connect(to, ALPN) {
            self.retry_at.insert(to, now + RETRY);
        }
    }

    fn queue(&mut self, now: u64, host: &mut dyn Host, to: usize, len: u32, final_: bool) {
        self.waiting.entry(to).or_default().push(Pending { len, final_ });
        match self.open.get(&to).copied() {
            Some(s) => self.flush(now, host, to, s),
            None => self.dial(now, host, to),
        }
    }

    fn flush(&mut self, now: u64, host: &mut dyn Host, to: usize, session: SessionId) {
        for p in self.waiting.remove(&to).unwrap_or_default() {
            let Some(stream) = host.open_stream(session) else {
                // No stream now (the stream table is full or the session is going): the message is tried again.
                self.waiting.entry(to).or_default().push(p);
                self.retry_at.insert(to, now + RETRY);
                continue;
            };
            self.seq += 1;
            let data = message(0xA5, self.idx, self.seq, p.len);
            self.led
                .borrow_mut()
                .sent
                .insert((self.idx, self.seq), (to, data.len() as u32, p.final_));
            self.out.insert(
                (session, stream),
                Out {
                    data,
                    off: 0,
                    to,
                    final_: p.final_,
                },
            );
            self.push(host, (session, stream));
        }
    }

    fn push(&mut self, host: &mut dyn Host, key: (SessionId, StreamId)) {
        let Some(o) = self.out.get_mut(&key) else { return };
        while o.off < o.data.len() {
            let n = host.write(key.0, key.1, &o.data[o.off..]);
            if n == 0 {
                return;
            }
            o.off += n;
        }
        host.finish(key.0, key.1);
        // The sender keeps a final message until the session ends: if it ends first, the message is sent again.
        if !o.final_ {
            self.out.remove(&key);
        }
    }

    fn data(&mut self, now: u64, session: SessionId, stream: StreamId, bytes: &[u8], fin: bool, from_peer: Option<usize>) {
        let key = (session, stream);
        let e = self.inbox.entry(key).or_insert(In {
            got: Vec::new(),
            done: false,
            log: Vec::new(),
        });
        if e.log.len() < 32 {
            e.log.push((now, bytes.len(), fin));
        }
        let mut led = self.led.borrow_mut();
        if e.done && (!bytes.is_empty() || fin) {
            let own = self.out.contains_key(&key);
            led.bad(
                "bytes or an end after the end of a stream",
                format!("node {} {key:?} from {from_peer:?}, own stream {own}, header {:?}, events {:?}", self.idx, header(0xA5, &e.got), e.log),
            );
            return;
        }
        e.got.extend_from_slice(bytes);
        if e.got.len() >= HDR {
            let Some((from, seq, len)) = header(0xA5, &e.got) else {
                led.bad("a stream began with a wrong header", format!("node {} {:?}", self.idx, &e.got[..HDR]));
                e.done = true;
                return;
            };
            if from_peer.is_some_and(|p| p != from) {
                led.bad("a message came from another node than it says", format!("{from} via {from_peer:?}"));
            }
            if let Some(p) = first_wrong(&e.got, from, seq) {
                led.bad(
                    "a stream's bytes differ from the bytes written",
                    format!("node {} from {from} seq {seq}: byte {p} of {len}", self.idx),
                );
                e.done = true;
                return;
            }
            if e.got.len() > len as usize {
                led.bad("a stream carried more bytes than were written", format!("{} of {len}", e.got.len()));
            }
            if fin {
                e.done = true;
                if e.got.len() != len as usize {
                    led.bad(
                        "a stream ended with fewer bytes than were written",
                        format!("node {} from {from} seq {seq}: {} of {len}", self.idx, e.got.len()),
                    );
                    return;
                }
                let c = led.delivered.entry((from, seq)).or_insert(0);
                *c += 1;
                if *c > 1 {
                    led.bad("a message was delivered twice", format!("from {from} seq {seq} at {}", self.idx));
                }
                if let Some(&(to, _, true)) = led.sent.get(&(from, seq)) {
                    led.final_ok.insert((from, to));
                }
            }
        } else if fin {
            e.done = true;
            led.bad("a stream ended before its header", format!("node {} {} bytes", self.idx, e.got.len()));
        }
    }

    fn opened(&mut self, now: u64, host: &mut dyn Host, session: SessionId, peer: usize) {
        self.ours.insert(session);
        self.open.insert(peer, session);
        self.retry_at.remove(&peer);
        self.flush(now, host, peer, session);
    }

    fn closed(&mut self, now: u64, session: SessionId) {
        self.ours.remove(&session);
        let peers: Vec<usize> = self.open.iter().filter(|(_, s)| **s == session).map(|(p, _)| *p).collect();
        for p in &peers {
            self.open.remove(p);
        }
        // Final messages still held on the ended session are sent again on a new one.
        let keys: Vec<(SessionId, StreamId)> = self.out.keys().filter(|k| k.0 == session).copied().collect();
        for k in keys {
            if let Some(o) = self.out.remove(&k)
                && o.final_
                && !self.led.borrow().final_ok.contains(&(self.idx, o.to))
            {
                self.waiting.entry(o.to).or_default().push(Pending {
                    len: o.data.len() as u32,
                    final_: true,
                });
                self.retry_at.insert(o.to, now + RETRY);
            }
        }
        self.inbox.retain(|k, _| k.0 != session);
    }
}

impl Layers for App {
    fn alpns(&self) -> Vec<&'static [u8]> {
        vec![ALPN]
    }

    fn boot(&mut self, _now: u64, host: &mut dyn Host) {
        if self.idx < self.apps {
            let _ = host.subscribe(TOPIC);
        }
    }

    /// Every intent is a tick of the application (see `tick`): it runs what is due.
    fn intent(&mut self, now: u64, host: &mut dyn Host, _intent: &Intent) {
        self.timeout(now, host);
    }

    fn event(&mut self, now: u64, host: &mut dyn Host, ev: LayerEvent<'_>) {
        match ev {
            LayerEvent::Incoming { alpn, .. } | LayerEvent::Connected { alpn, .. } | LayerEvent::ConnectFailed { alpn, .. }
                if alpn != ALPN => {},
            LayerEvent::Incoming { session, peer, .. } | LayerEvent::Connected { session, peer, .. } => {
                self.opened(now, host, session, peer);
            },
            LayerEvent::ConnectFailed { peer, .. } => {
                if self.waiting.get(&peer).is_some_and(|w| !w.is_empty()) {
                    self.retry_at.insert(peer, now + RETRY);
                }
            },
            LayerEvent::Closed { session } => self.closed(now, session),
            LayerEvent::StreamData {
                session,
                stream,
                data,
                fin,
            } if self.ours.contains(&session) => {
                let p = host.peer_of(session);
                self.data(now, session, stream, data, fin, p);
            },
            LayerEvent::StreamWritable { session, stream } => self.push(host, (session, stream)),
            LayerEvent::Message { origin, body } => {
                let Some((from, seq, len)) = header(0xB5, body) else { return };
                let mut led = self.led.borrow_mut();
                if body.len() != len as usize || first_wrong(body, from, seq).is_some() {
                    led.bad("a broadcast message came changed", format!("from {from} seq {seq} at {}", self.idx));
                }
                if origin != Some(from) {
                    led.bad("a broadcast message names another publisher", format!("{origin:?} for {from}"));
                }
                let c = led.bcast.entry((from, seq, self.idx)).or_insert(0);
                *c += 1;
                if *c > 1 {
                    led.bad("a broadcast message was delivered twice", format!("from {from} seq {seq} at {}", self.idx));
                }
            },
            _ => {},
        }
    }

    fn timeout(&mut self, now: u64, host: &mut dyn Host) {
        while self.next < self.script.len() && self.script[self.next].0 <= now {
            let op = self.script[self.next].1;
            self.next += 1;
            match op {
                AppOp::Dial(x) => {
                    if let Some(p) = self.peer(x) {
                        self.dial(now, host, p);
                    }
                },
                AppOp::Send(x, len) => {
                    // Best effort: only the final round's messages are owed.
                    if let Some(p) = self.peer(x) {
                        self.queue(now, host, p, len, false);
                    }
                },
                AppOp::Close(x) => {
                    if let Some(s) = self.peer(x).and_then(|p| self.open.get(&p).copied()) {
                        host.close(s, 0);
                    }
                },
                AppOp::Publish(len) => {
                    self.seq += 1;
                    let m = message(0xB5, self.idx, self.seq, u32::from(len));
                    let _ = host.publish(TOPIC, &m);
                },
            }
        }
        if now >= FINAL && self.idx < self.apps && !self.final_sent {
            // The final round: one owed message to every other application node.
            self.final_sent = true;
            let me = self.idx;
            for p in (0..self.apps).filter(|&p| p != me) {
                self.queue(now, host, p, 3000 + me as u32, true);
            }
        }
        let due: Vec<usize> = self.retry_at.iter().filter(|(_, t)| **t <= now).map(|(p, _)| *p).collect();
        for p in due {
            self.retry_at.remove(&p);
            let r = self.retries.entry(p).or_insert(0);
            *r += 1;
            if *r <= MAX_RETRIES && self.waiting.get(&p).is_some_and(|w| !w.is_empty()) {
                // A session to the peer may have opened meanwhile (the peer dialed): send on it, else dial.
                match self.open.get(&p).copied() {
                    Some(s) => self.flush(now, host, p, s),
                    None => self.dial(now, host, p),
                }
            }
        }
    }

    /// None: the application is driven by intents (`tick`), never by its own timer, since a dial from a layer timer
    /// is counted as a late timer (`repro_world.rs`, `a_dial_from_an_application_timer_leaves_no_late_timer`).
    fn poll_timeout(&self) -> Option<u64> {
        None
    }

    fn has_open_intents(&self, _now: u64) -> bool {
        self.waiting.values().any(|w| !w.is_empty()) || !self.out.is_empty()
    }

    fn stop(&mut self) {
        self.open.clear();
        self.ours.clear();
        self.out.clear();
        self.inbox.clear();
        self.retry_at.clear();
    }
}

// ---------------------------------------------------------------- one run

/// A tick of node `node`'s application at `t`: an intent the application reads as "run what is due". Only its time
/// matters; the kind is one the application does not act on otherwise.
fn tick(t: u64, node: usize) -> Intent {
    Intent {
        t,
        node,
        kind: IntentKind::Echo,
        to: None,
        topic: None,
        size: None,
        req: None,
        resp: None,
        deadline_ns: 0,
        receivers: Vec::new(),
        must: Must::Flag(false),
        value: None,
        providers: Vec::new(),
        ranges: Vec::new(),
        stream_rate: None,
        probe: false,
        under_bulk: false,
        set_ref: None,
    }
}

type Node = SuiteNode<App>;

/// What a run ends with, for the oracles and the comparison of two runs.
#[derive(Debug, PartialEq, Eq)]
struct Outcome {
    final_ok: BTreeSet<(usize, usize)>,
    bad: Vec<(&'static str, String)>,
}

struct Ran {
    out: Outcome,
    apps: usize,
    timer_violations: Vec<u64>,
    failed: Vec<String>,
    stuck: Vec<String>,
}

fn run(s: &Spec, extra_dedicated: usize) -> Ran {
    let l = layout(s, extra_dedicated);
    let world = Rc::new(make_world(s, &l));
    let rec = Rc::new(RefCell::new(Rec::new(Rc::clone(&world))));
    let reg = Registry::leak(world.seed);
    reg.install();
    let shared = Shared::new(Rc::clone(&world), Rc::clone(&rec), reg).unwrap();
    let loss = if s.loss_pm == 0 {
        Loss::None
    } else {
        Loss::Bernoulli(f64::from(s.loss_pm) / 1000.0)
    };
    let cfg = SimConfig {
        default_link: Some(LinkConfig {
            delay: 10 * MS,
            jitter: if s.reorder { 4 * MS } else { 0 },
            reorder_prob: if s.reorder { 0.05 } else { 0.0 },
            reorder_depth: 2,
            reorder_slot: MS,
            loss,
            ..LinkConfig::default()
        }),
        ..SimConfig::default()
    };
    let led = Rc::new(RefCell::new(Ledger::default()));
    let mut sim: Sim<Node, pinc_sim::Rng, SuiteCost> = Sim::with_parts(s.seed, cfg, SuiteCost);
    let n = l.apps + l.dedicated;
    let mut ids: Vec<NodeId> = Vec::new();
    for i in 0..n {
        let script: Vec<(u64, AppOp)> = if i < l.apps {
            s.script
                .iter()
                .filter(|st| usize::from(st.node) % l.apps == i)
                .map(|st| (u64::from(st.t_ms) * MS, st.op))
                .collect()
        } else {
            Vec::new()
        };
        let app = App::new(i, if i < l.apps { l.apps } else { 0 }, script, Rc::clone(&led));
        let node = SuiteNode::new(Rc::clone(&shared), i, app).unwrap();
        let spec = &world.nodes[i];
        let ip = iface_ip(&spec.ifaces[0].addr).unwrap();
        let id = if l.public[i] {
            let id = sim.add_node_at(node, ip);
            sim.listen(id, SocketAddr::new(ip, 443), StreamKind::Tcp);
            sim.listen(id, SocketAddr::new(ip, 8443), StreamKind::Ws);
            id
        } else {
            let id = sim.add_node(node);
            let kind = NATS[usize::from(s.apps.get(i).map_or(0, |a| a.nat)) % NATS.len()];
            let nat = sim.add_nat(NatConfig {
                kind,
                ext_ip: iface_ip(&Addr {
                    kind: "udp4".to_owned(),
                    host: 2_000_000 + i as u64,
                    port: 0,
                })
                .unwrap(),
                mapping_timeout: 120 * NS,
                tcp_timeout: 7200 * NS,
                refresh_on_inbound: false,
                port_base: 20_000,
                ports: PortPolicy::Sequential,
                no_punch: false,
            });
            sim.add_iface_behind(id, ip, nat);
            id
        };
        sim.set_cpu(id, SuiteCost::cpu(1000));
        ids.push(id);
    }
    for (i, id) in ids.iter().enumerate() {
        sim.crash(0, *id);
        sim.restart(NS + i as u64 * MS, *id);
    }
    if let Some(p) = s.partition {
        let side: Vec<NodeId> = (0..n).filter(|i| p.mask >> (i % 8) & 1 == 1).map(|i| ids[i]).collect();
        let at = u64::from(p.at_s) * NS;
        sim.partition(at, &[&side]);
        sim.heal(at + u64::from(p.len_s) * NS);
    }
    // The application's clock: a tick at each of its script steps and every second (retries, the final round).
    for i in 0..l.apps {
        let steps = s.script.iter().filter(|st| usize::from(st.node) % l.apps == i).map(|st| u64::from(st.t_ms) * MS);
        let seconds = (2..=(FINAL + FINAL_BOUND) / NS).map(|k| k * NS);
        let times: BTreeSet<u64> = steps.chain(seconds).collect();
        for t in times {
            sim.command(t, ids[i], Cmd::Intent(Box::new(tick(t, i))));
        }
    }
    if let Some(r) = s.restart {
        let h = ids[l.hubs[usize::from(r.hub) % l.hubs.len()]];
        let at = u64::from(r.at_s) * NS;
        if r.persist {
            sim.command(at - MS, h, Cmd::Persist);
        }
        sim.crash(at, h);
        sim.restart(at + u64::from(r.down_s) * NS, h);
    }
    sim.run_until(FINAL + FINAL_BOUND);
    let failed: Vec<String> = (0..l.apps)
        .flat_map(|i| {
            sim.events(ids[i]).iter().filter_map(move |(t, e)| match e {
                NodeEvent::ConnectFailed { peer, reason } => Some(format!("{t}: {i} -> {peer}: {reason:?}")),
                _ => None,
            })
        })
        .take(12)
        .collect();
    let timer_violations = ids.iter().map(|id| sim.node(*id).timer_violations()).collect();
    let led = led.borrow();
    // For each pair that missed its final message: what the sender's application holds, and the sender's sessions.
    let stuck: Vec<String> = (0..l.apps)
        .flat_map(|i| (0..l.apps).filter(move |&j| j != i).map(move |j| (i, j)))
        .filter(|p| !led.final_ok.contains(p))
        .take(3)
        .map(|(i, j)| {
            let a = sim.node(ids[i]).layers();
            let out: Vec<(SessionId, usize, usize)> =
                a.out.iter().filter(|(_, o)| o.to == j).map(|(k, o)| (k.0, o.off, o.data.len())).collect();
            let d: Vec<String> = sim.node(ids[i]).describe().into_iter().filter(|s| s.starts_with("session")).collect();
            format!(
                "{i}->{j}: open {:?}, waiting {}, out {out:?}, retries {:?}, retry_at {:?}; sessions {d:?}",
                a.open.get(&j),
                a.waiting.get(&j).map_or(0, Vec::len),
                a.retries.get(&j),
                a.retry_at.get(&j),
            )
        })
        .collect();
    Ran {
        out: Outcome {
            final_ok: led.final_ok.clone(),
            bad: led.bad.clone(),
        },
        apps: l.apps,
        timer_violations,
        failed,
        stuck,
    }
}

/// The delivery oracles: every byte intact and once, every pair reached within the bound.
fn check_delivery(r: &Ran) {
    if let Some((sig, d)) = r.out.bad.first() {
        ephyra::signature(*sig);
        panic!("{sig}: {d}");
    }
    let missing: Vec<(usize, usize)> = (0..r.apps)
        .flat_map(|i| (0..r.apps).filter(move |&j| j != i).map(move |j| (i, j)))
        .filter(|p| !r.out.final_ok.contains(p))
        .collect();
    if !missing.is_empty() {
        ephyra::signature("a pair did not reach each other after the faults stopped");
    }
    assert!(
        missing.is_empty(),
        "pairs that did not reach each other within the bound after the faults stopped: {missing:?}; failed dials: {:?}; {:?}",
        r.failed,
        r.stuck
    );
}

/// The timer oracles, checked last so a late timer never hides a delivery failure.
fn check_timers(r: &Ran) {
    if r.timer_violations.iter().any(|v| *v != 0) {
        ephyra::signature("a node was woken late");
    }
    assert!(r.timer_violations.iter().all(|v| *v == 0), "a node was woken late: {:?}", r.timer_violations);
    // The simulator's own count (`Metrics::timer_violations`) is not an oracle here: it counts every timer call that
    // leaves the node due at its own time, which pinc-node allows once ("A layer may name the time of a timer call as
    // its next deadline ... the next call moves it", pinc-node timers.rs). The conflict is `repro_world.rs`
    // `a_dial_from_an_application_timer_leaves_no_late_timer`.
}

fn prop(s: &Spec) {
    let r = run(s, 0);
    check_delivery(&r);
    if s.shape == Shape::Ordinary {
        // The same world with a dedicated relay-role node added reaches the same end state.
        let with = run(s, 1);
        check_delivery(&with);
        if with.out != r.out {
            ephyra::signature("adding a dedicated relay-role node changed the end state");
        }
        assert!(with.out == r.out, "adding a dedicated relay-role node changed the end state");
        check_timers(&with);
    }
    check_timers(&r);
}

fn big_stack(f: impl FnOnce() + Send + 'static) {
    let r = std::thread::Builder::new().stack_size(256 << 20).spawn(f).unwrap().join();
    if let Err(e) = r {
        std::panic::resume_unwind(e);
    }
}

#[test]
fn every_shape_of_network_reaches_every_pair_and_keeps_every_byte() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(6)
            .name("every_shape_of_network_reaches_every_pair_and_keeps_every_byte");
        ephyra::check(&config, ephyra::any::<Spec>(), |s: Spec| prop(&s)).assert_passed();
    });
}

#[test]
fn the_world_spec_generator_stays_in_support() {
    let ok = |s: &Spec| (2..=6).contains(&s.apps.len()) && (1..=2).contains(&s.dedicated) && s.loss_pm <= 30;
    check_generator(&ephyra::Config::default().tests(300), ephyra::any::<Spec>(), move |s: &Spec| ok(s)).assert_passed();
}
