//! Model-based test of the reconcile layer over its sessions (`pinc-node` `reconcile.rs` and `layer.rs`): a real node
//! over a scripted endpoint, driven along every edge of the state graph of `proofs/tla/MbtNodeSets.tla`.
//!
//! `scripts/proofs.sh` writes the paths to `$PINC_MBT_DIR/node_sets.ndjson`; this test runs each on a fresh node. The
//! model's two peers are `P1` (the one that runs rounds) and `P2` (a filler); its two endpoint session ids are bound
//! to the sessions the endpoint gave (a dial's, or an incoming one's) as they appear. The layer table of 1 stands for
//! the code's 4096: the setup fills 4095 of it with incoming sessions of other peers; the 15 answered streams the
//! model leaves out are held open on filler sessions. Model time 0 is `u64::MAX - OPEN_RETRY` and 1 is `u64::MAX`.
//! After every call the node's rounds running, round events, dials, closed sessions, streams held and answered must
//! be the model's. Without `PINC_MBT_DIR` it checks nothing.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::many_single_char_names,
    missing_docs,
    unreachable_pub,
    clippy::manual_is_multiple_of,
    clippy::unused_self
)]

mod node_script;

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::ops::Range;

use node_script::{DIALED, id_of};
use pinc_broadcast::Limits as BLimits;
use pinc_connect::client::{Config as ConnCfg, Port};
use pinc_core::{
    Command, CommandError, Event, Events, IfaceEvent, IfaceId, NodeStats, Reply, Role, SendState, SessionId,
    SessionStats, TraceRecord, Transmit, Value,
};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId};
use pinc_node::{
    Apps, Body, Config as NodeConfig, Enabled, Ep, NodeEvent, NodeTrace, ReconcileFailure, SETS_ALPN, SetsApp,
    SetsError,
};
use pinc_reconcile::{Limits, Responder, Step};
use pinc_security::{Alpn, Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftPrekeys};
use pinc_tests::{Caps, Json, LayerApps, MbtCase, SplitMix64, mbt_cases};
use pinc_transport::conn::{CloseReason, Stats};
use pinc_transport::stream::{NoSource, RecvStatus, StreamError, StreamId};
use pinc_values::knobs::OPEN_RETRY;

const SET: &[u8] = b"s";
const FILL: u64 = 1 << 42;
const INC: u64 = 1 << 41;
const TABLE: u64 = 4096;

/// The endpoint the test scripts: a node's dials, streams, writes, resets and closes are recorded.
#[derive(Default)]
struct SetsEp {
    events: VecDeque<Event>,
    closed: Vec<SessionId>,
    shutdown: bool,
    dials: Vec<(SessionId, NodeId, Vec<u8>)>,
    refuse_dials: bool,
    credit: bool,
    next_stream: u64,
    opened: BTreeMap<(SessionId, u64), Vec<u8>>,
    peer_streams: BTreeSet<(SessionId, u64)>,
    reset: Vec<(SessionId, u64, u64)>,
    finished: BTreeSet<(SessionId, u64)>,
    inbound: BTreeMap<(SessionId, u64), (Vec<u8>, RecvStatus)>,
    live: Vec<(SessionId, NodeId)>,
}

impl Port for SetsEp {
    type Src = NoSource;
    fn command(&mut self, _now: u64, cmd: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        let mut value = Value::None;
        match cmd {
            Command::Connect { node, alpn, .. } => {
                if self.refuse_dials {
                    return Err(CommandError::Refused);
                }
                let s = SessionId(DIALED + self.dials.len() as u64);
                self.dials.push((s, node, alpn.to_vec()));
                value = Value::Session(s);
            }
            Command::OpenStream { session, .. } => {
                if !self.credit {
                    return Err(CommandError::Stream(StreamError::StreamLimit));
                }
                let x = 4 * self.next_stream;
                self.next_stream += 1;
                self.opened.insert((session, x), Vec::new());
                value = Value::Stream(x);
            }
            Command::Write { session, stream, data } => {
                self.opened
                    .entry((session, stream))
                    .or_default()
                    .extend_from_slice(data);
                value = Value::Written(data.len());
            }
            Command::Consume { session, stream, n } => {
                let st = match self.inbound.get_mut(&(session, stream)) {
                    Some((b, st)) => {
                        b.drain(..n.min(b.len()));
                        if b.is_empty() { *st } else { RecvStatus::Open }
                    }
                    None => RecvStatus::Open,
                };
                value = Value::Recv(st);
            }
            Command::Reset { session, stream, error } => self.reset.push((session, stream, error)),
            Command::Finish { session, stream } => {
                self.finished.insert((session, stream));
            }
            Command::Close { session, .. } => self.closed.push(session),
            Command::Shutdown => self.shutdown = true,
            _ => {}
        }
        Ok(Reply {
            value,
            events: Events::default(),
        })
    }
    fn stats(&self, _session: SessionId) -> Option<SessionStats> {
        None
    }
    fn node(&self) -> Option<NodeStats> {
        None
    }
    fn peer(&self, _node: &NodeId) -> Option<pinc_core::PeerInfo> {
        None
    }
    fn reach_body(&self, _session: SessionId, _out: &mut [u8; pinc_core::REACH_BODY_MAX]) -> usize {
        0
    }
    fn by_conn_id(&self, _cid: &pinc_security::ConnId) -> Option<SessionStats> {
        None
    }
}

impl Ep for SetsEp {
    fn handle_datagram(&mut self, _now: u64, _local: SocketAddr, _remote: SocketAddr, _buf: &mut [u8]) {}
    fn poll_transmit(&mut self, _now: u64, _out: &mut [u8]) -> Option<Transmit> {
        None
    }
    fn transmit_waiting(&self) -> bool {
        false
    }
    fn poll_event(&mut self) -> Option<Event> {
        self.events.pop_front()
    }
    fn events_waiting(&self) -> bool {
        !self.events.is_empty()
    }
    fn poll_timeout(&self) -> Option<u64> {
        None
    }
    fn handle_timeout(&mut self, _now: u64) {}
    fn register_alpn(&mut self, _alpn: &[u8]) -> bool {
        true
    }
    fn read_chunk(&self, session: SessionId, stream: StreamId) -> Option<&[u8]> {
        self.inbound.get(&(session, stream)).map(|(b, _)| b.as_slice())
    }
    fn read_at(&self, _session: SessionId, _stream: StreamId, _offset: u64) -> Option<&[u8]> {
        None
    }
    fn stored_after(&self, _session: SessionId, _stream: StreamId, _from: u64) -> Option<Range<u64>> {
        None
    }
    fn send_state(&self, _session: SessionId, _stream: StreamId) -> Option<SendState> {
        None
    }
    fn in_flight(&self, _session: SessionId) -> Option<u64> {
        None
    }
    fn read_extension(&mut self, _out: &mut [u8]) -> Result<Option<(SessionId, u64, usize)>, CommandError> {
        Ok(None)
    }
    fn session_at(&self, n: usize) -> Option<SessionStats> {
        let (session, node) = *self.live.get(n)?;
        Some(SessionStats {
            session,
            node: Some(node),
            alpn: Alpn::new(SETS_ALPN),
            role: Role::Other,
            gossip: false,
            dialer: false,
            established: true,
            allowed: true,
            path: None,
            route: None,
            thin: false,
            held: 0,
            held_dropped: 0,
            pto: 0,
            pto_count: 0,
            path_validated: true,
            heard: 0,
            heard_any: 0,
            pulse_due: false,
            last_app: 0,
            sub: false,
            answered: true,
            transport: Stats::default(),
        })
    }
    fn session_from(&self, _remote: &SocketAddr, _keep: &dyn Fn(SessionId) -> bool) -> Option<SessionId> {
        None
    }
    fn poll_trace(&mut self) -> Option<TraceRecord> {
        None
    }
    fn add_iface(&mut self, _local: SocketAddr) -> Option<IfaceId> {
        None
    }
    fn iface_event(&mut self, _now: u64, _id: IfaceId, _ev: IfaceEvent) {}
}

type SNode = pinc_node::Node<SetsEp, Caps, (), 4, 32, LayerApps>;

/// The five items both sides hold.
fn items() -> Vec<Vec<u8>> {
    let mut rng = SplitMix64::new(7);
    (0..5)
        .map(|_| (0..16).map(|_| rng.next_u64().to_le_bytes()[0]).collect())
        .collect()
}

fn limits() -> Limits {
    Limits {
        max_item: 64,
        max_message: 8 << 10,
        ..Limits::default()
    }
}

fn apps() -> LayerApps {
    let mut a = LayerApps::new(
        0x11,
        Enabled {
            sets: true,
            ..Enabled::NONE
        },
    );
    a.sets.insert(SET, &items());
    a.sets.limits = Some(limits());
    a
}

/// A node of seed byte `0x11` over a [`SetsEp`], with its trace on and the reconcile layer enabled.
fn build() -> Box<SNode> {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[0x11; 32]).unwrap();
    let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let prov = Caps(pinc_crypto::Software, true);
    let mut drbg = Drbg::new(&[0x21; 32]);
    let mut env = Env {
        provider: &prov,
        now: 0,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
    let local = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(203, 0, 113, 10)), 4433);
    let cfg = NodeConfig {
        connect: ConnCfg {
            me: kp.node_id(),
            identity,
            relays: [None; 4],
            phone: false,
            restarted: false,
            start: 0,
            v6: false,
            keep_learn: false,
        },
        is_hub: false,
        version: 1,
        alpn: b"t",
        limits: BLimits::default(),
        map_keys: pinc_tests::id_key(0x5eed),
        wall_ms: 1_700_000_000_000,
        local,
        trace: true,
    };
    let ep = SetsEp {
        credit: true,
        ..SetsEp::default()
    };
    Box::new(
        pinc_node::Node::with_apps(
            &cfg,
            ep,
            prekey,
            prov,
            Drbg::new(&[0x31; 32]),
            Box::new(Keypair::from_seed(IdentityAlg::Ed25519, &[0x11; 32]).unwrap()),
            (),
            7,
            apps(),
        )
        .unwrap(),
    )
}

/// What the node showed in one step.
#[derive(Default)]
struct Seen {
    ends: BTreeSet<(u64, String)>,
    starts: Vec<(u64, u64)>,
}

struct Run {
    node: Box<SNode>,
    now_local: SocketAddr,
    map: BTreeMap<u64, SessionId>,
    out_bound: u64,
    inc_bound: u64,
    seen: BTreeSet<(u64, String)>,
    prev: BTreeMap<u64, (u64, u64)>,
    p1: NodeId,
    p2: NodeId,
}

fn num(j: &Json) -> u64 {
    j.u64().unwrap()
}

fn at(t: u64) -> u64 {
    if t == 0 { u64::MAX - OPEN_RETRY } else { u64::MAX }
}

impl Run {
    fn ep(&mut self) -> &mut SetsEp {
        self.node.endpoint_mut()
    }

    fn deliver(&mut self, now: u64, ev: Event) {
        self.ep().events.push_back(ev);
        let remote = SocketAddr::from(([192, 0, 2, 1], 9));
        self.node.handle_datagram(now, self.now_local, remote, &mut [0u8]);
    }

    fn peer(&self, p: u64) -> NodeId {
        if p == 1 { self.p1 } else { self.p2 }
    }

    fn drain(&mut self) -> Seen {
        let mut s = Seen::default();
        while let Some(ev) = self.node.poll_event() {
            match ev {
                NodeEvent::ReconcileDone { round, .. } => {
                    s.ends.insert((u64::from(round), "done".to_owned()));
                }
                NodeEvent::ReconcileFailed { round, reason, .. } => {
                    let why = match reason {
                        ReconcileFailure::Protocol => "protocol",
                        ReconcileFailure::UnknownSet => "unknownset",
                        ReconcileFailure::Exhausted => "exhausted",
                        ReconcileFailure::Cancelled => "cancelled",
                        other => panic!("the node failed a round for a reason the model has no word for: {other:?}"),
                    };
                    s.ends.insert((u64::from(round), why.to_owned()));
                }
                _ => {}
            }
        }
        while let Some(t) = self.node.poll_trace() {
            if let Body::Node(NodeTrace::SetsStart { round, attempt, .. }) = t.body {
                s.starts.push((round, attempt));
            }
        }
        s
    }

    /// The one stream of round `act` that is neither reset nor finished.
    fn live_streams(&mut self, sess: SessionId) -> Vec<u64> {
        let ep = self.ep();
        ep.opened
            .keys()
            .filter(|(s, x)| {
                *s == sess && !ep.reset.iter().any(|r| r.0 == *s && r.1 == *x) && !ep.finished.contains(&(*s, *x))
            })
            .map(|k| k.1)
            .collect()
    }

    fn step(&mut self, i: usize, case: &MbtCase) {
        let st = &case.steps[i];
        let a = &st.args;
        let m = st.state.get("st").unwrap();
        let live = m.get("eps").and_then(Json::arr).unwrap().len();
        self.ep().refuse_dials = live == 2;
        let p1 = self.p1;
        match (st.call.as_str(), a.as_slice()) {
            ("CallStart", [_, res]) => {
                let now = at(0);
                let r = self.node.sets_start(now, &p1.bytes, SET);
                match (num(res), r) {
                    (0, Err(SetsError::Busy)) => {}
                    (n, Ok(id)) if n == u64::from(id) => {}
                    (n, r) => panic!("step {i}: sets_start gave {r:?}, the model {n}"),
                }
            }
            ("CallCancel", [id, res]) => {
                let got = self.node.sets_cancel(at(0), u32::try_from(num(id)).unwrap());
                assert_eq!(
                    got,
                    res.bool().unwrap_or_else(|| num(res) != 0),
                    "step {i}: sets_cancel answered otherwise"
                );
            }
            ("CallRevoke", _) => {
                self.node.revoke(at(0), &p1.bytes).unwrap();
            }
            ("CallLeave", _) => self.node.leave(at(0)),
            ("CallTick", [t]) => self.node.handle_timeout(at(num(t))),
            ("EnvCredit", _) => {
                let c = &mut self.ep().credit;
                *c = !*c;
            }
            ("EvConnected", [sid]) => {
                let s = self.map[&num(sid)];
                self.deliver(
                    at(0),
                    Event::Connected {
                        session: s,
                        node: p1,
                        alpn: Alpn::new(SETS_ALPN).unwrap(),
                        resumed: false,
                    },
                );
            }
            ("EvFailed", [sid]) => {
                let s = self.map[&num(sid)];
                self.deliver(
                    at(0),
                    Event::ConnectFailed {
                        session: Some(s),
                        node: p1,
                        alpn: Alpn::new(SETS_ALPN).unwrap(),
                        reason: pinc_core::ConnectFailure::Timeout,
                    },
                );
            }
            ("EvIncoming", [p]) => {
                let s = SessionId(INC + self.inc_bound);
                self.inc_bound += 1;
                let node = self.peer(num(p));
                self.ep().live.push((s, node));
                self.deliver(
                    at(0),
                    Event::Incoming {
                        session: s,
                        node,
                        alpn: Alpn::new(SETS_ALPN).unwrap(),
                    },
                );
                // the new entry of the model's table is this session
                let known: BTreeSet<u64> = self.map.keys().copied().collect();
                let fresh = m
                    .get("eps")
                    .and_then(Json::arr)
                    .unwrap()
                    .iter()
                    .map(|e| num(e.get("sid").unwrap()))
                    .find(|x| !known.contains(x))
                    .unwrap();
                self.map.insert(fresh, s);
            }
            ("EvClosed", [sid]) => {
                let s = self.map[&num(sid)];
                self.deliver(
                    at(0),
                    Event::Closed {
                        session: s,
                        reason: pinc_core::EndReason::Transport(CloseReason::Peer { error: 0 }),
                    },
                );
            }
            ("EvReply", [id, kind]) => {
                let round = m
                    .get("rounds")
                    .and_then(Json::arr)
                    .unwrap()
                    .iter()
                    .find(|r| num(r.get("id").unwrap()) == num(id))
                    .map(|r| num(r.get("act").unwrap()));
                // the model state is after the reply: the round's session is the one the reply came on
                let prev = self.prev.get(&num(id)).copied().map_or(0, |p| p.0);
                let sid = round.filter(|r| *r != 0).unwrap_or(prev);
                let s = self.map[&sid];
                let x = *self
                    .live_streams(s)
                    .first()
                    .expect("a reply for a round with no open stream");
                let kind = kind.str().unwrap().to_owned();
                match kind.as_str() {
                    "end" => {
                        let msg = self.ep().opened[&(s, x)].clone();
                        let idx = self.node_index();
                        let mut tx = Vec::new();
                        let step = Responder::new(limits())
                            .handle(&idx, &msg, &mut tx)
                            .unwrap_or_else(|_| panic!("step {i}: the responder refused the request"));
                        assert_eq!(step, Step::Last, "step {i}: the responder did not end in one message");
                        self.ep().inbound.insert((s, x), (tx, RecvStatus::Finished));
                    }
                    "bad" => {
                        self.ep()
                            .inbound
                            .insert((s, x), (vec![0x00, 0x20, 0x01], RecvStatus::Open));
                    }
                    "fin" => {
                        self.ep().inbound.insert((s, x), (Vec::new(), RecvStatus::Finished));
                    }
                    "unknown" | "reset" => {
                        let error = if kind == "unknown" { 2 } else { 1 };
                        self.deliver(
                            at(0),
                            Event::StreamReset {
                                session: s,
                                stream: x,
                                error,
                            },
                        );
                        return;
                    }
                    other => panic!("a reply kind the test does not know: {other}"),
                }
                self.deliver(at(0), Event::StreamReadable { session: s, stream: x });
            }
            ("EvPeerStream", [sid, ..]) => {
                let s = self.map[&num(sid)];
                let k = self.ep().peer_streams.iter().filter(|p| p.0 == s).count() as u64;
                self.ep().peer_streams.insert((s, 4 * k + 1));
                self.deliver(
                    at(0),
                    Event::StreamOpened {
                        session: s,
                        stream: 4 * k + 1,
                    },
                );
            }
            ("EvRespEnd", [sid, ..]) => {
                let s = self.map[&num(sid)];
                let x = self.ep().peer_streams.iter().find(|p| p.0 == s).map_or(1, |p| p.1);
                self.deliver(
                    at(0),
                    Event::StreamReset {
                        session: s,
                        stream: x,
                        error: 0,
                    },
                );
            }
            _ => panic!("a call the test does not know: {st}"),
        }
    }

    fn node_index(&self) -> impl pinc_reconcile::ItemIndex + use<> {
        apps().sets().index(SET).unwrap()
    }

    /// Binds the dial a step made to the model's new outgoing entry, then compares the node with the model.
    fn compare(&mut self, i: usize, case: &MbtCase) {
        let seen = self.drain();
        let m = case.steps[i].state.get("st").unwrap();
        // a dial the node made binds to the model's new outgoing entry
        let eps = m.get("eps").and_then(Json::arr).unwrap();
        for e in eps {
            let sid = num(e.get("sid").unwrap());
            if e.get("out").and_then(Json::bool) == Some(true) && !self.map.contains_key(&sid) {
                let s = SessionId(DIALED + self.out_bound);
                assert!(
                    (self.out_bound as usize) < self.ep().dials.len(),
                    "step {i}: the model dialed and the node did not"
                );
                self.out_bound += 1;
                self.map.insert(sid, s);
            }
        }
        let rounds = m.get("rounds").and_then(Json::arr).unwrap();
        assert_eq!(
            self.node.sets_running(),
            rounds.len(),
            "step {i}: rounds running differ from the model's"
        );
        self.seen.extend(seen.ends);
        let want: BTreeSet<(u64, String)> = m
            .get("ends")
            .and_then(Json::arr)
            .unwrap()
            .iter()
            .map(|e| {
                (
                    num(e.get("id").unwrap()),
                    e.get("why").unwrap().str().unwrap().to_owned(),
                )
            })
            .collect();
        assert_eq!(
            self.seen, want,
            "step {i}: the rounds that ended differ from the model's"
        );
        for r in rounds {
            let (id, act, att) = (
                num(r.get("id").unwrap()),
                num(r.get("act").unwrap()),
                num(r.get("att").unwrap()),
            );
            if act != 0 {
                let s = self.map[&act];
                assert_eq!(
                    self.live_streams(s).len(),
                    1,
                    "step {i}: round {id} does not hold exactly one open stream on its session"
                );
                if self.prev.get(&id) != Some(&(act, att)) {
                    assert!(
                        seen.starts.contains(&(id, att)),
                        "step {i}: round {id} attempt {att} was not traced"
                    );
                }
            }
            self.prev.insert(id, (act, att));
        }
        let closing: BTreeSet<SessionId> = eps
            .iter()
            .filter(|e| e.get("closing").and_then(Json::bool) == Some(true))
            .map(|e| self.map[&num(e.get("sid").unwrap())])
            .collect();
        let closed: BTreeSet<SessionId> = self.ep().closed.iter().copied().collect();
        assert_eq!(
            closed, closing,
            "step {i}: the sessions the node closed differ from the model's"
        );
        let leaving = m.get("leaving").and_then(Json::bool).unwrap_or(false);
        assert_eq!(
            self.ep().shutdown,
            leaving,
            "step {i}: the shutdown differs from the model's"
        );
        let resps = m.get("resps").and_then(Json::arr).unwrap().len();
        let busy = self.ep().reset.iter().filter(|r| r.2 == 6).count();
        let accepted = self.ep().peer_streams.len().saturating_sub(busy);
        assert_eq!(
            accepted, resps,
            "step {i}: the answered streams differ from the model's"
        );
    }
}

/// A node with its table full but one place, 15 answered streams held, and the setup's records cleared.
fn start(seed_peers: (NodeId, NodeId)) -> Run {
    let mut node = build();
    let local = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(203, 0, 113, 10)), 4433);
    node.handle_timeout(at(0));
    let mut run = Run {
        node,
        now_local: local,
        map: BTreeMap::new(),
        out_bound: 0,
        inc_bound: 0,
        seen: BTreeSet::new(),
        prev: BTreeMap::new(),
        p1: seed_peers.0,
        p2: seed_peers.1,
    };
    let mut j = 0u64;
    while j < TABLE - 1 {
        // distinct identities: a seed per filler
        let mut seed = [0x77u8; 32];
        seed[..8].copy_from_slice(&j.to_le_bytes());
        let id = Keypair::from_seed(IdentityAlg::Ed25519, &seed).unwrap().node_id();
        let s = SessionId(FILL + j);
        run.ep().events.push_back(Event::Incoming {
            session: s,
            node: id,
            alpn: Alpn::new(SETS_ALPN).unwrap(),
        });
        j += 1;
        if j % 256 == 0 || j == TABLE - 1 {
            run.deliver(at(0), Event::StreamReadable { session: s, stream: 0 });
        }
    }
    for k in 0..15u64 {
        let s = SessionId(FILL + k);
        run.ep().reset.clear();
        run.deliver(at(0), Event::StreamOpened { session: s, stream: 1 });
    }
    assert!(run.ep().reset.is_empty(), "the setup's answered streams were refused");
    let ep = run.ep();
    ep.closed.clear();
    ep.dials.clear();
    ep.opened.clear();
    ep.peer_streams.clear();
    ep.events.clear();
    ep.live.clear();
    while run.node.poll_event().is_some() {}
    while run.node.poll_trace().is_some() {}
    run
}

#[test]
fn the_reconcile_layer_matches_the_model() {
    let Some(cases) = mbt_cases("node_sets.ndjson") else {
        eprintln!("mbt_node_sets: PINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)");
        return;
    };
    let mut cases = cases.unwrap();
    let head = cases.head.clone();
    let list: Vec<MbtCase> = (&mut cases).map(Result::unwrap).collect();
    let (n, steps) = std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(move || {
            let mut steps = 0usize;
            for case in &list {
                let mut run = start((id_of(0x41), id_of(0x42)));
                for i in 0..case.steps.len() {
                    run.step(i, case);
                    run.compare(i, case);
                    steps += 1;
                }
            }
            (list.len() as u64, steps as u64)
        })
        .unwrap()
        .join()
        .unwrap();
    println!("node_sets: {n} cases, {steps} steps");
    let count = |f: &str| head.get(f).and_then(Json::u64).unwrap();
    assert_eq!(
        (n, steps),
        (count("cases"), count("steps")),
        "node_sets.ndjson ends early"
    );
}
