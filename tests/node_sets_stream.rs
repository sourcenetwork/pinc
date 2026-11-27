//! How the node reads a reconcile stream: a peer that never ends a message cannot grow the node's buffer, and a peer
//! that writes faster than the node reads (several messages before one read) is not a protocol failure. A real node over
//! a scripted endpoint whose streams hold exactly the bytes a test puts there; the node consumes only what it reads.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    missing_docs,
    unreachable_pub
)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::ops::Range;

use pinc_broadcast::Limits as BLimits;
use pinc_connect::client::{Config as ConnCfg, Port};
use pinc_core::{
    Command, CommandError, Event, Events, IfaceEvent, IfaceId, NodeStats, Reply, Role, SendState, SessionId,
    SessionStats, TraceRecord, Transmit, Value,
};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId};
use pinc_node::{Config as NodeConfig, Enabled, Ep, NodeEvent, ReconcileFailure, SETS_ALPN};
use pinc_reconcile::{Initiator, Limits, MemIndex, Responder, Step};
use pinc_security::{Alpn, Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftPrekeys};
use pinc_tests::{Caps, LayerApps, SplitMix64};
use pinc_transport::conn::Stats;
use pinc_transport::stream::{NoSource, RecvStatus, StreamError, StreamId};

const SET: &[u8] = b"s";
const DIALED: u64 = 1 << 40;
const INC: u64 = 1 << 41;
const NOW: u64 = 1_000_000_000;

#[derive(Default)]
struct StreamEp {
    events: VecDeque<Event>,
    live: Vec<(SessionId, NodeId)>,
    dials: usize,
    opened: BTreeMap<(SessionId, u64), Vec<u8>>,
    next_stream: u64,
    reset: Vec<(SessionId, u64, u64)>,
    finished: BTreeSet<(SessionId, u64)>,
    inbound: BTreeMap<(SessionId, u64), (Vec<u8>, RecvStatus)>,
    /// What the node consumed of each stream: the node's buffer never holds more than it took from here.
    consumed: BTreeMap<(SessionId, u64), usize>,
}

impl Port for StreamEp {
    type Src = NoSource;
    fn command(&mut self, _now: u64, cmd: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        let mut value = Value::None;
        match cmd {
            Command::Connect { node, .. } => {
                let s = SessionId(DIALED + self.dials as u64);
                self.dials += 1;
                self.live.push((s, node));
                value = Value::Session(s);
            }
            Command::OpenStream { session, .. } => {
                if !self.live.iter().any(|l| l.0 == session) {
                    return Err(CommandError::Stream(StreamError::UnknownStream));
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
                        let n = n.min(b.len());
                        b.drain(..n);
                        // what the node reads into its buffer: a stream it has refused is only discarded
                        if !self.reset.iter().any(|r| r.0 == session && r.1 == stream) {
                            *self.consumed.entry((session, stream)).or_default() += n;
                        }
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

impl Ep for StreamEp {
    fn handle_datagram(&mut self, _now: u64, _local: SocketAddr, _remote: SocketAddr, _data: &mut [u8]) {}
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
            dialer: session.0 < INC,
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

type SNode = pinc_node::Node<StreamEp, Caps, (), 4, 32, LayerApps>;

fn limits() -> Limits {
    Limits {
        max_item: 64,
        max_message: 8 << 10,
        ..Limits::default()
    }
}

/// The most the node's buffer of one stream may hold.
fn bound() -> usize {
    2 * (limits().max_body() + 3)
}

fn items(seed: u64, n: usize) -> Vec<Vec<u8>> {
    let mut rng = SplitMix64::new(seed);
    let mut v: Vec<Vec<u8>> = (0..n)
        .map(|_| {
            let mut it = vec![0; 16];
            rng.fill(&mut it);
            it
        })
        .collect();
    v.sort_unstable();
    v.dedup();
    v
}

fn apps(mine: &[Vec<u8>]) -> LayerApps {
    let mut a = LayerApps::new(
        0x11,
        Enabled {
            sets: true,
            ..Enabled::NONE
        },
    );
    a.sets.insert(SET, mine);
    a.sets.limits = Some(limits());
    a
}

fn peer() -> NodeId {
    Keypair::from_seed(IdentityAlg::Ed25519, &[0x42; 32]).unwrap().node_id()
}

fn build(mine: &[Vec<u8>]) -> Box<SNode> {
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
        trace: false,
    };
    Box::new(
        pinc_node::Node::with_apps(
            &cfg,
            StreamEp::default(),
            prekey,
            prov,
            Drbg::new(&[0x31; 32]),
            Box::new(Keypair::from_seed(IdentityAlg::Ed25519, &[0x11; 32]).unwrap()),
            (),
            7,
            apps(mine),
        )
        .unwrap(),
    )
}

fn deliver(node: &mut SNode, ev: Event) {
    node.endpoint_mut().events.push_back(ev);
    let remote = SocketAddr::from(([192, 0, 2, 1], 9));
    let local = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(203, 0, 113, 10)), 4433);
    node.handle_datagram(NOW, local, remote, &mut [0u8]);
}

fn run<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// A node that started a round to the peer, its session up and its request written: the session, the stream, the
/// request.
fn initiating(node: &mut SNode) -> (SessionId, u64, Vec<u8>) {
    node.handle_timeout(NOW);
    node.sets_start(NOW, &peer().bytes, SET).unwrap();
    let s = SessionId(DIALED);
    deliver(
        node,
        Event::Connected {
            session: s,
            node: peer(),
            alpn: Alpn::new(SETS_ALPN).unwrap(),
            resumed: false,
        },
    );
    let (&(_, x), req) = node
        .endpoint_mut()
        .opened
        .iter()
        .find(|((sess, _), _)| *sess == s)
        .expect("the node opened a stream and wrote its request");
    let req = req.clone();
    (s, x, req)
}

/// A node that took an incoming session of the peer and its stream.
fn answering(node: &mut SNode) -> (SessionId, u64) {
    node.handle_timeout(NOW);
    let s = SessionId(INC);
    node.endpoint_mut().live.push((s, peer()));
    deliver(
        node,
        Event::Incoming {
            session: s,
            node: peer(),
            alpn: Alpn::new(SETS_ALPN).unwrap(),
        },
    );
    deliver(node, Event::StreamOpened { session: s, stream: 1 });
    (s, 1)
}

fn feed(node: &mut SNode, s: SessionId, x: u64, bytes: Vec<u8>, st: RecvStatus) {
    node.endpoint_mut().inbound.insert((s, x), (bytes, st));
    deliver(node, Event::StreamReadable { session: s, stream: x });
}

fn failures(node: &mut SNode) -> Vec<ReconcileFailure> {
    let mut v = Vec::new();
    while let Some(e) = node.poll_event() {
        if let NodeEvent::ReconcileFailed { reason, .. } = e {
            v.push(reason);
        }
    }
    v
}

/// Every message the responder `idx` writes for `request`, in one piece (a cold stream is a run of messages).
fn reply_for(idx: &MemIndex, request: &[u8]) -> Vec<u8> {
    let (mut r, mut all, mut tx) = (Responder::new(limits()), Vec::new(), Vec::new());
    let mut step = r.handle(idx, request, &mut tx).unwrap();
    loop {
        all.extend_from_slice(&tx);
        tx.clear();
        match step {
            Step::Chunk => step = r.resume(idx, &mut tx).unwrap(),
            Step::Last => return all,
            other => panic!("the reply is not one stream of messages: {other:?}"),
        }
    }
}

/// A message that never ends: it announces more than any honest message holds, or a length within the limit with
/// bytes that are no message, and the peer has far more to write. The node takes at most its bound from the stream
/// and the round ends as a protocol failure.
#[test]
fn an_endless_message_on_a_round_is_refused_and_the_buffer_does_not_grow() {
    run(|| {
        for announced in [0xff_ffff, limits().max_body() + 1] {
            let mut node = build(&items(1, 5));
            let (s, x, _) = initiating(&mut node);
            let mut endless = vec![(announced >> 16) as u8, (announced >> 8) as u8, announced as u8];
            endless.resize(10 * bound(), 0xaa);
            let total = endless.len();
            feed(&mut node, s, x, endless, RecvStatus::Open);
            assert_eq!(
                failures(&mut node),
                [ReconcileFailure::Protocol],
                "announced {announced}"
            );
            let took = node.endpoint_mut().consumed.get(&(s, x)).copied().unwrap_or(0);
            assert!(took <= bound(), "the node took {took} bytes, its bound is {}", bound());
            assert!(took < total, "the node did not swallow the whole stream");
            assert_eq!(node.sets_running(), 0);
        }
    });
}

/// The same on the answering side: the stream is reset with the protocol code and the node took no more than its bound.
#[test]
fn an_endless_message_on_an_answered_stream_is_refused_and_the_buffer_does_not_grow() {
    run(|| {
        let mut node = build(&items(1, 5));
        let (s, x) = answering(&mut node);
        let mut endless = vec![0xff, 0xff, 0xff];
        endless.resize(10 * bound(), 0xaa);
        feed(&mut node, s, x, endless, RecvStatus::Open);
        assert!(
            node.endpoint_mut().reset.iter().any(|r| r.0 == s && r.1 == x),
            "the stream was not refused"
        );
        let took = node.endpoint_mut().consumed.get(&(s, x)).copied().unwrap_or(0);
        assert!(took <= bound(), "the node took {took} bytes, its bound is {}", bound());
    });
}

/// A reply of many messages written before the node reads once (more than its buffer holds): every message is
/// handled and the round ends with the exact difference.
#[test]
fn a_reply_in_one_large_chunk_completes_the_round_with_the_right_report() {
    run(|| {
        let (mine, theirs) = (items(1, 5), items(2, 3000));
        let mut node = build(&mine);
        let (s, x, req) = initiating(&mut node);
        let reply = reply_for(&MemIndex::from_sorted(theirs.iter().map(Vec::as_slice)).unwrap(), &req);
        assert!(
            reply.len() > bound(),
            "the reply ({} bytes) must not fit the buffer",
            reply.len()
        );
        feed(&mut node, s, x, reply, RecvStatus::Finished);
        let (mut here, mut there, mut failed) = (Vec::new(), Vec::new(), Vec::new());
        while let Some(e) = node.poll_event() {
            match e {
                NodeEvent::ReconcileDone {
                    missing_here,
                    missing_there,
                    ..
                } => (here, there) = (missing_here, missing_there),
                NodeEvent::ReconcileFailed { reason, .. } => failed.push(reason),
                _ => {}
            }
        }
        assert!(failed.is_empty(), "the round failed: {failed:?}");
        here.sort_unstable();
        there.sort_unstable();
        assert_eq!(here, theirs, "the items only the peer holds");
        assert_eq!(there, mine, "the items only this node holds");
    });
}

/// The answering side with a request as large as an honest peer writes it, in one chunk: the node answers it with the
/// messages the library's responder writes, and refuses nothing.
#[test]
fn a_full_size_request_in_one_chunk_is_answered() {
    run(|| {
        let (mine, theirs) = (items(1, 5), items(2, 3000));
        let mut node = build(&mine);
        let (s, x) = answering(&mut node);
        let mut init = Initiator::new(limits());
        let mut req = Vec::new();
        init.start(
            &MemIndex::from_sorted(theirs.iter().map(Vec::as_slice)).unwrap(),
            SET,
            &mut req,
        )
        .unwrap();
        feed(&mut node, s, x, req.clone(), RecvStatus::Open);
        assert!(
            node.endpoint_mut().reset.is_empty(),
            "the node refused an honest request"
        );
        let mine_idx = MemIndex::from_sorted(mine.iter().map(Vec::as_slice)).unwrap();
        let want = {
            let (mut r, mut tx) = (Responder::new(limits()), Vec::new());
            let step = r.handle(&mine_idx, &req, &mut tx).unwrap();
            let mut all = tx.clone();
            let mut step = step;
            while step == Step::Chunk {
                tx.clear();
                step = r.resume(&mine_idx, &mut tx).unwrap();
                all.extend_from_slice(&tx);
            }
            all
        };
        assert_eq!(node.endpoint_mut().opened.get(&(s, x)), Some(&want));
    });
}
