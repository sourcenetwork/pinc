//! How the node reads a reconcile or a transfer stream: a peer that never ends a message cannot grow the node's
//! buffer, and a peer that writes faster than the node reads (several messages before one read) is not a protocol
//! failure. A real node over a scripted endpoint whose streams hold exactly the bytes a test puts there; the node
//! consumes only what it reads.
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
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Secret, Software};
use pinc_dtn::bundle::{Outgoing, Plan, seal_bundle, serve, serve_len};
use pinc_dtn::head::Erasure;
use pinc_dtn::hlc::Hlc;
use pinc_dtn::layout::SliceLayout;
use pinc_dtn::seal::SealSeeds;
use pinc_node::{Config as NodeConfig, DTN_ALPN, Enabled, Ep, NodeEvent, ReconcileFailure, SETS_ALPN};
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

/// The smallest message limit every valid exchange fits in, with the longest items the limits allow: a long set
/// reference and a full part make the first message longer than `max_message`.
fn edge_limits() -> Limits {
    let base = Limits {
        max_item: 16,
        ..Limits::default()
    };
    Limits {
        max_message: base.min_message(),
        ..base
    }
}

/// A set reference as long as `edge_limits` allow.
const LONG_SET: &[u8] = &[0x5a; 16];

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

const SETS_ON: Enabled = Enabled {
    sets: true,
    ..Enabled::NONE
};
const DTN_ON: Enabled = Enabled {
    dtn: true,
    ..Enabled::NONE
};

fn apps(mine: &[Vec<u8>], set: &[u8], lim: Limits, on: Enabled) -> LayerApps {
    let mut a = LayerApps::new(0x11, on);
    a.sets.insert(set, mine);
    a.sets.limits = Some(lim);
    a
}

fn peer() -> NodeId {
    Keypair::from_seed(IdentityAlg::Ed25519, &[0x42; 32]).unwrap().node_id()
}

fn build(mine: &[Vec<u8>]) -> Box<SNode> {
    build_with(mine, SET, limits(), SETS_ON)
}

fn build_with(mine: &[Vec<u8>], set: &[u8], lim: Limits, on: Enabled) -> Box<SNode> {
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
            apps(mine, set, lim, on),
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
/// and the round ends as a protocol failure. It guards the bound of the buffer only (it also passes on a reader that
/// refuses at once); a message the node must read whole is the other tests.
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

/// The same on the answering side: the stream is reset with the protocol code and the node took no more than its
/// bound. It guards the bound of the buffer only.
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

/// The answering side with a request longer than the message limit and no longer than the body bound (a long set
/// reference and a full part, as an honest peer writes it), in one chunk: the node answers it with the messages the
/// library's responder writes, and refuses nothing.
#[test]
fn a_request_longer_than_the_message_limit_is_answered() {
    run(|| {
        let lim = edge_limits();
        let mine = items(1, 5);
        let theirs: Vec<Vec<u8>> = (0u8..17).map(|i| vec![i; 16]).collect();
        let mut node = build_with(&mine, LONG_SET, lim, SETS_ON);
        let (s, x) = answering(&mut node);
        let mut req = Vec::new();
        Initiator::new(lim)
            .start(
                &MemIndex::from_sorted(theirs.iter().map(Vec::as_slice)).unwrap(),
                LONG_SET,
                &mut req,
            )
            .unwrap();
        let body = req.len() - 3;
        assert!(
            body > lim.max_message && body <= lim.max_body(),
            "the request body ({body}) must pass the message limit ({}) and stay within the body bound ({})",
            lim.max_message,
            lim.max_body()
        );
        feed(&mut node, s, x, req.clone(), RecvStatus::Open);
        assert!(
            node.endpoint_mut().reset.is_empty(),
            "the node refused an honest request"
        );
        let mine_idx = MemIndex::from_sorted(mine.iter().map(Vec::as_slice)).unwrap();
        let mut r = Responder::new(lim);
        let mut tx = Vec::new();
        let mut step = r.handle(&mine_idx, &req, &mut tx).unwrap();
        let mut want = tx.clone();
        while step == Step::Chunk {
            tx.clear();
            step = r.resume(&mine_idx, &mut tx).unwrap();
            want.extend_from_slice(&tx);
        }
        assert_eq!(node.endpoint_mut().opened.get(&(s, x)), Some(&want));
    });
}

/// A peer that writes two whole requests before the node reads once: both are answered, in order, with what the
/// library's responder writes for them.
#[test]
fn two_requests_in_one_chunk_are_both_answered() {
    run(|| {
        let mine = items(1, 100);
        let mut theirs: Vec<Vec<u8>> = mine.iter().take(90).cloned().chain(items(7, 10)).collect();
        theirs.sort_unstable();
        theirs.dedup();
        let (mine_idx, theirs_idx) = (
            MemIndex::from_sorted(mine.iter().map(Vec::as_slice)).unwrap(),
            MemIndex::from_sorted(theirs.iter().map(Vec::as_slice)).unwrap(),
        );
        // the exchange the library runs between the two sets: the first request, the reply, the request that answers it
        let (mut init, mut resp) = (Initiator::new(limits()), Responder::new(limits()));
        let (mut first, mut r1, mut second, mut r2) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        init.start(&theirs_idx, SET, &mut first).unwrap();
        assert_eq!(resp.handle(&mine_idx, &first, &mut r1).unwrap(), Step::Send);
        assert_eq!(init.handle(&theirs_idx, &r1, &mut second).unwrap(), Step::Send);
        assert_eq!(resp.handle(&mine_idx, &second, &mut r2).unwrap(), Step::Send);
        let mut node = build(&mine);
        let (s, x) = answering(&mut node);
        feed(&mut node, s, x, [first, second].concat(), RecvStatus::Open);
        assert!(node.endpoint_mut().reset.is_empty(), "the node refused honest requests");
        assert_eq!(node.endpoint_mut().opened.get(&(s, x)), Some(&[r1, r2].concat()));
    });
}

/// A holder that writes its whole bundle before the node reads once (the offer and every run of symbols the node will
/// ask for, more than twice the longest frame): the node takes every frame, asks for each run, receives the bundle and
/// acknowledges it, and does not reset the stream.
#[test]
fn a_transfer_in_one_large_chunk_is_received_whole() {
    run(|| {
        const BODY_MAX: usize = 1 << 20;
        let mut node = build_with(&[], SET, limits(), DTN_ON);
        let keys = LayerApps::new(0x11, DTN_ON).dtn.keys();
        let holder = Keypair::from_seed(IdentityAlg::Ed25519, &[0x42; 32]).unwrap();
        let mut payload = vec![0u8; 2300 << 10];
        SplitMix64::new(9).fill(&mut payload);
        // one erasure block of every data symbol, so each ask is the next `CHUNK` bytes of them
        let plan = Plan {
            created: Hlc::new(1_700_000_000_000, 0),
            lifetime_ms: 600_000,
            copies: 1,
            erasure: Erasure { k: 255, m: 0 },
            slice_log: 4,
        };
        let seeds = SealSeeds {
            eph_x25519: Secret::new([3; 32]),
            kem_m: Secret::new([4; 32]),
        };
        let layout = SliceLayout::new(plan.erasure.k, plan.erasure.m, plan.slice_log, payload.len() as u64).unwrap();
        let mut sealed = vec![0; layout.total_len() as usize];
        let mut outboard = vec![0; layout.outboard_len().unwrap() as usize];
        let out = Outgoing {
            recipient: &keys,
            plan,
            seeds: &seeds,
        };
        let signed = seal_bundle(&Software, &holder, &out, &payload, &mut sealed, &mut outboard).unwrap();
        let frame = |ty: u8, body: &[u8]| {
            let mut f = vec![ty];
            f.extend_from_slice(&(body.len() as u32).to_be_bytes());
            f.extend_from_slice(body);
            f
        };
        let mut offer = 1u16.to_be_bytes().to_vec();
        offer.extend_from_slice(&0u64.to_be_bytes());
        let at = offer.len();
        offer.resize(at + signed.encoded_len(), 0);
        signed.encode(&mut offer[at..]).unwrap();
        let mut all = frame(1, &offer);
        // the node asks for at most 64 KiB of symbols at a time, from the first one on
        let run = (64u64 << 10) / layout.slice_len();
        let total = layout.total_symbols();
        let mut asks = 0;
        for first in (0..total).step_by(run as usize) {
            let end = (first + run).min(total);
            let mut body = first.to_be_bytes().to_vec();
            body.extend_from_slice(&end.to_be_bytes());
            let at = body.len();
            body.resize(at + serve_len(&layout, &(first..end)).unwrap(), 0);
            serve(&layout, &sealed, &outboard, &(first..end), &mut body[at..]).unwrap();
            all.extend_from_slice(&frame(3, &body));
            asks += 1;
        }
        assert!(
            all.len() > 2 * BODY_MAX,
            "the burst ({} bytes) must not fit the buffer ({})",
            all.len(),
            2 * BODY_MAX
        );
        let s = SessionId(INC);
        node.handle_timeout(NOW);
        node.endpoint_mut().live.push((s, peer()));
        deliver(
            &mut node,
            Event::Incoming {
                session: s,
                node: peer(),
                alpn: Alpn::new(DTN_ALPN).unwrap(),
            },
        );
        deliver(&mut node, Event::StreamOpened { session: s, stream: 1 });
        feed(&mut node, s, 1, all, RecvStatus::Open);
        assert!(
            node.endpoint_mut().reset.is_empty(),
            "the node reset the stream of an honest holder: {:?}",
            node.endpoint_mut().reset
        );
        let mut got = Vec::new();
        while let Some(e) = node.poll_event() {
            if let NodeEvent::DtnReceived { payload, .. } = e {
                got.push(payload);
            }
        }
        assert_eq!(got, [payload], "the bundle is received once and intact");
        // what the node wrote: one ask per run, then the acknowledgement
        let wrote = node.endpoint_mut().opened.get(&(s, 1)).cloned().unwrap_or_default();
        let (mut types, mut at) = (Vec::new(), 0);
        while at + 5 <= wrote.len() {
            types.push(wrote[at]);
            at += 5 + u32::from_be_bytes(wrote[at + 1..at + 5].try_into().unwrap()) as usize;
        }
        let mut want = vec![2u8; asks];
        want.push(4);
        assert_eq!(types, want, "one ask for each run, then the acknowledgement");
    });
}
