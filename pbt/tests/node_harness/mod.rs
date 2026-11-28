//! A real `pinc_node::Node` with its reconcile layer on, over an endpoint the test scripts (the node's `Ep` surface,
//! as `tests/mbt_node_sets.rs` of the project builds it): the node's dials, streams, writes, resets and closes are
//! recorded, and the test hands it events and stream bytes. The peer on the other end of the stream is the real
//! `pinc-reconcile` state machine, so the bytes the node reads are what an honest peer writes.
#![allow(dead_code, clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::ops::Range;

use pinc_connect::client::{Config as ConnCfg, Port};
use pinc_core::{
    Command, CommandError, Event, Events, IfaceEvent, IfaceId, NodeStats, Reply, Role, SendState, SessionId,
    SessionStats, TraceRecord, Transmit, Value,
};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use pinc_node::{Apps, Config as NodeConfig, Enabled, Ep, NoDtn, NoValues, SETS_ALPN, SetsApp};
use pinc_node::NodeEvent;
use pinc_reconcile::{Initiator, Limits, MemIndex, Responder, Step};
use pinc_security::{Alpn, Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftPrekeys};
use pinc_transport::conn::{CloseReason, Stats};
use pinc_transport::stream::{NoSource, RecvStatus, StreamError, StreamId};

pub const DIALED: u64 = 1 << 40;
pub const INC: u64 = 1 << 41;
/// The transport's receive chunk (pinc-transport stream/pool.rs `CHUNK_SIZE`).
const CHUNK_SIZE: usize = 16 * 1024;
pub const SEC: u64 = 1_000_000_000;
/// The most exchanges one round may take: far above what the largest generated difference needs.
pub const MAX_TURNS: usize = 20_000;

/// The endpoint the test scripts.
#[derive(Default)]
pub struct SetsEp {
    pub events: VecDeque<Event>,
    pub closed: Vec<SessionId>,
    pub dials: Vec<(SessionId, NodeId, Vec<u8>)>,
    next_stream: u64,
    /// What the node wrote on each stream.
    pub opened: BTreeMap<(SessionId, u64), Vec<u8>>,
    pub reset: Vec<(SessionId, u64, u64)>,
    pub finished: BTreeSet<(SessionId, u64)>,
    /// What the node may read on each stream, and the stream's state once that is read.
    pub inbound: BTreeMap<(SessionId, u64), (Vec<u8>, RecvStatus)>,
    /// The bytes the node consumed on each stream: a read returns at most up to the end of the transport's 16 KiB
    /// receive chunk (`RecvStream::read_chunk`, pinc-transport stream/recv.rs), as the real endpoint does.
    read_off: BTreeMap<(SessionId, u64), u64>,
    pub live: Vec<(SessionId, NodeId, bool)>,
}

impl Port for SetsEp {
    type Src = NoSource;
    fn command(&mut self, _now: u64, cmd: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        let mut value = Value::None;
        match cmd {
            Command::Connect { node, alpn, .. } => {
                let s = SessionId(DIALED + self.dials.len() as u64);
                self.dials.push((s, node, alpn.to_vec()));
                self.live.push((s, node, true));
                value = Value::Session(s);
            },
            Command::OpenStream { session, .. } => {
                if self.closed.contains(&session) {
                    return Err(CommandError::Stream(StreamError::UnknownStream));
                }
                let x = 4 * self.next_stream;
                self.next_stream += 1;
                self.opened.insert((session, x), Vec::new());
                value = Value::Stream(x);
            },
            Command::Write { session, stream, data } => {
                self.opened.entry((session, stream)).or_default().extend_from_slice(data);
                value = Value::Written(data.len());
            },
            Command::Consume { session, stream, n } => {
                let st = match self.inbound.get_mut(&(session, stream)) {
                    Some((b, st)) => {
                        let n = n.min(b.len());
                        b.drain(..n);
                        *self.read_off.entry((session, stream)).or_default() += n as u64;
                        if b.is_empty() { *st } else { RecvStatus::Open }
                    },
                    None => RecvStatus::Open,
                };
                value = Value::Recv(st);
            },
            Command::Reset { session, stream, error } => self.reset.push((session, stream, error)),
            Command::Finish { session, stream } => {
                self.finished.insert((session, stream));
            },
            Command::Close { session, .. } => self.closed.push(session),
            _ => {},
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
        let at = self.read_off.get(&(session, stream)).copied().unwrap_or(0) % CHUNK_SIZE as u64;
        self.inbound
            .get(&(session, stream))
            .map(|(b, _)| &b[..b.len().min(CHUNK_SIZE - at as usize)])
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
        let (session, node, dialer) = *self.live.get(n)?;
        Some(SessionStats {
            session,
            node: Some(node),
            alpn: Alpn::new(SETS_ALPN),
            role: Role::Other,
            gossip: false,
            dialer,
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

/// The host's sets: one set under one reference, and the session limits.
pub struct SetsHost {
    pub set_ref: Vec<u8>,
    pub index: MemIndex,
    pub limits: Limits,
    values: NoValues,
    dtn: NoDtn,
}

impl SetsApp for SetsHost {
    type Index<'a> = &'a MemIndex;
    fn limits(&self) -> Limits {
        self.limits
    }
    fn index(&self, set_ref: &[u8]) -> Option<&MemIndex> {
        (set_ref == self.set_ref.as_slice()).then_some(&self.index)
    }
}

impl<P: pinc_crypto::Provider> Apps<P> for SetsHost {
    type Values = NoValues;
    type Sets = Self;
    type Dtn = NoDtn;
    fn enabled(&self) -> Enabled {
        Enabled {
            sets: true,
            ..Enabled::NONE
        }
    }
    fn values(&mut self) -> &mut NoValues {
        &mut self.values
    }
    fn sets(&self) -> &Self {
        self
    }
    fn dtn(&mut self) -> &mut NoDtn {
        &mut self.dtn
    }
}

pub type SNode = pinc_node::Node<SetsEp, Software, (), 4, 32, SetsHost>;

static MAP_SECRETS: [u64; 7] = [
    0x9e37_79b9_7f4a_7c15,
    0xbf58_476d_1ce4_e5b9,
    0x94d0_49bb_1331_11eb,
    0x2545_f491_4f6c_dd1d,
    0xd6e8_feb8_6659_fd93,
    0xff51_afd7_ed55_8ccd,
    0xc4ce_b9fe_1a85_ec53,
];

pub fn node_id(tag: u8) -> NodeId {
    Keypair::from_seed(IdentityAlg::Ed25519, &[tag; 32]).unwrap().node_id()
}

pub const LOCAL: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(203, 0, 113, 10)), 4433);

/// A node (seed byte `0x11`) holding `items` under `set_ref`, with the reconcile layer on and `limits`.
pub fn build(set_ref: &[u8], items: &[Vec<u8>], limits: Limits) -> Box<SNode> {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[0x11; 32]).unwrap();
    let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let mut drbg = Drbg::new(&[0x21; 32]);
    let mut env = Env {
        provider: &Software,
        now: 0,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
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
        limits: pinc_broadcast::Limits::default(),
        map_keys: pinc_broadcast::IdKey::new(0x5eed, &MAP_SECRETS).unwrap(),
        wall_ms: 1_700_000_000_000,
        local: LOCAL,
        trace: false,
    };
    let apps = SetsHost {
        set_ref: set_ref.to_vec(),
        index: MemIndex::from_sorted(items.iter().map(Vec::as_slice)).unwrap(),
        limits,
        values: NoValues,
        dtn: NoDtn,
    };
    Box::new(
        pinc_node::Node::with_apps(
            &cfg,
            SetsEp::default(),
            prekey,
            Software,
            Drbg::new(&[0x31; 32]),
            Box::new(Keypair::from_seed(IdentityAlg::Ed25519, &[0x11; 32]).unwrap()),
            (),
            7,
            apps,
        )
        .unwrap(),
    )
}

/// Lets the node take the events queued on its endpoint.
pub fn deliver(node: &mut SNode, now: u64, ev: Event) {
    node.endpoint_mut().events.push_back(ev);
    let remote = SocketAddr::from(([192, 0, 2, 1], 9));
    node.handle_datagram(now, LOCAL, remote, &mut [0u8]);
}

/// The whole framed messages at the front of `buf` (3-byte header, then the body), removed from it.
pub fn take_messages(buf: &mut Vec<u8>) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    while let Some(head) = buf.first_chunk::<3>() {
        let n = pinc_reconcile::frame_len(*head) + 3;
        if buf.len() < n {
            break;
        }
        out.push(buf.drain(..n).collect());
    }
    out
}

pub fn closed_peer() -> pinc_core::EndReason {
    pinc_core::EndReason::Transport(CloseReason::Peer { error: 0 })
}

/// The node starts a round with `peer`: it dials, the session comes up, and the node opens the round's stream.
pub fn node_opens(node: &mut SNode, peer: NodeId, set_ref: &[u8]) -> Result<(SessionId, u64), String> {
    let now = SEC;
    node.handle_timeout(now);
    node.sets_start(now, &peer.bytes, set_ref).map_err(|e| format!("the node refused to start the round: {e:?}"))?;
    let s = node
        .endpoint_mut()
        .dials
        .iter()
        .find(|d| d.1 == peer)
        .map(|d| d.0)
        .ok_or("the node did not dial the peer")?;
    deliver(node, now, Event::Connected {
        session: s,
        node: peer,
        alpn: Alpn::new(SETS_ALPN).ok_or("no alpn")?,
        resumed: false,
    });
    node.handle_timeout(now);
    let x = node
        .endpoint_mut()
        .opened
        .keys()
        .find(|k| k.0 == s)
        .map(|k| k.1)
        .ok_or("the node opened no stream on the session to the peer")?;
    Ok((s, x))
}

/// The peer starts a round with the node: an incoming session, a stream, and the peer's first message on it.
pub fn peer_opens(
    node: &mut SNode,
    peer: NodeId,
    init: &mut Initiator,
    idx: &MemIndex,
    set_ref: &[u8],
    seen: &mut Seen,
) -> Result<(SessionId, u64), String> {
    let now = SEC;
    node.handle_timeout(now);
    let s = SessionId(INC);
    node.endpoint_mut().live.push((s, peer, false));
    deliver(node, now, Event::Incoming {
        session: s,
        node: peer,
        alpn: Alpn::new(SETS_ALPN).ok_or("no alpn")?,
    });
    deliver(node, now, Event::StreamOpened { session: s, stream: 1 });
    let mut first = Vec::new();
    init.start(idx, set_ref, &mut first).map_err(|e| format!("the honest peer could not start: {e:?}"))?;
    seen.peer_body = first.len() - 3;
    node.endpoint_mut().inbound.insert((s, 1), (first, RecvStatus::Open));
    deliver(node, now, Event::StreamReadable { session: s, stream: 1 });
    Ok((s, 1))
}

/// The items of the peer initiator's report, as (`missing_here`, `missing_there`).
pub fn peer_report(init: &Initiator) -> Option<(BTreeSet<Vec<u8>>, BTreeSet<Vec<u8>>)> {
    let r = init.report()?;
    Some((r.missing_here().map(<[u8]>::to_vec).collect(), r.missing_there().map(<[u8]>::to_vec).collect()))
}

/// The honest peer's side of the round.
pub enum Peer {
    Resp(Responder),
    Init(Initiator),
}

/// What one round showed.
#[derive(Default)]
pub struct Seen {
    /// The node's end of the round it started: `Ok((missing_here, missing_there))`, or the failure.
    pub outcome: Option<Result<(BTreeSet<Vec<u8>>, BTreeSet<Vec<u8>>), String>>,
    /// The peer machine refused a message of the node.
    pub peer_error: Option<String>,
    pub peer_done: bool,
    pub node_reset: Option<u64>,
    /// The longest message bodies each side wrote.
    pub node_body: usize,
    pub peer_body: usize,
    pub turns: usize,
}

pub fn drain(node: &mut SNode, seen: &mut Seen) {
    while let Some(ev) = node.poll_event() {
        match ev {
            NodeEvent::ReconcileDone {
                missing_here,
                missing_there,
                ..
            } => {
                seen.outcome = Some(Ok((missing_here.into_iter().collect(), missing_there.into_iter().collect())));
            },
            NodeEvent::ReconcileFailed { reason, .. } => seen.outcome = Some(Err(format!("{reason:?}"))),
            _ => {},
        }
    }
}

/// Runs the round on `(s, x)` between the node and `peer` until it ends or stalls.
pub fn exchange(node: &mut SNode, s: SessionId, x: u64, peer: &mut Peer, idx: &MemIndex, seen: &mut Seen) {
    let mut now = 2 * SEC;
    let (mut taken, mut pending) = (0usize, Vec::new());
    while seen.turns < MAX_TURNS {
        seen.turns += 1;
        now += 1_000_000;
        drain(node, seen);
        if let Some(r) = node.endpoint_mut().reset.iter().find(|r| r.0 == s && r.1 == x) {
            seen.node_reset = Some(r.2);
        }
        if seen.outcome.is_some() || seen.node_reset.is_some() || seen.peer_error.is_some() {
            return;
        }
        let written = node.endpoint_mut().opened.get(&(s, x)).cloned().unwrap_or_default();
        pending.extend_from_slice(&written[taken..]);
        taken = written.len();
        let msgs = take_messages(&mut pending);
        if msgs.is_empty() {
            // the peer started (its first message is in place) or the round is over: nothing more will come
            if seen.peer_done || seen.turns > 1 {
                return;
            }
        }
        let (mut out, mut fin) = (Vec::new(), false);
        for m in &msgs {
            seen.node_body = seen.node_body.max(m.len() - 3);
            let mut tx = Vec::new();
            let step = match peer {
                Peer::Resp(r) => r.handle(idx, m, &mut tx),
                Peer::Init(i) => i.handle(idx, m, &mut tx),
            };
            let mut step = match step {
                Ok(st) => st,
                Err(e) => {
                    seen.peer_error = Some(format!("{e:?}"));
                    return;
                },
            };
            out.extend_from_slice(&tx);
            let mut chunks = 0;
            while step == Step::Chunk && chunks < MAX_TURNS {
                chunks += 1;
                tx.clear();
                let Peer::Resp(r) = peer else { break };
                match r.resume(idx, &mut tx) {
                    Ok(st) => step = st,
                    Err(e) => {
                        seen.peer_error = Some(format!("{e:?}"));
                        return;
                    },
                }
                out.extend_from_slice(&tx);
            }
            if matches!(step, Step::Last | Step::Done) {
                fin = true;
                seen.peer_done = true;
            }
        }
        let mut frames = out.clone();
        for f in take_messages(&mut frames) {
            seen.peer_body = seen.peer_body.max(f.len() - 3);
        }
        if out.is_empty() && !fin {
            continue;
        }
        let entry = node.endpoint_mut().inbound.entry((s, x)).or_insert((Vec::new(), RecvStatus::Open));
        entry.0.extend_from_slice(&out);
        if fin {
            entry.1 = RecvStatus::Finished;
        }
        deliver(node, now, Event::StreamReadable { session: s, stream: x });
    }
}

