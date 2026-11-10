//! A simulated VINC node: the real `vinc_node::Node` (endpoint, connectivity client, membership, broadcast) with the
//! host duties around it: carriers over simulated TCP and WebSocket streams, key answers, access checks, and, for a hub,
//! the relay that accepts the carriers of its members.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::missing_panics_doc,
    clippy::missing_errors_doc,
    clippy::must_use_candidate,
    clippy::large_stack_arrays,
    clippy::too_many_lines
)]

use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::net::SocketAddr;
use std::rc::Rc;

use vinc_broadcast::Limits;
use vinc_connect::carrier::MAX_FRAME_LEN;
use vinc_connect::carrier::session::{self, Poll, ProtectedCarrier};
use vinc_connect::carrier::ws::{self, Decoder, Opcode, Role as WsRole, WsFrame};
use vinc_connect::client::{Config as ConnCfg, Io, Kind, RelayCfg};
use vinc_connect::relay::{Config as RelayConfig, Effect, Relay, SessionId as RSession, Sink, Trace, UdpTarget};
use vinc_core::{Command, Endpoint, EndpointConfig, Event, Query, Slot, relay_addr, relay_parts};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId};
use vinc_keystore::{KeyStore, SoftwareStore};
use vinc_membership::session::StoreError;
use vinc_node::{
    Apps, Config as NodeConfig, DtnRestored, HUB_ALPN, MemberNotice, NoApps, Node, NodeEvent, ServeSource, Store,
    TraceItem, is_relay_request,
};
use vinc_security::{ConnId, Env, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys, SoftPrekeys};
use vinc_sim::{Clock, IfaceEvent, StreamEvent, StreamId, StreamKind, StreamOp, Time, WALL_EPOCH};
use vinc_transport::conn::Resources;
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::BufferPool;
use vinc_transport::stream::{self, NoSource, StreamSource, Streams};

use crate::Caps;
use crate::connect_host::{Outbox, answer_parts};
use crate::core_net::{CC, CCT, CF, CN, CNP, CPK, CTK, metered};

/// The chunks of each session's buffer pool unless a test asks for fewer. A hub session carries a stream in each
/// direction (the hub opens its own as soon as it accepts, to send the replay floor), each with its receive window
/// charged to the pool, beside the send buffers.
const CHUNKS_PER_CONN: usize = 64;

thread_local! {
    static POOL_CHUNKS: std::cell::Cell<usize> = const { std::cell::Cell::new(CHUNKS_PER_CONN) };
}

/// Run `f`, which builds its nodes, with `chunks` chunks in every session's buffer pool.
pub fn with_pool_chunks<T>(chunks: usize, f: impl FnOnce() -> T) -> T {
    let before = POOL_CHUNKS.replace(chunks);
    let out = f();
    POOL_CHUNKS.set(before);
    out
}

pub const NK: usize = 24;
pub const ND: usize = 384;
pub const NRL: usize = 4;
pub const NPEERS: usize = 32;
pub type NEpS<S> = Endpoint<'static, 'static, Caps, S, CN, CC, CF, CNP, NK, ND, CPK, CTK, CCT>;
pub type NEp = NEpS<NoSource>;

/// What a simulated node needs of the host stores of the layers above broadcast: the node's `Apps` and the stream
/// source type its endpoint is built with.
pub trait SimApps: Apps<Caps> + Clone + 'static {
    type Src: StreamSource + ServeSource<<Self as Apps<Caps>>::Values> + 'static;
}

impl SimApps for NoApps {
    type Src = NoSource;
}

/// The relay-path address family and index the hub's own relay uses for its members: an index no client has.
const LOCAL_RELAY: u8 = 0xFE;

fn memory_of<S: StreamSource + 'static>() -> Resources<'static, S, CN, CC> {
    let pool = BufferPool::new_boxed(POOL_CHUNKS.get());
    let streams: &'static mut Streams<S, CN, CC> =
        Box::leak(Box::new(Streams::new(&stream::Config::new(false), &pool)));
    let loss: &'static LossEstimate = Box::leak(Box::new(LossEstimate::new()));
    Resources { pool, streams, loss }
}

fn node_slots<S: StreamSource + 'static>() -> &'static mut [Slot<'static, Caps, S, CN, CC, CF, CNP>; NK] {
    let v: Vec<Slot<'static, Caps, S, CN, CC, CF, CNP>> = (0..NK).map(|_| Slot::new(memory_of::<S>())).collect();
    let b: Box<[Slot<'static, Caps, S, CN, CC, CF, CNP>; NK]> = v.into_boxed_slice().try_into().ok().unwrap();
    Box::leak(b)
}

/// The incarnation epoch kept sealed by a software key store, as a host would keep it.
#[derive(Clone)]
pub struct SealStore {
    pub persist: bool,
    pub ks: Rc<RefCell<SoftwareStore>>,
    pub blob: Rc<RefCell<Vec<u8>>>,
}

impl Store for SealStore {
    fn persistent(&self) -> bool {
        self.persist
    }

    fn load(&mut self) -> Result<Option<u64>, StoreError> {
        let blob = self.blob.borrow().clone();
        if blob.is_empty() {
            return Ok(None);
        }
        let plain = self.ks.borrow_mut().unseal(&blob).map_err(|_| StoreError)?;
        let b: [u8; 8] = plain.as_slice().try_into().map_err(|_| StoreError)?;
        Ok(Some(u64::from_be_bytes(b)))
    }

    fn save(&mut self, epoch: u64) -> Result<(), StoreError> {
        let sealed = self
            .ks
            .borrow_mut()
            .seal(&epoch.to_be_bytes())
            .map_err(|_| StoreError)?;
        *self.blob.borrow_mut() = sealed;
        Ok(())
    }
}

pub type NodeT<A = NoApps> = Node<NEpS<<A as SimApps>::Src>, Caps, SealStore, NRL, NPEERS, A>;
pub type HubRelay = Relay<24, 16, 8, 4096>;

/// How to reach a hub.
#[derive(Debug, Clone, Copy)]
pub struct HubAddr {
    pub id: NodeId,
    pub udp: SocketAddr,
    pub tcp: SocketAddr,
    pub ws: SocketAddr,
}

/// How a simulated node is built.
#[derive(Clone)]
pub struct NodeSpec {
    pub tag: u8,
    pub addr: SocketAddr,
    pub hubs: Vec<HubAddr>,
    pub is_hub: bool,
    pub persist: bool,
    pub limits: Limits,
    pub trace: bool,
    pub start: u64,
}

pub fn id_of(tag: u8) -> NodeId {
    let alg = IdentityAlg::Ed25519;
    let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    kp.node_id()
}

/// The address of a hub as clients reach it.
pub fn hub_addr(tag: u8, ip: std::net::IpAddr) -> HubAddr {
    HubAddr {
        id: id_of(tag),
        udp: SocketAddr::new(ip, 4433),
        tcp: SocketAddr::new(ip, 443),
        ws: SocketAddr::new(ip, 8443),
    }
}

/// A command from the scenario.
#[derive(Debug, Clone)]
pub enum NCmd {
    Tick,
    Subscribe(Vec<u8>),
    Unsubscribe(Vec<u8>),
    Publish {
        topic: Vec<u8>,
        body: Vec<u8>,
    },
    Leave,
    Revoke([u8; 32]),
    AddressChanged,
    /// Close every carrier stream of the node (a middlebox reset), as the client sees it.
    DropCarriers,
    /// Answer the access checks of the endpoint with refusals from now on.
    Deny(bool),
    /// Answer the broadcast access checks with this verdict from now on.
    BroadcastAllow(bool),
    /// Fetch a value from providers (node ids).
    ValuesFetch {
        root: [u8; 32],
        length: u64,
        ranges: Vec<(u64, u64)>,
        providers: Vec<[u8; 32]>,
    },
    /// Cancel a fetch.
    ValuesCancel(u32),
    /// Start a reconcile round against a peer.
    SetsStart {
        peer: [u8; 32],
        set_ref: Vec<u8>,
    },
    /// Create a bundle for a recipient.
    DtnSend {
        to: Box<vinc_dtn::seal::RecipientKeys>,
        payload: Vec<u8>,
        plan: vinc_node::DtnPlan,
    },
}

/// What the scenario reads of a node.
#[derive(Debug, Clone)]
pub enum NEv {
    Node(NodeEvent),
    Stream(StreamEvent),
    Relay(Trace),
}

enum Eff {
    Carrier(NodeId, Vec<u8>),
    Udp(UdpTarget, Vec<u8>),
    Local(NodeId, Vec<u8>),
    Close(NodeId, RSession),
    Trace(Trace),
}

#[derive(Default)]
struct Collect(Vec<Eff>);

impl Sink for Collect {
    fn emit(&mut self, e: Effect<'_>) {
        self.0.push(match e {
            Effect::Carrier { to, frame } => {
                let mut b = vec![0u8; MAX_FRAME_LEN];
                let n = frame.encode(&mut b).unwrap();
                b.truncate(n);
                Eff::Carrier(to, b)
            }
            Effect::Udp { to, datagram } => {
                let mut b = vec![0u8; 2048];
                let n = datagram.encode(&mut b).unwrap();
                b.truncate(n);
                Eff::Udp(to, b)
            }
            Effect::Local { from, packet } => Eff::Local(from, packet.to_vec()),
            Effect::Close { node, session, .. } => Eff::Close(node, session),
            Effect::PeerRelay { .. } | Effect::Wake { .. } => return,
            Effect::Trace(t) => Eff::Trace(t),
        });
    }
}

struct RStream {
    carrier: Box<ProtectedCarrier<Caps>>,
    node: Option<NodeId>,
    session: Option<RSession>,
    ws: Option<Decoder>,
    sniffed: bool,
}

/// The relay a hub runs for its members.
struct HubSide {
    relay: Box<HubRelay>,
    streams: HashMap<StreamId, RStream>,
    by_node: HashMap<NodeId, StreamId>,
    stores: ResponderStores<4, 4>,
    slots: Vec<NodeId>,
    scid: u64,
}

enum Step {
    Idle,
    Flush,
    Frame,
    Open(NodeId),
    Dead,
}

fn wrap(rs: &RStream, bytes: &[u8]) -> Vec<u8> {
    if rs.ws.is_some() {
        let mut f = vec![0u8; bytes.len() + 16];
        let n = ws::encode(Opcode::Binary, bytes, None, &mut f).unwrap();
        f.truncate(n);
        f
    } else {
        bytes.to_vec()
    }
}

pub struct SimNode<A: SimApps = NoApps> {
    pub node: Box<NodeT<A>>,
    apps: A,
    pub spec: NodeSpec,
    pub me: NodeId,
    prov: Caps,
    kp: Keypair,
    prekeys: SoftPrekeys<Caps>,
    hdrbg: Drbg,
    deny: bool,
    bc_allow: bool,
    seal: SealStore,
    clock: Clock,
    // the node as a client of the relays
    streams: [Option<StreamId>; NRL],
    opening: [Option<SocketAddr>; NRL],
    kinds: [Kind; NRL],
    cws: [Option<Decoder>; NRL],
    // the node as a hub
    hub: Option<HubSide>,
    pub out: Outbox,
    pub events: VecDeque<NEv>,
    pub traces: Vec<(Time, TraceItem)>,
    /// What the last restart found in the delay-tolerant records.
    pub restored: DtnRestored,
    now: Time,
    down: bool,
    pub addr: SocketAddr,
    /// Incarnations the node announced over its lives, for the monotonicity checks.
    pub incarnations: Vec<u64>,
}

fn build<A: SimApps>(
    apps: A,
    spec: &NodeSpec,
    now: u64,
    seal: &SealStore,
    restarted: bool,
) -> (Box<NodeT<A>>, Caps, Keypair, SoftPrekeys<Caps>, Drbg) {
    let alg = IdentityAlg::Ed25519;
    let tag = spec.tag;
    let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let prov = Caps(vinc_crypto::Software, true);
    let mut drbg = Drbg::new(&[tag ^ 0x5a; 32]);
    let mut cfg = EndpointConfig::new(u64::from(tag) * 0x9E37_79B9);
    cfg.conn.max_gso = 1;
    let ep_drbg = Drbg::new(&[tag ^ 0xa5; 32]);
    let mut ep: Box<NEpS<<A as SimApps>::Src>> = Box::new(Endpoint::new(
        now,
        prov,
        ep_drbg,
        identity,
        cfg,
        node_slots::<<A as SimApps>::Src>(),
    ));
    let mut env = Env {
        provider: &prov,
        now,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey_info = prekeys.acquire(&mut env).unwrap();
    ep.set_prekey(prekey_info.clone());
    ep.add_iface(spec.addr).unwrap();
    let mut relays: [Option<RelayCfg>; NRL] = [None; NRL];
    for (d, h) in relays.iter_mut().zip(spec.hubs.iter().filter(|h| h.id != kp.node_id())) {
        *d = Some(RelayCfg {
            id: h.id,
            udp: Some(h.udp),
            tcp: Some(h.tcp),
            ws: Some(h.ws),
        });
    }
    let cfg = NodeConfig {
        connect: ConnCfg {
            me: kp.node_id(),
            identity,
            relays,
            phone: false,
            restarted,
            start: now,
            v6: false,
            keep_learn: false,
        },
        is_hub: spec.is_hub,
        version: 1,
        alpn: HUB_ALPN,
        limits: spec.limits,
        wall_ms: (WALL_EPOCH + now) / 1_000_000,
        local: spec.addr,
        trace: spec.trace,
    };
    let drbg2 = Drbg::new(&[tag ^ 0x33; 32]);
    let kp2 = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    let node = Node::with_apps(
        &cfg,
        *ep,
        prekey_info,
        prov,
        drbg2,
        kp2,
        seal.clone(),
        u64::from(tag) << 32,
        apps,
    )
    .expect("the node starts");
    (Box::new(node), prov, kp, prekeys, drbg)
}

impl SimNode<NoApps> {
    pub fn new(spec: &NodeSpec) -> Self {
        Self::with_apps(spec, NoApps::default())
    }
}

impl<A: SimApps> SimNode<A> {
    pub fn with_apps(spec: &NodeSpec, apps: A) -> Self {
        let seal = SealStore {
            persist: spec.persist,
            ks: Rc::new(RefCell::new(SoftwareStore::new().unwrap())),
            blob: Rc::new(RefCell::new(Vec::new())),
        };
        Self::with_seal(apps, spec, seal, false)
    }

    fn with_seal(apps: A, spec: &NodeSpec, seal: SealStore, restarted: bool) -> Self {
        let (node, prov, kp, prekeys, hdrbg) = build(apps.clone(), spec, spec.start, &seal, restarted);
        let me = kp.node_id();
        let hub = spec.is_hub.then(|| HubSide {
            relay: Box::new(HubRelay::new(RelayConfig::new(me, 0x5eed ^ u64::from(spec.tag)))),
            streams: HashMap::new(),
            by_node: HashMap::new(),
            stores: ResponderStores::default(),
            slots: Vec::new(),
            scid: 0,
        });
        let mut n = Self {
            incarnations: vec![node.membership().incarnation()],
            node,
            apps,
            spec: spec.clone(),
            me,
            prov,
            kp,
            prekeys,
            hdrbg,
            deny: false,
            bc_allow: true,
            seal,
            clock: Clock::default(),
            streams: [None; NRL],
            opening: [None; NRL],
            kinds: [Kind::Tcp; NRL],
            cws: [None, None, None, None],
            hub,
            out: Outbox::default(),
            events: VecDeque::new(),
            traces: Vec::new(),
            restored: DtnRestored::default(),
            now: spec.start,
            down: false,
            addr: spec.addr,
        };
        n.node.set_local(&[spec.addr]);
        n
    }

    fn wall_ms(&self, now: Time) -> u64 {
        u64::try_from((WALL_EPOCH.cast_signed() + self.clock.local(now)).max(0)).unwrap() / 1_000_000
    }

    fn slot(&mut self, n: &NodeId) -> u16 {
        let hub = self.hub.as_mut().unwrap();
        let i = hub.slots.iter().position(|x| x == n).unwrap_or_else(|| {
            hub.slots.push(*n);
            hub.slots.len() - 1
        });
        u16::try_from(i).unwrap()
    }

    fn member_addr(&self, node: &NodeId) -> Option<SocketAddr> {
        self.node.member_addr(node)
    }

    fn member_at(&self, src: &SocketAddr) -> Option<NodeId> {
        self.node.member_at(src)
    }

    /// One turn of the host loop, repeated until nothing moves.
    pub fn pump(&mut self, now: Time) {
        if self.down {
            return;
        }
        self.now = now;
        self.node.set_wall_ms(now, self.wall_ms(now));
        for _ in 0..128 {
            metered(|| self.node.poll(now));
            let mut busy = self.events_step(now);
            busy |= self.members_step(now);
            busy |= self.keys_step(now);
            busy |= self.io_step(now);
            busy |= self.tx_step(now);
            busy |= self.udp_step();
            busy |= self.streams_out_step();
            busy |= self.trace_step(now);
            if !busy {
                return;
            }
        }
        panic!("the host loop of a node does not settle at {now}");
    }

    fn trace_step(&mut self, now: Time) -> bool {
        let mut did = false;
        while let Some(t) = self.node.poll_trace() {
            did = true;
            if !matches!(t.body, vinc_node::Body::Core(_)) {
                self.traces.push((now, t));
            }
        }
        let inc = self.node.membership().incarnation();
        if self.incarnations.last() != Some(&inc) {
            self.incarnations.push(inc);
        }
        did
    }

    fn events_step(&mut self, now: u64) -> bool {
        let mut did = false;
        while let Some(ev) = self.node.poll_event() {
            did = true;
            match &ev {
                NodeEvent::Endpoint(e) => self.duty(now, *e),
                NodeEvent::BroadcastAcpCheck { id, .. } => {
                    let allow = self.bc_allow;
                    self.node.broadcast_acp_answer(now, *id, allow);
                }
                _ => {}
            }
            self.events.push_back(NEv::Node(ev));
        }
        did
    }

    /// The host duties of one endpoint event: key requests, access checks, and the relay's view of its members.
    fn duty(&mut self, now: u64, ev: Event) {
        match ev {
            Event::KeyRequest { session } => {
                let owned = match self.node.endpoint().query(Query::KeyRequest(session)) {
                    vinc_core::Answer::KeyRequest(req) => Some(answer_parts(
                        &self.prov,
                        &self.kp,
                        &self.prekeys,
                        &mut self.hdrbg,
                        now,
                        &req,
                    )),
                    _ => None,
                };
                if let Some(owned) = owned {
                    let _ = self.node.command(
                        now,
                        Command::KeyResponse {
                            session,
                            response: owned.response(),
                        },
                    );
                }
            }
            Event::AcpCheck { check, .. } => {
                let allow = !self.deny;
                let _ = self.node.command(now, Command::AcpAnswer { check, allow });
            }
            _ => {}
        }
    }

    /// What the node tells the hub's relay about its members: a session ended, a member woke.
    fn members_step(&mut self, now: u64) -> bool {
        let mut did = false;
        while let Some(n) = self.node.poll_member() {
            did = true;
            let Some(h) = self.hub.as_mut() else { continue };
            match n {
                MemberNotice::Gone(m) => h.relay.udp_gone(&m),
                MemberNotice::Awake(m) => {
                    let mut s = Collect::default();
                    h.relay.member_returned(now, &m, &mut s);
                    self.apply(now, s);
                }
            }
        }
        did
    }

    fn keys_step(&mut self, now: u64) -> bool {
        let mut did = false;
        for i in 0..NRL {
            for _ in 0..8 {
                let owned = self
                    .node
                    .key_request(i)
                    .map(|r| answer_parts(&self.prov, &self.kp, &self.prekeys, &mut self.hdrbg, now, &r));
                let Some(owned) = owned else { break };
                did = true;
                self.node.key_response(now, i, owned.response());
            }
        }
        for _ in 0..8 {
            let owned = self
                .node
                .sign_request()
                .map(|r| answer_parts(&self.prov, &self.kp, &self.prekeys, &mut self.hdrbg, now, &r));
            let Some(owned) = owned else { break };
            did = true;
            self.node.sign_response(now, owned.response());
        }
        did
    }

    fn io_step(&mut self, now: u64) -> bool {
        let mut did = false;
        while let Some(io) = self.node.poll_io() {
            did = true;
            match io {
                Io::Open { relay, kind, to } => {
                    self.kinds[relay] = kind;
                    self.opening[relay] = Some(to);
                    self.out.ops.push_back((
                        StreamOp::Connect {
                            local: self.addr,
                            remote: to,
                            kind: match kind {
                                Kind::Tcp => StreamKind::Tcp,
                                Kind::Ws => StreamKind::Ws,
                            },
                            simultaneous: false,
                        },
                        Vec::new(),
                    ));
                }
                Io::Close { relay } => {
                    if let Some(s) = self.streams[relay].take() {
                        self.out.ops.push_back((StreamOp::Close { stream: s }, Vec::new()));
                    }
                    self.opening[relay] = None;
                    self.cws[relay] = None;
                }
            }
        }
        let _ = now;
        did
    }

    fn tx_step(&mut self, now: u64) -> bool {
        let mut did = false;
        let mut buf = vec![0u8; 2048];
        while let Some(t) = metered(|| self.node.poll_transmit(now, &mut buf)) {
            did = true;
            if let Some((relay, slot)) = relay_parts(&t.remote)
                && relay == LOCAL_RELAY
            {
                let Some(node) = self.hub.as_ref().and_then(|h| h.slots.get(usize::from(slot)).copied()) else {
                    continue;
                };
                let mut s = Collect::default();
                let _ = self
                    .hub
                    .as_mut()
                    .unwrap()
                    .relay
                    .send_local(now, &node, 0, &buf[..t.len], &mut s);
                self.apply(now, s);
            } else {
                self.out.datagrams.push_back((t.local, t.remote, buf[..t.len].to_vec()));
            }
        }
        did
    }

    fn udp_step(&mut self) -> bool {
        let mut did = false;
        let mut buf = vec![0u8; 2048];
        while let Some((to, n)) = self.node.poll_udp(&mut buf) {
            did = true;
            if to.port() == vinc_connect::local::PORT {
                continue;
            }
            self.out.datagrams.push_back((self.addr, to, buf[..n].to_vec()));
        }
        did
    }

    fn streams_out_step(&mut self) -> bool {
        let mut did = false;
        let mut buf = vec![0u8; 20_000];
        for i in 0..NRL {
            let Some(stream) = self.streams[i] else { continue };
            loop {
                let n = self.node.poll_stream(i, &mut buf);
                if n == 0 {
                    break;
                }
                did = true;
                let data = if self.kinds[i] == Kind::Ws {
                    let mut f = vec![0u8; n + 16];
                    let mask = [0x11, 0x22, 0x33, 0x44];
                    let m = ws::encode(Opcode::Binary, &buf[..n], Some(mask), &mut f).unwrap();
                    f.truncate(m);
                    f
                } else {
                    buf[..n].to_vec()
                };
                self.out.ops.push_back((
                    StreamOp::Write {
                        stream,
                        len: data.len(),
                        send_at: None,
                    },
                    data,
                ));
            }
        }
        did
    }

    fn feed(&mut self, now: u64, relay: usize, mut bytes: &[u8]) {
        for _ in 0..64 {
            let n = self.node.stream_data(now, relay, bytes);
            bytes = &bytes[n..];
            self.keys_step(now);
            if bytes.is_empty() || (n == 0 && self.node.key_request(relay).is_none()) {
                return;
            }
        }
    }

    // ---------------------------------------------------------------- the relay of a hub

    fn apply(&mut self, now: Time, s: Collect) {
        for e in s.0 {
            match e {
                Eff::Carrier(to, plain) => self.write_frame(to, &plain),
                Eff::Udp(UdpTarget::Reply(a), d) => self.out.datagrams.push_back((self.addr, a, d)),
                Eff::Udp(UdpTarget::Member(n), d) => {
                    if let Some(a) = self.member_addr(&n) {
                        self.out.datagrams.push_back((self.addr, a, d));
                    }
                }
                Eff::Local(from, packet) => {
                    let slot = self.slot(&from);
                    let mut p = packet;
                    self.node
                        .handle_datagram(now, self.addr, relay_addr(false, LOCAL_RELAY, slot), &mut p);
                }
                Eff::Close(node, session) => {
                    let hub = self.hub.as_mut().unwrap();
                    if let Some(sid) = hub.by_node.get(&node).copied()
                        && hub.streams.get(&sid).and_then(|r| r.session) == Some(session)
                    {
                        self.out.ops.push_back((StreamOp::Close { stream: sid }, Vec::new()));
                        hub.streams.remove(&sid);
                        hub.by_node.remove(&node);
                    }
                }
                Eff::Trace(t) => {
                    self.node.relay_trace(now, &t);
                    self.events.push_back(NEv::Relay(t));
                }
            }
        }
    }

    fn write_frame(&mut self, to: NodeId, plain: &[u8]) {
        let hub = self.hub.as_mut().unwrap();
        let Some(sid) = hub.by_node.get(&to).copied() else {
            return;
        };
        let Some(rs) = hub.streams.get_mut(&sid) else { return };
        let mut out = vec![0u8; MAX_FRAME_LEN + 64];
        let Ok(n) = rs.carrier.seal_bytes(&self.prov, plain, &mut out) else {
            return;
        };
        out.truncate(n);
        let data = wrap(rs, &out);
        self.out.ops.push_back((
            StreamOp::Write {
                stream: sid,
                len: data.len(),
                send_at: None,
            },
            data,
        ));
    }

    fn flush_handshake(&mut self, sid: StreamId) {
        let hub = self.hub.as_mut().unwrap();
        let Some(rs) = hub.streams.get_mut(&sid) else { return };
        let mut buf = vec![0u8; 32 * 1024];
        loop {
            let n = rs.carrier.transmit(&mut buf);
            if n == 0 {
                break;
            }
            let data = wrap(rs, &buf[..n]);
            self.out.ops.push_back((
                StreamOp::Write {
                    stream: sid,
                    len: data.len(),
                    send_at: None,
                },
                data,
            ));
        }
    }

    fn drain(&mut self, now: Time, sid: StreamId) {
        for _ in 0..1024 {
            let mut sink = Collect::default();
            let step = {
                let hub = self.hub.as_mut().unwrap();
                let Some(rs) = hub.streams.get_mut(&sid) else { return };
                let mut env = Env {
                    provider: &self.prov,
                    now,
                    drbg: &mut self.hdrbg,
                };
                match rs.carrier.poll(&mut env, &mut hub.stores) {
                    Ok(Poll::Idle) => Step::Idle,
                    Ok(Poll::Handshake) => Step::Flush,
                    Ok(Poll::KeyRequest) => {
                        let soft = SoftKeys {
                            signer: Some((KeyHandle(1), &self.kp)),
                            prekeys: None,
                        };
                        if rs.carrier.answer_soft(&mut env, &soft).is_ok() {
                            Step::Flush
                        } else {
                            Step::Dead
                        }
                    }
                    Ok(Poll::Open(peer)) => Step::Open(peer),
                    Ok(Poll::Frame(f)) => {
                        if let (Some(node), Some(sess)) = (rs.node, rs.session) {
                            let _ = hub.relay.carrier_frame(now, &node, sess, &f, &mut sink);
                        }
                        Step::Frame
                    }
                    Err(e) => {
                        if e.is_fatal() {
                            Step::Dead
                        } else {
                            Step::Flush
                        }
                    }
                }
            };
            match step {
                Step::Idle => {
                    self.flush_handshake(sid);
                    return;
                }
                Step::Flush => self.flush_handshake(sid),
                Step::Frame => self.apply(now, sink),
                Step::Open(peer) => {
                    self.flush_handshake(sid);
                    let mut s = Collect::default();
                    let hub = self.hub.as_mut().unwrap();
                    if let Ok(sess) = hub.relay.carrier_opened(now, peer, &mut s) {
                        if let Some(rs) = hub.streams.get_mut(&sid) {
                            rs.node = Some(peer);
                            rs.session = Some(sess);
                        }
                        if let Some(old) = hub.by_node.insert(peer, sid)
                            && old != sid
                        {
                            hub.streams.remove(&old);
                            self.out.ops.push_back((StreamOp::Close { stream: old }, Vec::new()));
                        }
                    }
                    self.apply(now, s);
                }
                Step::Dead => {
                    self.out.ops.push_back((StreamOp::Close { stream: sid }, Vec::new()));
                    self.drop_stream(now, sid);
                    return;
                }
            }
        }
    }

    fn drop_stream(&mut self, now: Time, sid: StreamId) {
        let Some(hub) = self.hub.as_mut() else { return };
        if let Some(rs) = hub.streams.remove(&sid)
            && let (Some(node), Some(sess)) = (rs.node, rs.session)
        {
            if hub.by_node.get(&node) == Some(&sid) {
                hub.by_node.remove(&node);
            }
            let mut s = Collect::default();
            hub.relay.carrier_closed(now, &node, sess, &mut s);
            self.apply(now, s);
        }
    }

    // ---------------------------------------------------------------- the simulator's node contract

    fn relay_of_stream(&self, s: StreamId) -> Option<usize> {
        self.streams.iter().position(|x| *x == Some(s))
    }

    pub fn handle_datagram(&mut self, now: Time, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        if self.down {
            return;
        }
        self.node.set_wall_ms(now, self.wall_ms(now));
        let request = self.hub.is_some() && is_relay_request(data);
        if request {
            let member = self.member_at(&remote);
            let mut s = Collect::default();
            let _ = self
                .hub
                .as_mut()
                .unwrap()
                .relay
                .datagram(now, remote, member.as_ref(), data, &mut s);
            self.apply(now, s);
        } else {
            if self.hub.is_some()
                && data.first().is_some_and(|b| *b >= 0x40)
                && let Some(n) = self.member_at(&remote)
            {
                let _ = self.hub.as_mut().unwrap().relay.udp_heard(&n, now);
            }
            metered(|| self.node.handle_datagram(now, local, remote, data));
        }
        self.pump(now);
    }

    pub fn poll_transmit(&mut self, buf: &mut [u8]) -> Option<vinc_sim::Transmit> {
        let (local, remote, d) = self.out.datagrams.pop_front()?;
        buf[..d.len()].copy_from_slice(&d);
        Some(vinc_sim::Transmit {
            local,
            remote,
            len: d.len(),
            send_at: None,
        })
    }

    pub fn poll_timeout(&self) -> Option<Time> {
        if self.down {
            return None;
        }
        [
            self.node.poll_timeout(),
            self.hub.as_ref().and_then(|h| h.relay.next_deadline()),
        ]
        .into_iter()
        .flatten()
        .min()
    }

    pub fn handle_timeout(&mut self, now: Time) {
        if self.down {
            return;
        }
        self.node.set_wall_ms(now, self.wall_ms(now));
        if let Some(h) = self.hub.as_mut()
            && h.relay.next_deadline().is_some_and(|d| d <= now)
        {
            let mut s = Collect::default();
            h.relay.handle_timeout(now, &mut s);
            self.apply(now, s);
        }
        metered(|| self.node.handle_timeout(now));
        self.pump(now);
    }

    pub fn command(&mut self, now: Time, cmd: NCmd) {
        if self.down {
            return;
        }
        self.now = now;
        self.node.set_wall_ms(now, self.wall_ms(now));
        match cmd {
            NCmd::Tick => {}
            NCmd::Subscribe(t) => {
                let _ = self.node.subscribe(now, &t);
            }
            NCmd::Unsubscribe(t) => self.node.unsubscribe(now, &t),
            NCmd::Publish { topic, body } => {
                let _ = self.node.publish(now, &topic, &body);
            }
            NCmd::Leave => self.node.leave(now),
            NCmd::Revoke(p) => {
                let _ = self.node.revoke(now, &p);
            }
            NCmd::AddressChanged => self.node.address_changed(now),
            NCmd::DropCarriers => {
                for i in 0..NRL {
                    if let Some(st) = self.streams[i].take() {
                        self.out.ops.push_back((StreamOp::Close { stream: st }, Vec::new()));
                        self.cws[i] = None;
                        self.node.stream_closed(now, i);
                    }
                }
            }
            NCmd::Deny(d) => self.deny = d,
            NCmd::BroadcastAllow(a) => self.bc_allow = a,
            NCmd::ValuesFetch {
                root,
                length,
                ranges,
                providers,
            } => {
                let spans: Vec<vinc_values::span::Span> = ranges
                    .iter()
                    .map(|(off, len)| vinc_values::span::Span { off: *off, len: *len })
                    .collect();
                let req = vinc_node::ValuesRequest {
                    root,
                    length,
                    ranges: &spans,
                    providers: &providers,
                    deadline: None,
                };
                let _ = self.node.values_fetch(now, &req);
            }
            NCmd::ValuesCancel(f) => {
                let _ = self.node.values_cancel(now, f);
            }
            NCmd::SetsStart { peer, set_ref } => {
                let _ = self.node.sets_start(now, &peer, &set_ref);
            }
            NCmd::DtnSend { to, payload, plan } => {
                let _ = self.node.dtn_send(now, &to, &payload, &plan);
            }
        }
        self.pump(now);
    }

    pub fn poll_stream(&mut self, buf: &mut [u8]) -> Option<StreamOp> {
        let (op, data) = self.out.ops.pop_front()?;
        buf[..data.len()].copy_from_slice(&data);
        Some(op)
    }

    pub fn handle_stream_event(&mut self, now: Time, event: StreamEvent) {
        if self.down {
            return;
        }
        self.events.push_back(NEv::Stream(event));
        match event {
            StreamEvent::Pending { stream, remote } => {
                if let Some(i) = self.opening.iter().position(|o| *o == Some(remote)) {
                    self.streams[i] = Some(stream);
                    self.opening[i] = None;
                }
            }
            StreamEvent::Opened { stream, .. } => {
                if let Some(i) = self.relay_of_stream(stream) {
                    self.cws[i] = (self.kinds[i] == Kind::Ws).then(|| Decoder::new(WsRole::Server));
                    self.node.stream_opened(now, i);
                } else if let Some(h) = self.hub.as_mut() {
                    h.scid += 1;
                    let scid = ConnId::new(&h.scid.to_be_bytes()).unwrap();
                    let identity = LocalIdentity::from_keypair(&self.kp, KeyHandle(1)).unwrap();
                    let cfg = session::responder_config(identity, scid).unwrap();
                    h.streams.insert(
                        stream,
                        RStream {
                            carrier: Box::new(ProtectedCarrier::accept(cfg)),
                            node: None,
                            session: None,
                            ws: None,
                            sniffed: false,
                        },
                    );
                }
            }
            StreamEvent::Failed { stream } | StreamEvent::Closed { stream } => {
                if let Some(i) = self.relay_of_stream(stream) {
                    self.streams[i] = None;
                    self.cws[i] = None;
                    self.node.stream_closed(now, i);
                } else {
                    self.drop_stream(now, stream);
                }
            }
        }
        self.pump(now);
    }

    pub fn handle_stream_record(&mut self, now: Time, stream: StreamId, data: &mut [u8]) {
        if self.down {
            return;
        }
        if let Some(i) = self.relay_of_stream(stream) {
            if let Some(dec) = self.cws[i].as_mut() {
                let mut rest: &mut [u8] = data;
                let mut payloads: Vec<Vec<u8>> = Vec::new();
                while let Ok(Some((frame, used))) = dec.decode(rest) {
                    if let WsFrame::Data(p) = frame {
                        payloads.push(p.to_vec());
                    }
                    let (_, tail) = std::mem::take(&mut rest).split_at_mut(used);
                    rest = tail;
                }
                for p in payloads {
                    self.feed(now, i, &p);
                }
            } else {
                let d = data.to_vec();
                self.feed(now, i, &d);
            }
            self.pump(now);
            return;
        }
        let Some(hub) = self.hub.as_mut() else { return };
        let Some(rs) = hub.streams.get_mut(&stream) else {
            return;
        };
        if !rs.sniffed {
            rs.sniffed = true;
            // A WebSocket frame starts 0x82 (final binary); a handshake unit starts with a length below 0x8000.
            if data.first() == Some(&0x82) {
                rs.ws = Some(Decoder::new(WsRole::Client));
            }
        }
        let mut payloads: Vec<Vec<u8>> = Vec::new();
        if let Some(dec) = rs.ws.as_mut() {
            let mut rest: &mut [u8] = data;
            while let Ok(Some((frame, used))) = dec.decode(rest) {
                if let WsFrame::Data(p) = frame {
                    payloads.push(p.to_vec());
                }
                let (_, tail) = std::mem::take(&mut rest).split_at_mut(used);
                rest = tail;
            }
        } else {
            payloads.push(data.to_vec());
        }
        for p in payloads {
            let mut rest: &[u8] = &p;
            for _ in 0..64 {
                let Some(rs) = self.hub.as_mut().unwrap().streams.get_mut(&stream) else {
                    return;
                };
                let n = rs.carrier.receive(rest);
                rest = &rest[n..];
                self.drain(now, stream);
                if rest.is_empty() || n == 0 {
                    break;
                }
            }
        }
        self.pump(now);
    }

    pub fn crash(&mut self, _now: Time) -> Vec<u8> {
        self.down = true;
        self.out = Outbox::default();
        // What the host keeps (its stores and records) survives the crash; the node's memory does not.
        self.apps = self.node.apps_mut().clone();
        self.seal.blob.borrow().clone()
    }

    pub fn restart(&mut self, now: Time, persisted: &[u8]) {
        let seal = self.seal.clone();
        *seal.blob.borrow_mut() = persisted.to_vec();
        let mut spec = self.spec.clone();
        spec.start = now;
        let incs = std::mem::take(&mut self.incarnations);
        let mut fresh = Self::with_seal(self.apps.clone(), &spec, seal, true);
        fresh.clock = self.clock.clone();
        fresh.node.set_wall_ms(now, fresh.wall_ms(now));
        fresh.restored = fresh.node.dtn_restore(now);
        fresh.incarnations = incs;
        let last = fresh.node.membership().incarnation();
        fresh.incarnations.push(last);
        *self = fresh;
        self.pump(now);
    }

    pub fn suspend(&mut self, now: Time) {
        self.node.suspend(now, self.wall_ms(now));
    }

    pub fn resume(&mut self, now: Time) {
        if self.down {
            return;
        }
        self.node.resume(now, false);
        self.pump(now);
    }

    pub fn iface_event(&mut self, now: Time, event: IfaceEvent) {
        if self.down {
            return;
        }
        if let IfaceEvent::Changed { new, .. } = event {
            self.addr = SocketAddr::new(new, self.addr.port());
        }
        self.node.address_changed(now);
        self.pump(now);
    }

    pub fn clock_changed(&mut self, now: Time, clock: &Clock) {
        self.clock = clock.clone();
        if !self.down {
            self.node.set_wall_ms(now, self.wall_ms(now));
        }
    }
}

impl<A: SimApps> vinc_sim::Node for SimNode<A> {
    type Cmd = NCmd;
    type Event = NEv;

    fn handle_datagram(&mut self, now: Time, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        SimNode::handle_datagram(self, now, local, remote, data);
    }

    fn poll_transmit(&mut self, _now: Time, buf: &mut [u8]) -> Option<vinc_sim::Transmit> {
        SimNode::poll_transmit(self, buf)
    }

    fn poll_timeout(&mut self) -> Option<Time> {
        SimNode::poll_timeout(self)
    }

    fn handle_timeout(&mut self, now: Time) {
        SimNode::handle_timeout(self, now);
    }

    fn command(&mut self, now: Time, cmd: NCmd) {
        SimNode::command(self, now, cmd);
    }

    fn poll_event(&mut self) -> Option<NEv> {
        self.events.pop_front()
    }

    fn crash(&mut self, now: Time) -> Vec<u8> {
        SimNode::crash(self, now)
    }

    fn restart(&mut self, now: Time, persisted: &[u8]) {
        SimNode::restart(self, now, persisted);
    }

    fn suspend(&mut self, now: Time) {
        SimNode::suspend(self, now);
    }

    fn resume(&mut self, now: Time) {
        SimNode::resume(self, now);
    }

    fn iface_event(&mut self, now: Time, event: IfaceEvent) {
        SimNode::iface_event(self, now, event);
    }

    fn poll_stream(&mut self, _now: Time, buf: &mut [u8]) -> Option<StreamOp> {
        SimNode::poll_stream(self, buf)
    }

    fn handle_stream_event(&mut self, now: Time, event: StreamEvent) {
        SimNode::handle_stream_event(self, now, event);
    }

    fn handle_stream_record(&mut self, now: Time, stream: StreamId, data: &mut [u8]) {
        SimNode::handle_stream_record(self, now, stream, data);
    }

    fn clock_changed(&mut self, now: Time, clock: &Clock) {
        SimNode::clock_changed(self, now, clock);
    }
}
