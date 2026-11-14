//! The VINC host without a runtime: one `vinc_node::Node` over real addresses, with every duty the node leaves to its
//! host. It answers the endpoint's key requests and access checks, serves the connectivity client's relay carriers
//! (TCP streams the runtime layer moves bytes of), and, on a hub, runs the relay that accepts the carriers of its
//! members.
//!
//! The runtime layer calls `handle_datagram`, `handle_timeout`, `command` and `stream_event`, then drains
//! `poll_transmit`, the stream operations in [`Core::ops`] and the application events in [`Core::events`]. Time is
//! the node's own clock in nanoseconds; the wall clock is read from the system when the node asks for it.
//!
//! Invariants: nothing here blocks, spawns or locks; every queue is drained by the layer that owns the runtime and is
//! bounded by the node's own limits; a failure of a carrier stream is reported to the node as a close, which it repairs
//! by its own rules.

use std::collections::{BTreeMap, HashMap, VecDeque};
use std::net::SocketAddr;

use vinc_connect::carrier::session::{self, ProtectedCarrier};
use vinc_connect::client::{Config as ConnCfg, Io, Kind, RelayCfg};
use vinc_connect::relay::Config as RelayConfig;
use vinc_core::{Command, Endpoint, EndpointConfig, Event, Query, relay_parts};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use vinc_dtn::seal::RecipientKeys;
use vinc_node::{
    Body, Config as NodeConfig, DtnPlan, DtnRestored, HUB_ALPN, MemberNotice, Node, NodeEvent, NodeTrace,
    ValuesRequest, is_relay_request,
};
use vinc_security::{ConnId, Env, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftPrekeys};
use vinc_values::source::ValueSource;

use super::apps::{VApps, VStore};
use super::hub::{Collect, HubRelay, HubSide, RStream};
use super::keys::answer;
use super::tracelog::TraceLog;
use crate::node::data::{seed_bytes, seed32};

/// The bytes of messages a hub keeps for each topic in the harness.
pub const TOPIC_LOG_BYTES: usize = 16 << 20;
/// Relays (hubs) a node knows.
pub const NRL: usize = 4;

/// The most streams a peer has open at once on a session: the facade's default.
pub fn stream_limit() -> u16 {
    vinc::Limits::default().streams
}
/// Peers the connectivity client keeps records of.
pub const NPEERS: usize = 128;
/// The endpoint's shape: the facade's stream slots and tables, with the stream source of the values layer and
/// stream rings of 65 chunks (windows of at most 1 MiB).
pub type Ep<const K: usize, const D: usize> =
    Endpoint<'static, 'static, Software, ValueSource<VStore>, { vinc::STREAMS }, 65, FLIGHT, 4, K, D, 8, 64, 32>;

/// The packets in flight one session can track: the facade's ceiling. The ring bounds the bytes in flight at this many
/// packets, so a smaller one caps a transfer at that many packets per round trip whatever the window allows (128
/// packets held a 50 ms path to 3.5 MiB/s).
pub const FLIGHT: usize = vinc_transport::recovery::SENT_PACKETS;
// A 1 Gbit/s path of 50 ms holds about 4,300 packets of 1,452 bytes.
const _: () = assert!(FLIGHT >= 4_300);
/// The node over that endpoint.
pub type VNode<const K: usize, const D: usize> = Node<Ep<K, D>, Software, (), NRL, NPEERS, VApps>;

/// The relay-path address family and index the hub's own relay uses for its members: an index no client has.
pub(super) const LOCAL_RELAY: u8 = 0xFE;

/// A stream the layer above moves bytes of.
pub type StreamId = u64;

/// How to reach a hub.
#[derive(Debug, Clone, Copy)]
pub struct HubAddr {
    /// Its identity.
    pub id: NodeId,
    /// Its UDP address.
    pub udp: SocketAddr,
    /// Its TCP address for relay carriers.
    pub tcp: SocketAddr,
}

/// How a core is built.
#[derive(Debug, Clone)]
pub struct Spec {
    /// The node's name; its keys derive from it.
    pub name: String,
    /// Where it listens (UDP and TCP).
    pub addr: SocketAddr,
    /// The hubs, this node's own entry included when it is one.
    pub hubs: Vec<HubAddr>,
    /// Whether this node is a hub.
    pub is_hub: bool,
    /// The interface size the endpoint is told.
    pub mtu: u16,
    /// Keep the node's trace and packet log (see [`TraceLog`]).
    pub trace: bool,
    /// Datagrams per transmit (segmentation offload), at least 1.
    pub batch: usize,
    /// The 16 KiB buffer chunks each session may hold.
    pub pool_chunks: usize,
    /// Ask the site's router for a port mapping (only the nodes of a site with a port-mapping service do).
    pub portmap: bool,
}

/// What the core asks the runtime layer to do with a stream.
#[derive(Debug)]
pub enum Op {
    /// Open a TCP connection to `to`; the layer reports [`StreamEv::Opened`] or [`StreamEv::Failed`] for `stream`.
    Connect {
        /// The stream's id.
        stream: StreamId,
        /// The address.
        to: SocketAddr,
    },
    /// Write bytes.
    Write {
        /// The stream.
        stream: StreamId,
        /// The bytes.
        data: Vec<u8>,
    },
    /// Close the stream.
    Close {
        /// The stream.
        stream: StreamId,
    },
}

/// What happened to a stream.
#[derive(Debug)]
pub enum StreamEv {
    /// A connection arrived at the hub's listener.
    Accepted(StreamId),
    /// A connection the core asked for is open.
    Opened(StreamId),
    /// A connection the core asked for could not be opened.
    Failed(StreamId),
    /// The stream ended.
    Closed(StreamId),
    /// Bytes arrived.
    Data(StreamId, Vec<u8>),
}

/// A command for the node.
#[derive(Debug)]
pub enum NCmd {
    /// Subscribe to a topic.
    Subscribe(Vec<u8>),
    /// Fetch a value.
    Fetch {
        /// Its root.
        root: [u8; 32],
        /// Its length.
        length: u64,
        /// The providers.
        providers: Vec<[u8; 32]>,
    },
    /// Start a reconcile round.
    Reconcile {
        /// The peer.
        peer: [u8; 32],
        /// The set.
        set: Vec<u8>,
    },
    /// Serve a value.
    Provide([u8; 32]),
    /// The node sleeps.
    Suspend,
    /// The node wakes.
    Resume,
    /// Leave the group.
    Leave,
}

/// The identity key of a node name.
///
/// # Errors
/// The key could not be made from the name's seed.
pub fn keypair(name: &str) -> Result<Keypair, String> {
    let alg = IdentityAlg::Ed25519;
    Keypair::from_seed(alg, &seed_bytes(name, "vinc-identity", alg.seed_len()))
        .map_err(|_| format!("the identity of {name} could not be made"))
}

/// The node id of a node name.
///
/// # Errors
/// The key could not be made from the name's seed.
pub fn node_id(name: &str) -> Result<NodeId, String> {
    keypair(name).map(|k| k.node_id())
}

/// One transmit for the runtime layer to send.
#[derive(Debug, Clone, Copy)]
pub struct Tx {
    /// Where to.
    pub remote: SocketAddr,
    /// Bytes in the buffer.
    pub len: usize,
    /// The size of each datagram.
    pub segment: usize,
}

/// The host core. See the module docs.
pub struct Core<const K: usize, const D: usize> {
    /// The node.
    pub node: Box<VNode<K, D>>,
    pub(super) prov: Software,
    pub(super) kp: Keypair,
    pub(super) prekeys: SoftPrekeys<Software>,
    pub(super) hdrbg: Drbg,
    pub(super) addr: SocketAddr,
    pub(super) is_hub: bool,
    /// This node's id.
    pub me: NodeId,
    pub(super) streams: [Option<StreamId>; NRL],
    pub(super) next_stream: StreamId,
    pub(super) hub: Option<HubSide>,
    pub(super) small: VecDeque<(SocketAddr, Vec<u8>)>,
    /// What the layer above does with streams, oldest first.
    pub ops: VecDeque<Op>,
    /// What the application layer reads, oldest first.
    pub events: VecDeque<NodeEvent>,
    /// The delay-tolerant layer's trace records with the wall clock (milliseconds) they were read at, oldest first;
    /// empty unless delay-tolerant delivery is on.
    pub dtn_trace: VecDeque<(u64, NodeTrace)>,
    /// What the node did besides delivering, counted by name: sessions that came up and ended, publishes
    /// acknowledged, given up, made to wait or refused, repairs, and, while the node's trace is on, the retries,
    /// rejected messages and closed backlogs its trace records. Reported with the node's counts, so a loss in a result
    /// can be traced to what happened on which node.
    pub counters: BTreeMap<&'static str, u64>,
    /// The trace and packet log, kept only when the scenario asks for it; every recording site tests this one option.
    pub tlog: Option<TraceLog>,
    /// What the node restored from a kept bundle store when it started.
    pub restored: DtnRestored,
    pub(super) start: std::time::Instant,
    pub(super) dirty: bool,
    /// The port-mapping client's HTTP exchange in flight, and how many there were.
    pub(super) http: Option<super::portmap::HttpLeg>,
    pub(super) http_count: u64,
}

/// Build the node of `spec` over `apps`.
fn build<const K: usize, const D: usize>(
    spec: &Spec,
    now: u64,
    apps: VApps,
) -> Result<(Box<VNode<K, D>>, Keypair, SoftPrekeys<Software>, Drbg), String> {
    let kp = keypair(&spec.name)?;
    let identity =
        LocalIdentity::from_keypair(&kp, KeyHandle(1)).map_err(|_| "the identity key was refused".to_owned())?;
    let prov = Software;
    let mut drbg = Drbg::new(&seed32(&spec.name, "vinc-drbg"));
    let mut cfg = EndpointConfig::new(u64::from_le_bytes(
        seed_bytes(&spec.name, "vinc-endpoint", 8)
            .try_into()
            .map_err(|_| "seed".to_owned())?,
    ));
    cfg.conn.max_gso = spec.batch.max(1);
    cfg.conn.interface_mtu = spec.mtu;
    cfg.conn.credit = vinc_security::CreditRecord::new(1 << 20, stream_limit(), u16::MAX);
    let ep_drbg = Drbg::new(&seed32(&spec.name, "vinc-ep-drbg"));
    let mut ep: Box<Ep<K, D>> = Endpoint::new_owned(now, prov, ep_drbg, identity, cfg, spec.pool_chunks);
    let mut env = Env {
        provider: &prov,
        now,
        drbg: &mut drbg,
    };
    let mut prekeys =
        SoftPrekeys::new(&mut env, PrekeyPolicy::default()).map_err(|_| "the prekeys could not be made".to_owned())?;
    let prekey_info = prekeys
        .acquire(&mut env)
        .map_err(|_| "the prekeys could not be made".to_owned())?;
    ep.set_prekey(prekey_info.clone());
    // Every node accepts the reach test's sessions.
    ep.register_alpn(super::portmap::REACH_ALPN);
    ep.add_iface(spec.addr)
        .ok_or_else(|| "the interface could not be added to the endpoint".to_owned())?;
    let mut relays: [Option<RelayCfg>; NRL] = [None; NRL];
    for (d, h) in relays.iter_mut().zip(spec.hubs.iter().filter(|h| h.id != kp.node_id())) {
        *d = Some(RelayCfg {
            id: h.id,
            udp: Some(h.udp),
            tcp: Some(h.tcp),
            ws: None,
        });
    }
    let wall_ms = wall_ms();
    let ncfg = NodeConfig {
        connect: ConnCfg {
            me: kp.node_id(),
            identity,
            relays,
            phone: false,
            restarted: false,
            start: now,
            v6: false,
            keep_learn: false,
        },
        is_hub: spec.is_hub,
        version: 1,
        alpn: HUB_ALPN,
        // A hub serves a subscriber on a slow path from the topic's log, so the log must hold the largest burst a
        // scenario publishes (2,000 messages of 4 KiB): 16 MiB a topic where the default is 4.
        limits: vinc_broadcast::Limits {
            log_bytes: TOPIC_LOG_BYTES,
            ..vinc_broadcast::Limits::default()
        },
        wall_ms,
        local: spec.addr,
        // The delay-tolerant layer's decisions are observable only through the trace: on with the layer.
        trace: apps.dtn.is_on() || spec.trace,
    };
    let drbg2 = Drbg::new(&seed32(&spec.name, "vinc-node-drbg"));
    let kp2 = keypair(&spec.name)?;
    let node = Node::with_apps(
        &ncfg,
        *ep,
        prekey_info,
        prov,
        drbg2,
        Box::new(kp2),
        (),
        u64::from_le_bytes(
            seed_bytes(&spec.name, "vinc-conn", 8)
                .try_into()
                .map_err(|_| "seed".to_owned())?,
        ),
        apps,
    )
    .map_err(|e| format!("the node did not start: {e}"))?;
    Ok((Box::new(node), kp, prekeys, drbg))
}

fn wall_ms() -> u64 {
    crate::node::data::wall_ns() / 1_000_000
}

impl<const K: usize, const D: usize> Core<K, D> {
    /// Build a core. The caller runs it on a thread with a large stack: the node holds its buffers inline.
    ///
    /// # Errors
    /// Why the node could not start.
    pub fn new(spec: &Spec, apps: VApps) -> Result<Self, String> {
        let start = std::time::Instant::now();
        let now = Self::epoch_ns();
        let resume = apps.dtn.has_records();
        let (mut node, kp, prekeys, hdrbg) = build::<K, D>(spec, now, apps)?;
        // A kept store is read back before any other input, as the node asks.
        let restored = if resume {
            node.set_wall_ms(now, wall_ms());
            node.dtn_restore(now)
        } else {
            DtnRestored::default()
        };
        let me = kp.node_id();
        let hub = spec.is_hub.then(|| HubSide {
            relay: Box::new(HubRelay::new(RelayConfig::new(
                me,
                u64::from_le_bytes(seed_bytes(&spec.name, "vinc-relay", 8).try_into().unwrap_or([0; 8])),
            ))),
            streams: HashMap::new(),
            by_node: HashMap::new(),
            stores: ResponderStores::default(),
            slots: Vec::new(),
            scid: 0,
        });
        let mut me_core = Self {
            node,
            prov: Software,
            kp,
            prekeys,
            hdrbg,
            addr: spec.addr,
            is_hub: spec.is_hub,
            me,
            streams: [None; NRL],
            next_stream: 1,
            hub,
            small: VecDeque::new(),
            ops: VecDeque::new(),
            events: VecDeque::new(),
            dtn_trace: VecDeque::new(),
            counters: BTreeMap::new(),
            tlog: spec.trace.then(TraceLog::new),
            restored,
            start,
            dirty: false,
            http: None,
            http_count: 0,
        };
        me_core.node.set_local(&[spec.addr]);
        let now = me_core.now();
        if spec.portmap {
            me_core.start_port_mapping(now);
        }
        me_core.pump(now);
        Ok(me_core)
    }

    /// A start point for the node's clock that is never zero.
    const fn epoch_ns() -> u64 {
        1_000_000_000
    }

    /// The node's clock now, in nanoseconds.
    pub fn now(&self) -> u64 {
        Self::epoch_ns() + u64::try_from(self.start.elapsed().as_nanos()).unwrap_or(u64::MAX)
    }

    /// The `Instant` at which the node's clock reads `t`.
    pub fn instant_of(&self, t: u64) -> std::time::Instant {
        self.start + std::time::Duration::from_nanos(t.saturating_sub(Self::epoch_ns()))
    }

    /// One turn of the host duties, repeated until nothing moves.
    pub fn pump(&mut self, now: u64) {
        self.node.set_wall_ms(now, wall_ms());
        for _ in 0..128 {
            self.node.poll(now);
            let mut busy = self.events_step(now);
            busy |= self.members_step(now);
            busy |= self.keys_step(now);
            busy |= self.io_step(now);
            busy |= self.udp_step();
            busy |= self.streams_out_step();
            busy |= self.http_step();
            busy |= std::mem::take(&mut self.dirty);
            self.trace_step();
            if !busy {
                return;
            }
        }
    }

    /// Keep the delay-tolerant layer's trace records (and the count of records lost), count the records that say
    /// why a message may not have arrived, drop the others. The trace is on only with the delay-tolerant layer.
    fn trace_step(&mut self) {
        use vinc_broadcast::Trace as Bc;

        let wall = wall_ms();
        while let Some(item) = self.node.poll_trace() {
            let counted = match item.body {
                Body::Node(NodeTrace::BacklogClosed { .. }) => Some(("backlog_closed", 1)),
                Body::Node(NodeTrace::DuplicateClosed { .. }) => Some(("duplicate_closed", 1)),
                Body::Node(NodeTrace::StreamReset { .. }) => Some(("stream_reset", 1)),
                Body::Node(NodeTrace::Backoff { .. }) => Some(("dial_backoff", 1)),
                Body::Node(NodeTrace::Lost { count }) => Some(("trace_lost", count)),
                Body::Broadcast(Bc::Lost { count }) => Some(("trace_lost", u64::from(count))),
                Body::Broadcast(Bc::PubRetry { .. }) => Some(("publish_retry", 1)),
                Body::Broadcast(Bc::Rejected { .. }) => Some(("message_rejected", 1)),
                Body::Broadcast(Bc::SubSent { .. }) => Some(("subscribe_sent", 1)),
                Body::Broadcast(Bc::GetSent { .. }) => Some(("repair_asked", 1)),
                _ => None,
            };
            if let Some((name, n)) = counted {
                *self.counters.entry(name).or_insert(0) += n;
            }
            if let Some(l) = self.tlog.as_mut() {
                let mut text = String::new();
                let _ = item.write_ndjson(&mut text);
                l.note("trace", text);
            }
            if let Body::Node(
                t @ (NodeTrace::DtnCreated { .. }
                | NodeTrace::DtnOffer { .. }
                | NodeTrace::DtnSymbols { .. }
                | NodeTrace::DtnParity { .. }
                | NodeTrace::DtnLost { .. }
                | NodeTrace::DtnComplete { .. }
                | NodeTrace::DtnCustody { .. }
                | NodeTrace::DtnAcked { .. }
                | NodeTrace::DtnRefused { .. }
                | NodeTrace::DtnReleased { .. }
                | NodeTrace::Lost { .. }),
            ) = item.body
            {
                self.dtn_trace.push_back((wall, t));
            }
        }
    }

    /// Make a bundle for `to` carrying `payload`; returns its id.
    ///
    /// # Errors
    /// Why the node refused it.
    pub fn dtn_send(
        &mut self,
        now: u64,
        to: &RecipientKeys,
        payload: &[u8],
        plan: &DtnPlan,
    ) -> Result<[u8; 32], String> {
        self.node.set_wall_ms(now, wall_ms());
        let r = self.node.dtn_send(now, to, payload, plan).map_err(|e| e.to_string());
        self.pump(now);
        r
    }

    fn events_step(&mut self, now: u64) -> bool {
        let mut did = false;
        while let Some(ev) = self.node.poll_event() {
            did = true;
            let counted = match &ev {
                NodeEvent::PublishAcked { .. } => Some("publish_acked"),
                NodeEvent::PublishGaveUp { .. } => Some("publish_gave_up"),
                NodeEvent::GapRepaired { .. } => Some("gap_repaired"),
                NodeEvent::Lost { .. } => Some("events_lost"),
                NodeEvent::Endpoint(Event::Closed { .. }) => Some("session_closed"),
                NodeEvent::Endpoint(Event::Connected { .. } | Event::Incoming { .. }) => Some("session_up"),
                _ => None,
            };
            if let Some(name) = counted {
                *self.counters.entry(name).or_insert(0) += 1;
            }
            match ev {
                NodeEvent::Endpoint(e) => self.duty(now, e),
                NodeEvent::BroadcastAcpCheck { id, .. } => self.node.broadcast_acp_answer(now, id, true),
                NodeEvent::Message { .. }
                | NodeEvent::PublishAcked { .. }
                | NodeEvent::PublishGaveUp { .. }
                | NodeEvent::PublishRoom
                | NodeEvent::GapRepaired { .. }
                | NodeEvent::Fallback { .. }
                | NodeEvent::Restored { .. }
                | NodeEvent::Subscribed { .. }
                | NodeEvent::Member(_)
                | NodeEvent::ValueComplete { .. }
                | NodeEvent::ValueFailed { .. }
                | NodeEvent::ReconcileDone { .. }
                | NodeEvent::ReconcileFailed { .. }
                | NodeEvent::DtnReceived { .. }
                | NodeEvent::DtnCustody { .. }
                | NodeEvent::DtnHandedOff { .. }
                | NodeEvent::DtnDelivered { .. }
                | NodeEvent::DtnExpired { .. }
                | NodeEvent::Lost { .. } => self.events.push_back(ev),
                _ => {}
            }
        }
        did
    }

    /// The host duties of one endpoint event: key requests and access checks.
    fn duty(&mut self, now: u64, ev: Event) {
        match ev {
            Event::KeyRequest { session } => {
                let owned = match self.node.endpoint().query(Query::KeyRequest(session)) {
                    vinc_core::Answer::KeyRequest(req) => {
                        Some(answer(self.prov, &self.kp, &self.prekeys, &mut self.hdrbg, now, &req))
                    }
                    _ => None,
                };
                if let Some(owned) = owned {
                    // A refused answer leaves the handshake to time out, which the node reports.
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
                let _ = self.node.command(now, Command::AcpAnswer { check, allow: true });
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
                    .map(|r| answer(self.prov, &self.kp, &self.prekeys, &mut self.hdrbg, now, &r));
                let Some(owned) = owned else { break };
                did = true;
                self.node.key_response(now, i, owned.response());
            }
        }
        for _ in 0..8 {
            let owned = self
                .node
                .sign_request()
                .map(|r| answer(self.prov, &self.kp, &self.prekeys, &mut self.hdrbg, now, &r));
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
                    if kind == Kind::Tcp {
                        let stream = self.next_stream;
                        self.next_stream += 1;
                        if let Some(s) = self.streams.get_mut(relay) {
                            *s = Some(stream);
                        }
                        self.ops.push_back(Op::Connect { stream, to });
                    } else {
                        // Only TCP carriers are configured (the hubs' WebSocket address is left out), so this does
                        // not happen; a refusal now is the node's cue to try its next way.
                        self.node.stream_closed(now, relay);
                    }
                }
                Io::Close { relay } => {
                    if let Some(s) = self.streams.get_mut(relay).and_then(Option::take) {
                        self.ops.push_back(Op::Close { stream: s });
                    }
                }
            }
        }
        did
    }

    fn udp_step(&mut self) -> bool {
        let mut did = false;
        let mut buf = [0u8; 2048];
        while let Some((to, n)) = self.node.poll_udp(&mut buf) {
            did = true;
            if to.port() == vinc_connect::local::PORT {
                continue;
            }
            if to.port() == vinc_portmap::client::PORT || to == vinc_portmap::upnp::SSDP {
                *self.counters.entry("portmap_udp").or_insert(0) += 1;
            }
            if let Some(d) = buf.get(..n) {
                self.small.push_back((to, d.to_vec()));
            }
        }
        did
    }

    fn streams_out_step(&mut self) -> bool {
        let mut did = false;
        let mut buf = vec![0u8; 20_000];
        for i in 0..NRL {
            let Some(stream) = self.streams.get(i).copied().flatten() else {
                continue;
            };
            loop {
                let n = self.node.poll_stream(i, &mut buf);
                if n == 0 {
                    break;
                }
                did = true;
                if let Some(d) = buf.get(..n) {
                    self.ops.push_back(Op::Write {
                        stream,
                        data: d.to_vec(),
                    });
                }
            }
        }
        did
    }

    /// The next datagram, or run of datagrams of one size, to send; fills `buf`.
    pub fn poll_transmit(&mut self, now: u64, buf: &mut [u8]) -> Option<Tx> {
        if let Some((remote, data)) = self.small.pop_front() {
            let dst = buf.get_mut(..data.len())?;
            dst.copy_from_slice(&data);
            return Some(Tx {
                remote,
                len: data.len(),
                segment: data.len(),
            });
        }
        loop {
            let Some(t) = self.node.poll_transmit(now, buf) else {
                // The node writes the datagrams of a relay path onto its carrier as it hands them out: they leave
                // with this drain, not with the next turn of the host duties.
                self.streams_out_step();
                return None;
            };
            if let Some((relay, slot)) = relay_parts(&t.remote)
                && relay == LOCAL_RELAY
            {
                let node = self.hub.as_ref().and_then(|h| h.slots.get(usize::from(slot)).copied());
                if let (Some(node), Some(data), Some(h)) = (node, buf.get(..t.len), self.hub.as_mut()) {
                    let mut s = Collect::default();
                    let _ = h.relay.send_local(now, &node, 0, data, &mut s);
                    self.apply(now, s);
                    self.dirty = true;
                }
                continue;
            }
            return Some(Tx {
                remote: t.remote,
                len: t.len,
                segment: t.segment_size.max(1),
            });
        }
    }

    fn relay_of_stream(&self, s: StreamId) -> Option<usize> {
        self.streams.iter().position(|x| *x == Some(s))
    }

    /// A datagram arrived from `remote`.
    pub fn handle_datagram(&mut self, now: u64, remote: SocketAddr, data: &mut [u8]) {
        self.node.set_wall_ms(now, wall_ms());
        let request = self.hub.is_some() && is_relay_request(data);
        if request {
            let member = self.node.member_at(&remote);
            let mut s = Collect::default();
            if let Some(h) = self.hub.as_mut() {
                let _ = h.relay.datagram(now, remote, member.as_ref(), data, &mut s);
            }
            self.apply(now, s);
        } else {
            if self.hub.is_some()
                && data.first().is_some_and(|b| *b >= 0x40)
                && let Some(n) = self.node.member_at(&remote)
                && let Some(h) = self.hub.as_mut()
            {
                let _ = h.relay.udp_heard(&n, now);
            }
            self.node.handle_datagram(now, self.addr, remote, data);
        }
        self.pump(now);
    }

    /// When the node next needs `handle_timeout`.
    pub fn poll_timeout(&self) -> Option<u64> {
        [
            self.node.poll_timeout(),
            self.hub.as_ref().and_then(|h| h.relay.next_deadline()),
        ]
        .into_iter()
        .flatten()
        .min()
    }

    /// Time passed.
    pub fn handle_timeout(&mut self, now: u64) {
        self.node.set_wall_ms(now, wall_ms());
        if let Some(h) = self.hub.as_mut()
            && h.relay.next_deadline().is_some_and(|d| d <= now)
        {
            let mut s = Collect::default();
            h.relay.handle_timeout(now, &mut s);
            self.apply(now, s);
        }
        self.node.handle_timeout(now);
        self.pump(now);
    }

    /// Publish `body` to `topic`.
    ///
    /// # Errors
    /// What the node refused. [`vinc_broadcast::Refused::Backlog`] means as many publishes as the node tracks are
    /// waiting for a hub: the message is to be offered again when one of them is acknowledged or given up.
    pub fn publish(&mut self, now: u64, topic: &[u8], body: &[u8]) -> Result<(), vinc_broadcast::Refused> {
        self.node.set_wall_ms(now, wall_ms());
        let r = self.node.publish(now, topic, body).map(|_| ());
        self.pump(now);
        r
    }

    /// Name the peers this node holds sessions with, so the hubs scope its topics to its connected component.
    ///
    /// # Errors
    /// What the node refused.
    pub fn set_adjacent(&mut self, peers: &[[u8; 32]]) -> Result<usize, vinc_broadcast::Refused> {
        let now = self.now();
        self.node.set_wall_ms(now, wall_ms());
        let r = self.node.set_adjacent(now, peers);
        self.pump(now);
        r
    }

    /// Apply a command of the application; the id of the fetch or round it started, else 0.
    ///
    /// # Errors
    /// What the node refused, in a sentence.
    pub fn command(&mut self, now: u64, cmd: NCmd) -> Result<u32, String> {
        self.node.set_wall_ms(now, wall_ms());
        let mut id = 0;
        match cmd {
            NCmd::Subscribe(t) => {
                self.node
                    .subscribe(now, &t)
                    .map_err(|e| format!("the topic was refused: {e:?}"))?;
            }
            NCmd::Fetch {
                root,
                length,
                providers,
            } => {
                let req = ValuesRequest {
                    root,
                    length,
                    ranges: &[],
                    providers: &providers,
                    deadline: None,
                };
                id = self.node.values_fetch(now, &req).map_err(|e| e.to_string())?;
            }
            NCmd::Reconcile { peer, set } => {
                id = self
                    .node
                    .sets_start(now, &peer, &set)
                    .map_err(|e| format!("the round did not start: {e:?}"))?;
            }
            NCmd::Provide(root) => {
                if !self.node.values_provide(&root) {
                    return Err("the node serves too many values already".into());
                }
            }
            NCmd::Suspend => self.node.suspend(now, wall_ms()),
            NCmd::Resume => self.node.resume(now, false),
            NCmd::Leave => self.node.leave(now),
        }
        self.pump(now);
        Ok(id)
    }

    /// A stream event from the runtime layer.
    pub fn stream_event(&mut self, now: u64, ev: StreamEv) {
        self.node.set_wall_ms(now, wall_ms());
        if self.http_event(now, &ev) {
            self.pump(now);
            return;
        }
        match ev {
            StreamEv::Accepted(stream) => {
                if let Some(h) = self.hub.as_mut() {
                    h.scid += 1;
                    let scid = ConnId::new(&h.scid.to_be_bytes());
                    let identity = LocalIdentity::from_keypair(&self.kp, KeyHandle(1));
                    if let (Some(scid), Ok(identity)) = (scid, identity)
                        && let Ok(cfg) = session::responder_config(identity, scid)
                    {
                        h.streams.insert(
                            stream,
                            RStream {
                                carrier: Box::new(ProtectedCarrier::accept(cfg)),
                                node: None,
                                session: None,
                            },
                        );
                    } else {
                        self.ops.push_back(Op::Close { stream });
                    }
                } else {
                    self.ops.push_back(Op::Close { stream });
                }
            }
            StreamEv::Opened(stream) => {
                if let Some(i) = self.relay_of_stream(stream) {
                    self.node.stream_opened(now, i);
                }
            }
            StreamEv::Failed(stream) | StreamEv::Closed(stream) => {
                if let Some(i) = self.relay_of_stream(stream) {
                    if let Some(s) = self.streams.get_mut(i) {
                        *s = None;
                    }
                    self.node.stream_closed(now, i);
                } else {
                    self.drop_stream(now, stream);
                }
            }
            StreamEv::Data(stream, data) => self.stream_data(now, stream, &data),
        }
        self.pump(now);
    }

    fn stream_data(&mut self, now: u64, stream: StreamId, data: &[u8]) {
        if let Some(l) = self.tlog.as_mut() {
            l.note("carrier_rx", format!("{stream} {}", data.len()));
        }
        if let Some(i) = self.relay_of_stream(stream) {
            let mut bytes = data;
            for _ in 0..64 {
                let n = self.node.stream_data(now, i, bytes);
                bytes = bytes.get(n..).unwrap_or_default();
                self.keys_step(now);
                if bytes.is_empty() || (n == 0 && self.node.key_request(i).is_none()) {
                    return;
                }
            }
            return;
        }
        let mut rest = data;
        for _ in 0..64 {
            let Some(rs) = self.hub.as_mut().and_then(|h| h.streams.get_mut(&stream)) else {
                return;
            };
            let n = rs.carrier.receive(rest);
            rest = rest.get(n..).unwrap_or_default();
            self.drain(now, stream);
            if rest.is_empty() || n == 0 {
                break;
            }
        }
    }

    /// Whether this node is a hub.
    pub const fn is_hub(&self) -> bool {
        self.is_hub
    }
}

impl<const K: usize, const D: usize> Core<K, D> {
    /// The value store the node serves from and fetches into.
    pub fn values(&self) -> VStore {
        self.node.apps().values.clone()
    }

    /// Hold a set under `name`.
    ///
    /// # Errors
    /// The set could not be indexed.
    pub fn hold_set(&mut self, name: &[u8], items: Vec<[u8; 32]>) -> Result<(), String> {
        self.node.apps_mut().sets.insert(name, items)
    }
}

#[cfg(test)]
mod tests;
