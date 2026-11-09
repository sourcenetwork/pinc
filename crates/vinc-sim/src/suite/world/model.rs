//! The data model of a generated world: the typed form of the reference harness's scenario description.
//!
//! A [`World`] is everything a run needs and nothing it produces: the sites and nodes, the schedule of environment
//! actions and application intents, the ground truth the gates compare against, and the adversary's plan. All times
//! are integer nanoseconds of virtual time; node and site numbers are indices into [`World::nodes`] and
//! [`World::sites`]. Every field name is the reference field name in snake case, so a reader can lay the two side by
//! side. The generator in this module's siblings is the only code that constructs a world; every other module reads
//! one.
//!
//! Invariants: `env` is sorted by `(t, kind order of the reference name)` and `intents` by `(t, node)`, exactly as
//! the reference sorts them, because equal-time ordering decides event order in a run.

use std::collections::BTreeMap;

/// A scenario parameter value, as the reference's parameter dictionaries hold them.
#[derive(Clone, Debug, PartialEq)]
pub enum Param {
    /// An integer.
    Int(i64),
    /// A float.
    Float(f64),
    /// A pair of numbers `(lo, hi)`, drawn from with `uniform`; `ints` is true when both were integers.
    Range {
        /// Lower bound.
        lo: f64,
        /// Upper bound.
        hi: f64,
        /// Both bounds were integers in the reference (it matters for `randint` and exact sizes).
        ints: bool,
    },
    /// A flag.
    Bool(bool),
    /// A tuple of integers (sizes).
    Ints(Vec<i64>),
    /// A tuple of names (profiles, partition modes).
    Strs(Vec<String>),
}

/// The parameters of one scenario: the public shape overridden by a variant.
pub type Params = BTreeMap<String, Param>;

/// One side of a site's access link and its loss process.
#[derive(Clone, Debug, PartialEq)]
pub struct Site {
    /// Site number (equal to its index).
    pub sid: usize,
    /// Region, an index into the region delay matrix.
    pub region: usize,
    /// Uplink bits per second.
    pub up_bps: u64,
    /// Downlink bits per second.
    pub down_bps: u64,
    /// Uplink one-way delay.
    pub up_delay_ns: u64,
    /// Downlink one-way delay.
    pub down_delay_ns: u64,
    /// Loss rate of the Gilbert-Elliott process (both directions).
    pub loss: f64,
    /// Mean burst length of the loss process.
    pub burst_ns: u64,
    /// Queue bytes of each direction.
    pub queue_bytes: u64,
    /// The NATs in front of the site, innermost first (every scenario has at most one).
    pub nats: Vec<NatSpec>,
    /// The IPv6 firewall admits inbound traffic.
    pub v6_open: bool,
    /// Site MTU.
    pub mtu: u32,
    /// The middlebox of a hostile site (S4).
    pub middlebox: Option<MiddleboxSpec>,
}

/// A NAT.
#[derive(Clone, Debug, PartialEq)]
pub struct NatSpec {
    /// NAT number (from 1).
    pub nid: usize,
    /// The external address (a host number).
    pub ext_ip: u64,
    /// `eim` or `edm`.
    pub mapping: String,
    /// `eif`, `adf` or `apdf`.
    pub filtering: String,
    /// UDP mapping timeout.
    pub timeout_ns: u64,
    /// Inbound only from public sources (S5).
    pub no_punch: bool,
    /// TCP mapping timeout when the scenario sets one (S4); the reference default (7200 s) otherwise.
    pub tcp_timeout_ns: Option<u64>,
}

/// The middlebox of a hostile site (S4).
#[derive(Clone, Debug, PartialEq)]
pub struct MiddleboxSpec {
    /// UDP is dropped both ways.
    pub udp_block: bool,
    /// Destination ports a SYN may use.
    pub tcp_ports: Vec<u16>,
    /// Only WebSocket carriers pass.
    pub tls_only: bool,
    /// A refused SYN is rejected rather than dropped.
    pub fw_reject: bool,
    /// The captive portal window after every start, if the site has one.
    pub portal_ns: Option<u64>,
}

/// An address of a node's interface, as the reference writes it: `(kind, host, port)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Addr {
    /// `udp4`, `udp6` or `tcp4`.
    pub kind: String,
    /// The host number.
    pub host: u64,
    /// The port.
    pub port: u16,
}

/// One interface of a node.
#[derive(Clone, Debug, PartialEq)]
pub struct IfaceSpec {
    /// `u4`, `u6`, `t` or `w`.
    pub name: String,
    /// `udp4`, `udp6`, `tcp` or `ws`.
    pub kind: String,
    /// The local address.
    pub addr: Addr,
    /// The interface MTU.
    pub mtu: u64,
    /// The address is public (a cloud or datacenter node).
    pub public: bool,
    /// The IPv6 interface of a private node.
    pub v6: bool,
}

/// A node's clock (S13).
#[derive(Clone, Debug, PartialEq)]
pub struct ClockSpec {
    /// Offset from true time.
    pub offset_ns: i64,
    /// Drift in parts per million.
    pub drift_ppm: i64,
    /// Forward jumps `(time, size)`.
    pub jumps: Vec<(u64, u64)>,
}

/// One node of the world.
#[derive(Clone, Debug, PartialEq)]
pub struct NodeSpec {
    /// `cloud`, `desktop`, `phone` or `browser`.
    pub device: String,
    /// The node's first site.
    pub site: usize,
    /// `cloud`, `home`, `mobile` or `browser`.
    pub kind: String,
    /// Region.
    pub region: usize,
    /// Interfaces in the reference order.
    pub ifaces: Vec<IfaceSpec>,
    /// Topics subscribed to, sorted.
    pub topics: Vec<Vec<u8>>,
    /// Sites a mobile node moves between (S3): its own first, then the Wi-Fi site.
    pub sites: Vec<usize>,
    /// Clock settings, if the scenario skews this node.
    pub clock: Option<ClockSpec>,
    /// CPU slowdown factor, if the scenario slows this node.
    pub cpu_factor: Option<u32>,
}

/// An environment action kind. The declaration order is the alphabetical order of the reference names, which is the
/// order that breaks ties between equal times (the reference sorts on `(time, name)`), so the derived `Ord` is the
/// reference's.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum EnvKind {
    /// A crash (`crash`).
    Crash,
    /// A handover (`handover`); the argument is the new site and the gap.
    Handover,
    /// A graceful leave (`leave`).
    Leave,
    /// An access outage (`outage`); the argument is its duration.
    Outage,
    /// A NAT rebind (`rebind`); the node field is the NAT number.
    Rebind,
    /// A restart (`restart`); the argument says whether it keeps its state.
    Restart,
    /// A revocation (`revoke`).
    Revoke,
    /// A node starts (`start`).
    Start,
    /// A suspension (`suspend`); the argument is its duration.
    Suspend,
    /// An upgrade (`upgrade`); the argument is the new version.
    Upgrade,
}

/// The argument of an environment action.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EnvArg {
    /// None.
    None,
    /// A flag (restart with state).
    Flag(bool),
    /// A number (version, duration).
    Num(u64),
    /// A site and a gap (handover).
    SiteGap(usize, u64),
}

/// One scheduled environment action: `(t, kind, node, arg)` in the reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EnvAction {
    /// When.
    pub t: u64,
    /// What.
    pub kind: EnvKind,
    /// The node (or the NAT number for a rebind).
    pub node: usize,
    /// The argument.
    pub arg: EnvArg,
}

/// A ground-truth change the awareness gate checks against.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Change {
    /// When.
    pub t: u64,
    /// `join`, `crash`, `leave`, `stack`, `revoke` or `addr`.
    pub kind: ChangeKind,
    /// The node that changed.
    pub node: usize,
    /// The new stack version for `stack`.
    pub version: Option<u64>,
}

/// The kind of a [`Change`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChangeKind {
    /// A node (re)joined.
    Join,
    /// A node crashed.
    Crash,
    /// A node left on purpose.
    Leave,
    /// A node upgraded its stack.
    Stack,
    /// A node was revoked.
    Revoke,
    /// A node's address changed.
    Addr,
}

/// What an intent asks of the application.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntentKind {
    /// Publish a message to a topic (broadcast layer).
    Publish,
    /// Push to a replicator through the durable log.
    Push,
    /// A document-sync request.
    Docsync,
    /// A management request.
    Manage,
    /// An echo round trip.
    Echo,
    /// A value fetch (values layer).
    Fetch,
    /// A set reconciliation session (reconcile layer).
    Reconcile,
}

/// Which receivers must get an intent: the reference stores either a flag or a set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Must {
    /// A flag: every receiver (publish) or the single flow (others).
    Flag(bool),
    /// An explicit set of receivers.
    Set(Vec<usize>),
}

/// One application intent: a dictionary in the reference.
#[derive(Clone, Debug, PartialEq)]
pub struct Intent {
    /// When.
    pub t: u64,
    /// The acting node.
    pub node: usize,
    /// What.
    pub kind: IntentKind,
    /// The peer (push, docsync, manage, echo, reconcile).
    pub to: Option<usize>,
    /// The topic (publish).
    pub topic: Option<Vec<u8>>,
    /// The message size (publish, push).
    pub size: Option<u64>,
    /// The request size (docsync).
    pub req: Option<u64>,
    /// The response size (docsync).
    pub resp: Option<u64>,
    /// The deadline, relative to `t`.
    pub deadline_ns: u64,
    /// The receivers (publish).
    pub receivers: Vec<usize>,
    /// The must set or flag.
    pub must: Must,
    /// The value name (fetch).
    pub value: Option<String>,
    /// The providers (fetch).
    pub providers: Vec<usize>,
    /// The byte ranges `(offset, length)` (fetch).
    pub ranges: Vec<(u64, u64)>,
    /// The playback rate in bits per second of a stream fetch.
    pub stream_rate: Option<u64>,
    /// A G-SURFACE probe echo.
    pub probe: bool,
    /// The intent runs under bulk transfers (S11).
    pub under_bulk: bool,
    /// The collection (reconcile).
    pub set_ref: Option<Vec<u8>>,
}

/// An adversary action kind. The declaration order is the alphabetical order of the reference names (the order that
/// breaks ties in the reference's sort), so the derived `Ord` is the reference's.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AdvKind {
    /// A spoofed-source amplification probe against a server.
    Amplify,
    /// An eclipse burst at a victim.
    Eclipse,
    /// A garbage flood at a victim.
    Garbage,
}

/// The adversary's static plan.
#[derive(Clone, Debug, PartialEq)]
pub struct Adversary {
    /// The victims, sorted.
    pub victims: Vec<usize>,
    /// Replay probability per inbound datagram at a victim.
    pub replay: f64,
    /// Modification probability per inbound datagram at a victim.
    pub modify: f64,
}

/// A partition: `(from, to, sites X, sites Y, mode)` in the reference.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cut {
    /// Start.
    pub from: u64,
    /// End.
    pub to: u64,
    /// One side's sites.
    pub x: Vec<usize>,
    /// The other side's sites.
    pub y: Vec<usize>,
    /// Both directions (true) or X to Y only.
    pub both: bool,
}

/// The reference sets of S14: the 40 byte items each node holds per collection.
pub type SetKey = (usize, Vec<u8>);

/// A generated world.
#[derive(Clone, Debug, PartialEq)]
pub struct World {
    /// The scenario id (`S1`..`S15`).
    pub id: String,
    /// The generator seed.
    pub seed: u64,
    /// The parameters after overrides.
    pub params: Params,
    /// The sites.
    pub sites: Vec<Site>,
    /// The nodes.
    pub nodes: Vec<NodeSpec>,
    /// One-way delay between regions, nanoseconds.
    pub region_delay_ns: Vec<Vec<u64>>,
    /// The bootstrap nodes (the first three clouds).
    pub bootstrap: Vec<usize>,
    /// Run length.
    pub duration_ns: u64,
    /// The idle window `(from, to)`.
    pub idle_window: (u64, u64),
    /// Environment actions, sorted.
    pub env: Vec<EnvAction>,
    /// Application intents, sorted.
    pub intents: Vec<Intent>,
    /// Value name to size.
    pub values: BTreeMap<String, u64>,
    /// Node to the names of the values it provides, in insertion order.
    pub provides: BTreeMap<usize, Vec<String>>,
    /// Ground-truth changes.
    pub changes: Vec<Change>,
    /// Denied nodes.
    pub denied: Vec<usize>,
    /// Revoked nodes with their revocation times.
    pub revoked: Vec<(usize, u64)>,
    /// Connect deadline for G-CONNECT.
    pub connect_deadline_ns: u64,
    /// Latency of an access answer.
    pub acp_latency_ns: u64,
    /// Validity of an access answer.
    pub acp_validity_ns: u64,
    /// Cap on the revocation bound.
    pub revocation_bound_cap_ns: u64,
    /// Cap on the awareness bound.
    pub awareness_bound_cap_ns: u64,
    /// Cap on the false-suspicion rate per member hour.
    pub false_suspicion_cap: f64,
    /// Term C3 applies (S3).
    pub score_c3: bool,
    /// The cloud nodes.
    pub clouds: Vec<usize>,
    /// The home nodes (S1: the servers after the clouds).
    pub homes: Vec<usize>,
    /// The mobile nodes (S10: the browsers).
    pub mobiles: Vec<usize>,
    /// Hostile nodes (S4).
    pub hostile: Vec<usize>,
    /// Browser nodes (S10).
    pub browsers: Vec<usize>,
    /// Lying providers (S12).
    pub liars: Vec<usize>,
    /// The soak growth check applies (S15).
    pub soak: bool,
    /// Partitions (S13).
    pub partitions: Vec<Cut>,
    /// The adversary's plan, once added.
    pub adversary: Option<Adversary>,
    /// Adversary actions `(t, kind, node)`, sorted.
    pub adversary_env: Vec<(u64, AdvKind, usize)>,
    /// Key compromises `(t, node)`.
    pub compromise: Vec<(u64, usize)>,
    /// The S12 compromise fixed by the scenario `(t, node)`, if any.
    pub compromise_node: Option<(u64, usize)>,
    /// The S12 eclipse victim.
    pub eclipse_victim: Option<usize>,
    /// S14 item sets per `(node, collection)`, each sorted.
    pub sets: BTreeMap<SetKey, Vec<[u8; 40]>>,
    /// S14 profile names per `(node, collection)`.
    pub set_profiles: BTreeMap<SetKey, String>,
    /// S6 load figures `(up, down)` per node, as the reference rounds them.
    pub load_used: BTreeMap<usize, (f64, f64)>,
}
