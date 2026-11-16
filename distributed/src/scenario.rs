//! Scenario files: the topology, the stacks, the workload, the fault schedule and the repetitions of one test, as the
//! dashboard edits them and `run` reads them (`distributed/scenarios/*.toml`).
//!
//! A scenario names sites (a LAN behind a router, optionally a home router doing address translation), node groups in
//! those sites, links between the sites' routers, the workload and its parameters, and faults at times into each
//! repetition. Every shaping value is per direction: a link's `shape` is the a-to-b direction and `reverse` patches it
//! for b-to-a. The scenario's `mtu` (1280 to 1500 bytes, 1500 when not set) is the size of every interface of the plan
//! and the interface size the stacks are told. [`Scenario::validate`] reports every problem at once, each with the path
//! of the field it concerns, so the dashboard can point at it.
//!
//! Invariants: a scenario that validates has unique names, existing references, values in range, a route between the
//! two ends of every transport pair, and no transport server behind address translation from its client.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use serde::{Deserialize, Serialize};

pub use crate::scenario_transport::{Transport, TransportTest};

/// The most nodes one scenario may have: the backend's address plan and the dashboard are sized for it.
pub const MAX_NODES: usize = 512;
/// The most nodes in one site (one /24 LAN).
pub const MAX_SITE_NODES: usize = 250;
/// The most sites (one router each).
pub const MAX_SITES: usize = 200;

/// The interface MTU of a scenario that does not set `mtu`.
pub const DEFAULT_MTU: u32 = 1500;
/// The smallest `mtu` a scenario may set: the smallest IPv6 link, and a path that carries the 1,200-byte datagrams the
/// stacks send.
pub const MIN_MTU: u32 = 1280;

/// A stack under test.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Stack {
    /// VINC.
    Vinc,
    /// iroh.
    Iroh,
    /// rust-libp2p over QUIC.
    Libp2p,
}

impl Stack {
    /// Every stack, in the order tables show them.
    pub const ALL: [Self; 3] = [Self::Vinc, Self::Iroh, Self::Libp2p];

    /// The name in files and on the command line.
    pub fn name(self) -> &'static str {
        match self {
            Self::Vinc => "vinc",
            Self::Iroh => "iroh",
            Self::Libp2p => "libp2p",
        }
    }

    /// Parse a name.
    pub fn parse(s: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|x| x.name() == s)
    }
}

impl fmt::Display for Stack {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// How one direction of a link is shaped.
#[derive(Debug, Clone, Copy, Default, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Shape {
    /// One-way delay in milliseconds.
    #[serde(default)]
    pub delay_ms: f64,
    /// Jitter around the delay (normal distribution); it reorders packets, as a real jittery path does.
    #[serde(default)]
    pub jitter_ms: f64,
    /// Random loss per packet, in percent.
    #[serde(default)]
    pub loss_pct: f64,
    /// The rate limit in Mbit/s; none means the link is not rate limited.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rate_mbit: Option<f64>,
    /// The bottleneck buffer as milliseconds of the rate (50 when not set); it sets the shaper's queue limit.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub queue_ms: Option<f64>,
}

/// Changes to a [`Shape`]: each field that is set replaces the shape's.
#[derive(Debug, Clone, Copy, Default, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ShapePatch {
    /// See [`Shape::delay_ms`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub delay_ms: Option<f64>,
    /// See [`Shape::jitter_ms`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub jitter_ms: Option<f64>,
    /// See [`Shape::loss_pct`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub loss_pct: Option<f64>,
    /// See [`Shape::rate_mbit`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rate_mbit: Option<f64>,
    /// See [`Shape::queue_ms`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub queue_ms: Option<f64>,
}

impl Shape {
    /// The default access link of a node: a switched LAN, 50 microseconds each way at 1 Gbit/s.
    pub fn lan() -> Self {
        Self {
            delay_ms: 0.05,
            rate_mbit: Some(1000.0),
            ..Self::default()
        }
    }

    /// This shape with `p` applied.
    #[must_use]
    pub fn patched(&self, p: &ShapePatch) -> Self {
        Self {
            delay_ms: p.delay_ms.unwrap_or(self.delay_ms),
            jitter_ms: p.jitter_ms.unwrap_or(self.jitter_ms),
            loss_pct: p.loss_pct.unwrap_or(self.loss_pct),
            rate_mbit: p.rate_mbit.or(self.rate_mbit),
            queue_ms: p.queue_ms.or(self.queue_ms),
        }
    }

    fn check(&self, path: &str, out: &mut Vec<Problem>) {
        let mut bad = |field: &str, msg: &str| out.push(Problem::new(format!("{path}.{field}"), msg));
        if !(self.delay_ms.is_finite() && (0.0..=10_000.0).contains(&self.delay_ms)) {
            bad("delay_ms", "the delay must be between 0 and 10000 ms");
        }
        if !(self.jitter_ms.is_finite() && (0.0..=10_000.0).contains(&self.jitter_ms)) {
            bad("jitter_ms", "the jitter must be between 0 and 10000 ms");
        }
        if !(self.loss_pct.is_finite() && (0.0..=100.0).contains(&self.loss_pct)) {
            bad("loss_pct", "the loss must be between 0 and 100 percent");
        }
        if let Some(r) = self.rate_mbit
            && !(r.is_finite() && (0.01..=100_000.0).contains(&r))
        {
            bad("rate_mbit", "the rate must be between 0.01 and 100000 Mbit/s");
        }
        if let Some(q) = self.queue_ms
            && !(q.is_finite() && (0.0..=10_000.0).contains(&q))
        {
            bad("queue_ms", "the queue must be between 0 and 10000 ms of the rate");
        }
    }
}

/// Address translation at a site's router, as a home router does it.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Nat {
    /// No translation: the site's LAN is routed.
    #[default]
    None,
    /// The mapping keeps the source port and replies are accepted only from the address and port a node sent to
    /// (Linux masquerading, with unsolicited packets dropped before conntrack keeps them): endpoint-independent
    /// mapping, address-and-port-dependent filtering (RFC 4787).
    PortRestricted,
    /// A new random port for every destination: endpoint-dependent mapping, the hardest case for hole punching.
    Symmetric,
}

/// A port-mapping service on a home router: miniupnpd, which has one switch for PCP and NAT-PMP together and one
/// for UPnP-IGD, so NAT-PMP alone cannot be offered.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PortMap {
    /// PCP, and NAT-PMP with it.
    Pcp,
    /// UPnP-IGD only.
    Upnp,
}

impl PortMap {
    /// Its name in a scenario file.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Pcp => "pcp",
            Self::Upnp => "upnp",
        }
    }
}

/// A site: a LAN with a router.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Site {
    /// The site's name.
    pub name: String,
    /// Whether the router translates addresses for the LAN.
    #[serde(default)]
    pub nat: Nat,
    /// A port-mapping service on the router; none by default. Only a router that translates has one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub portmap: Option<PortMap>,
    /// Each node's access link to the router, both directions.
    #[serde(default = "Shape::lan")]
    pub lan: Shape,
    /// Where the site sits on the dashboard's diagram (x, y in the diagram's units); layout only.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pos: Option<[f64; 2]>,
}

/// What a node does beyond the workload's own roles.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Role {
    /// An ordinary node.
    #[default]
    Peer,
    /// A site's hub (a node others keep sessions with).
    Hub,
    /// A relay or rendezvous point.
    Relay,
    /// A `vinc_relay` server (the binary in `VINC_RELAY_BIN`) in place of a VINC node: the other nodes list it as their
    /// first relay, ahead of the hubs, and join through it as a hub. VINC only.
    RelayServer,
}

/// One node, or `count` alike nodes named `<name>-1` to `<name>-<count>`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NodeGroup {
    /// The name, or the prefix when `count` is above one.
    pub name: String,
    /// The site the nodes are in.
    pub site: String,
    /// How many nodes.
    #[serde(default = "one")]
    pub count: u32,
    /// The role of every node of the group.
    #[serde(default)]
    pub role: Role,
    /// Changes to the site's access link for these nodes.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub link: Option<ShapePatch>,
}

fn one() -> u32 {
    1
}

/// A link between the routers of two sites.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Link {
    /// One site.
    pub a: String,
    /// The other site.
    pub b: String,
    /// The a-to-b direction, and the b-to-a direction unless `reverse` changes it.
    #[serde(default)]
    pub shape: Shape,
    /// Changes for the b-to-a direction.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reverse: Option<ShapePatch>,
}

impl Link {
    /// The b-to-a direction.
    pub fn reverse_shape(&self) -> Shape {
        self.reverse.map_or(self.shape, |p| self.shape.patched(&p))
    }
}

/// What every node gets, the same for every stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Resources {
    /// CPUs per node.
    #[serde(default = "two")]
    pub cpus: u32,
    /// Memory limit per node in MiB.
    #[serde(default = "mem_default")]
    pub memory_mib: u32,
}

fn two() -> u32 {
    2
}

fn mem_default() -> u32 {
    2048
}

impl Default for Resources {
    fn default() -> Self {
        Self {
            cpus: two(),
            memory_mib: mem_default(),
        }
    }
}

/// A client and the server it measures against.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Pair {
    /// The node that runs the client.
    pub client: String,
    /// The node that runs the server.
    pub server: String,
}

/// What the nodes do.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum Workload {
    /// The comparison benches' transport scenarios between pairs of nodes.
    Transport(Transport),
    /// Publish and subscribe on a topic every node takes part in.
    Pubsub(crate::workloads::Pubsub),
    /// Fetching a value from provider nodes.
    Sync(crate::workloads::ValueSync),
    /// Reconciling two sets that differ in a few items.
    Reconcile(crate::workloads::Reconcile),
    /// Bundles for nodes that are offline, carried by delay-tolerant delivery, with checks on its rules.
    Dtn(crate::dtn::Dtn),
    /// One node dials another by its node id; the session's path says whether it is direct (VINC only).
    Reach(crate::workloads::Reach),
}

/// A change to the network or a node during a repetition.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "do", rename_all = "kebab-case")]
pub enum FaultAction {
    /// Change the shaping of a link (both directions); `a` and `b` are two sites, or a node and its site.
    Set {
        /// One end.
        a: String,
        /// The other end.
        b: String,
        /// The changes.
        shape: ShapePatch,
    },
    /// Cut a link: every packet in both directions is lost, as on a black-holed path.
    Cut {
        /// One end.
        a: String,
        /// The other end.
        b: String,
    },
    /// Give a link back the scenario's shaping.
    Restore {
        /// One end.
        a: String,
        /// The other end.
        b: String,
    },
    /// Cut every link of a site to other sites.
    Partition {
        /// The site.
        site: String,
    },
    /// Restore every link of a site.
    Heal {
        /// The site.
        site: String,
    },
    /// Freeze every process of a node (its sockets stay open; nothing runs).
    Pause {
        /// The node.
        node: String,
        /// Tell the group the node is going to sleep first, for the stacks that have that notion (VINC does; the
        /// others are frozen all the same).
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        graceful: bool,
    },
    /// Thaw a paused node.
    Resume {
        /// The node.
        node: String,
        /// Tell the group the node is awake again, as `graceful` told it was asleep.
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        graceful: bool,
    },
    /// Kill a node's processes.
    Kill {
        /// The node.
        node: String,
    },
    /// Start a killed node again.
    Restart {
        /// The node.
        node: String,
    },
}

/// A fault at a time into each repetition.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Fault {
    /// Seconds after the repetition's workload starts.
    pub at_s: f64,
    /// What happens.
    pub action: FaultAction,
}

/// The scenario's `[debug]` table: options for looking inside a run. Off by default: with nothing set a run records
/// and costs the same as without this table.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DebugOpts {
    /// Record the VINC nodes' traces and packet log (datagrams and relay carrier bytes, with the milliseconds since
    /// the node started) and write them beside the results, one file per node after each pubsub, sync or reconcile
    /// measurement. Tracing slows the nodes, so every row made with it says its timings are not comparable. Other
    /// stacks and the transport workload ignore it.
    #[serde(default)]
    pub trace: bool,
}

impl DebugOpts {
    #[allow(
        clippy::trivially_copy_pass_by_ref,
        reason = "serde's skip_serializing_if passes a reference"
    )]
    fn is_default(&self) -> bool {
        *self == Self::default()
    }
}

/// A scenario file.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Scenario {
    /// The scenario's name: lower-case letters, digits and dashes.
    pub name: String,
    /// One line on what it tests.
    #[serde(default)]
    pub about: String,
    /// The stacks run, one after the other on the same network.
    #[serde(default = "all_stacks")]
    pub stacks: Vec<Stack>,
    /// Repetitions of every measurement; every number is reported with its spread over them.
    #[serde(default = "three")]
    pub repetitions: u32,
    /// The MTU of every interface, in bytes (1500 when not set): 1280 to 1500. The stacks are told it as the interface
    /// size.
    #[serde(default = "default_mtu", skip_serializing_if = "is_default_mtu")]
    pub mtu: u32,
    /// What every node gets.
    #[serde(default)]
    pub resources: Resources,
    /// The sites.
    pub sites: Vec<Site>,
    /// The nodes.
    pub nodes: Vec<NodeGroup>,
    /// The links between sites.
    #[serde(default)]
    pub links: Vec<Link>,
    /// What the nodes do.
    pub workload: Workload,
    /// Faults during each repetition.
    #[serde(default)]
    pub faults: Vec<Fault>,
    /// Options for looking inside the run (see [`DebugOpts`]).
    #[serde(default, skip_serializing_if = "DebugOpts::is_default")]
    pub debug: DebugOpts,
}

fn all_stacks() -> Vec<Stack> {
    Stack::ALL.to_vec()
}

fn three() -> u32 {
    3
}

fn default_mtu() -> u32 {
    DEFAULT_MTU
}

#[allow(
    clippy::trivially_copy_pass_by_ref,
    reason = "serde's skip_serializing_if passes a reference"
)]
fn is_default_mtu(m: &u32) -> bool {
    *m == DEFAULT_MTU
}

/// One problem found by [`Scenario::validate`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Problem {
    /// The field it concerns, such as `links[1].shape.loss_pct`.
    pub path: String,
    /// What is wrong and what to do.
    pub message: String,
}

impl Problem {
    pub(crate) fn new(path: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.path, self.message)
    }
}

/// A node after its group is expanded.
#[derive(Debug, Clone, PartialEq)]
pub struct NodeSpec {
    /// The node's name.
    pub name: String,
    /// Index of its site in [`Scenario::sites`].
    pub site: usize,
    /// Its role.
    pub role: Role,
    /// Its access link, both directions.
    pub link: Shape,
}

fn valid_name(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 32
        && s.bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
        && !s.starts_with('-')
}

impl Scenario {
    /// Parse a scenario file.
    ///
    /// # Errors
    /// The text is not TOML or does not have a scenario's fields; the message names the line.
    pub fn parse(text: &str) -> Result<Self, String> {
        toml::from_str(text).map_err(|e| e.to_string())
    }

    /// The file text of this scenario.
    ///
    /// # Errors
    /// A value cannot be written as TOML (not finite).
    pub fn to_toml(&self) -> Result<String, String> {
        toml::to_string_pretty(self).map_err(|e| e.to_string())
    }

    /// The nodes, groups expanded, in order.
    pub fn expand(&self) -> Vec<NodeSpec> {
        let sites: BTreeMap<&str, usize> = self
            .sites
            .iter()
            .enumerate()
            .map(|(i, s)| (s.name.as_str(), i))
            .collect();
        let mut out = Vec::new();
        for g in &self.nodes {
            let Some(&site) = sites.get(g.site.as_str()) else {
                continue;
            };
            let base = self.sites.get(site).map_or_else(Shape::lan, |s| s.lan);
            let link = g.link.map_or(base, |p| base.patched(&p));
            for i in 1..=g.count {
                let name = if g.count == 1 {
                    g.name.clone()
                } else {
                    format!("{}-{i}", g.name)
                };
                out.push(NodeSpec {
                    name,
                    site,
                    role: g.role,
                    link,
                });
            }
        }
        out
    }

    /// Every problem of this scenario; empty when it can run.
    pub fn validate(&self) -> Vec<Problem> {
        let mut out = Vec::new();
        if !valid_name(&self.name) {
            out.push(Problem::new(
                "name",
                "use 1 to 32 lower-case letters, digits and dashes",
            ));
        }
        if self.stacks.is_empty() {
            out.push(Problem::new("stacks", "name at least one stack: vinc, iroh or libp2p"));
        }
        if self.stacks.iter().collect::<BTreeSet<_>>().len() != self.stacks.len() {
            out.push(Problem::new("stacks", "a stack is named twice"));
        }
        if !(1..=100).contains(&self.repetitions) {
            out.push(Problem::new(
                "repetitions",
                "use 1 to 100 repetitions (3 or more to report a spread)",
            ));
        }
        if !(MIN_MTU..=DEFAULT_MTU).contains(&self.mtu) {
            out.push(Problem::new(
                "mtu",
                format!(
                    "use {MIN_MTU} to {DEFAULT_MTU} bytes: the stacks need a path that carries 1200-byte datagrams"
                ),
            ));
        }
        if !(1..=64).contains(&self.resources.cpus) {
            out.push(Problem::new("resources.cpus", "use 1 to 64 CPUs per node"));
        }
        if !(64..=262_144).contains(&self.resources.memory_mib) {
            out.push(Problem::new("resources.memory_mib", "use 64 to 262144 MiB per node"));
        }
        let site_names = self.check_sites(&mut out);
        let nodes = self.check_nodes(&site_names, &mut out);
        self.check_links(&site_names, &mut out);
        let node_names: BTreeMap<&str, &NodeSpec> = nodes.iter().map(|n| (n.name.as_str(), n)).collect();
        if nodes.iter().any(|n| n.role == Role::RelayServer) && self.stacks != [Stack::Vinc] {
            out.push(Problem::new(
                "stacks",
                "a relay-server node runs with the vinc stack only",
            ));
        }
        match &self.workload {
            Workload::Transport(t) => self.check_transport(t, &node_names, &mut out),
            Workload::Pubsub(w) => w.check(self, &node_names, &mut out),
            Workload::Sync(w) => w.check(self, &node_names, &mut out),
            Workload::Reconcile(w) => w.check(self, &node_names, &mut out),
            Workload::Dtn(w) => w.check(self, &node_names, &mut out),
            Workload::Reach(w) => w.check(self, &node_names, &mut out),
        }
        self.check_faults(&site_names, &node_names, &mut out);
        out
    }

    fn check_sites(&self, out: &mut Vec<Problem>) -> BTreeMap<&str, usize> {
        let mut names = BTreeMap::new();
        if self.sites.is_empty() {
            out.push(Problem::new("sites", "add at least one site"));
        }
        if self.sites.len() > MAX_SITES {
            out.push(Problem::new("sites", format!("use at most {MAX_SITES} sites")));
        }
        for (i, s) in self.sites.iter().enumerate() {
            if !valid_name(&s.name) {
                out.push(Problem::new(
                    format!("sites[{i}].name"),
                    "use 1 to 32 lower-case letters, digits and dashes",
                ));
            }
            if names.insert(s.name.as_str(), i).is_some() {
                out.push(Problem::new(format!("sites[{i}].name"), "another site has this name"));
            }
            s.lan.check(&format!("sites[{i}].lan"), out);
            if s.portmap.is_some() && s.nat == Nat::None {
                out.push(Problem::new(
                    format!("sites[{i}].portmap"),
                    "a port mapping needs address translation on the router; set nat",
                ));
            }
        }
        names
    }

    fn check_nodes(&self, sites: &BTreeMap<&str, usize>, out: &mut Vec<Problem>) -> Vec<NodeSpec> {
        let mut per_site = vec![0usize; self.sites.len()];
        for (i, g) in self.nodes.iter().enumerate() {
            if !valid_name(&g.name) {
                out.push(Problem::new(
                    format!("nodes[{i}].name"),
                    "use 1 to 32 lower-case letters, digits and dashes",
                ));
            }
            match sites.get(g.site.as_str()) {
                Some(&s) => {
                    if let Some(c) = per_site.get_mut(s) {
                        *c += g.count as usize;
                    }
                }
                None => out.push(Problem::new(format!("nodes[{i}].site"), "no site has this name")),
            }
            if g.count == 0 {
                out.push(Problem::new(
                    format!("nodes[{i}].count"),
                    "a group has at least one node",
                ));
            }
            if let Some(p) = g.link {
                Shape::lan().patched(&p).check(&format!("nodes[{i}].link"), out);
            }
            if sites.contains_key(g.name.as_str()) {
                out.push(Problem::new(
                    format!("nodes[{i}].name"),
                    "a site has this name; links and faults name both",
                ));
            }
        }
        for (s, n) in per_site.iter().enumerate() {
            if *n > MAX_SITE_NODES {
                out.push(Problem::new(
                    format!("sites[{s}]"),
                    format!("a site holds at most {MAX_SITE_NODES} nodes"),
                ));
            }
        }
        let nodes = self.expand();
        if nodes.is_empty() {
            out.push(Problem::new("nodes", "add at least one node"));
        }
        if nodes.len() > MAX_NODES {
            out.push(Problem::new("nodes", format!("use at most {MAX_NODES} nodes")));
        }
        let mut seen = BTreeSet::new();
        for n in &nodes {
            if !seen.insert(n.name.as_str()) {
                out.push(Problem::new("nodes", format!("two nodes are named {}", n.name)));
            }
        }
        nodes
    }

    fn check_links(&self, sites: &BTreeMap<&str, usize>, out: &mut Vec<Problem>) {
        let mut pairs = BTreeSet::new();
        for (i, l) in self.links.iter().enumerate() {
            for (end, name) in [("a", &l.a), ("b", &l.b)] {
                if !sites.contains_key(name.as_str()) {
                    out.push(Problem::new(format!("links[{i}].{end}"), "no site has this name"));
                }
            }
            if l.a == l.b {
                out.push(Problem::new(format!("links[{i}]"), "a link joins two different sites"));
            }
            let key = if l.a < l.b { (&l.a, &l.b) } else { (&l.b, &l.a) };
            if !pairs.insert(key) {
                out.push(Problem::new(
                    format!("links[{i}]"),
                    "these two sites are already linked",
                ));
            }
            l.shape.check(&format!("links[{i}].shape"), out);
            l.reverse_shape().check(&format!("links[{i}].reverse"), out);
        }
    }

    /// The sites reachable from `from` over links, `from` included.
    pub fn reachable(&self, from: usize) -> BTreeSet<usize> {
        let idx: BTreeMap<&str, usize> = self
            .sites
            .iter()
            .enumerate()
            .map(|(i, s)| (s.name.as_str(), i))
            .collect();
        let mut seen = BTreeSet::from([from]);
        let mut stack = vec![from];
        while let Some(s) = stack.pop() {
            for l in &self.links {
                let (Some(&a), Some(&b)) = (idx.get(l.a.as_str()), idx.get(l.b.as_str())) else {
                    continue;
                };
                for (x, y) in [(a, b), (b, a)] {
                    if x == s && seen.insert(y) {
                        stack.push(y);
                    }
                }
            }
        }
        seen
    }

    fn check_transport(&self, t: &Transport, nodes: &BTreeMap<&str, &NodeSpec>, out: &mut Vec<Problem>) {
        if t.pairs.is_empty() {
            out.push(Problem::new(
                "workload.pairs",
                "add at least one client and server pair",
            ));
        }
        if t.tests.is_empty() {
            out.push(Problem::new("workload.tests", "add at least one test"));
        }
        if !(1..=86_400).contains(&t.timeout_s) {
            out.push(Problem::new("workload.timeout_s", "use 1 to 86400 seconds"));
        }
        for (i, test) in t.tests.iter().enumerate() {
            test.check(&format!("workload.tests[{i}]"), out);
        }
        for (i, p) in t.pairs.iter().enumerate() {
            let (Some(c), Some(s)) = (nodes.get(p.client.as_str()), nodes.get(p.server.as_str())) else {
                out.push(Problem::new(
                    format!("workload.pairs[{i}]"),
                    "both ends must be nodes of the scenario",
                ));
                continue;
            };
            if p.client == p.server {
                out.push(Problem::new(
                    format!("workload.pairs[{i}]"),
                    "the client and the server are different nodes",
                ));
                continue;
            }
            if !self.reachable(c.site).contains(&s.site) {
                out.push(Problem::new(
                    format!("workload.pairs[{i}]"),
                    "no link path joins the two nodes' sites",
                ));
            }
            let behind_nat = self.sites.get(s.site).is_some_and(|x| x.nat != Nat::None);
            if behind_nat && c.site != s.site {
                out.push(Problem::new(
                    format!("workload.pairs[{i}].server"),
                    "the server is behind address translation, which a direct dial cannot cross; put the server in a routed site",
                ));
            }
        }
    }

    fn check_faults(&self, sites: &BTreeMap<&str, usize>, nodes: &BTreeMap<&str, &NodeSpec>, out: &mut Vec<Problem>) {
        for (i, f) in self.faults.iter().enumerate() {
            let path = format!("faults[{i}]");
            if !(f.at_s.is_finite() && (0.0..=86_400.0).contains(&f.at_s)) {
                out.push(Problem::new(format!("{path}.at_s"), "use 0 to 86400 seconds"));
            }
            match &f.action {
                FaultAction::Set { a, b, .. } | FaultAction::Cut { a, b } | FaultAction::Restore { a, b } => {
                    if !self.link_exists(a, b, sites, nodes) {
                        out.push(Problem::new(
                            format!("{path}.action"),
                            "name two linked sites, or a node and its site",
                        ));
                    }
                    if let FaultAction::Set { shape, .. } = &f.action {
                        Shape::default()
                            .patched(shape)
                            .check(&format!("{path}.action.shape"), out);
                    }
                }
                FaultAction::Partition { site } | FaultAction::Heal { site } => {
                    if !sites.contains_key(site.as_str()) {
                        out.push(Problem::new(format!("{path}.action.site"), "no site has this name"));
                    }
                }
                FaultAction::Pause { node, .. }
                | FaultAction::Resume { node, .. }
                | FaultAction::Kill { node }
                | FaultAction::Restart { node } => {
                    if !nodes.contains_key(node.as_str()) {
                        out.push(Problem::new(format!("{path}.action.node"), "no node has this name"));
                    }
                }
            }
        }
    }

    fn link_exists(&self, a: &str, b: &str, sites: &BTreeMap<&str, usize>, nodes: &BTreeMap<&str, &NodeSpec>) -> bool {
        let access = |n: &str, s: &str| nodes.get(n).is_some_and(|n| sites.get(s) == Some(&n.site));
        access(a, b)
            || access(b, a)
            || self
                .links
                .iter()
                .any(|l| (l.a == a && l.b == b) || (l.a == b && l.b == a))
    }
}
