//! Settings fixed when a simulator is created, a node's CPU parameters, the cost model and the shape of a LAN.
//!
//! Invariants: every type here is plain data; the cost model is a pure function of its arguments.

use crate::Time;
use crate::link::LinkConfig;
use crate::node::Work;

/// How the harness drives a node after a command.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Driver {
    /// Poll the node to quiescence (events, transmits, timer) after every command.
    #[default]
    Vinc,
    /// As the reference harness does: poll after [`crate::Sim::command`], but not after [`crate::Sim::command_nopump`] (a harness intent).
    /// Output produced by such a command waits for the node's next datagram, timer or pumped command.
    Reference,
}

/// Settings fixed when a simulator is created.
#[derive(Clone, Debug, Default)]
pub struct SimConfig {
    /// How nodes are driven after commands.
    pub driver: Driver,
    /// The link used between two sites that have no explicit link; `None` means such a pair cannot talk.
    pub default_link: Option<LinkConfig>,
    /// Record the ndjson trace.
    pub trace: bool,
    /// Include every datagram (tx, rx, drop) in the trace, not only node events and faults.
    pub trace_packets: bool,
    /// Keep every delivery latency so quantiles can be read; otherwise only count, sum, min and max.
    pub latency_samples: bool,
}

/// The run state of a node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeState {
    /// Running.
    Up,
    /// Crashed; waiting for a restart.
    Crashed,
    /// Suspended; waiting for a resume.
    Suspended,
}

/// A node's CPU parameters. The simulator's [`CostModel`] turns them into a cost per call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cpu {
    /// Speed factor in thousandths: 1000 is the model's speed, 4000 is a node four times slower.
    pub factor_milli: u32,
    /// Fixed cost of a call in nanoseconds (used by [`FlatCost`]).
    pub per_call: Time,
    /// Cost per KiB of datagram handled, in nanoseconds (used by [`FlatCost`]).
    pub per_kib: Time,
}

/// What kind of call a cost is for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Call {
    /// A datagram arrived.
    Datagram,
    /// A timer fired.
    Timer,
    /// A scenario command.
    Command,
    /// A stream record arrived, or a stream endpoint changed.
    Stream,
}

/// Turns one call of a node into busy time. A node is busy until its calls' cost has passed: later datagrams and
/// timers wait, and what the call transmits leaves at the end.
pub trait CostModel {
    /// Nanoseconds the call costs on a node with these CPU parameters, with the node's own work report.
    fn cost(&self, cpu: &Cpu, call: Call, bytes: usize, work: Work) -> Time;
}

/// The default cost model: `(per_call + bytes * per_kib / 1024 + work.ns) * factor_milli / 1000`; ticks are ignored.
#[derive(Clone, Copy, Debug, Default)]
pub struct FlatCost;

impl CostModel for FlatCost {
    fn cost(&self, cpu: &Cpu, _call: Call, bytes: usize, work: Work) -> Time {
        let base = u128::from(cpu.per_call) + bytes as u128 * u128::from(cpu.per_kib) / 1024 + u128::from(work.ns);
        (base * u128::from(cpu.factor_milli) / 1000) as Time
    }
}

/// The shape of a LAN (a site): its uplink and downlink, region, path MTU and middlebox settings.
#[derive(Clone, Debug)]
pub struct LanConfig {
    /// The uplink, shared by every datagram leaving the LAN.
    pub up: LinkConfig,
    /// The downlink, shared by every datagram entering the LAN.
    pub down: LinkConfig,
    /// The region, for the delay between regions.
    pub region: u32,
    /// The site MTU in bytes; the datagram limit is this minus 28 (IPv4) or 48 (IPv6).
    pub mtu: usize,
    /// Drop all UDP in and out of the LAN.
    pub udp_block: bool,
    /// What the LAN's middlebox lets through for stream connections; `None` for no restriction. A LAN with a stream
    /// policy or `udp_block` refuses every inbound connection (SYN), as does a LAN with a captive-portal node.
    pub stream: Option<StreamPolicy>,
    /// A stateful IPv6 firewall: inbound IPv6 is admitted only from remotes the host sent to (at most 256 each).
    pub v6_firewall: bool,
}

impl Default for LanConfig {
    fn default() -> Self {
        Self {
            up: LinkConfig::default(),
            down: LinkConfig::default(),
            region: 0,
            mtu: 1500,
            udp_block: false,
            stream: None,
            v6_firewall: false,
        }
    }
}

/// The stream rules of a LAN's middlebox, applied to the SYN of a connection leaving the LAN.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StreamPolicy {
    /// Destination ports a connection may use; `None` allows any.
    pub ports: Option<Vec<u16>>,
    /// Allow only WebSocket carriers (deep packet inspection blocks raw TCP).
    pub tls_only: bool,
    /// Answer a refused connection with a reset, so it fails after `2 * uplink delay + 1` ns; otherwise the SYN
    /// is dropped silently and the connection fails after its SYN retries.
    pub reject: bool,
}

/// Which link of a LAN.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LanDir {
    /// The uplink.
    Up,
    /// The downlink.
    Down,
    /// Both.
    Both,
}
