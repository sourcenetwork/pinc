//! The control protocol between the orchestrator and a node program that runs a workload: one JSON object per line,
//! requests on the program's standard input, replies and events on its standard output.
//!
//! The program prints `READY <json>` once its stack is up. After that every request carries an `id`; the program
//! answers each with a reply that carries the same `id` (a long request, such as a publication run, answers when it is
//! done, and the program takes the next request meanwhile). Nothing else is printed on standard output.
//!
//! Invariants: a request the program cannot parse is answered with an error and the program goes on; a reply says what
//! was not done and what to do, never an internal name; no unbounded value is sent in one line (histograms are sparse,
//! sets are summarised).

use std::net::Ipv4Addr;

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::node::data::Hist;
use crate::scenario::{Role, Stack};

/// One node of the scenario, as every node program knows it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PeerSpec {
    /// The node's name; its keys derive from it.
    pub name: String,
    /// Its index in the scenario's node list: the origin in message headers.
    pub index: u16,
    /// Its address on its LAN, as seen from inside its site.
    pub ip: Ipv4Addr,
    /// The address other sites reach it at: its own, or its site router's when the site translates addresses.
    pub public_ip: Ipv4Addr,
    /// Its role.
    pub role: Role,
    /// Among the nodes of its machine, from 0: ports of its stacks are spaced by this.
    #[serde(default)]
    pub slot: u16,
}

impl PeerSpec {
    /// The port of a stack whose base port is `base` for this node.
    pub fn port(&self, base: u16) -> u16 {
        crate::backend::fleet::port(base, self.slot)
    }
}

/// What a node program is started with, as its first input line.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Init {
    /// The stack to run.
    pub stack: Stack,
    /// This node's name.
    pub name: String,
    /// Every node of the scenario, this one included.
    pub peers: Vec<PeerSpec>,
    /// The interface size the stack is told.
    pub mtu: u32,
    /// The most nodes that may be in the group: sizes the VINC endpoint.
    pub sessions: u32,
    /// Ask the site's router for a port mapping: the node's site has a port-mapping service.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub portmap: bool,
    /// The largest iroh gossip message, when the workload sets one (see `Pubsub::iroh_gossip_max`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub iroh_gossip_max: Option<u32>,
    /// Delay-tolerant delivery for this node, on the stacks that have it (VINC); none leaves it off.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dtn: Option<DtnInit>,
    /// Record the node's trace and packet log and report them (VINC only; the other stacks ignore it).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub trace: bool,
}

/// How a node runs delay-tolerant delivery. Read once, when the program starts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DtnInit {
    /// The bytes the node may hold in bundles (its ledger's budget).
    pub budget: u64,
    /// Milliseconds of link-up time before an unacknowledged hand-over is sent again.
    pub retry_ms: u64,
    /// How many times a hand-over is sent in all before it is given up.
    pub max_sends: u8,
    /// Keep the bundle store and the node's records in this directory, so a program started again resumes from
    /// them; none keeps them in memory only.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dir: Option<String>,
    /// The store corrupts every slice it keeps: the node serves symbols that do not hash to their signed root.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub tamper_slices: bool,
    /// The store corrupts the first slice of every bundle it keeps, and no other: one data symbol of the first
    /// erasure block fails its proof, which the block's parity stands in for.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub tamper_one_slice: bool,
    /// When the program starts from a kept store, the head in every held bundle's record has a byte flipped.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub tamper_heads: bool,
}

/// A contact window of delay-tolerant delivery: this node and `peer` are in contact from `from_ms` to `to_ms` after
/// the workload's start.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Contact {
    /// The peer.
    pub peer: String,
    /// When it opens, in milliseconds after the start.
    pub from_ms: u64,
    /// When it closes.
    pub to_ms: u64,
}

impl Init {
    /// This node's own entry.
    pub fn me(&self) -> Option<&PeerSpec> {
        self.peers.iter().find(|p| p.name == self.name)
    }

    /// The peers with `role`, other than this node.
    pub fn others(&self, role: Role) -> impl Iterator<Item = &PeerSpec> {
        self.peers.iter().filter(move |p| p.role == role && p.name != self.name)
    }
}

/// One request.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Request {
    /// Echoed in the reply.
    pub id: u64,
    /// What to do.
    #[serde(flatten)]
    pub cmd: Cmd,
}

/// What a node program can be asked to do.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "cmd", rename_all = "snake_case")]
pub enum Cmd {
    /// Take part in a topic and wait until the stack has a path to the group (at most `wait_ms`).
    Join {
        /// The topic.
        topic: String,
        /// The longest wait for the group.
        wait_ms: u64,
    },
    /// Publish `count` messages of `size` bytes, one every `interval_us`, the first at the wall time `start_ns`; the
    /// reply comes when the last is published.
    Publish {
        /// The topic.
        topic: String,
        /// Messages.
        count: u32,
        /// Bytes each, header included.
        size: u32,
        /// Microseconds between two messages.
        interval_us: u64,
        /// The wall clock time of the first, in nanoseconds since the epoch; zero for now.
        start_ns: u64,
    },
    /// Make a value of `size` bytes from `seed` available to others; the reply carries what a fetcher needs.
    Provide {
        /// The value's size.
        size: u64,
        /// Its content seed.
        seed: u64,
    },
    /// Fetch a value from providers; the reply comes when it is complete and verified, or has failed.
    Fetch {
        /// What the provider(s) answered to [`Cmd::Provide`].
        value: Value,
        /// The providers' names.
        providers: Vec<String>,
        /// The longest wait.
        timeout_ms: u64,
    },
    /// Hold a set of `items` items of 32 bytes derived from `seed`, with the last `different` replaced by items
    /// derived from `other_seed`.
    HoldSet {
        /// The set's name.
        set: String,
        /// Items.
        items: u32,
        /// The seed of the shared items.
        seed: u64,
        /// How many items differ.
        different: u32,
        /// The seed of the items that differ.
        other_seed: u64,
    },
    /// Reconcile the set with a peer's; the reply carries the difference found.
    Reconcile {
        /// The peer.
        peer: String,
        /// The set's name.
        set: String,
        /// The longest wait.
        timeout_ms: u64,
    },
    /// Set the contacts of delay-tolerant delivery: none means every peer, always; a list means only its windows,
    /// counted from the wall clock `t0_ms` (milliseconds since the epoch).
    DtnContacts {
        /// The start the windows count from.
        t0_ms: u64,
        /// The windows; none for every peer, always.
        windows: Option<Vec<Contact>>,
    },
    /// Send a bundle of `size` payload bytes made from `seed` to `to`; the reply carries the bundle's tag.
    DtnSend {
        /// The destination.
        to: String,
        /// Payload bytes.
        size: u64,
        /// The payload's content seed.
        seed: u64,
        /// The copy budget of spray and wait.
        copies: u16,
        /// The lifetime in milliseconds.
        lifetime_ms: u64,
        /// Data symbols per erasure block.
        k: u8,
        /// Parity symbols per erasure block.
        m: u8,
        /// The slice size log (slices of 1 KiB to 16 KiB).
        slice_log: u8,
    },
    /// Tell the group this node is going to sleep (stacks that have the notion).
    Suspend,
    /// Tell the group this node is awake again.
    Resume,
    /// Dial `peer` by its node id alone and report the session's path when it comes up and again `hold_ms` later.
    Reach {
        /// The peer.
        peer: String,
        /// The longest wait for the session.
        timeout_ms: u64,
        /// How long to hold the session before the second look.
        hold_ms: u64,
    },
    /// What this node counted since it started.
    Report,
    /// Leave and end.
    Stop,
}

/// An answer.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Reply {
    /// The request's id.
    pub re: u64,
    /// Whether it was done.
    pub ok: bool,
    /// Why not, in a sentence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    /// The result.
    #[serde(default, skip_serializing_if = "Value::is_null")]
    pub data: Value,
}

impl Reply {
    /// The request was done.
    pub fn ok(re: u64, data: Value) -> Self {
        Self {
            re,
            ok: true,
            error: None,
            data,
        }
    }

    /// The request was not done.
    pub fn fail(re: u64, error: impl Into<String>) -> Self {
        Self {
            re,
            ok: false,
            error: Some(error.into()),
            data: Value::Null,
        }
    }
}

/// What the stack announces when it is up.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct Ready {
    /// The stack's name for itself and its version.
    pub stack: String,
    /// The node's identity as the stack writes it.
    pub id: String,
    /// How the stack was set up, in a sentence for the results.
    pub config: String,
}

/// What a node counted for the publish and subscribe workload.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct PubSubReport {
    /// Messages published.
    pub published: u64,
    /// Distinct messages delivered, own messages excluded.
    pub delivered: u64,
    /// Deliveries of a message already delivered.
    pub duplicates: u64,
    /// Deliveries not counted for duplicates because the table of seen messages was full.
    pub unchecked: u64,
    /// Payload bytes delivered.
    pub bytes: u64,
    /// Delivery latency in microseconds.
    pub latency_us: Hist,
    /// Distinct deliveries per origin index.
    pub per_origin: std::collections::BTreeMap<u16, u64>,
    /// The longest time between two deliveries in milliseconds; absent with fewer than two.
    pub gap_max_ms: Option<f64>,
    /// Where the longest gap began, as milliseconds after the first delivery.
    pub gap_at_ms: Option<f64>,
}

/// One thing that happened to a bundle at a node, as the node's events and its trace show it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "ev", rename_all = "snake_case")]
pub enum DtnWhat {
    /// The bundle was made here with this copy budget.
    Created {
        /// Its copies.
        copies: u64,
    },
    /// It was offered to a peer with this many copies (0 for a delivery to the destination).
    Offer {
        /// The peer.
        peer: String,
        /// The copies handed over.
        copies: u64,
    },
    /// A run of symbols from a peer verified against the signed root.
    Symbols {
        /// The peer.
        peer: String,
        /// The run's first symbol.
        first: u64,
    },
    /// A peer's answer did not verify, and this symbol is lost from it for the rest of the transfer.
    Lost {
        /// The peer.
        peer: String,
        /// The symbol.
        symbol: u64,
    },
    /// Parity symbols were asked of a peer in place of symbols it could not prove.
    Parity {
        /// The peer.
        peer: String,
        /// The parity symbols asked for.
        symbols: u64,
    },
    /// It arrived whole and verified from a peer.
    Complete {
        /// The peer.
        peer: String,
    },
    /// This node took custody (or, at the destination, delivery) from a peer and acknowledged it.
    Custody {
        /// The previous holder.
        peer: String,
    },
    /// A peer's acknowledgement was verified; `relieved` if custody moved to it.
    Acked {
        /// The peer.
        peer: String,
        /// Whether custody moved.
        relieved: bool,
    },
    /// A transfer was refused, by this node or by the peer, for this reason.
    Refused {
        /// The other side.
        peer: String,
        /// The reason, as the node's refusal code names it.
        reason: String,
    },
    /// It left this node: delivered or expired.
    Released {
        /// Whether the destination acknowledged it.
        delivered: bool,
    },
    /// It was opened here, at its destination.
    Received {
        /// The node that made it.
        source: String,
        /// Whether the payload is the one its seed makes.
        intact: bool,
        /// Its payload bytes.
        bytes: u64,
    },
    /// A peer took custody: this node is relieved.
    HandedOff {
        /// The new custodian.
        to: String,
    },
    /// Its destination acknowledged it.
    Delivered,
    /// It expired here before it was delivered.
    Expired,
}

/// One entry of a node's bundle log.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DtnEntry {
    /// The wall clock, in milliseconds since the epoch.
    pub ms: u64,
    /// The bundle's tag: the first eight bytes of its id, in hex.
    pub bundle: String,
    /// What happened.
    #[serde(flatten)]
    pub what: DtnWhat,
}

/// What a node's delay-tolerant layer did in one life of its program.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DtnReport {
    /// Everything that happened to bundles here, in order.
    pub log: Vec<DtnEntry>,
    /// Bundles held now.
    pub held: u64,
    /// The most sealed bytes the host store held at once.
    pub peak_bytes: u64,
    /// The ledger's budget.
    pub budget: u64,
    /// What the node restored from a kept store when it started: held, partial, received and dropped records.
    pub restored: [u64; 4],
    /// Trace records the node dropped because its queue was full; nonzero means the log may miss entries.
    pub lost: u64,
}

/// The kind of event a node prints on its own, not as a reply.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "ev", rename_all = "snake_case")]
pub enum Event {
    /// A line for the log pane.
    Log {
        /// The message.
        msg: String,
    },
}
