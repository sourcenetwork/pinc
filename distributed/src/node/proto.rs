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
    /// Tell the group this node is going to sleep (stacks that have the notion).
    Suspend,
    /// Tell the group this node is awake again.
    Resume,
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
