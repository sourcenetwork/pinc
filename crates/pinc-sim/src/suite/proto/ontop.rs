//! The shape of an on-top layer: a protocol that runs above the endpoint next to the harness protocols and that the
//! application drives with commands and listens to for events.
//!
//! Three layers have this shape: broadcast (publish and subscribe: gossip and late publishes), values (provide and
//! fetch verified values) and reconcile (set reconciliation of collections). [`OnTop`] is the one contract they
//! implement; the application ([`super::Stack`]) holds at most one per slot, sends [`Command`]s, drains
//! [`OnTopEvent`]s after every call and does the delivery accounting itself (integrity, provenance, duplicates,
//! access control, store-based fetch completion).
//!
//! Invariants: a layer talks to the endpoint only through the [`Host`] it is given; times are the node's local time;
//! a call never blocks; events are produced in the order they happened and drained until `poll_event` is `None`.

use crate::suite::crypto::MsgId;
use crate::suite::proto::host::{Host, LayerEvent};
use crate::suite::rec::MemberEvent;

/// The value table of a run: value name to the id of its generated content.
pub type ValueIds = std::collections::BTreeMap<String, MsgId>;

/// What the application asks of a layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Command {
    /// Receive the messages of a topic (broadcast).
    Subscribe {
        /// The topic.
        topic: Vec<u8>,
    },
    /// Publish a whole message to a topic (broadcast).
    Publish {
        /// The topic.
        topic: Vec<u8>,
        /// The message bytes.
        msg: Vec<u8>,
    },
    /// Serve a value held in the local store (values).
    Provide {
        /// The value.
        value: MsgId,
        /// Its length.
        len: u64,
    },
    /// Fetch a value, or some ranges of it, into the local store (values).
    Fetch {
        /// The id the layer reports progress under.
        fetch_id: u64,
        /// The value.
        value: MsgId,
        /// Its length.
        len: u64,
        /// The nodes that may hold it.
        providers: Vec<usize>,
        /// The ranges `(offset, length)` wanted; `None` is the whole value.
        ranges: Option<Vec<(u64, u64)>>,
        /// The priority (the application always asks for 3).
        priority: u8,
        /// The deadline in the node's local time.
        deadline: u64,
    },
    /// Reconcile a collection with a peer (reconcile).
    Reconcile {
        /// The collection.
        set_ref: Vec<u8>,
        /// The peer.
        peer: usize,
    },
}

/// What a layer reports to the application.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OnTopEvent {
    /// A broadcast message arrived; `origin` is the world index of its claimed publisher (`None`: not a known node).
    Message {
        /// The claimed publisher.
        origin: Option<usize>,
        /// The message bytes as delivered.
        msg: Vec<u8>,
    },
    /// A fetch made progress.
    FetchProgress {
        /// The fetch.
        fetch_id: u64,
    },
    /// A fetch finished.
    FetchComplete {
        /// The fetch.
        fetch_id: u64,
    },
    /// A fetch gave up.
    FetchFailed {
        /// The fetch.
        fetch_id: u64,
    },
    /// A range of a fetched value can be read.
    ValueReadable {
        /// The fetch.
        fetch_id: u64,
        /// Start of the range.
        offset: u64,
        /// Length of the range.
        length: u64,
    },
    /// A reconcile session ended with the two differences.
    ReconcileResult {
        /// The collection.
        set_ref: Vec<u8>,
        /// Items the peer has and this node lacks.
        missing_here: Vec<[u8; 40]>,
        /// Items this node has and the peer lacks.
        missing_there: Vec<[u8; 40]>,
    },
    /// A membership or connection event for the recorder.
    Member(MemberEvent),
}

/// An on-top layer.
pub trait OnTop {
    /// The protocols the layer needs registered with the endpoint.
    fn alpns(&self) -> Vec<&'static [u8]>;
    /// The node starts (every incarnation).
    fn boot(&mut self, now: u64, host: &mut dyn Host);
    /// A command from the application.
    fn command(&mut self, now: u64, host: &mut dyn Host, cmd: Command);
    /// An event of a session or stream that belongs to the layer.
    fn event(&mut self, now: u64, host: &mut dyn Host, ev: LayerEvent<'_>);
    /// The layer's deadline has come.
    fn timeout(&mut self, now: u64, host: &mut dyn Host);
    /// The layer's earliest deadline.
    fn poll_timeout(&self) -> Option<u64>;
    /// The next event for the application, if any.
    fn poll_event(&mut self) -> Option<OnTopEvent>;
    /// Whether the local store holds bytes `offset..offset + len` of `value`, verified (values only).
    fn holds(&self, _value: MsgId, _offset: u64, _len: u64) -> bool {
        false
    }
    /// How many bytes of `value` the local store holds contiguously from `offset` (values only).
    fn contiguous_from(&self, _value: MsgId, _offset: u64) -> u64 {
        0
    }
    /// The node stops: drop volatile state.
    fn stop(&mut self);
}
