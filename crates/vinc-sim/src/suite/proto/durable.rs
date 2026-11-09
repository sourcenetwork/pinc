//! The application's durable state: what the database of a node keeps across restarts.
//!
//! One [`Durable`] per node lives in an `Rc<RefCell<..>>` owned by the runner, outlives every [`super::Stack`] of the
//! node and is handed to each new one. It holds the PUSHLOG logs (sequence numbers and unacknowledged pushes), the
//! replicator high-water marks, the open fetches and reconciles and the counters that must not restart. The push
//! bodies are not stored: a message is regenerated from its id when it is (re)sent.
//!
//! Invariants: a push enters `pl_out` before any byte of it is written; an entry leaves `unacked` only by a
//! cumulative acknowledgement; `pl_in` only grows.

use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;

use crate::suite::crypto::MsgId;

/// Message id to the id of the intent that produced it, shared by all nodes of a run: a receiver finds the intent
/// of a message created by someone else here.
pub type MsgIntents = Rc<RefCell<BTreeMap<u64, u32>>>;

/// One push not yet acknowledged by its replicator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Unacked {
    /// The sequence number.
    pub seq: u64,
    /// The intent.
    pub iid: u32,
    /// The message.
    pub msg: MsgId,
    /// The message length in bytes.
    pub len: u64,
}

/// The log towards one replicator.
#[derive(Debug, Default, Clone)]
pub struct PushOut {
    /// The last sequence number issued.
    pub seq: u64,
    /// The pushes still to be acknowledged, oldest first.
    pub unacked: VecDeque<Unacked>,
}

/// The durable state of one node.
#[derive(Debug, Default, Clone)]
pub struct Durable {
    /// How many times the node has started; keys the view-epoch check of the recorder.
    pub incarnations: u64,
    /// Replicator to its push log.
    pub pl_out: BTreeMap<usize, PushOut>,
    /// Origin to the next sequence number expected from it.
    pub pl_in: BTreeMap<usize, u64>,
    /// Intents of fetches not yet complete, re-issued at every start.
    pub open_fetches: Vec<u32>,
    /// Value to the fetch intents of this node for it.
    pub fetch_intents: BTreeMap<u64, Vec<u32>>,
    /// Collection to the intent of the open reconcile on it.
    pub open_reconcile: BTreeMap<Vec<u8>, u32>,
    /// The next fetch id (unique per node).
    pub next_fetch_id: u64,
    /// Message to intent, shared by every node of the run (see [`Durable::sharing`]).
    pub msg_intents: MsgIntents,
}

impl Durable {
    /// A durable state that shares `msg_intents` with the other nodes of the run. The runner builds one map per run
    /// and passes a clone to every node; [`Durable::default`] has a private map and suits a single node.
    pub fn sharing(msg_intents: MsgIntents) -> Self {
        Self {
            msg_intents,
            ..Self::default()
        }
    }
}
