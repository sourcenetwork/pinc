//! What the node tells the application, in one ordered queue.
//!
//! The queue is bounded. While it is nearly full the node takes no more events from the endpoint, which keeps the ones
//! the application cannot recover. When it is full all the same, an event the application can recover by reading state
//! is dropped first and counted, and the count is delivered as [`NodeEvent::Lost`] before the next event, so a gap
//! never reads as silence.

use alloc::vec::Vec;
use vinc_connect::client::Notice;
use vinc_membership::NodeId;

/// Why a reconcile round did not finish.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReconcileFailure {
    /// The peer sent a message that breaks the protocol, or one over the limits.
    Protocol,
    /// The item index failed or is not sorted.
    Index,
    /// The difference is larger than the host's report limit.
    ReportTooLarge,
    /// The sets still disagree after the exact pass: the peer is faulty or a set changed during the round.
    Mismatch,
    /// The peer holds no set of that name.
    UnknownSet,
    /// Every attempt ended in a reset or a closed session.
    Exhausted,
    /// The node left the group or the peer was revoked.
    Cancelled,
}

/// An event for the application.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NodeEvent {
    /// An endpoint event of a session that is not a hub stream, unchanged.
    Endpoint(vinc_core::Event),
    /// A connectivity notice: a carrier opened or closed, the home relay or the class changed, a record was found.
    Connect(Notice),
    /// A change in the membership view or the local state.
    Member(vinc_membership::Event),
    /// A broadcast message, delivered once; its signature over this exact body verified.
    Message {
        /// The topic.
        topic: Vec<u8>,
        /// The origin's node id.
        origin: NodeId,
        /// The peer whose session delivered it: a hub, or the origin itself when it sent the message straight.
        hop: NodeId,
        /// The message id.
        mid: [u8; 8],
        /// The body.
        body: Vec<u8>,
    },
    /// A hub acknowledged a publish.
    PublishAcked {
        /// The message id.
        mid: [u8; 8],
    },
    /// No hub acknowledged a publish in time.
    PublishGaveUp {
        /// The message id.
        mid: [u8; 8],
    },
    /// On a hub: a publish of its own that was refused for want of room in the topic's log may be taken now.
    PublishRoom,
    /// A message that a gap repair asked for arrived.
    GapRepaired {
        /// The topic.
        topic: Vec<u8>,
        /// The message id.
        mid: [u8; 8],
    },
    /// A message was sent straight to a subscriber because no hub is reachable.
    Fallback {
        /// The topic.
        topic: Vec<u8>,
        /// The message id.
        mid: [u8; 8],
        /// The subscriber.
        to: NodeId,
    },
    /// A hub confirmed this node's subscription to a topic: it is in the hub's subscriber set.
    Subscribed {
        /// The hub.
        hub: NodeId,
        /// The topic.
        topic: Vec<u8>,
    },
    /// A hub restored this node's held subscription to a topic.
    Restored {
        /// The hub.
        hub: NodeId,
        /// The topic.
        topic: Vec<u8>,
    },
    /// On a hub: `origin`'s record did not fit its adjacency table's bytes and was refused; `origin` is alone
    /// here until a record of it fits (see [`Node::reach_stats`](crate::Node::reach_stats)).
    ReachRefused {
        /// The node whose record was refused.
        origin: NodeId,
    },
    /// On a hub: its adjacency table closed; every node without a record is alone here until it opens again.
    ReachClosed,
    /// On a hub: its closed adjacency table opened again.
    ReachOpened,
    /// The access-control layer must decide whether `origin` may publish here; answer with
    /// [`Node::broadcast_acp_answer`](crate::Node::broadcast_acp_answer).
    BroadcastAcpCheck {
        /// The check to answer.
        id: u32,
        /// The origin.
        origin: NodeId,
        /// The topic of the message that asked.
        topic: Vec<u8>,
    },
    /// Verified bytes `[off, off + len)` of a fetched value are in the store and may be read.
    ValueReadable {
        /// The fetch.
        fetch: u32,
        /// The first byte.
        off: u64,
        /// The number of bytes.
        len: u64,
    },
    /// Every byte a fetch wanted is verified and in the store.
    ValueComplete {
        /// The fetch.
        fetch: u32,
    },
    /// A fetch failed.
    ValueFailed {
        /// The fetch.
        fetch: u32,
        /// Why.
        reason: vinc_values::trace::FailReason,
    },
    /// A reconcile round finished: the exact difference between the two sets.
    ReconcileDone {
        /// The round.
        round: u32,
        /// The peer.
        peer: NodeId,
        /// The items the peer has and this node lacks.
        missing_here: Vec<Vec<u8>>,
        /// The items this node has and the peer lacks.
        missing_there: Vec<Vec<u8>>,
    },
    /// A reconcile round failed.
    ReconcileFailed {
        /// The round.
        round: u32,
        /// The peer.
        peer: NodeId,
        /// Why.
        reason: ReconcileFailure,
    },
    /// A bundle addressed to this node arrived and opened.
    DtnReceived {
        /// The bundle id.
        bundle: [u8; 32],
        /// The node that created it.
        source: NodeId,
        /// The payload.
        payload: Vec<u8>,
    },
    /// This node took custody of a bundle from `from` and acknowledged it.
    DtnCustody {
        /// The bundle id.
        bundle: [u8; 32],
        /// The previous custodian.
        from: NodeId,
    },
    /// A peer took custody of a bundle this node held: this node is relieved.
    DtnHandedOff {
        /// The bundle id.
        bundle: [u8; 32],
        /// The new custodian.
        to: NodeId,
    },
    /// The destination of a bundle acknowledged it.
    DtnDelivered {
        /// The bundle id.
        bundle: [u8; 32],
    },
    /// A bundle expired at this node before it was delivered.
    DtnExpired {
        /// The bundle id.
        bundle: [u8; 32],
    },
    /// This many events were dropped because the queue was full.
    Lost {
        /// How many.
        count: u32,
    },
}
