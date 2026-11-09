//! What the node tells the application, in one ordered queue.
//!
//! The queue is bounded. When it is full the newest event is dropped and counted, and the count is delivered as
//! [`NodeEvent::Lost`] before the next event, so a gap never reads as silence.

use alloc::vec::Vec;
use vinc_connect::client::Notice;
use vinc_membership::NodeId;

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
    /// A hub restored this node's held subscription to a topic.
    Restored {
        /// The hub.
        hub: NodeId,
        /// The topic.
        topic: Vec<u8>,
    },
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
    /// This many events were dropped because the queue was full.
    Lost {
        /// How many.
        count: u32,
    },
}
