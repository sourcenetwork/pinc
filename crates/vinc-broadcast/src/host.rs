//! The host interface: what the topic machine needs from the sessions around it, as plain traits with no dynamic
//! dispatch, and what it reports back.
//!
//! The machine opens no session and reads no clock. The host passes the monotonic time in every call, answers
//! [`Host::wall_ms`] for the hybrid logical clock, and carries the frames the machine hands to [`Host::send`] (the
//! hub stream of a peer, one stream per session) and [`Host::send_member`] (a member session, opened on demand).
//! Messages and results come back through [`Host::event`], borrowing the bytes they were parsed from, so delivering
//! a message copies nothing.

use vinc_membership::NodeId;

/// Which stream of a session a frame rides.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lane {
    /// The session's main stream (the hub stream).
    Main,
    /// A second stream at urgency 2, whose writes do not keep the session active: the copies of a publish a
    /// publisher fans to the hubs that are not its primary.
    Fan,
}

/// Sessions, the membership view and the clock.
pub trait Host {
    /// Hand one complete frame (length prefix included) to `peer` on `lane`. Returns whether a session took it. A
    /// `false` answer is not retried: the repair paths (retry, gap repair) cover a lost frame.
    fn send(&mut self, peer: &NodeId, lane: Lane, frame: &[u8]) -> bool;

    /// Hand one complete frame to `peer` over a member session, opening it if none is up. Returns whether the frame
    /// was handed to a session.
    fn send_member(&mut self, peer: &NodeId, frame: &[u8]) -> bool;

    /// Whether the session with `hub` is up and the hub was heard recently.
    fn hub_up(&self, hub: &NodeId) -> bool;

    /// Whether the membership view lists `member`.
    fn in_view(&self, member: &NodeId) -> bool;

    /// The wall clock in milliseconds.
    fn wall_ms(&self) -> u64;

    /// Report something to the application.
    fn event(&mut self, event: Event<'_>);
}

/// What the application hears, borrowing from the frame being handled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event<'a> {
    /// A message was delivered, once.
    Message {
        /// The topic.
        topic: &'a [u8],
        /// The origin's node id.
        origin: &'a NodeId,
        /// The message id.
        mid: [u8; 8],
        /// The body, already checked against the signature.
        body: &'a [u8],
    },
    /// A hub acknowledged a publish; it will not be retried.
    PublishAcked {
        /// The message id.
        mid: [u8; 8],
    },
    /// No hub acknowledged a publish in time; it will not be retried.
    PublishGaveUp {
        /// The message id.
        mid: [u8; 8],
    },
    /// A message that a gap repair asked for arrived.
    GapRepaired {
        /// The topic.
        topic: &'a [u8],
        /// The message id.
        mid: [u8; 8],
    },
    /// A message was sent straight to a subscriber because no hub is reachable.
    Fallback {
        /// The topic.
        topic: &'a [u8],
        /// The message id.
        mid: [u8; 8],
        /// The subscriber.
        to: &'a NodeId,
    },
    /// A hub restored this member's held subscription to a topic.
    Restored {
        /// The hub.
        hub: &'a NodeId,
        /// The topic.
        topic: &'a [u8],
    },
    /// The access-control layer must decide whether `origin` may publish to this node; answer with
    /// `Topics::acp_answer`.
    AcpCheck {
        /// The check to answer.
        id: u32,
        /// The origin.
        origin: &'a NodeId,
        /// The topic of the message that asked.
        topic: &'a [u8],
    },
}
