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
    /// The session's main stream for an answer or a push: with no stream up the frame is dropped and nothing is
    /// queued or dialed.
    Reply,
    /// A second stream at urgency 2, whose writes do not keep the session active: the copies of a publish a
    /// publisher fans to the hubs that are not its primary.
    Fan,
}

/// Sessions, the membership view and the clock.
pub trait Host {
    /// Hand one complete frame (length prefix included) to `peer` on `lane`. Returns whether a session took it. A
    /// `false` answer is not retried: the repair paths (retry, gap repair) cover a lost frame.
    fn send(&mut self, peer: &NodeId, lane: Lane, frame: &[u8]) -> bool;

    /// Whether a frame of `len` bytes was refused by `peer`'s stream only because the stream has no room for it now:
    /// the session is up and will take it later, and the host then calls [`Topics::peer_writable`](crate::Topics::peer_writable).
    /// A hub keeps its place in the topic's log for such a subscriber and loses nothing. A host that cannot tell
    /// answers `false`, and a refused frame is then left to the repair paths as before.
    fn backlogged(&self, _peer: &NodeId, _len: usize) -> bool {
        false
    }

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
        /// The peer whose session delivered it: a hub, or the origin itself when it sent the message straight.
        hop: &'a NodeId,
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
    /// On a hub: a publish of its own that was refused with [`Refused::Backlog`](crate::Refused::Backlog), because
    /// its topic's log was full of messages subscribers were still owed, may be taken now: a subscriber that was
    /// behind moved on, or one that stalled can be let go. The application publishes again.
    PublishRoom,
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
    /// A hub restored this member's held subscription to a topic: messages published while it was held may be
    /// missing (it was confirmed down, or its stream stalled or fell too far behind and the log evicted them).
    Restored {
        /// The hub.
        hub: &'a NodeId,
        /// The topic.
        topic: &'a [u8],
    },
    /// On a hub: `origin`'s record did not fit its adjacency table's bytes and was refused (see
    /// [`Topics::set_adjacent`](crate::Topics::set_adjacent)); `origin` is alone here until a record of it fits.
    ReachRefused {
        /// The node whose record was refused.
        origin: &'a NodeId,
    },
    /// On a hub: its adjacency table closed. Every node without a record is alone here until it opens again
    /// ([`Event::ReachOpened`]); [`Topics::reach_stats`](crate::Topics::reach_stats) says why it has not.
    ReachClosed,
    /// On a hub: its closed adjacency table opened again. Every node it refused has a record, was revoked or was
    /// released, so the nodes without a record are unscoped again.
    ReachOpened,
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
