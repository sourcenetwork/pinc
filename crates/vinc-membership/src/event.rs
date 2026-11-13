//! What the machines report: events for the application and trace records for the proofs.
//!
//! Both queues are bounded. When a queue is full the newest record is dropped and counted, and the count is
//! delivered as [`Event::Lost`] or [`Trace::Lost`] before the next record, so a consumer never mistakes a gap for
//! silence.

use crate::codec::{NodeId, Path};

/// A change in the membership view or the local state, for the application.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// A member appeared, or came back with a newer incarnation.
    MemberJoined {
        /// The member.
        member: NodeId,
    },
    /// A member was confirmed down.
    MemberConfirmedDown {
        /// The member.
        member: NodeId,
    },
    /// A member left gracefully.
    MemberLeft {
        /// The member.
        member: NodeId,
    },
    /// A member was revoked and every session with it closed.
    MemberRevoked {
        /// The member.
        member: NodeId,
    },
    /// A member's address hash changed.
    AddressChanged {
        /// The member.
        member: NodeId,
    },
    /// A member's stack version changed.
    StackChanged {
        /// The member.
        member: NodeId,
        /// The new version.
        version: u16,
    },
    /// The view changed; the epoch only increases.
    ViewChanged {
        /// The view epoch.
        epoch: u64,
        /// How many members the view lists.
        members: u32,
    },
    /// This many events were dropped because the queue was full.
    Lost {
        /// How many.
        count: u32,
    },
}

/// Why a member left the view.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Removal {
    /// A hub said the member is down (a delta or a DOWN with proof).
    Reported,
    /// A hub said the member left.
    Left,
    /// Every hub that listed the member stopped listing it for a full lease.
    LeaseExpired,
    /// The member was revoked.
    Revoked,
}

/// Why a hub refused a DOWN.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refusal {
    /// The sender is not a hub, or the member is a hub.
    NotApplicable,
    /// This hub holds no entry for the member, or a different incarnation.
    Unknown,
    /// This hub's own lease for the member is fresh.
    LeaseFresh,
    /// The member's carrier to this hub is open.
    CarrierOpen,
    /// The proof lists no independent path.
    NotIndependent,
    /// The proof claims less silence than its own probes span.
    BadProof,
}

/// What caused a quiet window to open.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuietCause {
    /// A timer ran late: the process was suspended.
    LateTimer,
    /// A hub or session returned after silence longer than the transport's give-up bound: a partition healed.
    Heal,
}

/// A trace record: every input the machine acts on and every decision it takes, in order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trace {
    /// The machine started with this incarnation word.
    Started {
        /// The incarnation word.
        inc: u64,
    },
    /// The incarnation word changed.
    Incarnation {
        /// The new word.
        inc: u64,
    },
    /// A frame of this type arrived from a peer.
    FrameIn {
        /// The sender.
        peer: NodeId,
        /// The frame type.
        ty: u8,
    },
    /// A frame of this type went to a peer.
    FrameOut {
        /// The receiver.
        peer: NodeId,
        /// The frame type.
        ty: u8,
    },
    /// A frame failed to parse.
    BadFrame {
        /// The sender.
        peer: NodeId,
    },
    /// A hub attached a member.
    Attached {
        /// The member.
        member: NodeId,
    },
    /// A hub renewed a lease from transport evidence.
    Pulse {
        /// The member.
        member: NodeId,
    },
    /// A hub's lease for a member expired.
    LeaseExpired {
        /// The member.
        member: NodeId,
    },
    /// A member's carrier closed.
    CarrierGone {
        /// The member.
        member: NodeId,
    },
    /// A hub probed a silent member.
    ProbeSent {
        /// The member.
        member: NodeId,
        /// The path.
        path: Path,
    },
    /// A hub could not probe on an independent path and waits for the lease.
    NoIndependentPath {
        /// The member.
        member: NodeId,
    },
    /// A hub confirmed a member down.
    Confirmed {
        /// The member.
        member: NodeId,
    },
    /// A hub saw a member leave.
    LeaveSeen {
        /// The member.
        member: NodeId,
    },
    /// A hub sent a DOWN.
    DownSent {
        /// The member.
        member: NodeId,
    },
    /// A hub accepted another hub's DOWN.
    DownAccepted {
        /// The member.
        member: NodeId,
    },
    /// A hub refused another hub's DOWN.
    DownRefused {
        /// The member.
        member: NodeId,
        /// Why.
        why: Refusal,
    },
    /// A member's carrier returned.
    CarrierReturned {
        /// The member.
        member: NodeId,
        /// Whether a held entry was restored.
        restored: bool,
    },
    /// A hub told the node about itself.
    SelfDelta {
        /// The hub.
        hub: NodeId,
    },
    /// A snapshot frame was applied to a hub copy.
    SnapApplied {
        /// The hub.
        hub: NodeId,
        /// How many entries.
        entries: u32,
        /// Whether more frames of the snapshot follow.
        more: bool,
    },
    /// A complete snapshot omitted a member, which starts its lease clock.
    Absent {
        /// The member.
        member: NodeId,
    },
    /// A member left the view.
    Removed {
        /// The member.
        member: NodeId,
        /// Why.
        why: Removal,
    },
    /// A removal was deferred by a quiet window.
    Deferred {
        /// The member.
        member: NodeId,
    },
    /// A quiet window opened.
    Quiet {
        /// Why.
        cause: QuietCause,
    },
    /// A hub went stale and its copy was dropped.
    HubStale {
        /// The hub.
        hub: NodeId,
    },
    /// The primary hub changed.
    Primary {
        /// The new primary.
        hub: NodeId,
    },
    /// A periodic HELLO was skipped on transport evidence.
    HelloSuppressed {
        /// The hub.
        hub: NodeId,
    },
    /// The incarnation could not be sealed; the record keeps its word.
    SealFailed,
    /// This many trace records were dropped because the queue was full.
    Lost {
        /// How many.
        count: u32,
    },
}
