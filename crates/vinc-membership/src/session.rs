//! The host interface: what the membership machines need from the sessions, the carriers, the broadcast layer and
//! the local node, as plain traits with no dynamic dispatch.
//!
//! The machines never open a session, read a clock or touch a socket. The host tells them what happened (a session
//! came up, a frame arrived, a carrier dropped) and answers their questions through [`Host`]. Every method is a
//! plain call, so a model of the host is as small as a model of the machine.
//!
//! Invariants: no method here may block; [`Session::send`] only reports whether the frame was handed to a session,
//! and a `false` answer is never retried by the machine (a session coming up resends what matters).

use crate::codec::NodeId;

/// Monotonic time in nanoseconds since an arbitrary origin chosen by the host.
pub type Nanos = u64;

/// What the transport knows about one hub session.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Evidence {
    /// When the last authenticated packet of any kind arrived on the session.
    pub last_rx: Nanos,
    /// The smoothed round trip time, 0 when unsampled.
    pub srtt: Nanos,
    /// The number of consecutive probe timeouts (0 means none outstanding).
    pub pto: u32,
    /// Bytes in flight; large values mean bulk traffic is queued behind the sample.
    pub inflight: u32,
    /// A validated direct UDP path to the peer exists.
    pub direct: bool,
}

/// The state of a member's relay carrier to this hub's relay.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Carrier {
    /// Never seen, or not a relay client.
    #[default]
    Unknown,
    /// Open.
    Open,
    /// Closed at `since`; `sleep` is when the member announced a suspension, if it did.
    Gone {
        /// When the carrier closed.
        since: Nanos,
        /// When the member announced a suspension.
        sleep: Option<Nanos>,
    },
}

/// Which way a frame travels to a peer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Route {
    /// The session as the transport routes it.
    Session,
    /// The session as the transport routes it, for an answer or a push: with no session up the frame is dropped and
    /// nothing is queued or dialed.
    Reply,
    /// The validated direct UDP path.
    Direct,
    /// Through the relay of the named hub.
    Via(NodeId),
}

/// Why the machine asks the host to close a session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CloseReason {
    /// A HELLO went unanswered.
    NoAck,
    /// The hub has been silent past the staleness bound.
    Stale,
    /// We are leaving the group; close with [`LEAVE_CODE`].
    Leave,
    /// The peer was revoked; close every session with it.
    Revoked,
}

/// The close code of a graceful leave.
pub const LEAVE_CODE: u64 = 0x4C;
/// The close code of a refusal (denied or revoked).
pub const DENIED_CODE: u64 = 3;

/// Sessions, carriers and transport evidence.
pub trait Session {
    /// Hand one complete frame (length prefix included) to the hub stream of `peer` along `route`. Returns whether a
    /// session took it.
    fn send(&mut self, peer: &NodeId, route: Route, frame: &[u8]) -> bool;

    /// The transport's view of the session with `peer`, if one is up.
    fn evidence(&self, peer: &NodeId) -> Option<Evidence>;

    /// The state of `member`'s relay carrier to this node's relay.
    fn carrier(&self, member: &NodeId) -> Carrier;

    /// How long silence on the path to `peer` lasts before the transport gives the path up (its probe-timeout bound
    /// at the last known round trip). A peer heard again after a longer silence means a partition healed. The
    /// default is the fixed [`HEAL_SILENCE`](crate::consts::HEAL_SILENCE).
    fn give_up(&self, _peer: &NodeId) -> Nanos {
        crate::consts::HEAL_SILENCE
    }

    /// Close the session with `peer`. The host reports it back with `session_down`.
    fn close(&mut self, peer: &NodeId, reason: CloseReason);
}

/// What the broadcast layer supplies and receives. Membership never looks inside any of it.
pub trait Broadcast {
    /// Write the body of the FLOOR frame for a member that has just attached, return its length (0 to send none).
    fn floor(&mut self, member: &NodeId, out: &mut [u8]) -> usize;

    /// A frame of a type membership does not own.
    fn frame(&mut self, from: &NodeId, ty: u8, topic: &[u8], rest: &[u8]);

    /// `member` was confirmed down: keep its subscriptions for the lease, send it nothing.
    fn hold(&mut self, member: &NodeId);

    /// `member` returned within the lease: its held subscriptions are live again.
    fn restore(&mut self, member: &NodeId);

    /// `member` is gone for good (lease over, left, revoked, session closed): forget its subscriptions.
    fn release(&mut self, member: &NodeId);

    /// The member side asks the broadcast layer to subscribe again at `hub` (a snapshot, a new session to the
    /// primary, or a record about ourselves arrived).
    fn resubscribe(&mut self, hub: &NodeId);

    /// The primary hub changed from `old` to `new`.
    fn primary_changed(&mut self, old: Option<&NodeId>, new: &NodeId);
}

/// The local node: its version, its address tag and where the incarnation survives a restart.
pub trait Local {
    /// The stack version announced in records.
    fn version(&self) -> u16;

    /// Whether the reflexive address is known. Right after a move, the previous address tag is kept until it is.
    fn reflexive_known(&self) -> bool;

    /// The hash of the identity ticket with the move counter folded in, 8 bytes. Called at most once per tick; a
    /// host caches the hash of an unchanged ticket.
    fn address_hash(&self, moves: u8) -> [u8; 8];

    /// Whether [`Local::unseal_counter`] and [`Local::seal_counter`] persist across restarts. When true the
    /// incarnation is a counter; otherwise it is a hybrid logical clock.
    fn persistent(&self) -> bool {
        false
    }

    /// The remembered incarnation epoch, unsealed from the key store, or `None` on a first start.
    ///
    /// # Errors
    /// [`StoreError`] if the sealed state is unreadable; the node must not start with a guessed epoch.
    fn unseal_counter(&mut self) -> Result<Option<u64>, StoreError> {
        Ok(None)
    }

    /// Seal and persist the incarnation epoch before it is used.
    ///
    /// # Errors
    /// [`StoreError`] if it could not be persisted.
    fn seal_counter(&mut self, _epoch: u64) -> Result<(), StoreError> {
        Ok(())
    }
}

/// The key store could not read or persist the incarnation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StoreError;

impl core::fmt::Display for StoreError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("the incarnation could not be read or persisted")
    }
}

impl core::error::Error for StoreError {}

/// Everything the machines ask of their host, in one object.
pub trait Host: Session + Broadcast + Local {}

impl<T: Session + Broadcast + Local> Host for T {}
