//! How a node is set up, and the numbers of its host-side duties.

use core::net::SocketAddr;

use vinc_broadcast::{IdKey, Limits};
use vinc_connect::client::Config as ConnectConfig;
use vinc_membership::session::StoreError;

/// Nanoseconds.
pub type Nanos = u64;

const S: Nanos = 1_000_000_000;
const MS: Nanos = 1_000_000;

/// The first wait after a refused dial.
pub const BACKOFF_FIRST: Nanos = 2 * S;
/// The longest wait after failed dials of a hub.
pub const BACKOFF_HUB_CAP: Nanos = 16 * S;
/// The longest wait after failed dials of any other node.
pub const BACKOFF_CAP: Nanos = 60 * S;
/// A session that lived this long resets the dial backoff of its peer.
pub const SESSION_LIVED: Nanos = 5 * S;
/// The first wait after the peer's access check refused the dial (a denied or revoked node).
pub const DENY_FIRST: Nanos = 60 * S;
/// The longest wait after refused dials.
pub const DENY_CAP: Nanos = 900 * S;
/// A hub adopts an older live session of a member when the newer one closes, if that session was heard within this.
pub const SURVIVOR: Nanos = 30 * S;
/// The adopted session is offered the log of this long.
pub const SURVIVOR_HAVE: Nanos = 90 * S;
/// A hub session without our write stream gets a fresh one after this long.
pub const STREAM_REPAIR: Nanos = 10 * S;
/// A hub redial after a close waits this long.
pub(crate) const REDIAL_SOON: Nanos = 20 * MS;
/// The cadence of the host-side duties of a member.
pub(crate) const DUTY_MEMBER: Nanos = 500 * MS;
/// The cadence of the host-side duties of a hub.
pub(crate) const DUTY_HUB: Nanos = S;
/// One tick of the node's timer: after a timer call that did not move a deadline, the node asks for the next call
/// this long after it.
pub const TIMER_TICK: Nanos = MS;
/// Frames kept for a peer while its session is being dialed.
pub const QUEUE_FRAMES: usize = 256;
/// The most entries of the dial backoff table and of the peer tables.
pub(crate) const TABLE_MAX: usize = 4096;
/// The most session table entries kept free for hub links: a member's session is refused once this many or fewer are
/// free, so a hub the members filled the table of can still link to the other hubs.
pub(crate) const HUB_RESERVE_MAX: usize = 64;
/// The most events queued for the application between two polls.
pub(crate) const EVENT_CAP: usize = 8192;
/// The node stops taking events from the endpoint at this many queued events, so the layers' own events from one
/// round still fit; it resumes at [`EVENT_LOW`].
pub(crate) const EVENT_HIGH: usize = EVENT_CAP - 1024;
/// The queued events at or below which the node takes events from the endpoint again.
pub(crate) const EVENT_LOW: usize = EVENT_CAP / 2;
/// A carrier that closed is remembered this long.
pub(crate) const GONE_TTL: Nanos = 600 * S;
/// The close code of a refusal (a denied or revoked node).
pub(crate) const DENIED: u64 = vinc_membership::session::DENIED_CODE;

/// The default protocol id of the hub stream. Its second name: the subscriber list moved to a new layout, so a node
/// and a hub that speak the first name do not connect to this build.
pub const HUB_ALPN: &[u8] = b"vinc/hub/2";
/// The protocol id of the values layer.
pub const VALUES_ALPN: &[u8] = b"vinc/values";
/// The protocol id of the reconcile layer.
pub const SETS_ALPN: &[u8] = b"vinc/reconcile";
/// The protocol id of the delay-tolerant layer.
pub const DTN_ALPN: &[u8] = b"vinc/dtn";

/// The urgency of the write stream of a hub session: membership and broadcast frames go before everything else on it.
pub const HUB_URGENCY: u8 = 1;
/// The urgency of a set reconciliation stream.
pub const SETS_URGENCY: u8 = 2;

/// Where the incarnation epoch survives a restart. The host backs it with the key store's `seal` and `unseal` (the
/// epoch is eight bytes), or with nothing.
pub trait Store {
    /// Whether [`Store::load`] and [`Store::save`] persist across restarts.
    fn persistent(&self) -> bool;

    /// The remembered epoch, or `None` on a first start.
    ///
    /// # Errors
    /// [`StoreError`] if the sealed state is unreadable; the node refuses to start with a guessed epoch.
    fn load(&mut self) -> Result<Option<u64>, StoreError>;

    /// Persist `epoch` before it is used.
    ///
    /// # Errors
    /// [`StoreError`] if it could not be persisted.
    fn save(&mut self, epoch: u64) -> Result<(), StoreError>;
}

/// No persistence: the incarnation is a hybrid logical clock.
impl Store for () {
    fn persistent(&self) -> bool {
        false
    }

    fn load(&mut self) -> Result<Option<u64>, StoreError> {
        Ok(None)
    }

    fn save(&mut self, _epoch: u64) -> Result<(), StoreError> {
        Ok(())
    }
}

/// How a node is set up. The relays of the connectivity configuration are the hubs of membership and broadcast; a
/// hub lists the other hubs.
#[derive(Debug, Clone, Copy)]
pub struct Config<const R: usize> {
    /// The connectivity client's configuration (identity, relays, start time).
    pub connect: ConnectConfig<R>,
    /// This node is a hub: a bootstrap node that also relays.
    pub is_hub: bool,
    /// The stack version announced in records.
    pub version: u16,
    /// The protocol id of the hub stream.
    pub alpn: &'static [u8],
    /// The size limits of broadcast.
    pub limits: Limits,
    /// The key that places message ids in the broadcast layer's tables: the endpoint's own map keys. Never the
    /// connectivity seed, which is sent in the clear.
    pub map_keys: IdKey,
    /// The wall clock in milliseconds when the node starts.
    pub wall_ms: u64,
    /// The address datagrams from relay paths are delivered to the endpoint as.
    pub local: SocketAddr,
    /// Record trace records for [`Node::poll_trace`](crate::Node::poll_trace).
    pub trace: bool,
}
