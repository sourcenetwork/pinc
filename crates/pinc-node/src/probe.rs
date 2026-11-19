//! A probe of the node's dial backoff table, for the trace check (cargo feature `trace`): a real [`Io`] over an
//! endpoint that does nothing, driven through the calls that set and read the table of failed dials.
//!
//! The probe makes no decision of its own. `backoff` and `deny_back` are the node's own calls; `gate` hands a frame
//! for a peer with no session and no frame queued to the node's own stream hand-off and reports whether it was
//! taken, which with nothing queued is exactly the answer of the backoff window check (`io.rs`, `enqueue`). The same
//! module holds a probe of the application event queue.
#![allow(clippy::missing_const_for_fn, reason = "a trace probe")]

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::net::SocketAddr;
use core::ops::Range;

use pinc_broadcast::Lane;
use pinc_connect::client::Port;
use pinc_core::{
    Command, CommandError, Event, Events, IfaceEvent, IfaceId, NodeStats, Reply, SendState, SessionId, SessionStats,
    TraceRecord, Transmit, Value,
};
use pinc_crypto::IdentityAlg;
use pinc_membership::NodeId;
use pinc_transport::stream::{NoSource, StreamId};

use crate::config::{BACKOFF_CAP, BACKOFF_FIRST, BACKOFF_HUB_CAP, DENY_CAP, DENY_FIRST, Nanos, TABLE_MAX};
use crate::ep::Ep;
use crate::event::NodeEvent;
use crate::io::Io;
use crate::layer::Layer;

/// An endpoint that does nothing.
#[derive(Default)]
struct Stub;

impl Port for Stub {
    type Src = NoSource;
    fn command(&mut self, _now: u64, _cmd: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        Ok(Reply {
            value: Value::None,
            events: Events::default(),
        })
    }
    fn stats(&self, _session: SessionId) -> Option<SessionStats> {
        None
    }
    fn peer(&self, _node: &pinc_crypto::NodeId) -> Option<pinc_core::PeerInfo> {
        None
    }
    fn by_conn_id(&self, _cid: &pinc_security::ConnId) -> Option<SessionStats> {
        None
    }
    fn node(&self) -> Option<NodeStats> {
        None
    }
    fn reach_body(&self, _session: SessionId, _out: &mut [u8; pinc_core::REACH_BODY_MAX]) -> usize {
        0
    }
}

impl Ep for Stub {
    fn handle_datagram(&mut self, _now: u64, _local: SocketAddr, _remote: SocketAddr, _buf: &mut [u8]) {}
    fn poll_transmit(&mut self, _now: u64, _out: &mut [u8]) -> Option<Transmit> {
        None
    }
    fn poll_event(&mut self) -> Option<Event> {
        None
    }
    fn poll_timeout(&self) -> Option<u64> {
        None
    }
    fn handle_timeout(&mut self, _now: u64) {}
    fn register_alpn(&mut self, _alpn: &[u8]) -> bool {
        true
    }
    fn read_chunk(&self, _session: SessionId, _stream: StreamId) -> Option<&[u8]> {
        None
    }
    fn read_at(&self, _session: SessionId, _stream: StreamId, _offset: u64) -> Option<&[u8]> {
        None
    }
    fn stored_after(&self, _session: SessionId, _stream: StreamId, _from: u64) -> Option<Range<u64>> {
        None
    }
    fn send_state(&self, _session: SessionId, _stream: StreamId) -> Option<SendState> {
        None
    }
    fn in_flight(&self, _session: SessionId) -> Option<u64> {
        None
    }
    fn read_extension(&mut self, _out: &mut [u8]) -> Result<Option<(SessionId, u64, usize)>, CommandError> {
        Ok(None)
    }
    fn session_at(&self, _n: usize) -> Option<SessionStats> {
        None
    }
    fn session_from(&self, _remote: &SocketAddr, _keep: &dyn Fn(SessionId) -> bool) -> Option<SessionId> {
        None
    }
    fn poll_trace(&mut self) -> Option<TraceRecord> {
        None
    }
    fn add_iface(&mut self, _local: SocketAddr) -> Option<IfaceId> {
        None
    }
    fn iface_event(&mut self, _now: u64, _id: IfaceId, _ev: IfaceEvent) {}
}

/// The node's table of failed dials, of its own, with its entries readable after every call.
pub struct BackoffProbe {
    io: Io<Stub, ()>,
}

impl BackoffProbe {
    /// The most entries of the table.
    pub const TABLE_MAX: usize = TABLE_MAX;
    /// The first wait after a failed dial.
    pub const FIRST: Nanos = BACKOFF_FIRST;
    /// The longest wait after failed dials of a hub.
    pub const HUB_CAP: Nanos = BACKOFF_HUB_CAP;
    /// The longest wait after failed dials of any other node.
    pub const CAP: Nanos = BACKOFF_CAP;
    /// The first wait after a refusal.
    pub const DENY_FIRST: Nanos = DENY_FIRST;
    /// The longest wait after refusals.
    pub const DENY_CAP: Nanos = DENY_CAP;

    /// An empty table of a node whose hubs are `hubs`.
    #[must_use]
    pub fn new(hubs: &[NodeId]) -> Self {
        Self {
            io: Io::new(
                Stub,
                (),
                [0xee; 32],
                IdentityAlg::Ed25519,
                false,
                b"t",
                1,
                0,
                0,
                hubs.to_vec(),
                BTreeMap::new(),
                4096,
                false,
            ),
        }
    }

    /// A dial of `peer` failed at `now`.
    pub fn backoff(&mut self, now: Nanos, peer: &NodeId) {
        self.io.now = now;
        self.io.backoff(peer);
    }

    /// The access check of `peer` refused our dial at `now`.
    pub fn deny_back(&mut self, now: Nanos, peer: &NodeId) {
        self.io.now = now;
        self.io.deny_back(peer);
    }

    /// Whether a frame for `peer` is taken at `now` when it has no session and nothing queued: false exactly inside
    /// its backoff window. The queue is emptied again.
    pub fn gate(&mut self, now: Nanos, peer: &NodeId) -> bool {
        self.io.now = now;
        let taken = self.io.send_stream(peer, Lane::Main, &[0]);
        self.io.drop_queue(peer);
        self.io.dials.clear();
        taken
    }

    /// The entry of `peer`: when its next dial may start, and the wait that was used.
    #[must_use]
    pub fn entry(&self, peer: &NodeId) -> Option<(Nanos, Nanos)> {
        self.io.failed.get(peer).copied()
    }

    /// Every entry, by peer.
    #[must_use]
    pub fn entries(&self) -> Vec<(NodeId, Nanos, Nanos)> {
        self.io.failed.iter().map(|(p, (u, b))| (*p, *u, *b)).collect()
    }
}

/// The node's table of delay-tolerant dial backoffs and its redial time, of its own, readable after every call.
pub struct DtnBackoffProbe {
    io: Io<Stub, ()>,
    redial_at: Option<Nanos>,
}

impl Default for DtnBackoffProbe {
    fn default() -> Self {
        Self::new()
    }
}

impl DtnBackoffProbe {
    /// The most entries the table holds.
    pub const TABLE_MAX: usize = TABLE_MAX;
    /// The first wait after a failed dial.
    pub const FIRST: Nanos = BACKOFF_FIRST;
    /// The longest wait.
    pub const CAP: Nanos = BACKOFF_CAP;

    /// An empty table and no redial time.
    #[must_use]
    pub fn new() -> Self {
        Self {
            io: Io::new(
                Stub,
                (),
                [0xee; 32],
                IdentityAlg::Ed25519,
                false,
                b"t",
                1,
                0,
                0,
                Vec::new(),
                BTreeMap::new(),
                4096,
                false,
            ),
            redial_at: None,
        }
    }

    /// A delay-tolerant dial of `peer` failed at `now`, as `layer_failed` records it; returns the end of the wait.
    pub fn failed(&mut self, now: Nanos, peer: &NodeId) -> Nanos {
        let at = self.io.dtn_failed(now, peer);
        self.redial_at = crate::dtn::sooner(self.redial_at, at);
        at
    }

    /// Whether `dial_layer` waits for `peer` at `now`.
    #[must_use]
    pub fn waits(&self, now: Nanos, peer: &NodeId) -> bool {
        self.io.dtn_waits(now, peer)
    }

    /// A membership event about `peer` (or a session to it that lived): its entry goes.
    pub fn forget(&mut self, peer: &NodeId) {
        self.io.dtn_forget(peer);
    }

    /// The timer at `now`, as `dtn_timeout` checks the redial time: true when it fired (and is cleared).
    pub fn fire(&mut self, now: Nanos) -> bool {
        let due = crate::dtn::redial_due(self.redial_at, now);
        if due {
            self.redial_at = None;
        }
        due
    }

    /// The redial time.
    #[must_use]
    pub fn redial_at(&self) -> Option<Nanos> {
        self.redial_at
    }

    /// The entry of `peer`: when the wait ends, and the wait.
    #[must_use]
    pub fn entry(&self, peer: &NodeId) -> Option<(Nanos, Nanos)> {
        self.io.lfailed.get(&(Layer::Dtn, *peer)).copied()
    }

    /// Every entry, in the table's order.
    #[must_use]
    pub fn entries(&self) -> Vec<(NodeId, Nanos, Nanos)> {
        self.io.lfailed.iter().map(|((_, p), (u, b))| (*p, *u, *b)).collect()
    }

    /// The entries held.
    #[must_use]
    pub fn len(&self) -> usize {
        self.io.lfailed.len()
    }

    /// Whether no entry is held.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.io.lfailed.is_empty()
    }
}

/// An event read from the queue, as the probe reports it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Popped {
    /// The count of lost events.
    Lost(u32),
    /// An event pushed by the probe: its tag and whether the application can recover it.
    Event {
        /// The tag the event was pushed with.
        tag: u64,
        /// Whether the application can recover it by reading state.
        lossy: bool,
    },
    /// Nothing queued.
    Empty,
}

/// The node's queue of application events, of its own, with its length and lost count readable after every call.
#[derive(Debug, Default)]
pub struct EventQueueProbe {
    q: crate::io::EventQueue,
}

impl EventQueueProbe {
    /// The capacity of the queue.
    pub const CAP: usize = crate::config::EVENT_CAP;
    /// The length at which the node stops taking events.
    pub const HIGH: usize = crate::config::EVENT_HIGH;
    /// The length at which it resumes.
    pub const LOW: usize = crate::config::EVENT_LOW;

    /// An empty queue.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Push the endpoint event tagged `tag`: `StreamReadable` (recoverable) when `lossy`, else `Closed` (not).
    pub fn push(&mut self, tag: u64, lossy: bool) {
        self.q.push(NodeEvent::Endpoint(event(tag, lossy)));
    }

    /// Push the events in order through `Extend`, as the node loop does.
    pub fn extend(&mut self, events: &[(u64, bool)]) {
        self.q.extend(events.iter().map(|&(t, l)| event(t, l)));
    }

    /// Read one event.
    pub fn pop(&mut self) -> Popped {
        match self.q.pop() {
            None => Popped::Empty,
            Some(NodeEvent::Lost { count }) => Popped::Lost(count),
            Some(NodeEvent::Endpoint(e)) => Popped::Event {
                tag: e.session().map_or(u64::MAX, |s| s.0),
                lossy: e.lossy(),
            },
            Some(_) => Popped::Event {
                tag: u64::MAX,
                lossy: false,
            },
        }
    }

    /// Whether the node may take another event from the endpoint.
    pub fn can_take(&mut self) -> bool {
        self.q.can_take()
    }

    /// Whether the node stopped taking events and the queue has since fallen to the point it resumes.
    #[must_use]
    pub fn resumable(&self) -> bool {
        self.q.resumable()
    }

    /// Whether nothing is queued and no loss is counted.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.q.is_empty()
    }

    /// The events queued, not counting the lost count.
    #[must_use]
    pub fn len(&self) -> usize {
        self.q.len()
    }

    /// The count of lost events not yet delivered.
    #[must_use]
    pub fn lost(&self) -> u32 {
        self.q.lost()
    }
}

fn event(tag: u64, lossy: bool) -> Event {
    if lossy {
        Event::StreamReadable {
            session: SessionId(tag),
            stream: 0,
        }
    } else {
        Event::Closed {
            session: SessionId(tag),
            reason: pinc_core::EndReason::Denied,
        }
    }
}
