//! A probe of the node's dial backoff table, for the trace check (cargo feature `trace`): a real [`Io`] over an
//! endpoint that does nothing, driven through the calls that set and read the table of failed dials.
//!
//! The probe makes no decision of its own. `backoff` and `deny_back` are the node's own calls; `gate` hands a frame
//! for a peer with no session and no frame queued to the node's own stream hand-off and reports whether it was
//! taken, which with nothing queued is exactly the answer of the backoff window check (`io.rs`, `enqueue`).
#![allow(clippy::missing_const_for_fn, reason = "a trace probe")]

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::net::SocketAddr;
use core::ops::Range;

use vinc_broadcast::Lane;
use vinc_connect::client::Port;
use vinc_core::{
    Command, CommandError, Event, Events, IfaceEvent, IfaceId, NodeStats, Reply, SendState, SessionId, SessionStats,
    TraceRecord, Transmit, Value,
};
use vinc_crypto::IdentityAlg;
use vinc_membership::NodeId;
use vinc_transport::stream::{NoSource, StreamId};

use crate::config::{BACKOFF_CAP, BACKOFF_FIRST, BACKOFF_HUB_CAP, DENY_CAP, DENY_FIRST, Nanos, TABLE_MAX};
use crate::ep::Ep;
use crate::io::Io;

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
    fn peer(&self, _node: &vinc_crypto::NodeId) -> Option<vinc_core::PeerInfo> {
        None
    }
    fn by_conn_id(&self, _cid: &vinc_security::ConnId) -> Option<SessionStats> {
        None
    }
    fn node(&self) -> Option<NodeStats> {
        None
    }
    fn reach_body(&self, _session: SessionId, _out: &mut [u8; vinc_core::REACH_BODY_MAX]) -> usize {
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
