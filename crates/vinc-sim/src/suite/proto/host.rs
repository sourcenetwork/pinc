//! The boundary between a node's protocol layers and the endpoint that carries them.
//!
//! A [`Host`] is what a layer may do (dial, open and write streams, close); a [`Layers`] value is what the node
//! adapter drives (intents, events, timeouts). The node adapter implements `Host` over a real `vinc-core` endpoint;
//! the application and the harness protocols implement `Layers`. Both sides are written against this file only.
//!
//! Invariants: a layer never touches the endpoint except through `Host`; all times are TRUE virtual time in
//! nanoseconds, as the reference's harness protocols see it, because the recorder they report to keeps true time; the
//! endpoint's own clock (local, skewed) is the adapter's business; a call into a layer never blocks.

use vinc_core::SessionId;
use vinc_transport::stream::StreamId;

use crate::suite::crypto::Registry;
use crate::suite::world::model::Intent;

/// What a layer can ask of the endpoint.
pub trait Host {
    /// This node's index in the world.
    fn idx(&self) -> usize;
    /// The payload registry of the run (message ids, payload bytes).
    fn registry(&self) -> &'static Registry;
    /// Dial `peer` for `alpn`. The outcome arrives as [`LayerEvent::Connected`] or [`LayerEvent::ConnectFailed`].
    /// Returns false when no dial can be started now (no known address, or the table is full); the layer treats it
    /// as a failed connect after its own backoff.
    fn connect(&mut self, peer: usize, alpn: &'static [u8]) -> bool;
    /// Open a bidirectional stream on `session`.
    fn open_stream(&mut self, session: SessionId) -> Option<StreamId>;
    /// Buffer bytes on a stream; returns how many were taken (the rest must be retried on `StreamWritable`).
    fn write(&mut self, session: SessionId, stream: StreamId, data: &[u8]) -> usize;
    /// End the send side of a stream after the bytes written.
    fn finish(&mut self, session: SessionId, stream: StreamId);
    /// Abandon the send side of a stream.
    fn reset(&mut self, session: SessionId, stream: StreamId, code: u64);
    /// Close a session.
    fn close(&mut self, session: SessionId, code: u64);
    /// The world index of the peer of a session, once known.
    fn peer_of(&self, session: SessionId) -> Option<usize>;
    /// Receive the messages of a topic. Returns false when the node refused.
    fn subscribe(&mut self, topic: &[u8]) -> bool;
    /// Publish a whole message to a topic. Returns false when the node refused.
    fn publish(&mut self, topic: &[u8], msg: &[u8]) -> bool;
}

/// An event for the layers. Stream bytes are read and consumed by the adapter before delivery.
#[derive(Debug)]
pub enum LayerEvent<'a> {
    /// A peer opened a session for `alpn`.
    Incoming {
        /// The session.
        session: SessionId,
        /// The peer's world index.
        peer: usize,
        /// The protocol.
        alpn: &'a [u8],
    },
    /// A dial of this node is open.
    Connected {
        /// The session.
        session: SessionId,
        /// The peer's world index.
        peer: usize,
        /// The protocol.
        alpn: &'a [u8],
    },
    /// A dial ended without a session.
    ConnectFailed {
        /// The peer's world index.
        peer: usize,
        /// The protocol.
        alpn: &'a [u8],
    },
    /// A session ended.
    Closed {
        /// The session.
        session: SessionId,
    },
    /// The peer opened a stream.
    StreamOpened {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
    },
    /// Bytes arrived on a stream (already consumed); `fin` says the peer finished it with these bytes.
    StreamData {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
        /// The bytes.
        data: &'a [u8],
        /// The stream is finished.
        fin: bool,
    },
    /// The peer reset a stream.
    StreamReset {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
    },
    /// A stream may accept more writes.
    StreamWritable {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
    },
    /// A broadcast message arrived; `origin` is the world index of its claimed publisher (`None`: not a known node).
    Message {
        /// The claimed publisher.
        origin: Option<usize>,
        /// The message bytes as delivered.
        body: &'a [u8],
    },
    /// A membership event of the node.
    Member(crate::suite::rec::MemberEvent),
}

/// The protocol layers and the application of one node, as the node adapter drives them.
pub trait Layers {
    /// The protocols to register with the endpoint (the layers' names).
    fn alpns(&self) -> Vec<&'static [u8]>;
    /// The node starts (every incarnation): the application boots and re-issues what it owes.
    fn boot(&mut self, now: u64, host: &mut dyn Host);
    /// A scenario intent for this node at `now`.
    fn intent(&mut self, now: u64, host: &mut dyn Host, intent: &Intent);
    /// An event from the endpoint.
    fn event(&mut self, now: u64, host: &mut dyn Host, ev: LayerEvent<'_>);
    /// The layers' deadlines have come.
    fn timeout(&mut self, now: u64, host: &mut dyn Host);
    /// The earliest deadline the layers want, in true time.
    fn poll_timeout(&self) -> Option<u64>;
    /// Whether the application has open fetches, undelivered pushes or any topic (a resume record is wanted).
    fn has_open_intents(&self, now: u64) -> bool;
    /// The node stops (crash or leave): drop all volatile state; durable state survives in shared storage.
    fn stop(&mut self);
}
