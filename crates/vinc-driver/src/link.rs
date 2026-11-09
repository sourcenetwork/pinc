//! The shared state between the engine thread and the handles of an application.
//!
//! The engine owns the endpoint and runs on one thread; handles run anywhere. They meet in a few small shared
//! values: a [`SessionShared`] per session, a [`StreamShared`] per stream, and bounded channels of owned blocks. A
//! stream's bytes cross in blocks of at most [`BLOCK`] bytes through a channel of at most `stream_blocks` blocks per
//! direction, so the memory a stream holds outside the endpoint is bounded in bytes, not only in count. A channel
//! also carries the end of the data: when the engine drops a sender, the reader sees the channel end and reads why from
//! the shared value, which is always set first.
//!
//! Invariants: an end reason is set once and before the channel it explains is closed; a handle keeps no state that a
//! dropped future could lose, so every wait is a plain channel wait that is safe to drop.

use std::sync::OnceLock;
use std::sync::atomic::AtomicBool;

use kovan_channel::bounded::{Receiver, Sender};
use vinc_core::SessionId;
use vinc_crypto::NodeId;
use vinc_security::Alpn;
use vinc_transport::stream::StreamId;

use crate::error::Error;

/// The most bytes in one block that crosses between a handle and the engine.
pub const BLOCK: usize = 16 * 1024;

/// What a handle sends the engine on a stream.
#[derive(Debug)]
pub enum Item {
    /// Bytes to send.
    Data(Vec<u8>),
    /// The end of the stream: no more bytes follow.
    Fin,
}

/// A stream the engine opened or the peer opened, with the channel ends the handles take.
pub struct NewStream {
    /// The shared state.
    pub shared: std::sync::Arc<StreamShared>,
    /// Where to write, for a stream this side can send on.
    pub tx: Option<Sender<Item>>,
    /// Where to read, for a stream this side can receive on.
    pub rx: Option<Receiver<Vec<u8>>>,
}

/// The state of one stream that both the engine and its handles read.
#[derive(Debug)]
pub struct StreamShared {
    /// The session.
    pub session: SessionId,
    /// The stream.
    pub id: StreamId,
    /// How the receive side ended: `Ok` for the end of the data, else why not. Set before the channel closes.
    pub rx_end: OnceLock<Result<(), Error>>,
    /// Why the send side can take no more. Set before the channel closes.
    pub tx_err: OnceLock<Error>,
    /// A wake for this stream is queued for the engine (so a burst of writes queues one).
    pub pump: AtomicBool,
    /// The engine stopped delivering because the read channel was full: the reader wakes it after it drains.
    pub starved: AtomicBool,
}

impl StreamShared {
    /// A stream's shared state.
    pub const fn new(session: SessionId, id: StreamId) -> Self {
        Self {
            session,
            id,
            rx_end: OnceLock::new(),
            tx_err: OnceLock::new(),
            pump: AtomicBool::new(false),
            starved: AtomicBool::new(false),
        }
    }
}

/// The state of one session that both the engine and its handles read.
pub struct SessionShared {
    /// The session.
    pub id: SessionId,
    /// The peer.
    pub node: NodeId,
    /// The protocol.
    pub alpn: Alpn,
    /// Whether this side dialed.
    pub dialer: bool,
    /// Why the session ended, set once before the channels below close.
    pub ended: OnceLock<Error>,
    /// Streams the peer opened that can be written and read.
    pub accept_bi: Receiver<NewStream>,
    /// Streams the peer opened that can only be read.
    pub accept_uni: Receiver<NewStream>,
    /// Closes (the channel ends) when the session ends.
    pub gone: Receiver<()>,
    /// Datagrams the peer sent, oldest first; at most `Limits::datagrams` wait here.
    pub datagrams: Receiver<Vec<u8>>,
    /// The engine stopped reading datagrams because the channel was full: the reader wakes it after it takes one.
    pub datagrams_starved: AtomicBool,
}

/// A bounded channel of `cap` messages (at least one).
pub fn chan<T: 'static>(cap: usize) -> (Sender<T>, Receiver<T>) {
    kovan_channel::bounded(cap.max(1))
}
