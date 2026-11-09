//! Events, close reasons, drop reasons and the bounded event queue.

use core::fmt;

use vinc_security::{Failure, KeyRequest, TicketBatch};

use super::config::PathId;
use crate::packet::PacketError;
use crate::stream::StreamId;

/// The codes a CLOSE frame carries. 0 and 3 are the codes of the protocol itself; 0x4C means the sender is leaving
/// the network on purpose; the rest are VINC's own and say which rule the peer broke. An application may close with
/// any other code of its own through [`Connection::close`](super::Connection::close).
pub mod code {
    /// No error: an orderly close.
    pub const NO_ERROR: u64 = 0;
    /// The peer broke a rule not named below.
    pub const PROTOCOL_VIOLATION: u64 = 1;
    /// A frame could not be decoded.
    pub const FRAME_ENCODING: u64 = 2;
    /// The peer sent beyond the credit it was given.
    pub const FLOW_CONTROL: u64 = 3;
    /// A frame did not fit the state of its stream.
    pub const STREAM_STATE: u64 = 4;
    /// A final size changed or was exceeded.
    pub const FINAL_SIZE: u64 = 5;
    /// Local state failed.
    pub const INTERNAL: u64 = 8;
    /// The sender leaves the network on purpose.
    pub const LEAVE: u64 = 0x4C;
}

/// Why a connection ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CloseReason {
    /// Nothing was heard for the idle timeout; no CLOSE was sent.
    IdleTimeout,
    /// The local application closed with this code.
    Local {
        /// The code.
        error: u64,
    },
    /// The peer sent CLOSE with this code.
    Peer {
        /// The code.
        error: u64,
    },
    /// The connection broke a rule and sent CLOSE with this code.
    Violation {
        /// The code.
        error: u64,
    },
    /// The active path gave up after repeated probe timeouts.
    PathDead,
    /// The handshake failed.
    Handshake(Failure),
    /// The handshake was not established in time (30 s, or 60 s on a thin node).
    HandshakeTimeout,
}

impl fmt::Display for CloseReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IdleTimeout => f.write_str("the connection was idle for too long"),
            Self::Local { error } => write!(f, "closed locally with code {error}"),
            Self::Peer { error } => write!(f, "the peer closed with code {error}"),
            Self::Violation { error } => write!(f, "closed after a protocol error {error}"),
            Self::PathDead => f.write_str("the peer stopped answering"),
            Self::Handshake(e) => write!(f, "the handshake failed: {e}"),
            Self::HandshakeTimeout => f.write_str("the handshake took too long"),
        }
    }
}

/// Why a received datagram, or part of it, was not used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Drop {
    /// The connection is closed.
    Closed,
    /// A header or length was malformed.
    Malformed(PacketError),
    /// The destination connection id is not one of ours.
    Unroutable,
    /// The packet did not authenticate, or its keys are not available.
    Undecryptable,
    /// The packet number was already received.
    Duplicate,
    /// The packet came before the peer was authenticated and was kept to try again.
    Buffered,
    /// The path table is full and nothing could be evicted.
    NoPath,
    /// A handshake message was refused.
    Handshake(Failure),
    /// The datagram held nothing to process.
    Empty,
}

impl fmt::Display for Drop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Closed => f.write_str("the connection is closed"),
            Self::Malformed(e) => write!(f, "malformed packet: {e}"),
            Self::Unroutable => f.write_str("the connection id is not ours"),
            Self::Undecryptable => f.write_str("the packet could not be decrypted"),
            Self::Duplicate => f.write_str("the packet was already received"),
            Self::Buffered => f.write_str("the packet was kept until the peer is authenticated"),
            Self::NoPath => f.write_str("no room for another path"),
            Self::Handshake(e) => write!(f, "handshake message refused: {e}"),
            Self::Empty => f.write_str("the datagram held nothing to process"),
        }
    }
}

impl core::error::Error for Drop {}

/// Something that happened to the connection. Events that carry data borrow it from the connection, so read them
/// before the next call.
#[derive(Debug)]
pub enum Event<'a> {
    /// The handshake needs a key operation from the host; answer with
    /// [`on_key_response`](super::Connection::on_key_response) or [`answer_soft`](super::Connection::answer_soft).
    KeyRequest(KeyRequest<'a>),
    /// The handshake completed and the peer is authenticated.
    Connected {
        /// Whether the session resumed an earlier one.
        resumed: bool,
    },
    /// The peer opened a stream.
    StreamOpened(StreamId),
    /// A stream has bytes to read.
    StreamReadable(StreamId),
    /// A stream may accept more writes.
    StreamWritable(StreamId),
    /// The peer reset a stream it sends on.
    StreamReset {
        /// The stream.
        id: StreamId,
        /// The application error code.
        error: u64,
    },
    /// A datagram arrived; read it with [`recv_datagram`](super::Connection::recv_datagram).
    DatagramReceived,
    /// An extension frame (type 0x40 and up) arrived. The body is a copy held in a bounded queue. A frame the sender
    /// repeated because its packet looked lost may arrive twice.
    Extension {
        /// The frame type.
        ty: u64,
        /// The frame body.
        body: &'a [u8],
    },
    /// A path answered its challenge.
    PathValidated(PathId),
    /// A path failed validation, or the active path stopped answering.
    PathFailed(PathId),
    /// The peer announced it is going to sleep.
    PeerAsleep,
    /// The peer woke up.
    PeerAwake,
    /// A WAKE got no answer within 800 ms: the peer may be gone, so the endpoint can redial.
    WakeUnanswered,
    /// The peer issued resumption tickets; store them with
    /// [`store_tickets`](super::Connection::store_tickets).
    TicketsReceived(TicketBatch),
    /// The peer sent READY.
    Ready,
    /// The connection ended.
    Closed(CloseReason),
}

/// An event without borrowed data, as queued.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Ev {
    KeyRequest,
    Connected(bool),
    Opened(StreamId),
    Readable(StreamId),
    Writable(StreamId),
    Reset(StreamId, u64),
    Datagram,
    Extension,
    PathValidated(PathId),
    PathFailed(PathId),
    PeerAsleep,
    PeerAwake,
    WakeUnanswered,
    Tickets(TicketBatch),
    Ready,
    Closed(CloseReason),
}

impl Ev {
    /// A notification that the application can recover by polling state; safe to drop when the queue is full.
    const fn lossy(&self) -> bool {
        matches!(
            self,
            Self::Readable(_) | Self::Writable(_) | Self::Datagram | Self::Extension
        )
    }
}

const QUEUE: usize = 128;

/// A fixed ring of pending events. When it is full, a lossy notification is dropped first.
#[derive(Debug)]
pub(crate) struct EvQueue {
    items: [Option<Ev>; QUEUE],
    head: usize,
    len: usize,
}

impl EvQueue {
    pub(crate) const fn new() -> Self {
        Self {
            items: [None; QUEUE],
            head: 0,
            len: 0,
        }
    }

    fn slot(&self, i: usize) -> usize {
        (self.head + i) % QUEUE
    }

    fn contains(&self, ev: &Ev) -> bool {
        (0..self.len).any(|i| {
            matches!(
                (self.items.get(self.slot(i)).copied().flatten(), ev),
                (Some(Ev::Readable(a)), Ev::Readable(b)) | (Some(Ev::Writable(a)), Ev::Writable(b)) if a == *b
            )
        })
    }

    /// Queue an event. A repeated readable or writable notification for the same stream is merged.
    pub(crate) fn push(&mut self, ev: Ev) {
        if self.contains(&ev) {
            return;
        }
        if self.len == QUEUE {
            if ev.lossy() {
                return;
            }
            self.head = (self.head + 1) % QUEUE;
            self.len -= 1;
        }
        let at = self.slot(self.len);
        if let Some(s) = self.items.get_mut(at) {
            *s = Some(ev);
            self.len += 1;
        }
    }

    pub(crate) fn pop(&mut self) -> Option<Ev> {
        if self.len == 0 {
            return None;
        }
        let ev = self.items.get_mut(self.head).and_then(Option::take);
        self.head = (self.head + 1) % QUEUE;
        self.len -= 1;
        ev
    }
}
