//! Events, close reasons, drop reasons and the bounded event queue.

use core::fmt;

use vinc_security::{Failure, KeyRequest, TicketBatch};

use super::config::PathId;
use crate::packet::PacketError;
use crate::stream::StreamId;
use crate::stream::lazy::{Blank, Lazy};

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
    /// A dial told to end early ([`Connection::end_unanswered`](super::Connection::end_unanswered)) had no answer to
    /// its first 4 flights.
    Unanswered,
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
            Self::Unanswered => f.write_str("the peer did not answer the handshake"),
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
    /// A 0-RTT packet carried a frame that only an established session sends (ACK, CLOSE, REKEY, NEW_TICKETS or
    /// PATH_RESPONSE); the packet was dropped whole and the connection stays open.
    EarlyFrame,
    /// The packet carries something that would raise an event and the application has not read the events it has
    /// (see [`set_gated`](super::Connection::set_gated)); it was not processed and not acknowledged.
    Gated,
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
            Self::EarlyFrame => f.write_str("a 0-RTT packet carried a frame only an established session sends"),
            Self::Gated => f.write_str("the packet waits until the application reads its events"),
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
    /// The peer asked this side to stop sending on a stream; the stream is reset with `error` and takes no more writes.
    StreamStopped {
        /// The stream.
        id: StreamId,
        /// The application error code the peer gave.
        error: u64,
    },
    /// A stream has bytes to read.
    StreamReadable(StreamId),
    /// A stream may accept more writes.
    StreamWritable(StreamId),
    /// A stream open that was refused with [`StreamError::StreamLimit`](crate::stream::StreamError::StreamLimit) or
    /// [`StreamError::Exhausted`](crate::stream::StreamError::Exhausted) may succeed now: the peer raised the number of
    /// streams it admits, or buffer room returned. The host may lose this notification and recover it by asking
    /// [`open_ready`](super::Connection::open_ready) again; it is raised once per refusal, not once per change.
    OpenReady,
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
    /// An extension frame that was queued with [`send_extension`](super::Connection::send_extension) no longer fits one
    /// packet because the path MTU fell. It was dropped and will not be sent: send it again in smaller frames.
    ExtensionUndeliverable {
        /// The frame type.
        ty: u64,
        /// The body length that no longer fits.
        len: usize,
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
    OpenReady,
    Reset(StreamId, u64),
    Stopped(StreamId, u64),
    Datagram,
    Extension,
    ExtensionUndeliverable(u64, usize),
    PathValidated(PathId),
    PathFailed(PathId),
    PeerAsleep,
    PeerAwake,
    WakeUnanswered,
    Tickets,
    Ready,
    Closed(CloseReason),
}

impl Ev {
    /// A notification that the application can recover by polling state; safe to drop when the queue is full.
    const fn lossy(&self) -> bool {
        matches!(
            self,
            Self::Readable(_) | Self::Writable(_) | Self::OpenReady | Self::Datagram | Self::Extension
        )
    }

    /// What makes a second event the same as one already queued, if anything does: a repeat of such an event tells
    /// the application nothing, so it is not queued again. Bounds how many unrecoverable events one packet can add.
    const fn same_as(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Opened(a), Self::Opened(b))
            | (Self::Reset(a, _), Self::Reset(b, _))
            | (Self::Stopped(a, _), Self::Stopped(b, _))
            | (Self::Readable(a), Self::Readable(b))
            | (Self::Writable(a), Self::Writable(b)) => *a == *b,
            (Self::PathValidated(a), Self::PathValidated(b)) | (Self::PathFailed(a), Self::PathFailed(b)) => a.0 == b.0,
            (Self::KeyRequest, Self::KeyRequest)
            | (Self::Connected(_), Self::Connected(_))
            | (Self::OpenReady, Self::OpenReady)
            | (Self::PeerAsleep, Self::PeerAsleep)
            | (Self::PeerAwake, Self::PeerAwake)
            | (Self::WakeUnanswered, Self::WakeUnanswered)
            | (Self::Tickets, Self::Tickets)
            | (Self::Ready, Self::Ready)
            | (Self::Closed(_), Self::Closed(_)) => true,
            _ => false,
        }
    }
}

/// The places of the event queue. With `alloc` a place is written when an event first uses it, so the queue is sized
/// for a session of 200 stream slots; without it the queue is inline in the connection and stays at 256, which
/// [`queue_fits`] holds a session of up to 77 slots to.
#[cfg(feature = "alloc")]
pub(crate) const QUEUE: usize = 640;
/// The places of the event queue.
#[cfg(not(feature = "alloc"))]
pub(crate) const QUEUE: usize = 256;
/// Events that cannot be recovered and may be queued at once besides one `Opened`, one `Reset` and one `Stopped` per stream slot and
/// one validated and one failed event per path: connected, key request, tickets, ready, asleep, awake, wake
/// unanswered, closed and the undeliverable extension frames of the 8 extension slots.
pub(crate) const FIXED_EVENTS: usize = 16;

/// Whether `streams` stream slots and `paths` paths leave room for every unrecoverable event: with the repeats of
/// [`Ev::same_as`] dropped, no more than this many can be queued, so a full queue always holds a notification to give up.
pub(crate) const fn queue_fits(streams: usize, paths: usize) -> bool {
    3 * streams + 2 * paths + FIXED_EVENTS <= QUEUE
}

/// A fixed ring of pending events. A repeat of an event the application learns nothing more from is not queued. When
/// the queue is full a notification the application can recover by polling state is dropped first; an event that
/// cannot be recovered is never dropped while [`queue_fits`] holds, and one that is dropped anyway is counted in
/// [`EvQueue::lost`].
#[derive(Debug)]
pub(crate) struct EvQueue {
    items: Lazy<Option<Ev>, QUEUE>,
    head: usize,
    len: usize,
    /// Unrecoverable events dropped because the queue held nothing else; 0 while the queue is sized by [`queue_fits`].
    pub(crate) lost: u64,
    /// The ticket batch the queued [`Ev::Tickets`] stands for: a newer batch replaces it, because the newest is kept.
    pub(crate) tickets: Option<TicketBatch>,
}

impl Blank for Option<Ev> {
    const BLANK: Self = None;
}

/// The room of a connection's event queue, handed over with its [`Resources`](super::Resources): with `alloc` it is
/// reserved once and written only as far as events were queued, so a new session builds none.
#[derive(Debug, Clone)]
pub struct EventTable(Lazy<Option<Ev>, QUEUE>);

impl Default for EventTable {
    fn default() -> Self {
        Self::new()
    }
}

impl EventTable {
    /// An empty table.
    pub fn new() -> Self {
        Self(Lazy::new())
    }

    /// Forget every queued event, keeping the room.
    pub fn clear(&mut self) {
        self.0.clear();
    }
}

impl EvQueue {
    pub(crate) fn new(table: EventTable) -> Self {
        Self {
            items: table.0,
            head: 0,
            len: 0,
            lost: 0,
            tickets: None,
        }
    }

    fn slot(&self, i: usize) -> usize {
        (self.head + i) % QUEUE
    }

    fn find(&self, ev: &Ev) -> Option<usize> {
        (0..self.len).find(|i| {
            self.items
                .get(self.slot(*i))
                .copied()
                .flatten()
                .is_some_and(|q| q.same_as(ev))
        })
    }

    /// Take the entry `i` out, closing the gap by moving the older entries up one place.
    fn remove(&mut self, i: usize) {
        for k in (0..i).rev() {
            let (from, to) = (self.slot(k), self.slot(k + 1));
            let moved = self.items.get(from).copied().flatten();
            if let Some(s) = self.items.get_mut(to) {
                *s = moved;
            }
        }
        self.head = if self.len == 1 { 0 } else { (self.head + 1) % QUEUE };
        self.len -= 1;
    }

    /// Queue an event; a repeat of a queued event is not queued again.
    pub(crate) fn push(&mut self, ev: Ev) {
        if !matches!(ev, Ev::Datagram | Ev::Extension | Ev::ExtensionUndeliverable(..)) && self.find(&ev).is_some() {
            return;
        }
        if self.len == QUEUE {
            if ev.lossy() {
                return;
            }
            let Some(victim) = (0..self.len).find(|i| {
                self.items
                    .get(self.slot(*i))
                    .copied()
                    .flatten()
                    .is_some_and(|e| e.lossy())
            }) else {
                self.lost += 1;
                return;
            };
            self.remove(victim);
        }
        let at = self.slot(self.len);
        if let Some(s) = self.items.get_mut(at) {
            *s = Some(ev);
            self.len += 1;
        }
    }

    /// Queue the arrival of `batch`, replacing the batch of a ticket event still queued.
    pub(crate) fn push_tickets(&mut self, batch: TicketBatch) {
        self.tickets = Some(batch);
        self.push(Ev::Tickets);
    }

    /// The room of the queue, for the next connection.
    pub(crate) fn into_table(self) -> EventTable {
        EventTable(self.items)
    }

    pub(crate) fn pop(&mut self) -> Option<Ev> {
        if self.len == 0 {
            return None;
        }
        let ev = self.items.written_mut(self.head).and_then(Option::take);
        self.head = if self.len == 1 { 0 } else { (self.head + 1) % QUEUE };
        self.len -= 1;
        ev
    }
}
