//! The typed surface of the endpoint: commands in, events out, queries for state.
//!
//! A [`Command`] is applied by [`Endpoint::command`](crate::Endpoint::command), which returns a [`Reply`] holding the
//! command's value and the events it produced at once, so a host never waits for a wake to learn the outcome. Every
//! other event is read with [`Endpoint::poll_event`](crate::Endpoint::poll_event). A [`Query`] reads state and
//! changes nothing; the answer may borrow from the endpoint.
//!
//! Invariants: an event names a session by [`SessionId`], which is never reused for another session; an event is a
//! small plain value, so reading it never borrows the endpoint; an event for an application stream is held back
//! until the access check of its peer allowed the session.

use core::net::SocketAddr;

use vinc_crypto::NodeId;
use vinc_security::{Alpn, Failure, KeyRequest, KeyResponse};
use vinc_transport::conn::{CloseReason, ExtensionError, PathId, Stats};
use vinc_transport::stream::datagram::DatagramError;
use vinc_transport::stream::{RecvStatus, StreamError, StreamId};

use crate::keepalive::Role;
use crate::ledger::LedgerEntry;

/// The name of a session: its table slot and how many sessions the slot held before it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SessionId(pub u64);

impl SessionId {
    pub(crate) const fn new(slot: usize, generation: u32) -> Self {
        Self((generation as u64) << 32 | slot as u64)
    }

    /// The table slot.
    #[allow(clippy::cast_possible_truncation, reason = "the low 32 bits are the slot")]
    pub const fn slot(self) -> usize {
        (self.0 & 0xFFFF_FFFF) as usize
    }

    /// How many sessions the slot held before this one.
    #[allow(clippy::cast_possible_truncation, reason = "the high 32 bits are the generation")]
    pub const fn generation(self) -> u32 {
        (self.0 >> 32) as u32
    }
}

/// Why a dial did not produce a session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConnectFailure {
    /// The node is this one, or no address could be used.
    Refused,
    /// The access check denied the peer.
    Denied,
    /// The handshake was not established in time.
    Timeout,
    /// The handshake failed.
    Handshake(Failure),
    /// The connection ended some other way before it was established.
    Closed,
}

/// Why a session the application knew ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EndReason {
    /// The connection ended for this transport reason.
    Transport(CloseReason),
    /// Its parent session closed before the peer was ever heard on it.
    Orphaned,
    /// The access check withdrew the peer.
    Denied,
    /// The node resumed from a suspension in a state that cannot be woken: dial again at once.
    Redial,
}

/// How a path changed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathState {
    /// The path answered its challenge.
    Validated,
    /// The path failed validation or stopped answering.
    Failed,
}

/// Something that happened.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// A session this node dialed is open for the application.
    Connected {
        /// The session.
        session: SessionId,
        /// The peer.
        node: NodeId,
        /// The protocol.
        alpn: Alpn,
        /// Whether it resumed an earlier session.
        resumed: bool,
    },
    /// A peer's session is open for the application.
    Incoming {
        /// The session.
        session: SessionId,
        /// The peer.
        node: NodeId,
        /// The protocol it asked for.
        alpn: Alpn,
    },
    /// A dial ended without a session the application knew.
    ConnectFailed {
        /// The peer.
        node: NodeId,
        /// The protocol.
        alpn: Alpn,
        /// Why.
        reason: ConnectFailure,
    },
    /// A session ended.
    Closed {
        /// The session.
        session: SessionId,
        /// Why.
        reason: EndReason,
    },
    /// The peer opened a stream.
    StreamOpened {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
    },
    /// A stream has bytes to read.
    StreamReadable {
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
    /// The peer reset a stream.
    StreamReset {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
        /// The application error code.
        error: u64,
    },
    /// The peer asked this side to stop sending on a stream; the stream is reset with `error`.
    StreamStopped {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
        /// The application error code the peer gave.
        error: u64,
    },
    /// A datagram arrived.
    DatagramReceived {
        /// The session.
        session: SessionId,
    },
    /// The access check is needed for a peer: answer with [`Command::AcpAnswer`].
    AcpCheck {
        /// The check to answer.
        check: u64,
        /// The peer.
        node: NodeId,
        /// The protocol of the session that asked.
        alpn: Alpn,
    },
    /// A key operation is needed: read it with [`Query::KeyRequest`] and answer with [`Command::KeyResponse`].
    KeyRequest {
        /// The session.
        session: SessionId,
    },
    /// A path of a session changed.
    PathChanged {
        /// The session.
        session: SessionId,
        /// The path.
        path: PathId,
        /// What happened to it.
        state: PathState,
    },
    /// The peer sent its candidate addresses for a direct path: read them with [`Query::ReachOut`] before the next
    /// few events arrive.
    ReachOut {
        /// The session.
        session: SessionId,
    },
    /// The peer announced it sleeps.
    PeerAsleep {
        /// The session.
        session: SessionId,
    },
    /// The peer woke up.
    PeerAwake {
        /// The session.
        session: SessionId,
    },
    /// The peer issued resumption tickets; the endpoint stored them.
    TicketsReceived {
        /// The session.
        session: SessionId,
        /// How many tickets.
        count: usize,
    },
}

impl Event {
    /// Whether the application can recover the event by reading state, so a full queue may drop it. A datagram
    /// cannot be recovered: each notification stands for one datagram.
    pub(crate) const fn lossy(&self) -> bool {
        matches!(self, Self::StreamReadable { .. } | Self::StreamWritable { .. })
    }
}

/// The events one command produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Events {
    items: [Option<Event>; Self::MAX],
    len: usize,
}

impl Events {
    /// The most events a reply carries; further ones are queued for [`poll_event`](crate::Endpoint::poll_event).
    pub const MAX: usize = 8;

    pub(crate) fn push(&mut self, ev: Event) -> bool {
        match self.items.get_mut(self.len) {
            Some(s) => {
                *s = Some(ev);
                self.len += 1;
                true
            }
            None => false,
        }
    }

    /// How many events.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Whether there is none.
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The events in the order they happened.
    pub fn iter(&self) -> impl Iterator<Item = &Event> {
        self.items.iter().take(self.len).flatten()
    }

    /// Whether an event satisfies `f`.
    pub fn any(&self, f: impl Fn(&Event) -> bool) -> bool {
        self.iter().any(f)
    }
}

/// What a command returns besides its events.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Value {
    /// Nothing.
    None,
    /// The session a [`Command::Connect`] started or opened.
    Session(SessionId),
    /// The stream a [`Command::OpenStream`] opened.
    Stream(StreamId),
    /// How many bytes a [`Command::Write`] took.
    Written(usize),
    /// The state of a stream after a [`Command::Consume`].
    Recv(RecvStatus),
}

/// A command's outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reply {
    /// The command's value.
    pub value: Value,
    /// The events the command produced at once.
    pub events: Events,
}

/// Why a command was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommandError {
    /// No such session (it ended, or the name is stale).
    NoSession,
    /// The connection table has no free slot.
    Full,
    /// No interface can reach any of the addresses given.
    NoRoute,
    /// The endpoint holds no prekey: set one with [`Endpoint::set_prekey`](crate::Endpoint::set_prekey).
    NoPrekey,
    /// The stream layer refused.
    Stream(StreamError),
    /// The datagram layer refused.
    Datagram(DatagramError),
    /// The extension frame could not be queued.
    Extension(ExtensionError),
    /// The handshake machine refused.
    Failure(Failure),
    /// The protocol name is empty or longer than a protocol name may be.
    BadAlpn,
    /// No access check is waiting under that number.
    NoCheck,
    /// The session has no key request waiting.
    NoKeyRequest,
    /// The node is this one: a node does not dial itself.
    Refused,
    /// The host left too many events unread: read them with `poll_event` and send the command again.
    EventsPending,
    /// The next received datagram does not fit the buffer; it stays queued. `len` is its size.
    BufferTooSmall {
        /// The size of the datagram.
        len: usize,
    },
}

/// What the application asks of the endpoint. `S` is the type of source-backed stream data.
#[derive(Debug)]
pub enum Command<'c, S = vinc_transport::stream::NoSource> {
    /// Dial `node` for `alpn`. A peer with an established session gets a sub-session at once, with no round trip.
    Connect {
        /// The peer.
        node: NodeId,
        /// The protocol.
        alpn: &'c [u8],
        /// The addresses to try; the first carries the first flight, the others become candidate paths.
        addrs: &'c [SocketAddr],
        /// The session's role.
        role: Role,
    },
    /// Open a stream.
    OpenStream {
        /// The session.
        session: SessionId,
        /// Bidirectional (true) or unidirectional.
        bidi: bool,
    },
    /// Buffer bytes on a stream.
    Write {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
        /// The bytes.
        data: &'c [u8],
    },
    /// Set the urgency of a stream: streams are served lowest number first (3 by default), then by id.
    SetUrgency {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
        /// The urgency.
        urgency: u8,
    },
    /// Send the peer an extension frame (type 0x40 and up, an assigned one from
    /// [`vinc_transport::frame::ext`]). It leaves ahead of stream data and is sent again until a packet carrying it is
    /// acknowledged. It must fit one packet.
    SendExtension {
        /// The session.
        session: SessionId,
        /// The frame type.
        ty: u64,
        /// The body.
        body: &'c [u8],
    },
    /// Back a stream with storage of `len` bytes the endpoint reads from when it builds packets.
    WriteSource {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
        /// The storage.
        source: S,
        /// Its length.
        len: u64,
    },
    /// End a buffered stream after the bytes written.
    Finish {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
    },
    /// Abandon the send side of a stream.
    Reset {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
        /// The application error code.
        error: u64,
    },
    /// Ask the peer to stop sending on a stream; it resets the stream with `error`.
    StopSending {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
        /// The application error code.
        error: u64,
    },
    /// Release bytes read from a stream.
    Consume {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
        /// How many bytes.
        n: usize,
    },
    /// Send an unreliable datagram.
    SendDatagram {
        /// The session.
        session: SessionId,
        /// The bytes.
        data: &'c [u8],
    },
    /// Close a session with `error`.
    Close {
        /// The session.
        session: SessionId,
        /// The code.
        error: u64,
    },
    /// Close every session with the code that says this node leaves the network on purpose (0x4C).
    Shutdown,
    /// Answer an [`Event::AcpCheck`].
    AcpAnswer {
        /// The check.
        check: u64,
        /// Whether the peer may connect.
        allow: bool,
    },
    /// Answer an [`Event::KeyRequest`].
    KeyResponse {
        /// The session.
        session: SessionId,
        /// The answer.
        response: KeyResponse<'c>,
    },
    /// Every established session goes to sleep (the application or the system suspends the node).
    Suspend,
    /// The node resumes from a suspension; `moved` says its address changed meanwhile.
    Resume {
        /// Whether the node's address changed while it was suspended.
        moved: bool,
    },
    /// Send the handshake flight of a session still dialing on these addresses as well as its first one, now and on
    /// every resend; an empty list turns it off. With `skip_primary` the flight leaves on these addresses only, never
    /// on the first one (exactly one path per try). The connectivity layer drives this to try candidate paths.
    FlightPaths {
        /// The session.
        session: SessionId,
        /// The remote addresses to copy the flight to.
        addrs: &'c [SocketAddr],
        /// Leave the session's first address out of the flight.
        skip_primary: bool,
    },
    /// A carrier PING and PONG stood for the session's keepalive (`CARRIER_PULSE`): count it as received, and as sent
    /// when `sent` says this side wrote the PING.
    Pulse {
        /// The session.
        session: SessionId,
        /// This side sent a carrier PING for the session.
        sent: bool,
    },
    /// Hand the keepalive of a quiet session to the connectivity layer: the endpoint sends no PING itself and
    /// reports [`SessionStats::pulse_due`] when one is due; the layer answers with [`Command::Pulse`].
    SetPulse {
        /// The session.
        session: SessionId,
        /// On or off.
        on: bool,
    },
    /// Move the first resend of a session still dialing to `delay` nanoseconds from now.
    FirstResend {
        /// The session.
        session: SessionId,
        /// The wait before the flight is sent again.
        delay: u64,
    },
    /// Send the peer a `REACH_OUT`: an opaque body (the candidate addresses, at most [`crate::REACH_BODY_MAX`]
    /// bytes) the layer above encodes.
    ReachOut {
        /// The session.
        session: SessionId,
        /// The body.
        body: &'c [u8],
    },
    /// Try a candidate address as a direct path of a session: add it and start its 9 probes, or start them again if
    /// the session already tracks it and it never validated.
    Punch {
        /// The session.
        session: SessionId,
        /// The candidate address.
        addr: SocketAddr,
    },
    /// Set a session's role (the layer above knows which sessions are hub sessions).
    SetRole {
        /// The session.
        session: SessionId,
        /// The role.
        role: Role,
    },
    /// Mark a session as carrying broadcast traffic, which is flushed after the others.
    SetGossip {
        /// The session.
        session: SessionId,
        /// The flag.
        gossip: bool,
    },
}

/// What the application asks to know.
#[derive(Debug, Clone, Copy)]
pub enum Query {
    /// The counters of a session.
    Stats(SessionId),
    /// The session at position `i` of the table, counting live sessions only.
    SessionAt(usize),
    /// The peer at position `i` of the round-trip table.
    PeerAt(usize),
    /// The readable bytes of a stream.
    Read {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
    },
    /// The stored bytes of a stream from an absolute offset, up to the end of the run holding them or of one chunk;
    /// the run may lie beyond a hole. Nothing is copied. Release bytes with [`Command::Consume`], which moves through
    /// the contiguous prefix only.
    ReadAt {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
        /// The absolute stream offset of the first byte.
        offset: u64,
    },
    /// The first run of stored bytes of a stream that reaches past `from`, cut to begin at `from` or later: how a
    /// host finds bytes that arrived beyond a hole.
    StoredAfter {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
        /// The absolute stream offset to look from.
        from: u64,
    },
    /// What the send half of a stream knows: how far it sent, the lowest byte waiting to be sent again, the
    /// connection's congestion window, and whether the stream is done (every byte and its end acknowledged by the
    /// peer, or the stream gone).
    SendState {
        /// The session.
        session: SessionId,
        /// The stream.
        stream: StreamId,
    },
    /// The bytes the session has sent that are neither acknowledged nor declared lost.
    InFlight(SessionId),
    /// The key operation a session waits for.
    KeyRequest(SessionId),
    /// The node-wide numbers.
    Node,
    /// The ledger entry of an address.
    Ledger(SocketAddr),
    /// The body of the latest `REACH_OUT` this session received.
    ReachOut(SessionId),
}

/// The counters of a session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SessionStats {
    /// The session.
    pub session: SessionId,
    /// The peer, once known.
    pub node: Option<NodeId>,
    /// The protocol.
    pub alpn: Option<Alpn>,
    /// The role.
    pub role: Role,
    /// Whether this side dialed.
    pub dialer: bool,
    /// Whether the session is established.
    pub established: bool,
    /// The access check allowed it.
    pub allowed: bool,
    /// The active path.
    pub path: Option<PathId>,
    /// The local and remote address of the active path.
    pub route: Option<(SocketAddr, SocketAddr)>,
    /// Whether the session is thin.
    pub thin: bool,
    /// Application events held back for the access check.
    pub held: usize,
    /// Held read and write notifications dropped because the hold was full; they are recoverable by reading state.
    pub held_dropped: u64,
    /// The probe timeout now: before any round trip sample it starts from the node's round trips.
    pub pto: u64,
    /// Probe timeouts in a row; above 0 the session is in loss recovery.
    pub pto_count: u32,
    /// Whether the active path is validated.
    pub path_validated: bool,
    /// When a datagram last arrived on the active path, in the endpoint's clock; 0 before the first.
    pub heard: u64,
    /// The keepalive was handed to the connectivity layer ([`Command::SetPulse`]) and is due now.
    pub pulse_due: bool,
    /// The transport counters, with the smoothed round trip in `srtt`.
    pub transport: Stats,
}

/// The send half of a stream, as [`Query::SendState`] answers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SendState {
    /// One past the highest stream offset sent so far.
    pub sent: u64,
    /// The lowest stream offset declared lost that waits to be sent again.
    pub lost: Option<u64>,
    /// The connection's congestion window in bytes.
    pub window: u64,
    /// Every byte and the end are acknowledged, or the stream is gone: nothing more will be sent.
    pub done: bool,
}

/// The node-wide numbers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeStats {
    /// Sessions in the table.
    pub sessions: usize,
    /// Sessions that have not authenticated their peer yet.
    pub half_open: usize,
    /// The node average handshake round trip.
    pub lrtt: u64,
    /// The node peak round trip.
    pub tgr: u64,
    /// The handshake floor.
    pub hs_floor: u64,
    /// Whether the node is on a constrained link.
    pub thin: bool,
    /// Addresses in the amplification ledger.
    pub ledger: usize,
    /// Datagrams received.
    pub datagrams_in: u64,
    /// Datagrams sent.
    pub datagrams_out: u64,
    /// Datagrams dropped before any connection (unroutable, too large, floors, the half-open cap, a full table).
    pub dropped_in: u64,
    /// Datagrams the ledger held back.
    pub held_by_ledger: u64,
    /// Packets refused because they would raise events while the host left unrecoverable events unread or a session's
    /// held events were full; the peer sends them again.
    pub stalled_in: u64,
    /// Events dropped because the event queue was full.
    pub events_dropped: u64,
    /// Events the application cannot recover that were dropped because the event queue held nothing else to give up;
    /// the endpoint keeps this at 0 by holding work back while the queue is near full.
    pub events_lost: u64,
}

/// A peer in the round-trip table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PeerInfo {
    /// The peer.
    pub node: NodeId,
    /// Its remembered handshake round trip.
    pub krtt: u64,
}

/// The answer to a [`Query`].
#[derive(Debug)]
pub enum Answer<'q> {
    /// There is nothing to answer.
    None,
    /// The counters of a session.
    Stats(SessionStats),
    /// A peer.
    Peer(PeerInfo),
    /// Readable stream bytes, borrowed from the session's pool.
    Chunk(&'q [u8]),
    /// A run of stored stream bytes by absolute offsets.
    Stored(core::ops::Range<u64>),
    /// The send half of a stream.
    SendState(SendState),
    /// Bytes in flight.
    InFlight(u64),
    /// A key operation, borrowed from the session.
    KeyRequest(KeyRequest<'q>),
    /// The node-wide numbers.
    Node(NodeStats),
    /// A ledger entry.
    Ledger(LedgerEntry),
    /// A `REACH_OUT` body, borrowed from the endpoint.
    ReachOut(&'q [u8]),
}
