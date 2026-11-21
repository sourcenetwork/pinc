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

use pinc_crypto::NodeId;
use pinc_security::{Alpn, ConnId, Failure, KeyRequest, KeyResponse};
use pinc_transport::conn::{CloseReason, ExtensionError, PathId, Stats};
use pinc_transport::stream::datagram::DatagramError;
use pinc_transport::stream::{RecvStatus, StreamError, StreamId};

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
        /// The session of the dial, or `None` when the dial was refused before one existed.
        session: Option<SessionId>,
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
    /// A stream open that was refused for want of stream credit or buffer room may succeed now. The application may lose
    /// this notification, like a read or write notification, and recover it by trying the open again; it is raised once
    /// per refusal.
    OpenReady {
        /// The session.
        session: SessionId,
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
    /// The peer was heard on a session reported before it answered: an optimistic dial finished its handshake, or a
    /// sub-session took its first packet from the peer. Raised once per session, and never for a session reported
    /// after its handshake ([`SessionStats::answered`] says which).
    Answered {
        /// The session.
        session: SessionId,
        /// Whether the dial resumed an earlier session with a ticket; `false` on the accepting side.
        resumed: bool,
    },
}

impl Event {
    /// Whether the application can recover the event by reading state, so a full queue may drop it. A datagram
    /// cannot be recovered: each notification stands for one datagram.
    pub const fn lossy(&self) -> bool {
        matches!(
            self,
            Self::StreamReadable { .. } | Self::StreamWritable { .. } | Self::OpenReady { .. }
        )
    }

    /// The session the event names, if any.
    pub const fn session(&self) -> Option<SessionId> {
        match *self {
            Self::Connected { session, .. }
            | Self::Incoming { session, .. }
            | Self::Closed { session, .. }
            | Self::StreamOpened { session, .. }
            | Self::StreamReadable { session, .. }
            | Self::StreamWritable { session, .. }
            | Self::OpenReady { session }
            | Self::StreamReset { session, .. }
            | Self::StreamStopped { session, .. }
            | Self::DatagramReceived { session }
            | Self::KeyRequest { session }
            | Self::PathChanged { session, .. }
            | Self::ReachOut { session }
            | Self::PeerAsleep { session }
            | Self::PeerAwake { session }
            | Self::TicketsReceived { session, .. }
            | Self::Answered { session, .. } => Some(session),
            // A failed dial's session is no longer kept: the queue purges the events of a closed session, and this
            // one must reach the application.
            Self::ConnectFailed { .. } | Self::AcpCheck { .. } => None,
        }
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
pub enum Command<'c, S = pinc_transport::stream::NoSource> {
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
    /// [`pinc_transport::frame::ext`]). It leaves ahead of stream data and is sent again until a packet carrying it is
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
    /// Drop the cached answer of the access check for `peer`: its next session raises [`Event::AcpCheck`] again, and
    /// an allowed session of it holds its next event until a fresh allow comes. A check already pending is kept. A
    /// revoke, its lifting and a change of the access hook's answer call it.
    AcpForget {
        /// The peer.
        peer: NodeId,
    },
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
    /// A carrier PING and PONG stood for the session's keepalive: a PONG that came back (`sent` false) counts as a
    /// datagram received, a PING this side wrote (`sent` true) as a datagram sent.
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
    /// Hold the resends of the flight of a session still dialing while the address of its peer is looked up, or let
    /// them go on again. A held flight is checked again every 500 ms and sent when released.
    HoldFlight {
        /// The session.
        session: SessionId,
        /// Whether to hold.
        hold: bool,
    },
    /// A punch round. Send the peer a `REACH_OUT`: an opaque body (the candidate addresses, at most
    /// [`crate::REACH_BODY_MAX`] bytes) the layer above encodes. And probe every direct path the session tracks that
    /// is not validated and has no probe left.
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
    /// Send the peer an acknowledgement-eliciting PING on the session's active path, to learn whether it still holds the
    /// session.
    Ping {
        /// The session.
        session: SessionId,
    },
    /// When the carrier of the relay the session's active path runs through last heard anything, in the endpoint's
    /// clock; 0 when that carrier is not open. A session on a relay path whose probe timeouts keep firing while the
    /// carrier answers is closed: its peer no longer holds it. Send it while the session's probes are timing out.
    CarrierHeard {
        /// The session.
        session: SessionId,
        /// When the carrier last heard anything, 0 when it is not open.
        at: u64,
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
    /// The session at position `i` of the table, counting live sessions only. A dial that probes a quiet parent
    /// (it has no connection yet) is listed, answering as a dial that has not connected.
    SessionAt(usize),
    /// The session of `node` made next after `after` (the oldest when `after` is `None`), a dial that has not
    /// finished included; nothing after the newest, or when `after` is not a session of `node`. One lookup a step.
    PeerSession {
        /// The peer.
        node: NodeId,
        /// The session to continue from.
        after: Option<SessionId>,
    },
    /// The answer of the access check the endpoint holds for a peer, with when it runs out.
    Access(NodeId),
    /// The peer at position `i` of the round-trip table.
    PeerAt(usize),
    /// A peer of the round-trip table by node id; nothing when it holds no round trip of that peer.
    Peer(NodeId),
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
    /// The counters of the session that accepts datagrams for this connection id, if any.
    ByConnId(ConnId),
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
    /// The session carries broadcast traffic and is flushed after the others ([`Command::SetGossip`]).
    pub gossip: bool,
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
    /// When the peer was last heard on any path (an authenticated packet, or a carrier keepalive answer), in the
    /// endpoint's clock; 0 before the first.
    pub heard_any: u64,
    /// The keepalive was handed to the connectivity layer ([`Command::SetPulse`]) and is due now.
    pub pulse_due: bool,
    /// When the application last moved data on the session, in the endpoint's clock (a quiet role's small control
    /// writes do not count).
    pub last_app: u64,
    /// This is a sub-session of another session to the same peer.
    pub sub: bool,
    /// The peer was heard on the session since the application was told of it, or before ([`Event::Answered`]). A
    /// dial with a cached allow and a sub-session are reported before the peer answers, so a peer that stopped can
    /// look connected until this turns true or the session ends.
    pub answered: bool,
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
    /// Sessions that count against the cap on unauthenticated sessions: those that have not authenticated their peer
    /// yet, but for a resumption in its handshake, which the cap exempts.
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
    /// Datagrams dropped before any connection (unroutable, too large, floors, the half-open cap, a full table), and
    /// the rejects dropped because the queue of rejects waiting to be sent was full.
    pub dropped_in: u64,
    /// Datagrams a connection produced that could not leave: the path they were for is gone, or the buffer offered
    /// for a datagram kept from the last call or for a reject is shorter than it.
    pub dropped_out: u64,
    /// Reach-out bodies lost: kept no longer because newer ones took their place, or too long to keep.
    pub reach_dropped: u64,
    /// Extension frames lost: dropped as the oldest of a full ring, or too long to keep.
    pub ext_dropped: u64,
    /// Datagrams of sessions the ledger held back; a reject it refused is counted in `stateless_refused` instead.
    pub held_by_ledger: u64,
    /// Packets refused because they would raise events while the host left unrecoverable events unread or a session's
    /// held events were full; the peer sends them again.
    pub stalled_in: u64,
    /// First flights refused before any work because the sessions this node owes its host would fill the room the
    /// host left to accept them ([`Endpoint::set_backlog_room`](crate::Endpoint::set_backlog_room)); the peer sends
    /// them again.
    pub backlog_refused: u64,
    /// First flights dropped because the id they name already has four half-open sessions (also counted in
    /// `dropped_in`).
    pub holders_refused: u64,
    /// First handshake messages dropped before admission because their datagram was shorter than the least a first
    /// packet of their type is (also counted in `dropped_in`).
    pub first_too_short: u64,
    /// Rejects written to the caller's buffer, without a session, for a first message the responder would only have
    /// rejected: a resumption Hello whose ticket does not open, a short Initial whose prekey this node does not hold.
    pub stateless_rejects: u64,
    /// Rejects thrown away, not kept for later, because the ledger would not let this node answer that address.
    /// With today's sizes it stays 0, as a first message of the floor's size pays for its reject three times over; it
    /// guards the bound should a reject ever grow.
    pub stateless_refused: u64,
    /// Events waiting for the host now.
    pub events_queued: usize,
    /// Events dropped because the event queue was full.
    pub events_dropped: u64,
    /// Events the application cannot recover that were dropped because the event queue held nothing else to give up;
    /// the endpoint keeps this at 0 by holding work back while the queue is near full.
    pub events_lost: u64,
    /// Handshake datagrams held because they carried a later part of a first message whose start had not arrived.
    pub fragments_held: u64,
    /// Held handshake datagrams given to the session that the start of their message created.
    pub fragments_replayed: u64,
    /// Held handshake datagrams let go because the start of their message did not come within 1 s.
    pub fragments_expired: u64,
    /// Held handshake datagrams let go to make room for a newer one.
    pub fragments_evicted: u64,
    /// Handshake datagrams held now (at most 4).
    pub fragments_waiting: usize,
    /// Server sessions this node made that the host has not taken yet
    /// ([`Endpoint::session_taken`](crate::Endpoint::session_taken)): their handshakes are under way, or their
    /// `Incoming` waits to be read.
    pub owed: usize,
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
    /// The answer of the access check held for a peer.
    Access {
        /// Whether it is an allow.
        allow: bool,
        /// When it runs out, in the endpoint's clock; it counts for nothing from then on.
        until: u64,
    },
}
