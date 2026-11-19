//! The endpoint as the node uses it: one trait over the endpoint's thirteen type and const parameters, so the node
//! carries one parameter instead of thirteen.
//!
//! The trait adds to the connectivity client's `Port` the calls only the node's own loop needs: datagrams in and out,
//! events, the clock, the protocol registry and the reading of a stream. [`Endpoint`] implements it by forwarding.

use core::net::SocketAddr;

use core::ops::Range;
use pinc_connect::client::Port;

use pinc_core::{
    Answer, CommandError, Endpoint, Event, IfaceEvent, IfaceId, Query, SendState, SessionId, SessionStats, TraceRecord,
    Transmit,
};
use pinc_crypto::Provider;
use pinc_transport::stream::{StreamId, StreamSource};

/// The endpoint calls the node makes besides the commands and queries of `Port`.
pub trait Ep: Port {
    /// A datagram arrived.
    fn handle_datagram(&mut self, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]);
    /// The next datagram to send.
    fn poll_transmit(&mut self, now: u64, out: &mut [u8]) -> Option<Transmit>;
    /// Whether [`poll_transmit`](Self::poll_transmit) has anything to write or to do. When it says no, a call returns
    /// `None` and changes nothing. An endpoint that cannot tell says yes.
    fn transmit_waiting(&self) -> bool {
        true
    }
    /// The next event.
    fn poll_event(&mut self) -> Option<Event>;
    /// Whether [`poll_event`](Self::poll_event) has anything to give or to do. An endpoint that cannot tell says yes.
    fn events_waiting(&self) -> bool {
        true
    }
    /// The next deadline.
    fn poll_timeout(&self) -> Option<u64>;
    /// Time passed.
    fn handle_timeout(&mut self, now: u64);
    /// Accept sessions for a protocol.
    fn register_alpn(&mut self, alpn: &[u8]) -> bool;
    /// The next received bytes of a stream, not yet consumed.
    fn read_chunk(&self, session: SessionId, stream: StreamId) -> Option<&[u8]>;
    /// The stored bytes of a stream from an absolute offset, possibly beyond a hole, borrowed.
    fn read_at(&self, session: SessionId, stream: StreamId, offset: u64) -> Option<&[u8]>;
    /// The first run of stored bytes of a stream that reaches past `from`.
    fn stored_after(&self, session: SessionId, stream: StreamId, from: u64) -> Option<Range<u64>>;
    /// The send half of a stream.
    fn send_state(&self, session: SessionId, stream: StreamId) -> Option<SendState>;
    /// The bytes a session has in flight.
    fn in_flight(&self, session: SessionId) -> Option<u64>;
    /// Copy the oldest extension frame held for the application into `out`.
    ///
    /// # Errors
    /// The endpoint's refusal when the frame does not fit `out`.
    fn read_extension(&mut self, out: &mut [u8]) -> Result<Option<(SessionId, u64, usize)>, CommandError>;
    /// The `n`th live session.
    fn session_at(&self, n: usize) -> Option<SessionStats>;
    /// The live session with a validated direct path from `remote` that `keep` accepts, the lowest session id of
    /// those, found without a walk of the sessions.
    fn session_from(&self, remote: &SocketAddr, keep: &dyn Fn(SessionId) -> bool) -> Option<SessionId>;
    /// The next trace record of the endpoint (always `None` without the endpoint's `trace` feature).
    fn poll_trace(&mut self) -> Option<TraceRecord>;
    /// Add an interface; `None` when the table is full.
    fn add_iface(&mut self, local: SocketAddr) -> Option<IfaceId>;
    /// An interface came up, went down or changed its address.
    fn iface_event(&mut self, now: u64, id: IfaceId, ev: IfaceEvent);
}

impl<
    P,
    S,
    const N: usize,
    const C: usize,
    const F: usize,
    const NP: usize,
    const K: usize,
    const D: usize,
    const PK: usize,
    const TK: usize,
    const CT: usize,
> Ep for Endpoint<'_, '_, P, S, N, C, F, NP, K, D, PK, TK, CT>
where
    P: Provider,
    S: StreamSource,
{
    fn handle_datagram(&mut self, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]) {
        Endpoint::handle_datagram(self, now, local, remote, buf);
    }

    fn poll_transmit(&mut self, now: u64, out: &mut [u8]) -> Option<Transmit> {
        Endpoint::poll_transmit(self, now, out)
    }

    fn transmit_waiting(&self) -> bool {
        Endpoint::transmit_waiting(self)
    }

    fn poll_event(&mut self) -> Option<Event> {
        Endpoint::poll_event(self)
    }

    fn events_waiting(&self) -> bool {
        Endpoint::events_waiting(self)
    }

    fn poll_timeout(&self) -> Option<u64> {
        Endpoint::poll_timeout(self)
    }

    fn handle_timeout(&mut self, now: u64) {
        Endpoint::handle_timeout(self, now);
    }

    fn register_alpn(&mut self, alpn: &[u8]) -> bool {
        Endpoint::register_alpn(self, alpn)
    }

    fn read_chunk(&self, session: SessionId, stream: StreamId) -> Option<&[u8]> {
        match self.query(Query::Read { session, stream }) {
            Answer::Chunk(c) => Some(c),
            _ => None,
        }
    }

    fn read_at(&self, session: SessionId, stream: StreamId, offset: u64) -> Option<&[u8]> {
        match self.query(Query::ReadAt {
            session,
            stream,
            offset,
        }) {
            Answer::Chunk(c) => Some(c),
            _ => None,
        }
    }

    fn stored_after(&self, session: SessionId, stream: StreamId, from: u64) -> Option<Range<u64>> {
        match self.query(Query::StoredAfter { session, stream, from }) {
            Answer::Stored(r) => Some(r),
            _ => None,
        }
    }

    fn send_state(&self, session: SessionId, stream: StreamId) -> Option<SendState> {
        match self.query(Query::SendState { session, stream }) {
            Answer::SendState(s) => Some(s),
            _ => None,
        }
    }

    fn in_flight(&self, session: SessionId) -> Option<u64> {
        match self.query(Query::InFlight(session)) {
            Answer::InFlight(n) => Some(n),
            _ => None,
        }
    }

    fn read_extension(&mut self, out: &mut [u8]) -> Result<Option<(SessionId, u64, usize)>, CommandError> {
        Endpoint::read_extension(self, out)
    }

    fn session_at(&self, n: usize) -> Option<SessionStats> {
        match self.query(Query::SessionAt(n)) {
            Answer::Stats(s) => Some(s),
            _ => None,
        }
    }

    fn session_from(&self, remote: &SocketAddr, keep: &dyn Fn(SessionId) -> bool) -> Option<SessionId> {
        Endpoint::session_from(self, remote, keep)
    }

    fn poll_trace(&mut self) -> Option<TraceRecord> {
        Endpoint::poll_trace(self)
    }

    fn add_iface(&mut self, local: SocketAddr) -> Option<IfaceId> {
        Endpoint::add_iface(self, local)
    }

    fn iface_event(&mut self, now: u64, id: IfaceId, ev: IfaceEvent) {
        Endpoint::iface_event(self, now, id, ev);
    }
}
