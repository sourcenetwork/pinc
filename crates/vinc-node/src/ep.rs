//! The endpoint as the node uses it: one trait over the endpoint's thirteen type and const parameters, so the node
//! carries one parameter instead of thirteen.
//!
//! The trait adds to the connectivity client's `Port` the calls only the node's own loop needs: datagrams in and out,
//! events, the clock, the protocol registry and the reading of a stream. [`Endpoint`] implements it by forwarding.

use core::net::SocketAddr;

use vinc_connect::client::Port;
use vinc_core::{Answer, Endpoint, Event, Query, SessionId, SessionStats, TraceRecord, Transmit};
use vinc_crypto::Provider;
use vinc_transport::stream::{StreamId, StreamSource};

/// The endpoint calls the node makes besides the commands and queries of `Port`.
pub trait Ep: Port {
    /// A datagram arrived.
    fn handle_datagram(&mut self, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]);
    /// The next datagram to send.
    fn poll_transmit(&mut self, now: u64, out: &mut [u8]) -> Option<Transmit>;
    /// The next event.
    fn poll_event(&mut self) -> Option<Event>;
    /// The next deadline.
    fn poll_timeout(&self) -> Option<u64>;
    /// Time passed.
    fn handle_timeout(&mut self, now: u64);
    /// Accept sessions for a protocol.
    fn register_alpn(&mut self, alpn: &[u8]) -> bool;
    /// The next received bytes of a stream, not yet consumed.
    fn read_chunk(&self, session: SessionId, stream: StreamId) -> Option<&[u8]>;
    /// The `n`th live session.
    fn session_at(&self, n: usize) -> Option<SessionStats>;
    /// The next trace record of the endpoint (always `None` without the endpoint's `trace` feature).
    fn poll_trace(&mut self) -> Option<TraceRecord>;
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

    fn poll_event(&mut self) -> Option<Event> {
        Endpoint::poll_event(self)
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

    fn session_at(&self, n: usize) -> Option<SessionStats> {
        match self.query(Query::SessionAt(n)) {
            Answer::Stats(s) => Some(s),
            _ => None,
        }
    }

    fn poll_trace(&mut self) -> Option<TraceRecord> {
        Endpoint::poll_trace(self)
    }
}
