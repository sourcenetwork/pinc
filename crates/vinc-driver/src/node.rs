//! The endpoint behind a trait object, so the engine does not carry the session capacity in its type.
//!
//! The endpoint's tables are const-generic. The engine reaches it through this trait, one virtual call per datagram,
//! command or timer, so [`Engine`](crate::Engine) is the same type whatever the capacity and only the code that builds
//! the shape (see [`start`]) is repeated per entry of [`CAPACITIES`](crate::CAPACITIES).
//!
//! Invariants: every method forwards to the endpoint method of the same name and adds nothing.

use std::net::SocketAddr;

use vinc_core::{
    Answer, Command, CommandError, Event, IfaceEvent, IfaceId, NodeStats, Query, Reply, SessionId, Transmit,
};
use vinc_security::PrekeyInfo;
use vinc_transport::stream::NoSource;

use crate::mem::Ep;

/// What the engine asks of the endpoint.
pub(crate) trait Node {
    fn handle_datagram(&mut self, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]);
    fn handle_timeout(&mut self, now: u64);
    fn poll_transmit(&mut self, now: u64, out: &mut [u8]) -> Option<Transmit>;
    fn poll_timeout(&self) -> Option<u64>;
    fn poll_event(&mut self) -> Option<Event>;
    fn command(&mut self, now: u64, c: Command<'_, NoSource>) -> Result<Reply, CommandError>;
    fn query(&self, q: Query) -> Answer<'_>;
    fn read_datagram(&mut self, session: SessionId, out: &mut [u8]) -> Result<Option<usize>, CommandError>;
    fn node_stats(&self) -> NodeStats;
    fn set_prekey(&mut self, prekey: PrekeyInfo);
    fn register_alpn(&mut self, alpn: &[u8]) -> bool;
    fn iface_event(&mut self, now: u64, id: IfaceId, ev: IfaceEvent);
}

impl<const K: usize, const D: usize> Node for Ep<'_, '_, K, D> {
    fn handle_datagram(&mut self, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]) {
        Self::handle_datagram(self, now, local, remote, buf);
    }
    fn handle_timeout(&mut self, now: u64) {
        Self::handle_timeout(self, now);
    }
    fn poll_transmit(&mut self, now: u64, out: &mut [u8]) -> Option<Transmit> {
        Self::poll_transmit(self, now, out)
    }
    fn poll_timeout(&self) -> Option<u64> {
        Self::poll_timeout(self)
    }
    fn poll_event(&mut self) -> Option<Event> {
        Self::poll_event(self)
    }
    fn command(&mut self, now: u64, c: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        Self::command(self, now, c)
    }
    fn query(&self, q: Query) -> Answer<'_> {
        Self::query(self, q)
    }
    fn read_datagram(&mut self, session: SessionId, out: &mut [u8]) -> Result<Option<usize>, CommandError> {
        Self::read_datagram(self, session, out)
    }
    fn node_stats(&self) -> NodeStats {
        Self::node_stats(self)
    }
    fn set_prekey(&mut self, prekey: PrekeyInfo) {
        Self::set_prekey(self, prekey);
    }
    fn register_alpn(&mut self, alpn: &[u8]) -> bool {
        Self::register_alpn(self, alpn)
    }
    fn iface_event(&mut self, now: u64, id: IfaceId, ev: IfaceEvent) {
        Self::iface_event(self, now, id, ev);
    }
}
