//! The blocking mirror of the async API, for threads that are not async and for scripts.
//!
//! Every type wraps its async twin and every method runs the twin's future to completion on the calling thread with
//! [`crate::block_on`], so the two cannot differ. Streams also implement `std::io::Read` and `Write`.
//!
//! Invariants: a blocking call parks only the calling thread; the engine thread never runs a blocking call.

use std::io;
use std::net::SocketAddr;

use vinc_crypto::NodeId;
use vinc_driver::Result;

use crate::addr::NodeAddr;
use crate::conn::{ConnStats, Connection as AConn};
use crate::endpoint::{Direction, Endpoint as AEndpoint};
use crate::rt::block_on;
use crate::stream::{RecvStream as ARecv, SendStream as ASend};

/// The blocking endpoint.
#[derive(Debug, Clone)]
pub struct Endpoint(AEndpoint);

impl From<AEndpoint> for Endpoint {
    fn from(e: AEndpoint) -> Self {
        Self(e)
    }
}

impl Endpoint {
    /// The async endpoint.
    pub const fn as_async(&self) -> &AEndpoint {
        &self.0
    }

    /// See [`crate::Endpoint::id`].
    pub fn id(&self) -> NodeId {
        self.0.id()
    }

    /// See [`crate::Endpoint::sign`].
    ///
    /// # Errors
    /// As the async method.
    pub fn sign(&self, data: &[u8]) -> Result<Vec<u8>> {
        self.0.sign(data)
    }

    /// See [`crate::Endpoint::addr`].
    pub fn addr(&self) -> NodeAddr {
        self.0.addr()
    }

    /// See [`crate::Endpoint::local_addr`].
    pub fn local_addr(&self) -> SocketAddr {
        self.0.local_addr()
    }

    /// See [`crate::Endpoint::connect`].
    ///
    /// # Errors
    /// As the async method.
    pub fn connect(&self, to: impl Into<NodeAddr>, alpn: &[u8]) -> Result<Connection> {
        block_on(self.0.connect(to, alpn)).map(Connection)
    }

    /// See [`crate::Endpoint::accept`]; blocks until a session arrives.
    pub fn accept(&self) -> Option<(NodeId, Vec<u8>, Connection)> {
        let inc = block_on(self.0.accept())?;
        let (node, alpn) = (inc.remote(), inc.alpn().to_vec());
        Some((node, alpn, Connection(inc.into_connection())))
    }

    /// See [`crate::Endpoint::peers`].
    ///
    /// # Errors
    /// As the async method.
    pub fn peers(&self) -> Result<Vec<NodeId>> {
        block_on(self.0.peers())
    }

    /// See [`crate::Endpoint::close_peer`].
    pub fn close_peer(&self, peer: &NodeId) {
        self.0.close_peer(peer);
    }

    /// See [`crate::Endpoint::admit`].
    pub fn admit(&self, peer: &NodeId, alpn: &[u8], dir: Direction) -> bool {
        self.0.admit(peer, alpn, dir)
    }

    /// See [`crate::Endpoint::close`].
    pub fn close(&self) {
        block_on(self.0.close());
    }
}

/// The blocking connection.
#[derive(Debug, Clone)]
pub struct Connection(AConn);

impl Connection {
    /// The async connection.
    pub const fn as_async(&self) -> &AConn {
        &self.0
    }

    /// See [`crate::Connection::remote`].
    pub fn remote(&self) -> NodeId {
        self.0.remote()
    }

    /// See [`crate::Connection::alpn`].
    pub fn alpn(&self) -> &[u8] {
        self.0.alpn()
    }

    /// See [`crate::Connection::open_bi`].
    ///
    /// # Errors
    /// As the async method.
    pub fn open_bi(&self) -> Result<(SendStream, RecvStream)> {
        block_on(self.0.open_bi()).map(|(s, r)| (SendStream(s), RecvStream(r)))
    }

    /// See [`crate::Connection::open_uni`].
    ///
    /// # Errors
    /// As the async method.
    pub fn open_uni(&self) -> Result<SendStream> {
        block_on(self.0.open_uni()).map(SendStream)
    }

    /// See [`crate::Connection::accept_bi`].
    ///
    /// # Errors
    /// As the async method.
    pub fn accept_bi(&self) -> Result<(SendStream, RecvStream)> {
        block_on(self.0.accept_bi()).map(|(s, r)| (SendStream(s), RecvStream(r)))
    }

    /// See [`crate::Connection::accept_uni`].
    ///
    /// # Errors
    /// As the async method.
    pub fn accept_uni(&self) -> Result<RecvStream> {
        block_on(self.0.accept_uni()).map(RecvStream)
    }

    /// See [`crate::Connection::read_datagram`].
    ///
    /// # Errors
    /// As the async method.
    pub fn read_datagram(&self) -> Result<Vec<u8>> {
        block_on(self.0.read_datagram())
    }

    /// See [`crate::Connection::send_datagram`].
    ///
    /// # Errors
    /// As the async method.
    pub fn send_datagram(&self, data: &[u8]) -> Result<()> {
        block_on(self.0.send_datagram(data))
    }

    /// See [`crate::Connection::stats`].
    ///
    /// # Errors
    /// As the async method.
    pub fn stats(&self) -> Result<ConnStats> {
        block_on(self.0.stats())
    }

    /// See [`crate::Connection::close`].
    pub fn close(&self, code: u64) {
        self.0.close(code);
    }

    /// See [`crate::Connection::closed`].
    pub fn closed(&self) -> vinc_driver::Error {
        block_on(self.0.closed())
    }
}

/// The blocking send half; also `std::io::Write`.
#[derive(Debug)]
pub struct SendStream(ASend);

impl SendStream {
    /// See [`crate::SendStream::write_all`].
    ///
    /// # Errors
    /// As the async method.
    pub fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        block_on(self.0.write_all(buf))
    }

    /// See [`crate::SendStream::finish`].
    ///
    /// # Errors
    /// As the async method.
    pub fn finish(&mut self) -> Result<()> {
        block_on(self.0.finish())
    }

    /// See [`crate::SendStream::reset`].
    pub fn reset(&mut self, code: u64) {
        self.0.reset(code);
    }
}

impl io::Write for SendStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        block_on(self.0.write(buf)).map_err(Into::into)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// The blocking receive half; also `std::io::Read`.
#[derive(Debug)]
pub struct RecvStream(ARecv);

impl RecvStream {
    /// See [`crate::RecvStream::read_exact`].
    ///
    /// # Errors
    /// As the async method.
    pub fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        block_on(self.0.read_exact(buf))
    }

    /// See [`crate::RecvStream::read_to_end`].
    ///
    /// # Errors
    /// As the async method.
    pub fn read_to_end(&mut self, limit: usize) -> Result<Vec<u8>> {
        block_on(self.0.read_to_end(limit))
    }

    /// See [`crate::RecvStream::stop`].
    pub fn stop(&mut self, code: u64) {
        self.0.stop(code);
    }
}

impl io::Read for RecvStream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        block_on(self.0.read(buf)).map(|n| n.unwrap_or(0)).map_err(Into::into)
    }
}
