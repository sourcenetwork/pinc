//! Connections: a session with one peer for one protocol.
//!
//! A [`Connection`] is a cheap handle (`Clone + Send + Sync`). The session lives while any handle to it, or to a stream
//! of it, lives; dropping the last one closes it with code 0. Streams, datagrams, counters and the close are all
//! operations on the handle.
//!
//! Invariants: an operation on a session that ended fails with the reason it ended; a handle never blocks the engine
//! thread; a dial whose future is dropped before it finishes closes the session it started, so nothing is left open
//! that no one holds.

use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use vinc_crypto::NodeId;
use vinc_driver::{Ctl, Error, ErrorKind, Remote, Request, Result, SessionShared};

use crate::protocol::{read_tag, write_tag};
use crate::stream::{RecvStream, SendStream, halves};

pub(crate) struct ConnInner {
    pub(crate) shared: Arc<SessionShared>,
    pub(crate) remote: Remote,
}

impl Drop for ConnInner {
    fn drop(&mut self) {
        if self.shared.ended.get().is_none() {
            self.remote.ctl(Ctl::Close(self.shared.id, 0));
        }
    }
}

/// A connection to one peer for one protocol.
#[derive(Clone)]
pub struct Connection(pub(crate) Arc<ConnInner>);

impl core::fmt::Debug for Connection {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Connection")
            .field("session", &self.0.shared.id)
            .finish_non_exhaustive()
    }
}

/// The counters of a connection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConnStats {
    /// The peer.
    pub remote: NodeId,
    /// Whether this side dialed.
    pub dialed_by_us: bool,
    /// The smoothed round trip of the active path; zero before the first sample.
    pub rtt: Duration,
    /// The congestion window in bytes.
    pub cwnd: u64,
    /// The datagram size of the active path.
    pub mtu: u16,
    /// Bytes sent.
    pub bytes_sent: u64,
    /// Bytes received.
    pub bytes_received: u64,
    /// Packets sent.
    pub packets_sent: u64,
    /// Packets declared lost.
    pub packets_lost: u64,
    /// The local and remote address of the active path.
    pub route: Option<(SocketAddr, SocketAddr)>,
}

/// A session a peer opened on a protocol this node serves.
#[derive(Debug, Clone)]
pub struct Incoming {
    conn: Connection,
}

impl Incoming {
    /// The peer, as the handshake authenticated it.
    pub fn remote(&self) -> NodeId {
        self.conn.remote()
    }

    /// The protocol the peer asked for.
    pub fn alpn(&self) -> &[u8] {
        self.conn.alpn()
    }

    /// The connection.
    pub const fn connection(&self) -> &Connection {
        &self.conn
    }

    /// Take the connection.
    pub fn into_connection(self) -> Connection {
        self.conn
    }
}

impl Connection {
    pub(crate) fn new(shared: Arc<SessionShared>, remote: Remote) -> Self {
        Self(Arc::new(ConnInner { shared, remote }))
    }

    pub(crate) fn incoming(shared: Arc<SessionShared>, remote: Remote) -> Incoming {
        Incoming {
            conn: Self::new(shared, remote),
        }
    }

    /// Dial `node` for `alpn` through `remote`, trying `addrs`. A peer already connected gets a sub-session at once.
    pub(crate) async fn dial(remote: &Remote, node: NodeId, alpn: &[u8], addrs: Vec<SocketAddr>) -> Result<Self> {
        let alpn = alpn.to_vec();
        let shared = remote
            .call(|reply| Request::Connect {
                node,
                alpn,
                addrs,
                reply,
            })
            .await??;
        Ok(Self::new(shared, remote.clone()))
    }

    /// The peer, as the handshake authenticated it.
    pub fn remote(&self) -> NodeId {
        self.0.shared.node
    }

    /// The protocol of this connection.
    pub fn alpn(&self) -> &[u8] {
        self.0.shared.alpn.as_bytes()
    }

    /// Whether this node dialed.
    pub fn is_dialer(&self) -> bool {
        self.0.shared.dialer
    }

    fn ended(&self) -> Error {
        self.0.shared.ended.get().copied().unwrap_or_else(Error::shutdown)
    }

    /// Open a stream both sides can write.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Busy`] if the peer's stream limit is reached; the reason the connection ended if it did.
    pub async fn open_bi(&self) -> Result<(SendStream, RecvStream)> {
        let session = self.0.shared.id;
        let n = self
            .0
            .remote
            .call(|reply| Request::Open {
                session,
                bidi: true,
                reply,
            })
            .await??;
        match halves(&self.0, n) {
            (Some(s), Some(r)) => Ok((s, r)),
            _ => Err(Error::new(ErrorKind::Busy, "the stream did not open")),
        }
    }

    /// Open a stream this side writes and the peer reads.
    ///
    /// # Errors
    /// As [`open_bi`](Self::open_bi).
    pub async fn open_uni(&self) -> Result<SendStream> {
        let session = self.0.shared.id;
        let n = self
            .0
            .remote
            .call(|reply| Request::Open {
                session,
                bidi: false,
                reply,
            })
            .await??;
        halves(&self.0, n)
            .0
            .ok_or(Error::new(ErrorKind::Busy, "the stream did not open"))
    }

    /// Open a stream and write `tag` at its start.
    ///
    /// # Errors
    /// As [`open_bi`](Self::open_bi), or [`crate::ErrorKind::Config`] for a tag that is empty or over 64 bytes.
    pub async fn open_bi_tagged(&self, tag: &[u8]) -> Result<(SendStream, RecvStream)> {
        let (mut s, r) = self.open_bi().await?;
        write_tag(&mut s, tag).await?;
        Ok((s, r))
    }

    /// Wait for the next stream the peer opened that both sides can write.
    ///
    /// # Errors
    /// The reason the connection ended.
    pub async fn accept_bi(&self) -> Result<(SendStream, RecvStream)> {
        match self.0.shared.accept_bi.recv_async().await {
            Some(n) => match halves(&self.0, n) {
                (Some(s), Some(r)) => Ok((s, r)),
                _ => Err(Error::new(ErrorKind::Busy, "the stream did not open")),
            },
            None => Err(self.ended()),
        }
    }

    /// Wait for the next stream the peer opened that it only writes.
    ///
    /// # Errors
    /// The reason the connection ended.
    pub async fn accept_uni(&self) -> Result<RecvStream> {
        match self.0.shared.accept_uni.recv_async().await {
            Some(n) => halves(&self.0, n)
                .1
                .ok_or(Error::new(ErrorKind::Busy, "the stream did not open")),
            None => Err(self.ended()),
        }
    }

    /// Wait for the next stream the peer opened and read its tag.
    ///
    /// # Errors
    /// As [`accept_bi`](Self::accept_bi), or the error of reading the tag.
    pub async fn accept_bi_tagged(&self) -> Result<(Vec<u8>, SendStream, RecvStream)> {
        let (s, mut r) = self.accept_bi().await?;
        let tag = read_tag(&mut r).await?;
        Ok((tag, s, r))
    }

    /// Send an unreliable datagram.
    ///
    /// # Errors
    /// [`crate::ErrorKind::TooLarge`] if it does not fit one packet; the reason the connection ended if it did.
    pub async fn send_datagram(&self, data: &[u8]) -> Result<()> {
        let session = self.0.shared.id;
        let data = data.to_vec();
        self.0
            .remote
            .call(|reply| Request::Datagram { session, data, reply })
            .await?
    }

    /// Open a second protocol to the same peer. It costs no round trip, as the peer is already connected.
    ///
    /// # Errors
    /// As [`Endpoint::connect`](crate::Endpoint::connect).
    pub async fn open_protocol(&self, alpn: &[u8]) -> Result<Self> {
        Self::dial(&self.0.remote, self.remote(), alpn, Vec::new()).await
    }

    /// The counters of the connection.
    ///
    /// # Errors
    /// The reason the connection ended if it did.
    pub async fn stats(&self) -> Result<ConnStats> {
        let session = self.0.shared.id;
        let s = self.0.remote.call(|reply| Request::Stats { session, reply }).await??;
        Ok(ConnStats {
            remote: self.remote(),
            dialed_by_us: s.dialer,
            rtt: Duration::from_nanos(s.transport.srtt),
            cwnd: s.transport.cwnd,
            mtu: s.transport.mtu,
            bytes_sent: s.transport.bytes_sent,
            bytes_received: s.transport.bytes_received,
            packets_sent: s.transport.packets_sent,
            packets_lost: s.transport.packets_lost,
            route: s.route,
        })
    }

    /// Close the connection with `code`. The peer sees the code; streams fail with the connection's error.
    pub fn close(&self, code: u64) {
        self.0.remote.ctl(Ctl::Close(self.0.shared.id, code));
    }

    /// Wait until the connection ends and return why.
    pub async fn closed(&self) -> Error {
        let _ = self.0.shared.gone.recv_async().await;
        self.ended()
    }

    /// Why the connection ended, or `None` while it lives.
    pub fn close_reason(&self) -> Option<Error> {
        self.0.shared.ended.get().copied()
    }
}
