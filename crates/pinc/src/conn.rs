//! Connections: a session with one peer for one protocol.
//!
//! A [`Connection`] is a cheap handle (`Clone`, `!Send`: it stays on the thread that built the endpoint). The session lives while any
//! handle to it, or to a stream of it, lives; dropping the last one closes it with code 0 (the close leaves with the
//! next future that runs the endpoint). Streams, datagrams, counters and the close are all operations on the handle.
//!
//! Invariants: an operation on a session that ended fails with the reason it ended; no operation holds a borrow of the
//! core while it waits; a dial whose future is dropped before it finishes closes the session it started, so nothing is left open
//! that no one holds.

use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;
use core::net::SocketAddr;
use core::time::Duration;

use pinc_core::SessionId;
use pinc_crypto::NodeId;

use crate::drive::Shared;
use crate::engine::{SessInfo, Try};
use crate::error::{Error, Result};
use crate::host::Hosted;
use crate::protocol::{read_tag, write_tag};
use crate::stream::{RecvStream, SendStream};

pub(crate) struct ConnInner<H: Hosted> {
    pub(crate) sh: Rc<Shared<H>>,
    pub(crate) info: Rc<SessInfo>,
}

impl<H: Hosted> Drop for ConnInner<H> {
    fn drop(&mut self) {
        if self.info.ended.get().is_none() {
            let now = self.sh.now();
            if let Some(mut core) = self.sh.lock() {
                core.close_session(now, self.info.id, 0);
            }
        }
    }
}

/// A connection to one peer for one protocol.
pub struct Connection<H: Hosted>(pub(crate) Rc<ConnInner<H>>);

impl<H: Hosted> Clone for Connection<H> {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

impl<H: Hosted> core::fmt::Debug for Connection<H> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Connection")
            .field("session", &self.0.info.id)
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
pub struct Incoming<H: Hosted> {
    conn: Connection<H>,
}

impl<H: Hosted> Clone for Incoming<H> {
    fn clone(&self) -> Self {
        Self {
            conn: self.conn.clone(),
        }
    }
}

impl<H: Hosted> core::fmt::Debug for Incoming<H> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Incoming").field("conn", &self.conn).finish()
    }
}

impl<H: Hosted> Incoming<H> {
    /// The peer, as the handshake authenticated it.
    pub fn remote(&self) -> NodeId {
        self.conn.remote()
    }

    /// The protocol the peer asked for.
    pub fn alpn(&self) -> &[u8] {
        self.conn.alpn()
    }

    /// The connection.
    pub const fn connection(&self) -> &Connection<H> {
        &self.conn
    }

    /// Take the connection.
    pub fn into_connection(self) -> Connection<H> {
        self.conn
    }
}

/// A dial in flight: if the future that started it is dropped, the dial is given up.
struct DialGuard<'a, H: Hosted> {
    sh: &'a Shared<H>,
    session: Option<SessionId>,
}

impl<H: Hosted> Drop for DialGuard<'_, H> {
    fn drop(&mut self) {
        if let Some(s) = self.session {
            let now = self.sh.now();
            if let Some(mut core) = self.sh.lock() {
                core.dial_cancel(now, s);
            }
        }
    }
}

impl<H: Hosted> Connection<H> {
    pub(crate) fn new(sh: &Rc<Shared<H>>, info: Rc<SessInfo>) -> Self {
        Self(Rc::new(ConnInner {
            sh: Rc::clone(sh),
            info,
        }))
    }

    pub(crate) fn incoming(sh: &Rc<Shared<H>>, info: Rc<SessInfo>) -> Incoming<H> {
        Incoming {
            conn: Self::new(sh, info),
        }
    }

    /// Dial `node` for `alpn`, trying `addrs`. A peer already connected gets a sub-session at once.
    pub(crate) async fn dial(sh: &Rc<Shared<H>>, node: NodeId, alpn: &[u8], addrs: Vec<SocketAddr>) -> Result<Self> {
        let mut guard = DialGuard { sh, session: None };
        let info = sh
            .run(|core, now| {
                let session = match guard.session {
                    Some(s) => s,
                    None => match core.connect_start(now, node, alpn, &addrs) {
                        Ok(s) => *guard.session.insert(s),
                        Err(e) => return Try::Taken(Err(e)),
                    },
                };
                core.dial_poll(session)
            })
            .await;
        guard.session = None;
        Ok(Self::new(sh, info?))
    }

    /// The peer, as the handshake authenticated it.
    pub fn remote(&self) -> NodeId {
        self.0.info.node
    }

    /// The protocol of this connection.
    pub fn alpn(&self) -> &[u8] {
        self.0.info.alpn.as_bytes()
    }

    /// Whether this node dialed.
    pub fn is_dialer(&self) -> bool {
        self.0.info.dialer
    }

    /// Whether this node's dial resumed an earlier session with a ticket, which saves a round trip and lets data go in
    /// the first flight. Only the dialing side knows; the accepting side reports `false`. Exact once the peer has
    /// answered ([`answered`](Self::answered)); a connection handed over before that reads `false` until then.
    pub fn resumed(&self) -> bool {
        self.0.info.resumed.get()
    }

    /// Open a stream both sides can write. Waits while the connection has no room for another stream.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Busy`] if the peer's stream limit is reached; the reason the connection ended if it did.
    pub async fn open_bi(&self) -> Result<(SendStream<H>, RecvStream<H>)> {
        let id = self.0.sh.run(|core, now| core.open(now, &self.0.info, true)).await?;
        Ok((SendStream::new(&self.0, id), RecvStream::new(&self.0, id)))
    }

    /// Open a stream this side writes and the peer reads.
    ///
    /// # Errors
    /// As [`open_bi`](Self::open_bi).
    pub async fn open_uni(&self) -> Result<SendStream<H>> {
        let id = self.0.sh.run(|core, now| core.open(now, &self.0.info, false)).await?;
        Ok(SendStream::new(&self.0, id))
    }

    /// Open a stream and write `tag` at its start.
    ///
    /// # Errors
    /// As [`open_bi`](Self::open_bi), or [`crate::ErrorKind::Config`] for a tag that is empty or over 64 bytes.
    pub async fn open_bi_tagged(&self, tag: &[u8]) -> Result<(SendStream<H>, RecvStream<H>)> {
        let (mut s, r) = self.open_bi().await?;
        write_tag(&mut s, tag).await?;
        Ok((s, r))
    }

    /// Wait for the next stream the peer opened that both sides can write.
    ///
    /// # Errors
    /// The reason the connection ended.
    pub async fn accept_bi(&self) -> Result<(SendStream<H>, RecvStream<H>)> {
        let id = self.0.sh.run(|core, _| core.accept_stream(&self.0.info, true)).await?;
        Ok((SendStream::new(&self.0, id), RecvStream::new(&self.0, id)))
    }

    /// Wait for the next stream the peer opened that it only writes.
    ///
    /// # Errors
    /// The reason the connection ended.
    pub async fn accept_uni(&self) -> Result<RecvStream<H>> {
        let id = self.0.sh.run(|core, _| core.accept_stream(&self.0.info, false)).await?;
        Ok(RecvStream::new(&self.0, id))
    }

    /// Wait for the next stream the peer opened and read its tag.
    ///
    /// # Errors
    /// As [`accept_bi`](Self::accept_bi), or the error of reading the tag.
    pub async fn accept_bi_tagged(&self) -> Result<(Vec<u8>, SendStream<H>, RecvStream<H>)> {
        let (s, mut r) = self.accept_bi().await?;
        let tag = read_tag(&mut r).await?;
        Ok((tag, s, r))
    }

    /// Send an unreliable datagram. The call returns once the endpoint has sent it to the host.
    ///
    /// # Errors
    /// [`crate::ErrorKind::TooLarge`] if it does not fit one packet; the reason the connection ended if it did.
    pub async fn send_datagram(&self, data: &[u8]) -> Result<()> {
        self.0
            .sh
            .run(|core, now| Try::Done(core.send_datagram(now, &self.0.info, data)))
            .await
    }

    /// Wait for the next datagram the peer sent into `buf`, in the order they arrived, and return its length. The
    /// endpoint holds a bounded number of datagrams for a session and drops the oldest when a new one arrives, counting
    /// each drop. Allocates nothing. Cancel safe: the datagram is taken out in the poll that returns it, so a future
    /// dropped after that loses nothing, and one dropped while it waits leaves the datagram queued.
    ///
    /// # Errors
    /// [`crate::ErrorKind::TooLarge`] if the datagram does not fit `buf` (it stays queued); the reason the connection
    /// ended; datagrams still queued when it ended are dropped with it.
    pub async fn recv_datagram(&self, buf: &mut [u8]) -> Result<usize> {
        self.0.sh.run(|core, _| core.read_datagram(&self.0.info, buf)).await
    }

    /// Wait for the next datagram the peer sent, in the order they arrived. Allocates the datagram; use
    /// [`recv_datagram`](Self::recv_datagram) to reuse a buffer. Cancel safe, as [`recv_datagram`](Self::recv_datagram).
    ///
    /// # Errors
    /// The reason the connection ended; datagrams still queued when it ended are dropped with it.
    pub async fn read_datagram(&self) -> Result<Vec<u8>> {
        let mut buf = vec![0u8; 2048];
        let n = match self.recv_datagram(&mut buf).await {
            Err(e) if e.kind() == crate::ErrorKind::TooLarge => {
                buf.resize(pinc_core::MAX_DATAGRAM, 0);
                self.recv_datagram(&mut buf).await?
            }
            r => r?,
        };
        buf.truncate(n);
        Ok(buf)
    }

    /// Open a second protocol to the same peer. It costs no round trip, as the peer is already connected.
    ///
    /// # Errors
    /// As [`Endpoint::connect`](crate::Endpoint::connect).
    pub async fn open_protocol(&self, alpn: &[u8]) -> Result<Self> {
        Self::dial(&self.0.sh, self.remote(), alpn, Vec::new()).await
    }

    /// The counters of the connection.
    ///
    /// # Errors
    /// The reason the connection ended if it did.
    pub async fn stats(&self) -> Result<ConnStats> {
        let s = self.0.sh.run(|core, _| Try::Done(core.stats(&self.0.info))).await?;
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
    pub async fn close(&self, code: u64) {
        let id = self.0.info.id;
        self.0
            .sh
            .run(|core, now| {
                core.close_session(now, id, code);
                Try::Done(())
            })
            .await;
    }

    /// Wait until the peer has been heard on this connection. A dial towards a peer with a fresh cached allow, and a
    /// protocol opened over a session the peer already has, are handed over before the peer answers, so a peer that
    /// stopped looks connected until the dial ends: as unanswered after its 4th unanswered first flight (3 s for a
    /// resume and 7.5 s for a full handshake at the 500 ms first delay), or, on a thin node, at the 60 s handshake
    /// limit. This returns at once for an accepted connection and for a dial handed over after its handshake. A
    /// protocol opened over another session hears the peer once it answers what this side sends, or sends something
    /// itself.
    ///
    /// # Errors
    /// The reason the connection ended before the peer was heard.
    pub async fn answered(&self) -> Result<()> {
        self.0.sh.run(|core, _| core.answered(&self.0.info)).await
    }

    /// Whether the peer has been heard on this connection; see [`answered`](Self::answered).
    pub fn is_answered(&self) -> bool {
        self.0.info.answered.get()
    }

    /// Wait until the connection ends and return why.
    pub async fn closed(&self) -> Error {
        self.0.sh.run(|core, _| core.closed(&self.0.info)).await
    }

    /// Why the connection ended, or `None` while it lives.
    pub fn close_reason(&self) -> Option<Error> {
        self.0.info.ended.get().copied()
    }

    /// Whether the endpoint holds unread bytes of `stream` (test probe).
    #[cfg(feature = "trace")]
    #[doc(hidden)]
    pub fn trace_held(&self, stream: u64) -> bool {
        self.0
            .sh
            .lock()
            .is_some_and(|core| core.trace_held(&self.0.info, stream))
    }
}
