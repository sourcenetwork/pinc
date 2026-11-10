//! The extension point for the layers above the endpoint, and the framing of a protocol tag on a stream.
//!
//! A higher layer (values, broadcast, reconcile, membership, delay-tolerant delivery) is a [`Protocol`]: it names an
//! ALPN and serves each session the peers open on it. [`Endpoint::register`](crate::Endpoint::register) hands the
//! ALPN to the endpoint and returns a [`Registered`]; the host takes each session from it and spawns the protocol's
//! future on its own executor, as the library spawns nothing. A second
//! protocol to a peer you are already connected to is a sub-session and costs no round trip: dial it with
//! [`Connection::open_protocol`](crate::Connection::open_protocol).
//!
//! One ALPN per protocol is limited by the endpoint (four in all), so a protocol that needs many sub-protocols names
//! them per stream: a tag, written as one length byte (1 to 64) and the tag bytes at the start of the stream.
//!
//! Invariants: a tag is never empty and never longer than 64 bytes; reading a tag consumes exactly its bytes.

use std::future::Future;
use std::sync::{Arc, Weak};

use crate::conn::Connection;
use crate::drive::Shared;
use crate::error::{Error, ErrorKind, Result};
use crate::host::Hosted;
use crate::stream::{RecvStream, SendStream};

/// The longest stream tag.
pub const MAX_TAG: usize = 64;

/// A protocol served on its own ALPN.
pub trait Protocol: Send + Sync + 'static {
    /// The ALPN: 1 to 32 bytes.
    fn alpn(&self) -> &'static [u8];

    /// Serve one session a peer opened. The host spawns the future; the session closes when the last handle to it is
    /// dropped.
    fn serve<H: Hosted + 'static>(self: Arc<Self>, conn: Connection<H>) -> impl Future<Output = ()>;
}

/// The sessions a registered [`Protocol`] is to serve. Holds the endpoint only weakly, so a registered protocol does not
/// keep the endpoint alive.
pub struct Registered<P, H: Hosted> {
    shared: Weak<Shared<H>>,
    route: usize,
    protocol: Arc<P>,
}

impl<P: Protocol, H: Hosted> Registered<P, H> {
    pub(crate) fn new(shared: &Arc<Shared<H>>, route: usize, protocol: Arc<P>) -> Self {
        Self {
            shared: Arc::downgrade(shared),
            route,
            protocol,
        }
    }

    /// The protocol.
    pub fn protocol(&self) -> Arc<P> {
        Arc::clone(&self.protocol)
    }

    /// Wait for the next session a peer opened on the protocol's ALPN. `None` once the endpoint stopped. The host runs
    /// `registered.protocol().serve(conn)` on its executor.
    pub async fn accept(&self) -> Option<Connection<H>> {
        let shared = self.shared.upgrade()?;
        let info = shared.run(|core, _| core.accept_route(self.route)).await?;
        Some(Connection::new(&shared, info))
    }
}

/// Write a tag at the start of `send`.
///
/// # Errors
/// [`crate::ErrorKind::Config`] if the tag is empty or longer than [`MAX_TAG`]; the stream's error otherwise.
pub async fn write_tag<H: Hosted>(send: &mut SendStream<H>, tag: &[u8]) -> Result<()> {
    let len = u8::try_from(tag.len()).ok().filter(|l| (1..=64).contains(l));
    let Some(len) = len else {
        return Err(Error::new(ErrorKind::Config, "a stream tag is 1 to 64 bytes"));
    };
    let mut head = Vec::with_capacity(tag.len() + 1);
    head.push(len);
    head.extend_from_slice(tag);
    send.write_all(&head).await
}

/// Read the tag at the start of `recv`.
///
/// # Errors
/// [`crate::ErrorKind::Config`] if the tag length is not 1 to 64; the stream's error otherwise.
pub async fn read_tag<H: Hosted>(recv: &mut RecvStream<H>) -> Result<Vec<u8>> {
    let mut len = [0u8; 1];
    recv.read_exact(&mut len).await?;
    let [n] = len;
    let n = usize::from(n);
    if !(1..=MAX_TAG).contains(&n) {
        return Err(Error::new(ErrorKind::Config, "a stream tag is 1 to 64 bytes"));
    }
    let mut tag = vec![0u8; n];
    recv.read_exact(&mut tag).await?;
    Ok(tag)
}
