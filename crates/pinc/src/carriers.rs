//! The relays an endpoint knows and the byte-stream carriers the host opens to them.
//!
//! A [`Relay`] is a node id and the addresses it listens on. The endpoint talks to a relay over UDP (address discovery,
//! lookups) and over a reliable byte stream, a carrier, that the host opens: the TCP connect, or the HTTP upgrade of
//! a WebSocket, are the host's work, as the socket is. The endpoint sees only the finished stream through four host
//! closures, set with [`Builder::carriers`](crate::Builder::carriers): `open`, `read`, `write` and `close`. The buffers
//! are owned and come back with the result (see [`CarrierKind`] for the convention), because an operation may outlive
//! the future that started it.
//!
//! A read that is dropped before it completes must lose no byte, as for the datagram receive (true of readiness-based
//! reads). A write that is dropped before it completes may have sent part of its buffer, so the endpoint closes that
//! carrier and the connectivity layer opens it again; nothing else is lost.
//!
//! Invariants: [`Relay`] is plain data; the closures are called only from the future that drives the endpoint.

use alloc::format;
use alloc::string::String;
use alloc::string::ToString;
use alloc::vec::Vec;
use core::future::{Future, pending, ready};
use core::marker::PhantomData;
use core::net::SocketAddr;

use pinc_connect::client::RelayCfg;
use pinc_crypto::NodeId;

use crate::addr::node_to_string;
use crate::carrier::CarrierKind;
use crate::platform::{Platform, System};

/// A relay: where to reach it, by UDP and by carrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Relay {
    /// The relay's node id.
    pub id: NodeId,
    /// Its UDP address: address discovery, lookups and the hub session.
    pub udp: Option<SocketAddr>,
    /// Its TCP carrier address.
    pub tcp: Option<SocketAddr>,
    /// Its WebSocket carrier address.
    pub ws: Option<SocketAddr>,
    /// The host's WebSocket delivers whole messages, as a browser's does: the carrier kind is
    /// [`CarrierKind::WsMessages`] instead of [`CarrierKind::Ws`].
    pub messages: bool,
    /// The endpoint's home relay whatever the round trips (the deployment's own relay): see [`Relay::home`].
    pub home: bool,
}

impl Relay {
    /// A relay with no address yet.
    pub const fn new(id: NodeId) -> Self {
        Self {
            id,
            udp: None,
            tcp: None,
            ws: None,
            messages: false,
            home: false,
        }
    }

    /// Pin this relay as the endpoint's home: the relay its record names and its first stop, taken over one with a lower
    /// round trip once it has answered a probe and is healthy. While it fails the home moves as without a pin and comes
    /// back with its next answer. Of several relays marked so, the first in [`relays`](crate::Builder::relays) is the
    /// home.
    #[must_use]
    pub const fn home(mut self) -> Self {
        self.home = true;
        self
    }

    /// Set the UDP address.
    #[must_use]
    pub const fn with_udp(mut self, addr: SocketAddr) -> Self {
        self.udp = Some(addr);
        self
    }

    /// Set the TCP carrier address.
    #[must_use]
    pub const fn with_tcp(mut self, addr: SocketAddr) -> Self {
        self.tcp = Some(addr);
        self
    }

    /// Set the WebSocket carrier address.
    #[must_use]
    pub const fn with_ws(mut self, addr: SocketAddr) -> Self {
        self.ws = Some(addr);
        self
    }

    /// The host's WebSocket delivers whole messages (a browser).
    #[must_use]
    pub const fn with_messages(mut self) -> Self {
        self.messages = true;
        self
    }

    /// The relay as a URL for a [`NodeAddr`](crate::NodeAddr): `relay://<id>@<address>`, the first address it has.
    pub fn url(&self) -> String {
        let at = self
            .udp
            .or(self.tcp)
            .or(self.ws)
            .map(|a| a.to_string())
            .unwrap_or_default();
        format!("relay://{}@{at}", node_to_string(&self.id))
    }

    pub(crate) const fn cfg(&self) -> RelayCfg {
        RelayCfg {
            id: self.id,
            udp: self.udp,
            tcp: self.tcp,
            ws: self.ws,
        }
    }

    /// The carrier kind used for a stream of connectivity kind `ws`.
    pub(crate) const fn kind(&self, ws: bool) -> CarrierKind {
        match (ws, self.messages) {
            (false, _) => CarrierKind::Tcp,
            (true, false) => CarrierKind::Ws,
            (true, true) => CarrierKind::WsMessages,
        }
    }
}

/// The host's carriers: open a byte stream to a relay, read it, write it, close it. `Pf` is the host's
/// [`Platform`], whose error the operations return.
pub trait Carriers<Pf: Platform = System> {
    /// A carrier the host opened.
    type Stream;

    /// The host gave no carriers: the driver fails an open itself, with no error value to make.
    #[doc(hidden)]
    const NONE: bool = false;

    /// Open a carrier of `kind` to `relay`.
    fn open(&self, relay: &Relay, kind: CarrierKind) -> impl Future<Output = Result<Self::Stream, Pf::Error>>;

    /// Fill at most `buf.len()` bytes of `buf` from its start and return the count; the length of the vector does not
    /// change and what it holds past the count is unspecified. Zero means the peer closed.
    fn read(&self, stream: &Self::Stream, buf: Vec<u8>) -> impl Future<Output = (Result<usize, Pf::Error>, Vec<u8>)>;

    /// Write `buf` from offset `from`; returns how many bytes went out.
    fn write(
        &self,
        stream: &Self::Stream,
        buf: Vec<u8>,
        from: usize,
    ) -> impl Future<Output = (Result<usize, Pf::Error>, Vec<u8>)>;

    /// End the carrier.
    fn close(&self, stream: Self::Stream) -> impl Future<Output = ()>;
}

/// No carriers: the host gave none, so a relay is reached by UDP only and an open fails at once.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoCarriers;

// The driver reads `NONE` and fails the open itself, so these never run to an end: a platform's error type may be
// one that no value of can be made (`Infallible`).
impl<Pf: Platform> Carriers<Pf> for NoCarriers {
    type Stream = ();
    const NONE: bool = true;

    fn open(&self, _relay: &Relay, _kind: CarrierKind) -> impl Future<Output = Result<(), Pf::Error>> {
        pending()
    }

    fn read(&self, _stream: &(), _buf: Vec<u8>) -> impl Future<Output = (Result<usize, Pf::Error>, Vec<u8>)> {
        pending()
    }

    fn write(
        &self,
        _stream: &(),
        _buf: Vec<u8>,
        _from: usize,
    ) -> impl Future<Output = (Result<usize, Pf::Error>, Vec<u8>)> {
        pending()
    }

    fn close(&self, _stream: ()) -> impl Future<Output = ()> {
        ready(())
    }
}

/// The host's carriers as four async closures; made by [`Builder::carriers`](crate::Builder::carriers).
pub struct CarrierFns<O, R, W, C, St> {
    open: O,
    read: R,
    write: W,
    close: C,
    _stream: PhantomData<fn() -> St>,
}

impl<O, R, W, C, St> CarrierFns<O, R, W, C, St> {
    pub(crate) const fn new(open: O, read: R, write: W, close: C) -> Self {
        Self {
            open,
            read,
            write,
            close,
            _stream: PhantomData,
        }
    }
}

impl<O, R, W, C, St> core::fmt::Debug for CarrierFns<O, R, W, C, St> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("CarrierFns")
    }
}

impl<Pf, O, R, W, C, St> Carriers<Pf> for CarrierFns<O, R, W, C, St>
where
    Pf: Platform,
    O: AsyncFn(&Relay, CarrierKind) -> Result<St, Pf::Error>,
    R: AsyncFn(&St, Vec<u8>) -> (Result<usize, Pf::Error>, Vec<u8>),
    W: AsyncFn(&St, Vec<u8>, usize) -> (Result<usize, Pf::Error>, Vec<u8>),
    C: AsyncFn(St),
{
    type Stream = St;

    fn open(&self, relay: &Relay, kind: CarrierKind) -> impl Future<Output = Result<St, Pf::Error>> {
        (self.open)(relay, kind)
    }

    fn read(&self, stream: &St, buf: Vec<u8>) -> impl Future<Output = (Result<usize, Pf::Error>, Vec<u8>)> {
        (self.read)(stream, buf)
    }

    fn write(
        &self,
        stream: &St,
        buf: Vec<u8>,
        from: usize,
    ) -> impl Future<Output = (Result<usize, Pf::Error>, Vec<u8>)> {
        (self.write)(stream, buf, from)
    }

    fn close(&self, stream: St) -> impl Future<Output = ()> {
        (self.close)(stream)
    }
}
