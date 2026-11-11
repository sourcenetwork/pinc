//! The host's I/O for a relay: async closures for the UDP socket, for the carrier streams and for the clock.
//!
//! The relay opens no socket and starts no timer. The host passes:
//!
//! - [`Udp`]: `recv` fills a buffer with one datagram and returns its length and sender; `send` sends one datagram.
//! - [`Carriers`]: `accept` waits for the next byte stream a member opened and says how its bytes travel
//!   ([`CarrierKind`]), `read` and `write` follow the buffer convention of [`crate::carrier`], and `close` ends a
//!   stream the relay is done with. The host has done the TCP accept, or the HTTP upgrade of a WebSocket.
//! - [`Clock`]: a clock in nanoseconds since the Unix epoch that never goes backward, and a sleep until an instant of it.
//!
//! The closures may borrow from the caller. The stream type is the host's own; the relay keeps it in an `Rc` while an
//! operation on it is in flight and calls `close` with the owned value when the last operation has been dropped.
//! Dropping the future of [`Relay::run`](super::Relay::run) drops every stream without calling `close`, so a stream
//! type whose drop ends the connection (a socket) closes its carriers at once.

use alloc::vec::Vec;
use core::marker::PhantomData;
use core::net::SocketAddr;

use crate::carrier::CarrierKind;
use crate::error::Result;

mod sealed {
    pub trait Sealed {}
}

/// The UDP side: one datagram per call.
#[derive(Debug)]
pub struct Udp<R, S> {
    pub(crate) recv: R,
    pub(crate) send: S,
}

impl<R, S> Udp<R, S>
where
    R: AsyncFn(&mut [u8]) -> Result<(usize, SocketAddr)>,
    S: AsyncFn(&[u8], SocketAddr) -> Result<usize>,
{
    /// `recv` fills the buffer with one datagram and returns its length and sender; `send` sends one datagram.
    pub const fn new(recv: R, send: S) -> Self {
        Self { recv, send }
    }
}

/// The carrier side, for a stream type `T` of the host's.
pub struct Carriers<A, Rd, Wr, Cl, T> {
    pub(crate) accept: A,
    pub(crate) read: Rd,
    pub(crate) write: Wr,
    pub(crate) close: Cl,
    _stream: PhantomData<fn() -> T>,
}

impl<A, Rd, Wr, Cl, T> core::fmt::Debug for Carriers<A, Rd, Wr, Cl, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Carriers")
    }
}

impl<A, Rd, Wr, Cl, T> Carriers<A, Rd, Wr, Cl, T>
where
    A: AsyncFn() -> Result<(T, CarrierKind)>,
    Rd: AsyncFn(&T, Vec<u8>) -> (Result<usize>, Vec<u8>),
    Wr: AsyncFn(&T, Vec<u8>, usize) -> (Result<usize>, Vec<u8>),
    Cl: AsyncFn(T),
{
    /// `accept` waits for the next stream; `read(&s, buf)` fills `buf` from its start, up to its length, and returns
    /// the count (zero when the peer closed); `write(&s, buf, from)` writes `buf` from `from` to its end and returns
    /// the count it wrote; `close(s)` ends the stream. Read and write return the buffer.
    pub const fn new(accept: A, read: Rd, write: Wr, close: Cl) -> Self {
        Self {
            accept,
            read,
            write,
            close,
            _stream: PhantomData,
        }
    }
}

/// The clock: nanoseconds since the Unix epoch that never go backward, and a sleep until an instant of the same clock.
/// A member's sleep notice carries its wall clock and is checked against this one, so the origin matters.
#[derive(Debug)]
pub struct Clock<N, Z> {
    pub(crate) now: N,
    pub(crate) sleep: Z,
}

impl<N, Z> Clock<N, Z>
where
    N: Fn() -> u64,
    Z: AsyncFn(u64),
{
    /// `now` reads the clock; `sleep(at)` returns when `now()` has reached `at`.
    pub const fn new(now: N, sleep: Z) -> Self {
        Self { now, sleep }
    }
}

/// The host's closures as one type; only [`Host`] implements it.
pub trait Hosted: sealed::Sealed {
    /// The host's byte stream.
    type Stream;

    #[doc(hidden)]
    fn recv(&self, buf: &mut [u8]) -> impl Future<Output = Result<(usize, SocketAddr)>>;
    #[doc(hidden)]
    fn send(&self, pkt: &[u8], to: SocketAddr) -> impl Future<Output = Result<usize>>;
    #[doc(hidden)]
    fn accept(&self) -> impl Future<Output = Result<(Self::Stream, CarrierKind)>>;
    #[doc(hidden)]
    fn read(&self, s: &Self::Stream, buf: Vec<u8>) -> impl Future<Output = (Result<usize>, Vec<u8>)>;
    #[doc(hidden)]
    fn write(&self, s: &Self::Stream, buf: Vec<u8>, from: usize) -> impl Future<Output = (Result<usize>, Vec<u8>)>;
    #[doc(hidden)]
    fn close(&self, s: Self::Stream) -> impl Future<Output = ()>;
    #[doc(hidden)]
    fn now(&self) -> u64;
    #[doc(hidden)]
    fn sleep(&self, at: u64) -> impl Future<Output = ()>;
}

/// The host's closures, grouped as [`Udp`], [`Carriers`] and [`Clock`].
pub struct Host<R, S, A, Rd, Wr, Cl, N, Z, T> {
    udp: Udp<R, S>,
    carriers: Carriers<A, Rd, Wr, Cl, T>,
    clock: Clock<N, Z>,
}

impl<R, S, A, Rd, Wr, Cl, N, Z, T> Host<R, S, A, Rd, Wr, Cl, N, Z, T> {
    pub(crate) const fn new(udp: Udp<R, S>, carriers: Carriers<A, Rd, Wr, Cl, T>, clock: Clock<N, Z>) -> Self {
        Self { udp, carriers, clock }
    }
}

impl<R, S, A, Rd, Wr, Cl, N, Z, T> core::fmt::Debug for Host<R, S, A, Rd, Wr, Cl, N, Z, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Host")
    }
}

impl<R, S, A, Rd, Wr, Cl, N, Z, T> sealed::Sealed for Host<R, S, A, Rd, Wr, Cl, N, Z, T> {}

impl<R, S, A, Rd, Wr, Cl, N, Z, T> Hosted for Host<R, S, A, Rd, Wr, Cl, N, Z, T>
where
    R: AsyncFn(&mut [u8]) -> Result<(usize, SocketAddr)>,
    S: AsyncFn(&[u8], SocketAddr) -> Result<usize>,
    A: AsyncFn() -> Result<(T, CarrierKind)>,
    Rd: AsyncFn(&T, Vec<u8>) -> (Result<usize>, Vec<u8>),
    Wr: AsyncFn(&T, Vec<u8>, usize) -> (Result<usize>, Vec<u8>),
    Cl: AsyncFn(T),
    N: Fn() -> u64,
    Z: AsyncFn(u64),
{
    type Stream = T;

    async fn recv(&self, buf: &mut [u8]) -> Result<(usize, SocketAddr)> {
        (self.udp.recv)(buf).await
    }

    async fn send(&self, pkt: &[u8], to: SocketAddr) -> Result<usize> {
        (self.udp.send)(pkt, to).await
    }

    async fn accept(&self) -> Result<(T, CarrierKind)> {
        (self.carriers.accept)().await
    }

    async fn read(&self, s: &T, buf: Vec<u8>) -> (Result<usize>, Vec<u8>) {
        (self.carriers.read)(s, buf).await
    }

    async fn write(&self, s: &T, buf: Vec<u8>, from: usize) -> (Result<usize>, Vec<u8>) {
        (self.carriers.write)(s, buf, from).await
    }

    async fn close(&self, s: T) {
        (self.carriers.close)(s).await;
    }

    fn now(&self) -> u64 {
        (self.clock.now)()
    }

    async fn sleep(&self, at: u64) {
        (self.clock.sleep)(at).await;
    }
}

/// The host of a relay that is not built yet; it has no values and only gives [`Relay::builder`](super::Relay::builder)
/// a home.
#[derive(Debug, Clone, Copy)]
pub enum Unbuilt {}

impl sealed::Sealed for Unbuilt {}

#[allow(clippy::unused_async_trait_impl, reason = "no value of this type exists")]
impl Hosted for Unbuilt {
    type Stream = ();

    async fn recv(&self, _: &mut [u8]) -> Result<(usize, SocketAddr)> {
        match *self {}
    }

    async fn send(&self, _: &[u8], _: SocketAddr) -> Result<usize> {
        match *self {}
    }

    async fn accept(&self) -> Result<((), CarrierKind)> {
        match *self {}
    }

    async fn read(&self, (): &(), _: Vec<u8>) -> (Result<usize>, Vec<u8>) {
        match *self {}
    }

    async fn write(&self, (): &(), _: Vec<u8>, _: usize) -> (Result<usize>, Vec<u8>) {
        match *self {}
    }

    async fn close(&self, (): ()) {
        match *self {}
    }

    fn now(&self) -> u64 {
        match *self {}
    }

    async fn sleep(&self, _: u64) {
        match *self {}
    }
}
