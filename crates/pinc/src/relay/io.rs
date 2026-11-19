//! The host's I/O for a relay: async closures for the UDP socket, for the carrier streams and for the clock.
//!
//! The relay opens no socket and starts no timer. The host passes:
//!
//! - [`Udp`]: `recv` fills a buffer with one datagram and returns its length and sender; `send` sends one datagram.
//! - [`Carriers`], given to the builder beside these: the byte streams members open and the relay opens to its peers, as
//!   a completion queue (see [`Carriers`]); [`CarrierFns`] builds it from async closures. The host has done the TCP
//!   accept, or the HTTP upgrade of a WebSocket.
//! - [`Clock`]: a clock in nanoseconds since the Unix epoch that never goes backward, and a sleep until an instant of it.
//!
//! The closures may borrow from the caller. The stream type is the host's own, kept in an `Rc`. Dropping the future of
//! [`Relay::run`](super::Relay::run) drops the relay's streams without calling `close`; a stream type whose last drop ends
//! the connection (a socket) closes its carriers at once, and a host with tasks of its own ends them itself.

use alloc::rc::Rc;
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::net::SocketAddr;
use core::task::{Context, Poll};

use super::carriers::{Carriers, Completion, Tag};
use super::peers::Peer;
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

/// The host's I/O as one type; only [`Host`] implements it.
pub trait Hosted: sealed::Sealed {
    /// The host's byte stream.
    type Stream;
    /// The host's carriers.
    type Streams: Carriers<Stream = Self::Stream>;

    #[doc(hidden)]
    fn recv(&self, buf: &mut [u8]) -> impl Future<Output = Result<(usize, SocketAddr)>>;
    #[doc(hidden)]
    fn send(&self, pkt: &[u8], to: SocketAddr) -> impl Future<Output = Result<usize>>;
    #[doc(hidden)]
    fn now(&self) -> u64;
    #[doc(hidden)]
    fn sleep(&self, at: u64) -> impl Future<Output = ()>;
}

/// The host's I/O, grouped as [`Udp`], [`Carriers`] and [`Clock`].
pub struct Host<R, S, C, N, Z> {
    udp: Udp<R, S>,
    clock: Clock<N, Z>,
    carriers: PhantomData<fn() -> C>,
}

impl<R, S, C, N, Z> Host<R, S, C, N, Z> {
    pub(crate) const fn new(udp: Udp<R, S>, clock: Clock<N, Z>) -> Self {
        Self {
            udp,
            clock,
            carriers: PhantomData,
        }
    }
}

impl<R, S, C, N, Z> core::fmt::Debug for Host<R, S, C, N, Z> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Host")
    }
}

impl<R, S, C, N, Z> sealed::Sealed for Host<R, S, C, N, Z> {}

impl<R, S, C, N, Z> Hosted for Host<R, S, C, N, Z>
where
    R: AsyncFn(&mut [u8]) -> Result<(usize, SocketAddr)>,
    S: AsyncFn(&[u8], SocketAddr) -> Result<usize>,
    C: Carriers,
    N: Fn() -> u64,
    Z: AsyncFn(u64),
{
    type Stream = C::Stream;
    type Streams = C;

    async fn recv(&self, buf: &mut [u8]) -> Result<(usize, SocketAddr)> {
        (self.udp.recv)(buf).await
    }

    async fn send(&self, pkt: &[u8], to: SocketAddr) -> Result<usize> {
        (self.udp.send)(pkt, to).await
    }

    fn now(&self) -> u64 {
        (self.clock.now)()
    }

    async fn sleep(&self, at: u64) {
        (self.clock.sleep)(at).await;
    }
}

/// The carriers of a relay that is not built yet; there is no value of the type.
#[derive(Debug, Clone, Copy)]
pub enum NoCarriers {}

impl Carriers for NoCarriers {
    type Stream = ();

    fn submit_accept(&self, _: Tag) {
        match *self {}
    }

    fn submit_open(&self, _: Tag, _: &Peer, _: CarrierKind) {
        match *self {}
    }

    fn submit_read(&self, _: &Rc<()>, _: Tag, _: Vec<u8>) {
        match *self {}
    }

    fn submit_write(&self, _: &Rc<()>, _: Tag, _: Vec<u8>, _: usize) {
        match *self {}
    }

    fn close(&self, _: Tag, _: Rc<()>) {
        match *self {}
    }

    fn poll_completed(&self, _: &mut Context<'_>) -> Poll<Completion<()>> {
        match *self {}
    }

    fn drive(&self) -> impl Future<Output = ()> {
        core::future::pending()
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
    type Streams = NoCarriers;

    async fn recv(&self, _: &mut [u8]) -> Result<(usize, SocketAddr)> {
        match *self {}
    }

    async fn send(&self, _: &[u8], _: SocketAddr) -> Result<usize> {
        match *self {}
    }

    fn now(&self) -> u64 {
        match *self {}
    }

    async fn sleep(&self, _: u64) {
        match *self {}
    }
}
