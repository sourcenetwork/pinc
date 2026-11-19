//! The host's I/O: three async closures, and the types that carry them.
//!
//! The facade opens no socket and starts no timer. The host passes a closure that receives, one that sends and one that
//! sleeps until an instant, and the futures of the facade call them. There are two shapes of the first two, and the host
//! picks one by the builder method it calls:
//!
//! - [`Builder::build`](crate::Builder::build): one datagram per call. `recv` fills the buffer with one datagram and
//!   returns its length and sender; `send` sends one datagram to an address. Nothing else to know.
//! - [`Builder::build_batched`](crate::Builder::build_batched): for a host with segmentation offload or coalesced
//!   receives. `send` gets a whole transmit, a buffer of equal-size datagrams (the last may be shorter) and their
//!   segment size, and sends it in one call; `recv` may return several datagrams of one sender that it received in one
//!   call, as the length filled and the segment size. A host without those features uses [`Builder::build`].
//!
//! - [`Builder::build_io`](crate::Builder::build_io): the same batched contract as a trait ([`Io`]) instead of closures,
//!   for a host that must name the endpoint's type, because it keeps the endpoint in a struct field, say. A closure's
//!   type cannot be written; a type that implements [`Io`] can.
//!
//! [`Host`], [`BatchHost`] and [`IoHost`] are the types the closures (with the key store and the access hook) make; [`Hosted`] is how
//! the facade's types name them, so a handle is generic over one parameter instead of five.
//!
//! The instant the sleep closure takes and the error the I/O closures return are the host's [`Platform`]'s; a host on
//! the standard library has [`System`] and writes `std::time::Instant` and `std::io::Error` as before.
//!
//! The closures may borrow from the caller; the handles are `'static` exactly when the closures are.
//!
//! Invariants: the closures are called from whichever task polls a facade future, never from a thread of the library;
//! a receive future that is dropped before it completes loses no datagram (true of readiness-based receives such as
//! nuclei's and tokio's `recv_from`).

use core::cell::RefCell;
use core::marker::PhantomData;
use core::net::SocketAddr;

use pinc_keystore::KeyStore;

use crate::carriers::{Carriers, NoCarriers};
use crate::engine::Admit;
use crate::platform::{Platform, System};
use crate::role::Role;

mod sealed {
    pub trait Sealed {}
}

/// The host's I/O and settings as one type; only [`Host`], [`BatchHost`] and [`IoHost`] implement it.
pub trait Hosted: sealed::Sealed {
    /// The key store that holds the identity.
    type Keys: KeyStore;
    /// The access hook.
    type Access: Admit;
    /// The host's clock, randomness and the types of its instant and error.
    type Platform: Platform;
    /// The carriers to relays.
    type Carriers: Carriers<Self::Platform>;
    /// The relay role of the endpoint: the unit type when it has none.
    type Role: Role;

    /// The most bytes one receive can fill: one datagram one byte longer than the endpoint takes (so a longer one shows
    /// itself whole and is dropped), or, for a host that may coalesce several, a whole UDP payload.
    #[doc(hidden)]
    const RECV_MAX: usize;

    /// Receive into `buf`: the length filled, the sender and the size of each datagram in the filled part.
    #[doc(hidden)]
    fn recv(
        &self,
        buf: &mut [u8],
    ) -> impl Future<Output = Result<(usize, SocketAddr, usize), <Self::Platform as Platform>::Error>>;

    /// Send a transmit: equal-size datagrams of `segment` bytes (the last may be shorter) to `to`.
    #[doc(hidden)]
    fn send(
        &self,
        buf: &[u8],
        to: SocketAddr,
        segment: usize,
    ) -> impl Future<Output = Result<usize, <Self::Platform as Platform>::Error>>;

    /// Sleep until `at`.
    #[doc(hidden)]
    fn sleep(&self, at: <Self::Platform as Platform>::Instant) -> impl Future<Output = ()>;

    /// The host's platform.
    #[doc(hidden)]
    fn platform(&self) -> &Self::Platform;

    /// The host's carriers to relays.
    #[doc(hidden)]
    fn carriers(&self) -> &Self::Carriers;

    /// The relay role.
    #[doc(hidden)]
    fn role(&self) -> &RefCell<Self::Role>;
}

/// The host's three closures, one datagram per call, with the type of the key store and of the access hook.
pub struct Host<R, S, Z, K, A, C = NoCarriers, P = (), Pf = System> {
    recv: R,
    send: S,
    sleep: Z,
    carriers: C,
    role: RefCell<P>,
    platform: Pf,
    _types: PhantomData<fn() -> (K, A)>,
}

/// The host's three closures, a whole transmit per send and possibly several datagrams per receive, with the type of the
/// key store and of the access hook.
pub struct BatchHost<R, S, Z, K, A, C = NoCarriers, P = (), Pf = System> {
    recv: R,
    send: S,
    sleep: Z,
    carriers: C,
    role: RefCell<P>,
    platform: Pf,
    _types: PhantomData<fn() -> (K, A)>,
}

macro_rules! host_new {
    ($($t:ident),+) => {$(
        impl<R, S, Z, K, A, C, P, Pf> $t<R, S, Z, K, A, C, P, Pf> {
            pub(crate) const fn new(recv: R, send: S, sleep: Z, carriers: C, role: P, platform: Pf) -> Self {
                Self {
                    recv,
                    send,
                    sleep,
                    carriers,
                    role: RefCell::new(role),
                    platform,
                    _types: PhantomData,
                }
            }
        }

        impl<R, S, Z, K, A, C, P, Pf> core::fmt::Debug for $t<R, S, Z, K, A, C, P, Pf> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(stringify!($t))
            }
        }

        impl<R, S, Z, K, A, C, P, Pf> sealed::Sealed for $t<R, S, Z, K, A, C, P, Pf> {}
    )+};
}
host_new!(Host, BatchHost);

impl<R, S, Z, K, A, C, P, Pf> Hosted for Host<R, S, Z, K, A, C, P, Pf>
where
    R: AsyncFn(&mut [u8]) -> Result<(usize, SocketAddr), Pf::Error>,
    S: AsyncFn(&[u8], SocketAddr) -> Result<usize, Pf::Error>,
    Z: AsyncFn(Pf::Instant),
    K: KeyStore,
    A: Admit,
    C: Carriers<Pf>,
    P: Role,
    Pf: Platform,
{
    type Keys = K;
    type Access = A;
    type Platform = Pf;
    type Carriers = C;
    type Role = P;
    const RECV_MAX: usize = pinc_core::MAX_DATAGRAM + 1;

    async fn recv(&self, buf: &mut [u8]) -> Result<(usize, SocketAddr, usize), Pf::Error> {
        let (n, from) = (self.recv)(buf).await?;
        Ok((n, from, n))
    }

    async fn send(&self, buf: &[u8], to: SocketAddr, segment: usize) -> Result<usize, Pf::Error> {
        let mut sent = 0;
        for datagram in buf.chunks(segment.max(1)) {
            (self.send)(datagram, to).await?;
            sent += 1;
        }
        Ok(sent)
    }

    async fn sleep(&self, at: Pf::Instant) {
        (self.sleep)(at).await;
    }

    fn platform(&self) -> &Pf {
        &self.platform
    }

    fn carriers(&self) -> &C {
        &self.carriers
    }

    fn role(&self) -> &RefCell<P> {
        &self.role
    }
}

impl<R, S, Z, K, A, C, P, Pf> Hosted for BatchHost<R, S, Z, K, A, C, P, Pf>
where
    R: AsyncFn(&mut [u8]) -> Result<(usize, SocketAddr, usize), Pf::Error>,
    S: AsyncFn(&[u8], SocketAddr, usize) -> Result<usize, Pf::Error>,
    Z: AsyncFn(Pf::Instant),
    K: KeyStore,
    A: Admit,
    C: Carriers<Pf>,
    P: Role,
    Pf: Platform,
{
    type Keys = K;
    type Access = A;
    type Platform = Pf;
    type Carriers = C;
    type Role = P;
    const RECV_MAX: usize = 65_536;

    async fn recv(&self, buf: &mut [u8]) -> Result<(usize, SocketAddr, usize), Pf::Error> {
        (self.recv)(buf).await
    }

    async fn send(&self, buf: &[u8], to: SocketAddr, segment: usize) -> Result<usize, Pf::Error> {
        (self.send)(buf, to, segment).await
    }

    async fn sleep(&self, at: Pf::Instant) {
        (self.sleep)(at).await;
    }

    fn platform(&self) -> &Pf {
        &self.platform
    }

    fn carriers(&self) -> &C {
        &self.carriers
    }

    fn role(&self) -> &RefCell<P> {
        &self.role
    }
}

/// The host's I/O as a trait, with the contract of [`Builder::build_batched`](crate::Builder::build_batched): `recv` fills
/// the buffer and returns the length, the sender and the segment size; `send` gets a whole transmit and its segment
/// size and returns how many datagrams went; `sleep` waits until an instant. A host that handles one datagram per call
/// returns the length as the segment size and sends the buffer as one datagram when the segment size is its length.
pub trait Io<#[cfg(feature = "std")] Pf: Platform = System, #[cfg(not(feature = "std"))] Pf: Platform> {
    /// Receive into `buf`: the length filled, the sender and the size of each datagram in the filled part.
    fn recv(&self, buf: &mut [u8]) -> impl Future<Output = Result<(usize, SocketAddr, usize), Pf::Error>>;

    /// Send equal-size datagrams of `segment` bytes (the last may be shorter) to `to`.
    fn send(&self, buf: &[u8], to: SocketAddr, segment: usize) -> impl Future<Output = Result<usize, Pf::Error>>;

    /// Sleep until `at`.
    fn sleep(&self, at: Pf::Instant) -> impl Future<Output = ()>;
}

/// A host that implements [`Io`], with the type of the key store and of the access hook.
pub struct IoHost<N, K, A, C = NoCarriers, P = (), Pf = System> {
    io: N,
    carriers: C,
    role: RefCell<P>,
    platform: Pf,
    _types: PhantomData<fn() -> (K, A)>,
}

impl<N, K, A, C, P, Pf> IoHost<N, K, A, C, P, Pf> {
    pub(crate) const fn new(io: N, carriers: C, role: P, platform: Pf) -> Self {
        Self {
            io,
            carriers,
            role: RefCell::new(role),
            platform,
            _types: PhantomData,
        }
    }
}

impl<N, K, A, C, P, Pf> core::fmt::Debug for IoHost<N, K, A, C, P, Pf> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("IoHost")
    }
}

impl<N, K, A, C, P, Pf> sealed::Sealed for IoHost<N, K, A, C, P, Pf> {}

impl<N, K, A, C, P, Pf> Hosted for IoHost<N, K, A, C, P, Pf>
where
    N: Io<Pf>,
    K: KeyStore,
    A: Admit,
    C: Carriers<Pf>,
    P: Role,
    Pf: Platform,
{
    type Keys = K;
    type Access = A;
    type Platform = Pf;
    type Carriers = C;
    type Role = P;
    const RECV_MAX: usize = 65_536;

    fn recv(&self, buf: &mut [u8]) -> impl Future<Output = Result<(usize, SocketAddr, usize), Pf::Error>> {
        self.io.recv(buf)
    }

    fn send(&self, buf: &[u8], to: SocketAddr, segment: usize) -> impl Future<Output = Result<usize, Pf::Error>> {
        self.io.send(buf, to, segment)
    }

    fn sleep(&self, at: Pf::Instant) -> impl Future<Output = ()> {
        self.io.sleep(at)
    }

    fn platform(&self) -> &Pf {
        &self.platform
    }

    fn carriers(&self) -> &C {
        &self.carriers
    }

    fn role(&self) -> &RefCell<P> {
        &self.role
    }
}
