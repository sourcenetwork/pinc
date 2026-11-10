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
//! [`Host`] and [`BatchHost`] are the types the closures (with the key store and the access hook) make; [`Hosted`] is how
//! the facade's types name them, so a handle is generic over one parameter instead of five.
//!
//! The closures may borrow from the caller; the handles are `'static` exactly when the closures are.
//!
//! Invariants: the closures are called from whichever task polls a facade future, never from a thread of the library;
//! a receive future that is dropped before it completes loses no datagram (true of readiness-based receives such as
//! nuclei's and tokio's `recv_from`).

use std::io;
use std::marker::PhantomData;
use std::net::SocketAddr;
use std::time::Instant;

use vinc_keystore::KeyStore;

use crate::engine::Admit;

mod sealed {
    pub trait Sealed {}
}

/// The host's I/O and settings as one type; only [`Host`] and [`BatchHost`] implement it.
pub trait Hosted: sealed::Sealed + Send + Sync {
    /// The key store that holds the identity.
    type Keys: KeyStore + Send;
    /// The access hook.
    type Access: Admit;

    /// Receive into `buf`: the length filled, the sender and the size of each datagram in the filled part.
    #[doc(hidden)]
    fn recv(&self, buf: &mut [u8]) -> impl Future<Output = io::Result<(usize, SocketAddr, usize)>>;

    /// Send a transmit: equal-size datagrams of `segment` bytes (the last may be shorter) to `to`.
    #[doc(hidden)]
    fn send(&self, buf: &[u8], to: SocketAddr, segment: usize) -> impl Future<Output = io::Result<usize>>;

    /// Sleep until `at`.
    #[doc(hidden)]
    fn sleep(&self, at: Instant) -> impl Future<Output = ()>;
}

/// The host's three closures, one datagram per call, with the type of the key store and of the access hook.
pub struct Host<R, S, Z, K, A> {
    recv: R,
    send: S,
    sleep: Z,
    _types: PhantomData<fn() -> (K, A)>,
}

/// The host's three closures, a whole transmit per send and possibly several datagrams per receive, with the type of the
/// key store and of the access hook.
pub struct BatchHost<R, S, Z, K, A> {
    recv: R,
    send: S,
    sleep: Z,
    _types: PhantomData<fn() -> (K, A)>,
}

macro_rules! host_new {
    ($($t:ident),+) => {$(
        impl<R, S, Z, K, A> $t<R, S, Z, K, A> {
            pub(crate) const fn new(recv: R, send: S, sleep: Z) -> Self {
                Self {
                    recv,
                    send,
                    sleep,
                    _types: PhantomData,
                }
            }
        }

        impl<R, S, Z, K, A> core::fmt::Debug for $t<R, S, Z, K, A> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(stringify!($t))
            }
        }

        impl<R, S, Z, K, A> sealed::Sealed for $t<R, S, Z, K, A> {}
    )+};
}
host_new!(Host, BatchHost);

impl<R, S, Z, K, A> Hosted for Host<R, S, Z, K, A>
where
    R: AsyncFn(&mut [u8]) -> io::Result<(usize, SocketAddr)> + Send + Sync,
    S: AsyncFn(&[u8], SocketAddr) -> io::Result<usize> + Send + Sync,
    Z: AsyncFn(Instant) + Send + Sync,
    K: KeyStore + Send,
    A: Admit,
{
    type Keys = K;
    type Access = A;

    async fn recv(&self, buf: &mut [u8]) -> io::Result<(usize, SocketAddr, usize)> {
        let (n, from) = (self.recv)(buf).await?;
        Ok((n, from, n))
    }

    async fn send(&self, buf: &[u8], to: SocketAddr, segment: usize) -> io::Result<usize> {
        let mut sent = 0;
        for datagram in buf.chunks(segment.max(1)) {
            (self.send)(datagram, to).await?;
            sent += 1;
        }
        Ok(sent)
    }

    async fn sleep(&self, at: Instant) {
        (self.sleep)(at).await;
    }
}

impl<R, S, Z, K, A> Hosted for BatchHost<R, S, Z, K, A>
where
    R: AsyncFn(&mut [u8]) -> io::Result<(usize, SocketAddr, usize)> + Send + Sync,
    S: AsyncFn(&[u8], SocketAddr, usize) -> io::Result<usize> + Send + Sync,
    Z: AsyncFn(Instant) + Send + Sync,
    K: KeyStore + Send,
    A: Admit,
{
    type Keys = K;
    type Access = A;

    async fn recv(&self, buf: &mut [u8]) -> io::Result<(usize, SocketAddr, usize)> {
        (self.recv)(buf).await
    }

    async fn send(&self, buf: &[u8], to: SocketAddr, segment: usize) -> io::Result<usize> {
        (self.send)(buf, to, segment).await
    }

    async fn sleep(&self, at: Instant) {
        (self.sleep)(at).await;
    }
}
