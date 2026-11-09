//! What the driver asks of the host: datagrams and time, as async traits the host's runtime implements.
//!
//! The driver owns no socket and no timer. It awaits [`Datagrams`] for the next datagram and [`Timer`] for the next
//! deadline, on whatever executor polls it, so a thread-per-core runtime keeps the endpoint on the core that owns the
//! socket. The futures the traits return are `Send` so a host can spawn the driver on a work-stealing or a pinned
//! executor alike.
//!
//! Invariants: a future the driver drops mid-way loses nothing the driver has not already been told; `try_recv` never
//! waits.

use std::future::Future;
use std::io;
use std::net::SocketAddr;

/// The host's UDP socket.
pub trait Datagrams: Send + Sync + 'static {
    /// The address the socket is bound to.
    ///
    /// # Errors
    /// The socket's error if the address is unknown.
    fn local_addr(&self) -> io::Result<SocketAddr>;

    /// Send `buf` to `to` as datagrams of `segment_size` bytes each (the last may be shorter). A host with
    /// segmentation offload sends them in one call; one without sends each on its own. Returns how many datagrams went.
    fn send(&self, to: SocketAddr, buf: &[u8], segment_size: usize) -> impl Future<Output = io::Result<usize>> + Send;

    /// Wait for the next datagram into `buf`; returns its length and sender.
    fn recv(&self, buf: &mut [u8]) -> impl Future<Output = io::Result<(usize, SocketAddr)>> + Send;

    /// The next datagram if one is already waiting, else `None`.
    ///
    /// # Errors
    /// The socket's error.
    fn try_recv(&self, buf: &mut [u8]) -> io::Result<Option<(usize, SocketAddr)>>;
}

/// The host's clock and timer.
pub trait Timer: Send + Sync + 'static {
    /// Nanoseconds on a monotonic clock with any fixed origin.
    fn now(&self) -> u64;

    /// Wait until [`now`](Self::now) reaches `at`; at once if it already has.
    fn sleep_until(&self, at: u64) -> impl Future<Output = ()> + Send;
}
