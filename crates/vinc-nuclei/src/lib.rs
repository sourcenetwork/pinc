//! The nuclei runtime's I/O for the VINC driver: a UDP [`Socket`] and a [`Clock`] that implement the driver's
//! [`Datagrams`] and [`Timer`] traits.
//!
//! Spawn the driver on the worker that owns the socket (`nuclei::spawn`, or [`spawn_on_worker`] to name the worker):
//! nuclei pins a worker to a core, and the socket, the timers and the endpoint's state all stay on it. The driver is
//! parked on an await while the endpoint is idle.
//!
//! Thread-per-core today means one endpoint per worker, each with its own socket and identity. Sharing one identity and
//! one port across workers needs the endpoints to hand a datagram to the worker that owns its connection, which the
//! endpoint does not have yet.
//!
//! Invariants: the socket and the clock hold no thread; a timer is armed on the shard that polls the driver.
#![forbid(unsafe_code)]

use std::io;
use std::net::{SocketAddr, UdpSocket};
use std::time::Duration;

use nuclei::Handle;
use nuclei::time::{Instant, sleep_until_precise};
use nuclei::{RuntimeHandle, Task};
use vinc_driver::{Datagrams, Timer};

/// A UDP socket on the nuclei runtime.
pub struct Socket(Handle<UdpSocket>);

impl Socket {
    /// Bind a socket to `addr`.
    ///
    /// # Errors
    /// The error of binding the address.
    pub async fn bind(addr: SocketAddr) -> io::Result<Self> {
        Handle::<UdpSocket>::bind(addr).await.map(Self)
    }
}

impl Datagrams for Socket {
    fn local_addr(&self) -> io::Result<SocketAddr> {
        self.0.local_addr()
    }

    async fn send(&self, to: SocketAddr, buf: &[u8], segment_size: usize) -> io::Result<usize> {
        let mut sent = 0;
        for seg in buf.chunks(segment_size.max(1)) {
            self.0.send_to(seg, to).await?;
            sent += 1;
        }
        Ok(sent)
    }

    async fn recv(&self, buf: &mut [u8]) -> io::Result<(usize, SocketAddr)> {
        self.0.recv_from(buf).await
    }

    fn try_recv(&self, buf: &mut [u8]) -> io::Result<Option<(usize, SocketAddr)>> {
        match self.0.try_recv_from(buf) {
            Ok(got) => Ok(Some(got)),
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => Ok(None),
            Err(e) => Err(e),
        }
    }
}

/// The nuclei clock and its timers, to the microsecond.
#[derive(Debug, Clone, Copy)]
pub struct Clock {
    origin: Instant,
}

impl Clock {
    /// A clock whose zero is now.
    pub fn new() -> Self {
        Self { origin: Instant::now() }
    }
}

impl Default for Clock {
    fn default() -> Self {
        Self::new()
    }
}

impl Timer for Clock {
    fn now(&self) -> u64 {
        u64::try_from(self.origin.elapsed().as_nanos()).unwrap_or(u64::MAX)
    }

    async fn sleep_until(&self, at: u64) {
        if let Some(deadline) = self.origin.checked_add(Duration::from_nanos(at)) {
            sleep_until_precise(deadline).await;
        }
    }
}

/// Spawn `driver` on nuclei worker `worker` of `runtime`, so the endpoint and its socket stay on that worker's core.
///
/// # Errors
/// The runtime's error if the worker does not exist or has stopped.
pub fn spawn_on_worker<F>(runtime: &RuntimeHandle, worker: usize, driver: F) -> io::Result<Task<F::Output>>
where
    F: std::future::Future + Send + 'static,
    F::Output: Send + 'static,
{
    runtime.spawn_on_worker(worker, driver)
}
