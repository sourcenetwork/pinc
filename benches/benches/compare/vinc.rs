//! The comparison harness for VINC, on the nuclei runtime the way a host would run it (see `compare/mod.rs`).
//!
//! Defaults: `Vinc::builder()` with the default limits on the server (1024 sessions, 512 chunks of 16 KiB per session,
//! 256 KiB stream windows). A client endpoint holds one session, so it asks for exactly one (`connections: 1`); the
//! endpoint reserves its tables for the smallest shape that holds the request, which is what the documentation tells a
//! host to do. The endpoint's three I/O calls are a type here (`Net`, an `Io`), not closures, only so the harness can
//! write the endpoint's type down; the facade's own calls are made directly, with no boxing and no `unsafe`. Everything
//! runs on the thread that started it, one endpoint per thread, as the facade is meant to be used.
//!
//! With `--endpoints=per-core` (see `compare/mod.rs`) the server runs one endpoint on every worker of the runtime, all
//! with one identity, each on a socket of its own on one port (`SO_REUSEPORT`: the kernel spreads peers among them by
//! their address), and the clients of the `many` test are spread over the workers, each endpoint made, driven and
//! dropped on its worker. Every other test's client runs on the thread that drives it.
//!
//! Limits of the per-core server, stated: a peer's datagrams reach the endpoint its address hashes to. A peer that moves
//! to another address (a new socket, a changed port or address) may land on an endpoint that holds neither its session
//! nor the tickets it was given; its session then ends at its timeouts and it dials again, as a stranger (a full
//! handshake, not a resumption). A resumption from the same socket reaches the same endpoint and resumes. Each
//! endpoint also limits its own sessions and half-open dials.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::unreadable_literal,
    clippy::missing_errors_doc,
    clippy::doc_markdown,
    clippy::needless_pass_by_value,
    clippy::items_after_statements,
    clippy::cast_lossless,
    clippy::format_push_string,
    clippy::unused_async_trait_impl,
    clippy::default_trait_access
)]

use std::future::Future;
use std::io;
use std::net::{SocketAddr, UdpSocket};
use std::rc::Rc;
use std::time::{Duration, Instant};

use super::{Lib, Rx, Tx};
use futures::StreamExt;
use futures::channel::mpsc;
use nuclei::Handle;
use nuclei::net::UdpSocketBuilder;
use quinn_udp::{RecvMeta, Transmit, UdpSockRef, UdpSocketState};
use vinc::{AllowAll, Connection, Endpoint, Io, IoHost, Limits, NodeAddr, RecvStream, SendStream, Vinc};
use vinc_keystore::{KeyStore, SoftwareStore};

const ALPN: &[u8] = b"bench/1";
/// What the socket's send and receive buffers are asked to hold.
const SOCKET_BUFFER: u32 = 8 << 20;

fn io_err(e: vinc::Error) -> io::Error {
    io::Error::other(e.to_string())
}

/// The endpoint's socket and timer: nuclei's, called directly.
pub struct Net {
    sock: Rc<Handle<UdpSocket>>,
    /// The socket's offload state: segmented sends and coalesced receives where the system has them.
    udp: UdpSocketState,
}

impl Io for Net {
    async fn recv(&self, buf: &mut [u8]) -> io::Result<(usize, SocketAddr, usize)> {
        // One call takes every datagram of one sender the system coalesced; only an empty socket is waited on.
        loop {
            let mut meta = [RecvMeta::default()];
            let got = self.udp.recv(
                UdpSockRef::from(&*self.sock),
                &mut [io::IoSliceMut::new(buf)],
                &mut meta,
            );
            match got {
                Ok(_) => {
                    let [m] = meta;
                    if m.len > 0 {
                        return Ok((m.len, m.addr, m.stride.max(1)));
                    }
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => self.sock.readable().await?,
                Err(e) => return Err(e),
            }
        }
    }

    async fn send(&self, buf: &[u8], to: SocketAddr, segment: usize) -> io::Result<usize> {
        // One call sends the whole run of equal-size datagrams; the system cuts it into datagrams of `segment`.
        let count = buf.len().div_ceil(segment.max(1));
        let transmit = Transmit {
            destination: to,
            ecn: None,
            contents: buf,
            segment_size: (count > 1).then_some(segment),
            src_ip: None,
        };
        loop {
            match self.udp.try_send(UdpSockRef::from(&*self.sock), &transmit) {
                Ok(()) => return Ok(count),
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => self.sock.writable().await?,
                Err(e) => return Err(e),
            }
        }
    }

    async fn sleep(&self, at: Instant) {
        nuclei::time::sleep_until_precise(at).await;
    }
}

type H = IoHost<Net, SoftwareStore, AllowAll>;
type Ep = Endpoint<H>;
type Conn = Connection<H>;

fn bind(limits: Limits, run: bool) -> io::Result<Ep> {
    endpoint(socket(0, false)?, limits, None, run)
}

/// A socket on `port` (0 picks one) of the bind address; `shared` lets several sockets of the process bind the port
/// (`SO_REUSEPORT`).
fn socket(port: u16, shared: bool) -> io::Result<Handle<UdpSocket>> {
    // Socket buffers as a busy host sizes them (the system clamps them to its limit): the default of about 200 KiB
    // drops the first flights of a few hundred peers dialing at once.
    let builder = UdpSocketBuilder::new_v4()?;
    builder.set_recv_buffer_size(SOCKET_BUFFER)?;
    builder.set_send_buffer_size(SOCKET_BUFFER)?;
    if shared {
        builder.set_reuseport(true)?;
    }
    builder.bind(SocketAddr::new(super::bind_ip()?, port))
}

/// An endpoint over `sock`, with the identity of `seed` (a fresh one without), driven by a task of its own if `run`.
fn endpoint(sock: Handle<UdpSocket>, limits: Limits, seed: Option<&[u8; 32]>, run: bool) -> io::Result<Ep> {
    let sock = Rc::new(sock);
    let udp = UdpSocketState::new(UdpSockRef::from(&*sock))?;
    // As many datagrams per transmit as the system sends in one call and the endpoint's 64 KiB buffer holds.
    let batch = udp.max_gso_segments().clamp(1, 40);
    let mut builder = Vinc::builder();
    if let Some(seed) = seed {
        builder = builder.seed(seed).map_err(io_err)?;
    }
    let ep = builder
        .alpn(ALPN.to_vec())
        .limits(limits)
        .local_addr(sock.local_addr()?)
        // The loopback device carries datagrams of any size, so the endpoint may probe its largest. `VINC_BENCH_MTU`
        // states another interface size, such as the 1500 bytes of an ordinary network.
        .mtu(
            std::env::var("VINC_BENCH_MTU")
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(u16::MAX),
        )
        .batch(batch)
        .build_io(Net { sock, udp })
        .map_err(io_err)?;
    if run {
        let runner = ep.clone();
        nuclei::spawn_local(async move {
            let _ = runner.run().await;
        })
        .detach();
    }
    Ok(ep)
}

/// Serve every stream of every session `ep` accepts, on this worker.
async fn accept_all(ep: Ep) {
    while let Some(inc) = ep.accept().await {
        let conn = inc.into_connection();
        nuclei::spawn_local(async move {
            while let Ok((tx, rx)) = conn.accept_bi().await {
                nuclei::spawn_local(async move {
                    let _ = super::handle(tx, rx).await;
                })
                .detach();
            }
        })
        .detach();
    }
}

/// One endpoint on every worker of the runtime, all with one identity, each on a socket of its own on one port. The
/// first socket of the group picks the port; it leaves once every endpoint has its own, before any peer is told the
/// address, so nothing arrives on it. The address of the group is the first endpoint's.
async fn serve_per_core() -> io::Result<String> {
    let mut seed = [0u8; 32];
    SoftwareStore::new()
        .and_then(|mut s| s.random(&mut seed))
        .map_err(|e| io::Error::other(e.to_string()))?;
    let probe = socket(0, true)?;
    let port = probe.local_addr()?.port();
    let rt = nuclei::RuntimeHandle::current();
    let workers = rt.workers().max(1);
    let (ready, mut started) = mpsc::unbounded::<io::Result<String>>();
    for w in 0..workers {
        let ready = ready.clone();
        let job = move || async move {
            match socket(port, true).and_then(|s| endpoint(s, Limits::default(), Some(&seed), true)) {
                Ok(ep) => {
                    let _ = ready.unbounded_send(Ok(ep.addr().ticket()));
                    drop(ready);
                    accept_all(ep).await;
                }
                Err(e) => {
                    let _ = ready.unbounded_send(Err(e));
                }
            }
        };
        if rt.workers() == 0 {
            nuclei::spawn_local(job()).detach();
        } else {
            rt.spawn_local_on_worker(w, job)?.detach();
        }
    }
    drop(ready);
    let mut addr = None;
    for _ in 0..workers {
        let ticket = started
            .next()
            .await
            .ok_or_else(|| io::Error::other("a worker's endpoint did not start"))??;
        addr.get_or_insert(ticket);
    }
    drop(probe);
    addr.ok_or_else(|| io::Error::other("no endpoint started"))
}

/// The library under test.
pub struct Vinc1;

impl Tx for SendStream<H> {
    async fn write_all(&mut self, b: &[u8]) -> io::Result<()> {
        SendStream::write_all(self, b).await.map_err(io_err)
    }
    async fn finish(&mut self) -> io::Result<()> {
        SendStream::finish(self).await.map_err(io_err)
    }
}

impl Rx for RecvStream<H> {
    async fn read(&mut self, b: &mut [u8]) -> io::Result<usize> {
        RecvStream::read(self, b).await.map(|n| n.unwrap_or(0)).map_err(io_err)
    }
}

impl Lib for Vinc1 {
    fn name() -> &'static str {
        "vinc"
    }

    const RESUMES: bool = true;
    const PER_CORE: bool = true;
    type Ep = Ep;
    type Conn = Conn;
    type Tx = SendStream<H>;
    type Rx = RecvStream<H>;

    fn run<T>(f: impl Future<Output = T>) -> T {
        match nuclei::Builder::new().build() {
            Ok(rt) => rt.block_on(f),
            Err(e) => panic!("the runtime did not start: {e}"),
        }
    }

    fn spawn(f: impl Future<Output = ()> + 'static) {
        nuclei::spawn_local(f).detach();
    }

    fn spawn_client<F: Future<Output = ()> + 'static>(i: usize, make: impl FnOnce() -> F + Send + 'static) -> bool {
        let rt = nuclei::RuntimeHandle::current();
        let workers = rt.workers();
        if workers == 0 || !super::per_core() {
            Self::spawn(make());
            return true;
        }
        rt.spawn_local_on_worker(i % workers, make)
            .map(nuclei::Task::detach)
            .is_ok()
    }

    async fn sleep(d: Duration) {
        nuclei::time::sleep(d).await;
    }

    async fn serve() -> io::Result<String> {
        if super::per_core() {
            return serve_per_core().await;
        }
        let ep = bind(Limits::default(), true)?;
        let addr = ep.addr().ticket();
        nuclei::spawn_local(accept_all(ep)).detach();
        Ok(addr)
    }

    async fn client() -> io::Result<Ep> {
        bind(
            Limits {
                connections: 1,
                ..Limits::default()
            },
            false,
        )
    }

    async fn burst_client() -> io::Result<Ep> {
        // A host that keeps connections drives its endpoint (`run()`); the undriven reading leaves it to the dial.
        bind(
            Limits {
                connections: 1,
                ..Limits::default()
            },
            super::driven(),
        )
    }

    async fn connect(ep: &Ep, addr: &str) -> io::Result<Conn> {
        let addr = NodeAddr::parse(addr).map_err(io_err)?;
        ep.connect(addr, ALPN).await.map_err(io_err)
    }

    async fn open(conn: &Conn) -> io::Result<(SendStream<H>, RecvStream<H>)> {
        conn.open_bi().await.map_err(io_err)
    }

    async fn close(ep: &Ep, conn: &Conn) {
        ep.close_peer(&conn.remote()).await;
    }

    async fn shutdown(ep: Ep) {
        ep.close().await;
    }
}

#[cfg(test)]
#[allow(unused_imports)]
mod tests {
    use super::*;
    use std::sync::atomic::Ordering::Relaxed;

    /// Run `f` on a runtime of two workers.
    fn on_two_workers<T>(f: impl Future<Output = T>) -> T {
        let rt = nuclei::Builder::new().worker_threads(2).build().unwrap();
        rt.block_on(f)
    }

    /// The worker each of `n` clients started by [`Vinc1::spawn_client`] ran on, in client order.
    async fn workers_of(n: usize) -> Vec<Option<usize>> {
        let (tx, mut rx) = mpsc::unbounded::<(usize, Option<usize>)>();
        for i in 0..n {
            let tx = tx.clone();
            let started = Vinc1::spawn_client(i, move || async move {
                let _ = tx.unbounded_send((i, nuclei::runtime::worker_index()));
            });
            assert!(started, "client {i} was started");
        }
        drop(tx);
        let mut at = vec![None; n];
        let deadline = Box::pin(nuclei::time::sleep(Duration::from_secs(30)));
        let all = Box::pin(async {
            while let Some((i, w)) = rx.next().await {
                at[i] = w;
            }
        });
        let ended = futures::future::select(all, deadline).await;
        let ran = matches!(ended, futures::future::Either::Left(_));
        drop(ended);
        assert!(ran, "every client ran");
        at
    }

    #[test]
    fn per_core_clients_run_on_worker_i_modulo_the_workers() {
        super::super::PER_CORE.store(true, Relaxed);
        let at = on_two_workers(workers_of(6));
        assert_eq!(at, [Some(0), Some(1), Some(0), Some(1), Some(0), Some(1)]);
    }

    #[test]
    fn without_per_core_a_client_runs_where_it_was_started() {
        super::super::PER_CORE.store(false, Relaxed);
        let at = on_two_workers(workers_of(4));
        assert!(
            at.iter().all(|w| w == &at[0]),
            "one-endpoint clients all run on one thread: {at:?}"
        );
    }
}
