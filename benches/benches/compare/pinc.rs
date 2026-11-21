//! The comparison harness for PINC, on the nuclei runtime the way a host would run it (see `compare/mod.rs`).
//!
//! Defaults: `Pinc::builder()` with the default limits on the server (1024 sessions, 512 chunks of 16 KiB per session,
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
//! Limits of the per-core server, stated: a peer's datagrams reach the endpoint its address hashes to. A peer that
//! moves to another address (a new socket, a changed port or address) may land on an endpoint that holds neither its
//! session nor the tickets it was given; its session then ends at its timeouts and it dials again, as a stranger (a
//! full handshake, not a resumption). A resumption from the same socket reaches the same endpoint and resumes. Each
//! endpoint also limits its own sessions and half-open dials.
//!
//! A per-core process builds its runtime with the handoff off (`runtime`): an endpoint's tasks are bound to the thread
//! that made them, so a handoff would move only the worker's shard and leave the endpoint serving off its worker. With
//! it off a long poll only delays its own worker, and every endpoint stays on the worker it was placed on for its life.
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
use pinc::{AllowAll, Connection, Endpoint, Io, IoHost, Limits, NodeAddr, Pinc, RecvStream, SendStream};
use pinc_keystore::{KeyStore, SoftwareStore};
use quinn_udp::{RecvMeta, Transmit, UdpSockRef, UdpSocketState};

const ALPN: &[u8] = b"bench/1";
/// What the socket's send and receive buffers are asked to hold.
const SOCKET_BUFFER: u32 = 8 << 20;

/// The first polls of endpoint drivers, so a test can see that one ran.
#[cfg(test)]
static DRIVER_POLLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The connections each worker of a test runtime accepted.
#[cfg(test)]
static ACCEPTED: [std::sync::atomic::AtomicUsize; 2] = [
    std::sync::atomic::AtomicUsize::new(0),
    std::sync::atomic::AtomicUsize::new(0),
];

fn io_err(e: pinc::Error) -> io::Error {
    io::Error::other(e.to_string())
}

/// Every UDP payload this process's sockets sent.
static SENT: super::Sent = super::Sent::new();

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
                Ok(()) => {
                    SENT.add(buf.len(), if count > 1 { segment } else { buf.len() });
                    return Ok(count);
                }
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
    let mut builder = Pinc::builder();
    if let Some(seed) = seed {
        builder = builder.seed(seed).map_err(io_err)?;
    }
    let ep = builder
        .alpn(ALPN.to_vec())
        .limits(limits)
        .local_addr(sock.local_addr()?)
        // The loopback device carries datagrams of any size, so the endpoint may probe its largest. `PINC_BENCH_MTU`
        // states another interface size, such as the 1500 bytes of an ordinary network.
        .mtu(
            std::env::var("PINC_BENCH_MTU")
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
            #[cfg(test)]
            DRIVER_POLLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
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
        #[cfg(test)]
        if let Some(w) = nuclei::runtime::worker_index().and_then(|w| ACCEPTED.get(w)) {
            w.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
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
    let workers = rt.workers();
    if workers == 0 {
        return Err(io::Error::other("the runtime has no worker to run an endpoint on"));
    }
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
        rt.spawn_local_on_worker(w, job)?.detach();
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

/// The runtime of this process, from `builder`. A per-core process never hands a worker's shard off (see the module's
/// top comment); the one-endpoint path keeps nuclei's defaults. The harness and its tests build every runtime here.
fn runtime(builder: nuclei::Builder) -> io::Result<nuclei::Runtime> {
    if super::per_core() {
        builder.handoff_after(None)
    } else {
        builder
    }
    .build()
}

/// The library under test.
pub struct Pinc1;

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

impl Lib for Pinc1 {
    fn name() -> &'static str {
        "pinc"
    }

    const RESUMES: bool = true;
    const PER_CORE: bool = true;
    type Ep = Ep;
    type Conn = Conn;
    type Tx = SendStream<H>;
    type Rx = RecvStream<H>;

    fn run<T>(f: impl Future<Output = T>) -> T {
        match runtime(nuclei::Builder::new()) {
            Ok(rt) => rt.block_on(f),
            Err(e) => panic!("the runtime did not start: {e}"),
        }
    }

    fn spawn(f: impl Future<Output = ()> + 'static) {
        nuclei::spawn_local(f).detach();
    }

    fn spawn_client<F: Future<Output = ()> + 'static>(
        i: usize,
        make: impl FnOnce() -> F + Send + 'static,
    ) -> io::Result<()> {
        let rt = nuclei::RuntimeHandle::current();
        if !super::per_core() {
            Self::spawn(make());
            return Ok(());
        }
        let workers = rt.workers();
        if workers == 0 {
            return Err(io::Error::other("the runtime has no worker to run a client on"));
        }
        rt.spawn_local_on_worker(i % workers, make)?.detach();
        Ok(())
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
        let driven = super::driven();
        let ep = bind(
            Limits {
                connections: 1,
                ..Limits::default()
            },
            driven,
        )?;
        if driven {
            // The driver has had its first poll when the endpoint is returned, as the other libraries' drivers
            // start when their endpoint is made, so what it allocates there is not read as the connection's.
            nuclei::task::yield_now().await;
        }
        Ok(ep)
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

    async fn wire(conn: &Conn) -> super::Wire {
        let (max, mean) = SENT.read();
        let (kx_group, kx_source) = if conn.resumed() {
            (
                "psk+X25519",
                "protocol: a resumption is the ticket's PSK with a fresh X25519 (pinc-security message.rs ResumeHello)",
            )
        } else {
            (
                "X25519+ML-KEM-768",
                "protocol: every full or prekey handshake is X25519 plus ML-KEM-768 (pinc-security lib.rs)",
            )
        };
        let stats = conn.stats().await.ok();
        super::Wire {
            max_udp_payload: max,
            mean_udp_payload: mean,
            udp_source: format!(
                "socket: every send of this process, at the harness's socket; path datagram size now {}",
                stats.map_or_else(|| "unknown".to_owned(), |s| s.mtu.to_string())
            ),
            kx_group: kx_group.into(),
            kx_source: kx_source.into(),
            cwnd: stats.map(|s| s.cwnd),
            knobs: String::new(),
        }
    }
}

#[cfg(test)]
#[allow(unused_imports)]
mod tests {
    use super::*;
    use std::sync::atomic::Ordering::Relaxed;

    /// Run `f` on a runtime of two workers.
    fn on_two_workers<T>(f: impl Future<Output = T>) -> T {
        runtime(nuclei::Builder::new().worker_threads(2)).unwrap().block_on(f)
    }

    /// The worker each of `n` clients started by [`Pinc1::spawn_client`] ran on, in client order.
    async fn workers_of(n: usize) -> Vec<Option<usize>> {
        let (tx, mut rx) = mpsc::unbounded::<(usize, Option<usize>)>();
        for i in 0..n {
            let tx = tx.clone();
            let started = Pinc1::spawn_client(i, move || async move {
                let _ = tx.unbounded_send((i, nuclei::runtime::worker_index()));
            });
            assert!(started.is_ok(), "client {i} was started");
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

    /// Run `f` with the process-wide switches `per_core` and `driven` set, then put back what was found.
    fn with_switches<T>(per_core: bool, driven: bool, f: impl FnOnce() -> T) -> T {
        use super::super::{DRIVEN, PER_CORE, SwitchGuard};
        let _switches = SwitchGuard::hold();
        PER_CORE.store(per_core, Relaxed);
        DRIVEN.store(driven, Relaxed);
        f()
    }

    #[test]
    fn per_core_clients_run_on_worker_i_modulo_the_workers() {
        let at = with_switches(true, false, || on_two_workers(workers_of(6)));
        assert_eq!(at, [Some(0), Some(1), Some(0), Some(1), Some(0), Some(1)]);
    }

    #[test]
    fn without_per_core_a_client_runs_where_it_was_started() {
        let at = with_switches(false, false, || on_two_workers(workers_of(4)));
        assert!(
            at.iter().all(|w| w == &at[0]),
            "one-endpoint clients all run on one thread: {at:?}"
        );
    }

    #[test]
    fn a_driven_client_endpoint_has_had_its_drivers_first_poll_when_it_is_returned() {
        use std::sync::atomic::Ordering::Relaxed;
        let polled = |driven| {
            with_switches(false, driven, || {
                on_two_workers(async {
                    let before = DRIVER_POLLS.load(Relaxed);
                    let ep = Pinc1::burst_client().await.unwrap();
                    let after = DRIVER_POLLS.load(Relaxed);
                    drop(ep);
                    after - before
                })
            })
        };
        assert_eq!(polled(true), 1, "the driver ran before burst_client returned");
        assert_eq!(polled(false), 0, "an undriven endpoint has no driver");
    }

    #[test]
    fn a_driven_client_started_on_a_worker_has_had_its_drivers_first_poll_when_it_is_returned() {
        let polls = with_switches(true, true, || {
            on_two_workers(async {
                let (tx, mut rx) = mpsc::unbounded::<usize>();
                let started = Pinc1::spawn_client(1, move || async move {
                    let before = DRIVER_POLLS.load(Relaxed);
                    let ep = Pinc1::burst_client().await.unwrap();
                    let _ = tx.unbounded_send(DRIVER_POLLS.load(Relaxed) - before);
                    drop(ep);
                });
                assert!(started.is_ok(), "the client was started");
                let limit = Box::pin(nuclei::time::sleep(Duration::from_secs(30)));
                match futures::future::select(Box::pin(rx.next()), limit).await {
                    futures::future::Either::Left((Some(n), _)) => n,
                    _ => panic!("the client did not report in 30 s"),
                }
            })
        });
        assert_eq!(polls, 1, "the driver ran before burst_client returned on a worker");
    }

    #[test]
    fn a_per_core_runtime_keeps_a_worker_held_past_the_handoff_threshold_and_its_tasks() {
        let (reads, handoffs) = with_switches(true, false, || {
            on_two_workers(async {
                let rt = nuclei::RuntimeHandle::current();
                let (tx, mut rx) = mpsc::unbounded::<(Option<usize>, Option<usize>)>();
                rt.spawn_local_on_worker(0, move || async move {
                    let first = nuclei::runtime::worker_index();
                    // The stimulus: a poll held past the default threshold of 10 ms.
                    std::thread::sleep(Duration::from_millis(50));
                    nuclei::task::yield_now().await;
                    let _ = tx.unbounded_send((first, nuclei::runtime::worker_index()));
                })
                .unwrap()
                .detach();
                let limit = Box::pin(nuclei::time::sleep(Duration::from_secs(30)));
                let futures::future::Either::Left((Some(reads), _)) =
                    futures::future::select(Box::pin(rx.next()), limit).await
                else {
                    panic!("the job did not report in 30 s");
                };
                let stats = rt.stats();
                let shard = stats.shards.iter().find(|s| s.worker == Some(0)).unwrap();
                (reads, shard.handoffs)
            })
        });
        assert_eq!(reads, (Some(0), Some(0)), "the job stayed on worker 0 in both polls");
        assert_eq!(handoffs, 0, "the worker's shard was not handed off");
    }

    #[test]
    fn a_per_core_server_or_client_on_a_runtime_without_workers_fails() {
        let (served, started) = with_switches(true, false, || {
            runtime(nuclei::Builder::new().worker_threads(0))
                .unwrap()
                .block_on(async { (serve_per_core().await, Pinc1::spawn_client(0, || async {})) })
        });
        assert!(served.is_err(), "a server with no worker to run on failed: {served:?}");
        assert!(started.is_err(), "a client with no worker to run on failed");
    }

    #[test]
    fn the_per_core_server_serves_every_dial_from_both_workers() {
        use std::sync::atomic::Ordering::Relaxed;
        let served = with_switches(true, false, || {
            on_two_workers(async {
                let addr = serve_per_core().await.unwrap();
                let before: Vec<usize> = ACCEPTED.iter().map(|a| a.load(Relaxed)).collect();
                let mut held = Vec::new();
                for _ in 0..64 {
                    let ep = Pinc1::client().await.unwrap();
                    // A bound on the dial: a lost datagram must fail the test, not hang it.
                    let dial = Box::pin(Pinc1::hello(&ep, &addr, false));
                    let limit = Box::pin(nuclei::time::sleep(Duration::from_secs(30)));
                    let futures::future::Either::Left((conn, _)) = futures::future::select(dial, limit).await else {
                        panic!("a dial was not served in 30 s");
                    };
                    held.push((ep, conn.unwrap()));
                }
                let after: Vec<usize> = ACCEPTED.iter().map(|a| a.load(Relaxed)).collect();
                after.iter().zip(&before).map(|(a, b)| a - b).collect::<Vec<_>>()
            })
        });
        assert_eq!(
            served.iter().sum::<usize>(),
            64,
            "every dial was accepted once: {served:?}"
        );
        // The kernel hashes each peer's address to a socket: all 64 on one worker has a chance of 2^-63.
        assert!(served.iter().all(|&s| s > 0), "both workers served some: {served:?}");
    }
}
