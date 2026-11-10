//! The comparison harness for VINC, on the nuclei runtime the way a host would run it (see `compare/mod.rs`).
//!
//! Defaults: `Vinc::builder()` with the default limits on the server (1024 sessions, 512 chunks of 16 KiB per session,
//! 256 KiB stream windows). A client endpoint holds one session, so it asks for exactly one (`connections: 1`); the
//! endpoint reserves its tables for the smallest shape that holds the request, which is what the documentation tells a
//! host to do. The endpoint's three I/O calls are a type here (`Net`, an `Io`), not closures, only so the harness can
//! write the endpoint's type down; the facade's own calls are made directly, with no boxing and no `unsafe`.
//!
//! One endpoint per core, as the facade is meant to be run: the server runs one endpoint on every worker of the
//! runtime, all with one identity, each on its own socket of one port (`SO_REUSEPORT`: the kernel spreads peers among
//! them by their address), and the clients of the many-connection scenario are spread over the workers, each endpoint
//! made, driven and dropped on its worker. The other scenarios' clients run on the thread that drives them.
//!
//! Limits of the per-worker server, stated: a peer's datagrams reach the worker its address hashes to, so a peer that
//! moves to another address (or dials again from a new socket) may land on an endpoint that holds neither its session
//! nor the ticket it was given, and then dials as a stranger (a full handshake instead of a resumption); and each
//! endpoint caps its own half-open sessions.
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

mod compare;

use std::future::Future;
use std::io;
use std::net::{SocketAddr, UdpSocket};
use std::rc::Rc;
use std::time::{Duration, Instant};

use compare::{Counting, Lib, Rx, Tx};
use futures::StreamExt;
use futures::channel::mpsc;
use nuclei::Handle;
use nuclei::net::UdpSocketBuilder;
use vinc::{AllowAll, Connection, Endpoint, Io, IoHost, Limits, NodeAddr, RecvStream, SendStream, Vinc};
use vinc_keystore::SoftwareStore;

#[global_allocator]
static ALLOC: Counting = Counting;

const ALPN: &[u8] = b"bench/1";

fn io_err(e: vinc::Error) -> io::Error {
    io::Error::other(e.to_string())
}

/// The endpoint's socket and timer: nuclei's, called directly.
struct Net {
    sock: Rc<Handle<UdpSocket>>,
}

impl Io for Net {
    async fn recv(&self, buf: &mut [u8]) -> io::Result<(usize, SocketAddr, usize)> {
        let (n, from) = self.sock.recv_from(buf).await?;
        Ok((n, from, n))
    }

    async fn send(&self, buf: &[u8], to: SocketAddr, segment: usize) -> io::Result<usize> {
        let mut sent = 0;
        for d in buf.chunks(segment.max(1)) {
            self.sock.send_to(d, to).await?;
            sent += 1;
        }
        Ok(sent)
    }

    async fn sleep(&self, at: Instant) {
        nuclei::time::sleep_until_precise(at).await;
    }
}

type H = IoHost<Net, SoftwareStore, AllowAll>;
type Ep = Endpoint<H>;
type Conn = Connection<H>;

async fn bind(limits: Limits, run: bool) -> io::Result<Ep> {
    let sock = Handle::<UdpSocket>::bind(SocketAddr::from(([127, 0, 0, 1], 0))).await?;
    endpoint(sock, limits, None, run)
}

/// An endpoint over `sock`, with the identity of `seed` (a fresh one without), driven by a task of its own if `run`.
fn endpoint(sock: Handle<UdpSocket>, limits: Limits, seed: Option<&[u8; 32]>, run: bool) -> io::Result<Ep> {
    let sock = Rc::new(sock);
    let mut builder = Vinc::builder();
    if let Some(seed) = seed {
        builder = builder.seed(seed).map_err(io_err)?;
    }
    let ep = builder
        .alpn(ALPN.to_vec())
        .limits(limits)
        .local_addr(sock.local_addr()?)
        .batch(1)
        .build_io(Net { sock })
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

/// A loopback socket of the group that shares `port` (`SO_REUSEPORT`); port 0 picks a free one.
fn shared_socket(port: u16) -> io::Result<Handle<UdpSocket>> {
    let builder = UdpSocketBuilder::new_v4()?;
    builder.set_reuseport(true)?;
    builder.bind(SocketAddr::from(([127, 0, 0, 1], port)))
}

/// Serve every stream of every session `ep` accepts, on this worker.
async fn accept_all(ep: Ep) {
    while let Some(inc) = ep.accept().await {
        let conn = inc.into_connection();
        nuclei::spawn_local(async move {
            while let Ok((tx, rx)) = conn.accept_bi().await {
                nuclei::spawn_local(async move {
                    let _ = compare::handle(tx, rx).await;
                })
                .detach();
            }
        })
        .detach();
    }
}

struct Vinc1;

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

    fn spawn_client<F: Future<Output = ()> + 'static>(i: usize, make: impl FnOnce() -> F + Send + 'static) {
        let rt = nuclei::RuntimeHandle::current();
        match rt.workers() {
            0 => nuclei::spawn_local(make()).detach(),
            n => match rt.spawn_local_on_worker(i % n, make) {
                Ok(task) => task.detach(),
                Err(e) => panic!("worker {} took no client: {e}", i % n),
            },
        }
    }

    async fn sleep(d: Duration) {
        nuclei::time::sleep(d).await;
    }

    async fn serve() -> io::Result<String> {
        let mut seed = [0u8; 32];
        getrandom::fill(&mut seed).map_err(|e| io::Error::other(e.to_string()))?;
        // The first socket of the group picks the port; it leaves once every endpoint has its own, before any peer is
        // told the address, so nothing arrives on it.
        let probe = shared_socket(0)?;
        let port = probe.local_addr()?.port();
        let rt = nuclei::RuntimeHandle::current();
        let workers = rt.workers();
        let (ready, mut started) = mpsc::unbounded::<io::Result<String>>();
        for w in 0..workers.max(1) {
            let ready = ready.clone();
            let job = move || async move {
                let ep = shared_socket(port).and_then(|s| endpoint(s, Limits::default(), Some(&seed), true));
                match ep {
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
            if workers == 0 {
                nuclei::spawn_local(job()).detach();
            } else {
                rt.spawn_local_on_worker(w, job)?.detach();
            }
        }
        drop(ready);
        let mut addr = None;
        for _ in 0..workers.max(1) {
            let ticket = started
                .next()
                .await
                .ok_or_else(|| io::Error::other("a worker's endpoint did not start"))??;
            addr.get_or_insert(ticket);
        }
        drop(probe);
        addr.ok_or_else(|| io::Error::other("no endpoint started"))
    }

    async fn client() -> io::Result<Ep> {
        bind(
            Limits {
                connections: 1,
                ..Limits::default()
            },
            false,
        )
        .await
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

fn main() {
    compare::main::<Vinc1>();
}
