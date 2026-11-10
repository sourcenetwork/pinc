//! The comparison harness for VINC, on the nuclei runtime the way a host would run it (see `compare/mod.rs`).
//!
//! Defaults: `Vinc::builder()` with the default limits on the server (1024 sessions, 512 chunks of 16 KiB per session,
//! 256 KiB stream windows). A client endpoint holds one session, so it asks for exactly one (`connections: 1`); the
//! endpoint reserves its tables for the smallest shape that holds the request, which is what the documentation tells a
//! host to do. The harness needs types it can name, and the closures of an endpoint have none, so the endpoint,
//! its connections and its streams are held behind small object-safe traits; every call through them boxes its
//! future, which costs one allocation per call that a host calling the facade directly does not pay (the
//! `messages_allocate_nothing_in_the_facade` test measures the facade itself). The futures are marked `Send`
//! without proof because the proof is not available for an unnamed closure type: every task of this bench runs on the
//! one thread that spawned it (`spawn_local`), so nothing is ever sent. Run with `just compare`; the binary is not meant to be started by hand.
#![allow(
    missing_docs,
    unsafe_code,
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
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

use compare::{Counting, Lib, Rx, Tx};
use nuclei::Handle;
use vinc::{Connection, Endpoint, Hosted, Limits, NodeAddr, NodeId, RecvStream, SendStream, Vinc};

#[global_allocator]
static ALLOC: Counting = Counting;

const ALPN: &[u8] = b"bench/1";

fn io_err(e: vinc::Error) -> io::Error {
    io::Error::other(e.to_string())
}

/// A future declared `Send` without proof; see the module docs for why that holds here.
struct Local<F>(F);

// SAFETY: every future wrapped here is created and polled on one thread (the bench spawns with `spawn_local` and runs
// on a single `block_on`), so it never crosses threads.
#[allow(unsafe_code)]
unsafe impl<F> Send for Local<F> {}

impl<F: Future> Future for Local<F> {
    type Output = F::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<F::Output> {
        // SAFETY: the field is never moved out of the pinned wrapper.
        #[allow(unsafe_code)]
        unsafe { self.map_unchecked_mut(|l| &mut l.0) }.poll(cx)
    }
}

type Fut<'a, T> = Pin<Box<dyn Future<Output = T> + Send + 'a>>;

fn erase<'a, T>(f: impl Future<Output = T> + 'a) -> Fut<'a, T> {
    Box::pin(Local(f))
}

trait TxDyn: Send {
    fn write_all<'a>(&'a mut self, b: &'a [u8]) -> Fut<'a, io::Result<()>>;
    fn finish(&mut self) -> Fut<'_, io::Result<()>>;
}

trait RxDyn: Send {
    fn read<'a>(&'a mut self, b: &'a mut [u8]) -> Fut<'a, io::Result<usize>>;
}

trait ConnDyn: Send + Sync {
    fn remote(&self) -> NodeId;
    fn open(&self) -> Fut<'_, io::Result<(Box<dyn TxDyn>, Box<dyn RxDyn>)>>;
}

trait EpDyn: Send + Sync {
    fn connect(&self, addr: NodeAddr) -> Fut<'_, io::Result<Arc<dyn ConnDyn>>>;
    fn close_peer(&self, node: NodeId) -> Fut<'_, ()>;
    fn shutdown(&self) -> Fut<'_, ()>;
}

impl<H: Hosted + 'static> TxDyn for SendStream<H> {
    fn write_all<'a>(&'a mut self, b: &'a [u8]) -> Fut<'a, io::Result<()>> {
        erase(async move { SendStream::write_all(self, b).await.map_err(io_err) })
    }

    fn finish(&mut self) -> Fut<'_, io::Result<()>> {
        erase(async move { SendStream::finish(self).await.map_err(io_err) })
    }
}

impl<H: Hosted + 'static> RxDyn for RecvStream<H> {
    fn read<'a>(&'a mut self, b: &'a mut [u8]) -> Fut<'a, io::Result<usize>> {
        erase(async move { RecvStream::read(self, b).await.map(|n| n.unwrap_or(0)).map_err(io_err) })
    }
}

impl<H: Hosted + 'static> ConnDyn for Connection<H> {
    fn remote(&self) -> NodeId {
        Connection::remote(self)
    }

    fn open(&self) -> Fut<'_, io::Result<(Box<dyn TxDyn>, Box<dyn RxDyn>)>> {
        erase(async move {
            let (tx, rx) = self.open_bi().await.map_err(io_err)?;
            Ok((Box::new(tx) as Box<dyn TxDyn>, Box::new(rx) as Box<dyn RxDyn>))
        })
    }
}

impl<H: Hosted + 'static> EpDyn for Endpoint<H> {
    fn connect(&self, addr: NodeAddr) -> Fut<'_, io::Result<Arc<dyn ConnDyn>>> {
        erase(async move {
            let c = Endpoint::connect(self, addr, ALPN).await.map_err(io_err)?;
            Ok(Arc::new(c) as Arc<dyn ConnDyn>)
        })
    }

    fn close_peer(&self, node: NodeId) -> Fut<'_, ()> {
        erase(async move { Endpoint::close_peer(self, &node).await })
    }

    fn shutdown(&self) -> Fut<'_, ()> {
        erase(async move { Endpoint::close(self).await })
    }
}

async fn bind(limits: Limits) -> io::Result<Arc<dyn EpDyn>> {
    let sock = Arc::new(Handle::<UdpSocket>::bind(SocketAddr::from(([127, 0, 0, 1], 0))).await?);
    let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
    let ep = Vinc::builder()
        .alpn(ALPN.to_vec())
        .limits(limits)
        .local_addr(sock.local_addr()?)
        .build(
            async move |buf: &mut [u8]| r.recv_from(buf).await,
            async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
            async |at: Instant| nuclei::time::sleep_until_precise(at).await,
        )
        .map_err(io_err)?;
    let runner = ep.clone();
    nuclei::spawn_local(async move {
        let _ = runner.run().await;
    })
    .detach();
    Ok(Arc::new(ep))
}

struct Vinc1;

impl Tx for Box<dyn TxDyn> {
    async fn write_all(&mut self, b: &[u8]) -> io::Result<()> {
        TxDyn::write_all(&mut **self, b).await
    }

    async fn finish(&mut self) -> io::Result<()> {
        TxDyn::finish(&mut **self).await
    }
}

impl Rx for Box<dyn RxDyn> {
    async fn read(&mut self, b: &mut [u8]) -> io::Result<usize> {
        RxDyn::read(&mut **self, b).await
    }
}

impl Lib for Vinc1 {
    fn name() -> &'static str {
        "vinc"
    }

    const RESUMES: bool = true;
    type Ep = Arc<dyn EpDyn>;
    type Conn = Arc<dyn ConnDyn>;
    type Tx = Box<dyn TxDyn>;
    type Rx = Box<dyn RxDyn>;

    fn run<T>(f: impl Future<Output = T>) -> T {
        match nuclei::Builder::new().build() {
            Ok(rt) => rt.block_on(f),
            Err(e) => panic!("the runtime did not start: {e}"),
        }
    }

    fn spawn(f: impl Future<Output = ()> + Send + 'static) {
        // One endpoint per core: its tasks stay on the thread that started them.
        nuclei::spawn_local(f).detach();
    }

    async fn sleep(d: Duration) {
        nuclei::time::sleep(d).await;
    }

    async fn serve() -> io::Result<String> {
        let sock = Arc::new(Handle::<UdpSocket>::bind(SocketAddr::from(([127, 0, 0, 1], 0))).await?);
        let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
        let ep = Vinc::builder()
            .alpn(ALPN.to_vec())
            .local_addr(sock.local_addr()?)
            .build(
                async move |buf: &mut [u8]| r.recv_from(buf).await,
                async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
                async |at: Instant| nuclei::time::sleep_until_precise(at).await,
            )
            .map_err(io_err)?;
        let addr = ep.addr().ticket();
        nuclei::spawn_local(async move {
            while let Some(inc) = ep.accept().await {
                let conn = inc.into_connection();
                nuclei::spawn_local(async move {
                    while let Ok((tx, rx)) = conn.accept_bi().await {
                        nuclei::spawn_local(async move {
                            let _ =
                                compare::handle(Box::new(tx) as Box<dyn TxDyn>, Box::new(rx) as Box<dyn RxDyn>).await;
                        })
                        .detach();
                    }
                })
                .detach();
            }
        })
        .detach();
        Ok(addr)
    }

    async fn client() -> io::Result<Arc<dyn EpDyn>> {
        bind(Limits {
            connections: 1,
            ..Limits::default()
        })
        .await
    }

    async fn connect(ep: &Arc<dyn EpDyn>, addr: &str) -> io::Result<Arc<dyn ConnDyn>> {
        ep.connect(NodeAddr::parse(addr).map_err(io_err)?).await
    }

    async fn open(conn: &Arc<dyn ConnDyn>) -> io::Result<(Box<dyn TxDyn>, Box<dyn RxDyn>)> {
        conn.open().await
    }

    async fn close(ep: &Arc<dyn EpDyn>, conn: &Arc<dyn ConnDyn>) {
        ep.close_peer(conn.remote()).await;
    }

    async fn shutdown(ep: Arc<dyn EpDyn>) {
        ep.shutdown().await;
    }
}

fn main() {
    compare::main::<Vinc1>();
}
