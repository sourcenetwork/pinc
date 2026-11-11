//! The comparison harness for VINC, on the nuclei runtime the way a host would run it (see `compare/mod.rs`).
//!
//! Defaults: `Vinc::builder()` with the default limits on the server (1024 sessions, 512 chunks of 16 KiB per session,
//! 256 KiB stream windows). A client endpoint holds one session, so it asks for exactly one (`connections: 1`); the
//! endpoint reserves its tables for the smallest shape that holds the request, which is what the documentation tells a
//! host to do. The endpoint's three I/O calls are a type here (`Net`, an `Io`), not closures, only so the harness can
//! write the endpoint's type down; the facade's own calls are made directly, with no boxing and no `unsafe`. Everything
//! runs on the thread that started it, one endpoint per thread, as the facade is meant to be used.
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
use nuclei::Handle;
use nuclei::net::UdpSocketBuilder;
use vinc::{AllowAll, Connection, Endpoint, Io, IoHost, Limits, NodeAddr, RecvStream, SendStream, Vinc};
use vinc_keystore::SoftwareStore;

const ALPN: &[u8] = b"bench/1";
/// What the socket's send and receive buffers are asked to hold.
const SOCKET_BUFFER: u32 = 8 << 20;

fn io_err(e: vinc::Error) -> io::Error {
    io::Error::other(e.to_string())
}

/// The endpoint's socket and timer: nuclei's, called directly.
pub struct Net {
    sock: Rc<Handle<UdpSocket>>,
}

impl Io for Net {
    async fn recv(&self, buf: &mut [u8]) -> io::Result<(usize, SocketAddr, usize)> {
        // A datagram that is already there costs one system call; only an empty socket is waited on.
        let (n, from) = match self.sock.try_recv_from(buf) {
            Ok(got) => got,
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => self.sock.recv_from(buf).await?,
            Err(e) => return Err(e),
        };
        Ok((n, from, n))
    }

    async fn send(&self, buf: &[u8], to: SocketAddr, segment: usize) -> io::Result<usize> {
        let mut sent = 0;
        for d in buf.chunks(segment.max(1)) {
            match self.sock.try_send_to(d, to) {
                Ok(_) => {}
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    self.sock.send_to(d, to).await?;
                }
                Err(e) => return Err(e),
            }
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

fn bind(limits: Limits, run: bool) -> io::Result<Ep> {
    // Socket buffers as a busy host sizes them (the system clamps them to its limit): the default of about 200 KiB
    // drops the first flights of a few hundred peers dialing at once.
    let builder = UdpSocketBuilder::new_v4()?;
    builder.set_recv_buffer_size(SOCKET_BUFFER)?;
    builder.set_send_buffer_size(SOCKET_BUFFER)?;
    let sock = Rc::new(builder.bind(SocketAddr::new(super::bind_ip()?, 0))?);
    let ep = Vinc::builder()
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

    async fn sleep(d: Duration) {
        nuclei::time::sleep(d).await;
    }

    async fn serve() -> io::Result<String> {
        let ep = bind(Limits::default(), true)?;
        let addr = ep.addr().ticket();
        nuclei::spawn_local(async move {
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
        })
        .detach();
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

