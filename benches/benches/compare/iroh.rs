//! The comparison harness for iroh (see `compare/mod.rs`).
//!
//! Defaults: `Endpoint::builder(presets::Minimal)` with the relay and every address lookup service off and one UDP
//! socket on the bench's address (`PINC_BENCH_BIND`, loopback by default), so no run touches a network it was not given; iroh's own transport configuration and its tokio
//! multi-thread runtime with one worker per core. The resumed scenario uses iroh's 0-RTT path
//! (`connect_with_opts` then `into_0rtt` on the dialer, `into_0rtt` on the acceptor).
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

use std::io;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::time::Duration;

use super::{Lib, Rx, Tx, read_exact, say_hello};
use iroh::endpoint::{Connection, RecvStream, SendStream, ZeroRttStatus, presets};
use iroh::{Endpoint, EndpointAddr, EndpointId, RelayMode};

const ALPN: &[u8] = b"bench/1";

static ACCEPTED: AtomicU64 = AtomicU64::new(0);
static REJECTED: AtomicU64 = AtomicU64::new(0);
static UNAVAILABLE: AtomicU64 = AtomicU64::new(0);

fn io_err(e: impl std::fmt::Display) -> io::Error {
    io::Error::other(e.to_string())
}

async fn bind(alpns: Vec<Vec<u8>>) -> io::Result<Endpoint> {
    Endpoint::builder(presets::Minimal)
        .relay_mode(RelayMode::Disabled)
        .alpns(alpns)
        .clear_ip_transports()
        .bind_addr(std::net::SocketAddr::new(super::bind_ip()?, 0))
        .map_err(io_err)?
        .bind()
        .await
        .map_err(io_err)
}

impl Tx for SendStream {
    async fn write_all(&mut self, b: &[u8]) -> io::Result<()> {
        SendStream::write_all(self, b).await.map_err(io_err)
    }
    async fn finish(&mut self) -> io::Result<()> {
        SendStream::finish(self).map_err(io_err)
    }
}

impl Rx for RecvStream {
    async fn read(&mut self, b: &mut [u8]) -> io::Result<usize> {
        RecvStream::read(self, b).await.map(|n| n.unwrap_or(0)).map_err(io_err)
    }
}

static RT: OnceLock<tokio::runtime::Runtime> = OnceLock::new();

/// The library under test.
pub struct Iroh;

impl Lib for Iroh {
    fn name() -> &'static str {
        "iroh"
    }

    const RESUMES: bool = true;
    type Ep = Endpoint;
    type Conn = Connection;
    type Tx = SendStream;
    type Rx = RecvStream;

    fn run<T>(f: impl Future<Output = T>) -> T {
        let rt = tokio::runtime::Builder::new_multi_thread().enable_all().build();
        RT.get_or_init(|| rt.unwrap_or_else(|e| panic!("the runtime did not start: {e}")))
            .block_on(tokio::task::LocalSet::new().run_until(f))
    }

    fn spawn(f: impl Future<Output = ()> + 'static) {
        // The scenarios run on the thread that drives them; the library's own tasks use the runtime's threads.
        tokio::task::spawn_local(f);
    }

    async fn sleep(d: Duration) {
        tokio::time::sleep(d).await;
    }

    async fn serve() -> io::Result<String> {
        let ep = bind(vec![ALPN.to_vec()]).await?;
        let sock = ep
            .bound_sockets()
            .into_iter()
            .next()
            .ok_or_else(|| io_err("no socket"))?;
        let addr = format!("{}@{sock}", ep.id());
        tokio::spawn(async move {
            while let Some(incoming) = ep.accept().await {
                tokio::spawn(async move {
                    let Ok(accepting) = incoming.accept() else { return };
                    let conn = accepting.into_0rtt();
                    while let Ok((tx, rx)) = conn.accept_bi().await {
                        tokio::spawn(async move {
                            let _ = super::handle(tx, rx).await;
                        });
                    }
                });
            }
        });
        Ok(addr)
    }

    async fn client() -> io::Result<Endpoint> {
        bind(Vec::new()).await
    }

    async fn connect(ep: &Endpoint, addr: &str) -> io::Result<Connection> {
        ep.connect(parse(addr)?, ALPN).await.map_err(io_err)
    }

    async fn open(conn: &Connection) -> io::Result<(SendStream, RecvStream)> {
        conn.open_bi().await.map_err(io_err)
    }

    async fn close(_ep: &Endpoint, conn: &Connection) {
        conn.close(0u32.into(), b"");
    }

    async fn shutdown(ep: Endpoint) {
        ep.close().await;
    }

    async fn hello(ep: &Endpoint, addr: &str, resumed: bool) -> io::Result<Connection> {
        if !resumed {
            let c = Self::connect(ep, addr).await?;
            say_hello::<Self>(&c).await?;
            return Ok(c);
        }
        let connecting = ep
            .connect_with_opts(parse(addr)?, ALPN, Default::default())
            .await
            .map_err(io_err)?;
        let Ok(early) = connecting.into_0rtt() else {
            UNAVAILABLE.fetch_add(1, Relaxed);
            return Err(io_err("no session ticket to resume with"));
        };
        let first = async {
            let (mut tx, mut rx) = early.open_bi().await.map_err(io_err)?;
            Tx::write_all(&mut tx, b"H").await?;
            read_exact(&mut rx, &mut [0u8; 1]).await
        }
        .await;
        match early.handshake_completed().await.map_err(io_err)? {
            ZeroRttStatus::Accepted(c) => {
                first?;
                ACCEPTED.fetch_add(1, Relaxed);
                Ok(c)
            }
            ZeroRttStatus::Rejected(c) => {
                REJECTED.fetch_add(1, Relaxed);
                say_hello::<Self>(&c).await?;
                Ok(c)
            }
        }
    }

    fn note() -> String {
        format!(
            "0-RTT accepted {}, rejected {}, no ticket {}",
            ACCEPTED.load(Relaxed),
            REJECTED.load(Relaxed),
            UNAVAILABLE.load(Relaxed)
        )
    }
}

fn parse(addr: &str) -> io::Result<EndpointAddr> {
    let (id, sock) = addr.split_once('@').ok_or_else(|| io_err("bad address"))?;
    let id: EndpointId = id.parse().map_err(io_err)?;
    Ok(EndpointAddr::new(id).with_ip_addr(sock.parse().map_err(io_err)?))
}
