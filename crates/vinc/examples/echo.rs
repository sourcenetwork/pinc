//! An echo protocol: a server registers a [`Protocol`] and a client sends bytes and reads them back, on nuclei.
//!
//! Run with `cargo run -p vinc --example echo`.

#![allow(
    missing_docs,
    unreachable_pub,
    async_fn_in_trait,
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::indexing_slicing,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::single_match_else,
    reason = "an example favours the short form"
)]

use std::net::{SocketAddr, UdpSocket};
use std::sync::Arc;
use std::time::Instant;

use nuclei::Handle;
use nuclei::time::sleep_until_precise;

use vinc::{Builder, Connection, Endpoint, Error, ErrorKind, Hosted, Limits, Protocol, Vinc};

const ALPN: &[u8] = b"example/echo/1";

struct Echo;

impl Protocol for Echo {
    fn alpn(&self) -> &'static [u8] {
        ALPN
    }

    async fn serve<H: Hosted + 'static>(self: Arc<Self>, conn: Connection<H>) {
        while let Ok((mut tx, mut rx)) = conn.accept_bi().await {
            while let Ok(Some(chunk)) = rx.read_chunk(4096).await {
                if tx.write_all(&chunk).await.is_err() {
                    return;
                }
            }
            let _ = tx.finish().await;
        }
    }
}

/// Run a server and a client on loopback; returns what the client got back.
pub async fn run() -> vinc::Result<Vec<u8>> {
    let server = endpoint(Vinc::builder()).await?;
    let client = endpoint(Vinc::builder()).await?;

    let registered = server.register(Arc::new(Echo)).await?;
    nuclei::spawn_local(async move {
        while let Some(conn) = registered.accept().await {
            nuclei::spawn_local(registered.protocol().serve(conn)).detach();
        }
    })
    .detach();

    let conn = client.connect(server.addr(), ALPN).await?;
    let (mut tx, mut rx) = conn.open_bi().await?;
    tx.write_all(b"hello, vinc").await?;
    tx.finish().await?;
    rx.read_to_end(1 << 16).await
}

/// An endpoint over a UDP socket of the nuclei runtime: the three closures are the whole of the host's I/O.
async fn endpoint(builder: Builder) -> vinc::Result<Endpoint<impl Hosted>> {
    let sock = Arc::new(
        Handle::<UdpSocket>::bind(SocketAddr::from(([127, 0, 0, 1], 0)))
            .await
            .map_err(|_| Error::new(ErrorKind::Unreachable, "the address cannot be bound"))?,
    );
    let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
    let local = sock
        .local_addr()
        .map_err(|_| Error::new(ErrorKind::Unreachable, "the socket has no address"))?;
    // Room for 64 sessions keeps the endpoint small enough to build on any thread's stack.
    builder
        .limits(Limits {
            connections: 64,
            ..Limits::default()
        })
        .local_addr(local)
        .build(
            async move |buf: &mut [u8]| r.recv_from(buf).await,
            async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
            async |at: Instant| sleep_until_precise(at).await,
        )
}

#[allow(dead_code)]
#[nuclei::main]
async fn main() {
    match run().await {
        Ok(b) => println!("echoed: {}", String::from_utf8_lossy(&b)),
        Err(e) => eprintln!("failed: {e}"),
    }
}
