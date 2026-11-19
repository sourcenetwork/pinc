//! A large stream transfer: a client sends 32 MiB and the server answers with the byte count and a checksum.
//!
//! Run with `cargo run --release -p pinc --features nuclei --example transfer`.

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
use std::rc::Rc;
use std::sync::Arc;
use std::time::Instant;

use nuclei::Handle;
use nuclei::time::sleep_until_precise;

use pinc::{Builder, Connection, Endpoint, Error, ErrorKind, Hosted, Protocol, Pinc};

const ALPN: &[u8] = b"example/transfer/1";

/// A running 64-bit FNV-1a hash: enough to show the bytes arrived in order.
fn fnv(mut h: u64, data: &[u8]) -> u64 {
    for b in data {
        h = (h ^ u64::from(*b)).wrapping_mul(0x0100_0000_01b3);
    }
    h
}

struct Sink;

impl Protocol for Sink {
    fn alpn(&self) -> &'static [u8] {
        ALPN
    }

    async fn serve<H: Hosted + 'static>(self: Rc<Self>, conn: Connection<H>) {
        while let Ok((mut tx, mut rx)) = conn.accept_bi().await {
            let (mut total, mut h) = (0u64, 0xcbf2_9ce4_8422_2325_u64);
            while let Ok(Some(chunk)) = rx.read_chunk(64 * 1024).await {
                total += chunk.len() as u64;
                h = fnv(h, &chunk);
            }
            let mut reply = total.to_le_bytes().to_vec();
            reply.extend_from_slice(&h.to_le_bytes());
            let _ = tx.write_all(&reply).await;
            let _ = tx.finish().await;
        }
    }
}

/// Send `len` bytes; returns `(bytes the server counted, whether its checksum matches ours)`.
pub async fn run(len: usize) -> pinc::Result<(u64, bool)> {
    let server = endpoint(Pinc::builder()).await?;
    let client = endpoint(Pinc::builder()).await?;
    {
        let registered = server.register(Rc::new(Sink)).await?;
        nuclei::spawn_local(async move {
            while let Some(conn) = registered.accept().await {
                nuclei::spawn_local(registered.protocol().serve(conn)).detach();
            }
        })
        .detach();
        let conn = client.connect(server.addr(), ALPN).await?;
        let (mut tx, mut rx) = conn.open_bi().await?;
        let block: Vec<u8> = (0..64 * 1024).map(|i| (i % 251) as u8).collect();
        let (mut sent, mut h) = (0usize, 0xcbf2_9ce4_8422_2325_u64);
        while sent < len {
            let n = block.len().min(len - sent);
            tx.write_all(&block[..n]).await?;
            h = fnv(h, &block[..n]);
            sent += n;
        }
        tx.finish().await?;
        let reply = rx.read_to_end(64).await?;
        let total = u64::from_le_bytes(reply[..8].try_into().unwrap_or_default());
        let theirs = u64::from_le_bytes(reply[8..16].try_into().unwrap_or_default());
        Ok((total, theirs == h))
    }
}

/// An endpoint over a UDP socket of the nuclei runtime: the three closures are the whole of the host's I/O.
async fn endpoint(builder: Builder) -> pinc::Result<Endpoint<impl Hosted>> {
    let sock = Arc::new(
        Handle::<UdpSocket>::bind(SocketAddr::from(([127, 0, 0, 1], 0)))
            .await
            .map_err(|_| Error::new(ErrorKind::Unreachable, "the address cannot be bound"))?,
    );
    let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
    let local = sock
        .local_addr()
        .map_err(|_| Error::new(ErrorKind::Unreachable, "the socket has no address"))?;
    builder.local_addr(local).build(
        async move |buf: &mut [u8]| r.recv_from(buf).await,
        async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
        async |at: Instant| sleep_until_precise(at).await,
    )
}

#[allow(dead_code)]
#[nuclei::main]
async fn main() {
    match run(32 << 20).await {
        Ok((n, ok)) => println!(
            "server counted {n} bytes, checksum {}",
            if ok { "matches" } else { "differs" }
        ),
        Err(e) => eprintln!("failed: {e}"),
    }
}
