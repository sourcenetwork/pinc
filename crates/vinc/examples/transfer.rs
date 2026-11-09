//! A large stream transfer: a client sends 32 MiB and the server answers with the byte count and a checksum.
//!
//! Run with `cargo run --release -p vinc --features nuclei --example transfer`.

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

use std::sync::Arc;

use vinc::{Connection, Protocol, Vinc};

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

    async fn serve(self: Arc<Self>, conn: Connection) {
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
pub async fn run(len: usize) -> vinc::Result<(u64, bool)> {
    let lo = ([127, 0, 0, 1], 0).into();
    let (server, driver) = Vinc::builder().bind_nuclei(lo).await?;
    nuclei::spawn(driver.run()).detach();
    let (client, driver) = Vinc::builder().bind_nuclei(lo).await?;
    nuclei::spawn(driver.run()).detach();
    {
        let registered = server.register(Arc::new(Sink)).await?;
        nuclei::spawn(async move {
            while let Some(conn) = registered.accept().await {
                nuclei::spawn(registered.protocol().serve(conn)).detach();
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
