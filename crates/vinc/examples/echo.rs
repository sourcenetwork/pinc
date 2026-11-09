//! An echo protocol: a server registers a [`Protocol`] and a client sends bytes and reads them back.
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

use std::net::SocketAddr;
use std::sync::Arc;

use vinc::{Connection, Protocol, Task, Vinc, block_on};

const ALPN: &[u8] = b"example/echo/1";

struct Echo;

impl Protocol for Echo {
    fn alpn(&self) -> &'static [u8] {
        ALPN
    }

    fn serve(self: Arc<Self>, conn: Connection) -> Task {
        Box::pin(async move {
            while let Ok((mut tx, mut rx)) = conn.accept_bi().await {
                while let Ok(Some(chunk)) = rx.read_chunk(4096).await {
                    if tx.write_all(&chunk).await.is_err() {
                        return;
                    }
                }
                let _ = tx.finish().await;
            }
        })
    }
}

/// Run a server and a client on loopback; returns what the client got back.
pub fn run() -> vinc::Result<Vec<u8>> {
    let lo: SocketAddr = ([127, 0, 0, 1], 0).into();
    let server = Vinc::builder().bind_addr(lo).bind_blocking()?;
    let client = Vinc::builder().bind_addr(lo).bind_blocking()?;
    block_on(async {
        server.register(Arc::new(Echo)).await?;
        let conn = client.connect(server.addr(), ALPN).await?;
        let (mut tx, mut rx) = conn.open_bi().await?;
        tx.write_all(b"hello, vinc").await?;
        tx.finish().await?;
        rx.read_to_end(1 << 16).await
    })
}

#[allow(dead_code)]
fn main() {
    match run() {
        Ok(b) => println!("echoed: {}", String::from_utf8_lossy(&b)),
        Err(e) => eprintln!("failed: {e}"),
    }
}
