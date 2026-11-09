//! An echo protocol: a server registers a [`Protocol`] and a client sends bytes and reads them back, on nuclei.
//!
//! Run with `cargo run -p vinc --features nuclei --example echo`.

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

const ALPN: &[u8] = b"example/echo/1";

struct Echo;

impl Protocol for Echo {
    fn alpn(&self) -> &'static [u8] {
        ALPN
    }

    async fn serve(self: Arc<Self>, conn: Connection) {
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
    let lo = ([127, 0, 0, 1], 0).into();
    let (server, driver) = Vinc::builder().bind_nuclei(lo).await?;
    nuclei::spawn(driver.run()).detach();
    let (client, driver) = Vinc::builder().bind_nuclei(lo).await?;
    nuclei::spawn(driver.run()).detach();

    let registered = server.register(Arc::new(Echo)).await?;
    nuclei::spawn(async move {
        while let Some(conn) = registered.accept().await {
            nuclei::spawn(registered.protocol().serve(conn)).detach();
        }
    })
    .detach();

    let conn = client.connect(server.addr(), ALPN).await?;
    let (mut tx, mut rx) = conn.open_bi().await?;
    tx.write_all(b"hello, vinc").await?;
    tx.finish().await?;
    rx.read_to_end(1 << 16).await
}

#[allow(dead_code)]
#[nuclei::main]
async fn main() {
    match run().await {
        Ok(b) => println!("echoed: {}", String::from_utf8_lossy(&b)),
        Err(e) => eprintln!("failed: {e}"),
    }
}
