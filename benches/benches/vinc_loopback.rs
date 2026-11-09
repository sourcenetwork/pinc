//! Loopback throughput and latency through the facade: on the nuclei runtime.
//!
//! Two endpoints in one process talk over 127.0.0.1 UDP. The numbers depend on the machine and its load, so the load
//! average is printed with them. Run with `cargo bench -p vinc-benches --bench vinc_loopback`.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation
)]

use std::time::{Duration, Instant};

use vinc::{Endpoint, NodeAddr, Vinc};

const BULK: usize = 256 << 20;
const PINGS: usize = 20_000;

async fn node() -> Endpoint {
    let (ep, driver) = Vinc::builder()
        .alpn(b"bench/1".to_vec())
        .bind_nuclei(([127, 0, 0, 1], 0).into())
        .await
        .unwrap();
    nuclei::spawn(driver.run()).detach();
    ep
}

fn loadavg() -> String {
    std::fs::read_to_string("/proc/loadavg").map_or_else(|_| "unavailable".into(), |s| s.trim().to_owned())
}

fn pct(v: &mut [Duration], p: f64) -> Duration {
    v.sort();
    v[((v.len() as f64 * p) as usize).min(v.len() - 1)]
}

/// Serve: a bulk sink (counts bytes, replies with the count) and a ping stream (echoes every byte).
async fn serve(server: Endpoint) {
    while let Some(inc) = server.accept().await {
        let conn = inc.into_connection();
        nuclei::spawn(async move {
            while let Ok((mut tx, mut rx)) = conn.accept_bi().await {
                nuclei::spawn(async move {
                    let mut total = 0u64;
                    let mut buf = vec![0u8; 64 * 1024];
                    // A ping stream echoes at once; a bulk stream is counted. The first byte says which.
                    let mut mode = None;
                    while let Ok(Some(n)) = rx.read(&mut buf).await {
                        if mode.is_none() {
                            mode = buf.first().copied();
                        }
                        if mode == Some(b'p') {
                            let _ = tx.write_all(&buf[..n]).await;
                        } else {
                            total += n as u64;
                        }
                    }
                    if mode != Some(b'p') {
                        let _ = tx.write_all(&total.to_le_bytes()).await;
                    }
                    let _ = tx.finish().await;
                })
                .detach();
            }
        })
        .detach();
    }
}

#[nuclei::main]
async fn main() {
    println!("load average before: {}", loadavg());
    let (server, client) = (node().await, node().await);
    let addr: NodeAddr = server.addr();
    nuclei::spawn(serve(server.clone())).detach();

    let conn = client.connect(addr, b"bench/1").await.unwrap();

    // Bulk upload, one stream.
    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
    let chunk = vec![b'b'; 64 * 1024];
    let t = Instant::now();
    let mut sent = 0;
    while sent < BULK {
        tx.write_all(&chunk).await.unwrap();
        sent += chunk.len();
    }
    tx.finish().await.unwrap();
    let mut reply = [0u8; 8];
    rx.read_exact(&mut reply).await.unwrap();
    let secs = t.elapsed().as_secs_f64();
    assert_eq!(u64::from_le_bytes(reply) as usize, BULK);
    println!(
        "stream upload: {} MiB in {secs:.2} s = {:.0} MiB/s",
        BULK >> 20,
        (BULK >> 20) as f64 / secs
    );

    // Ping-pong of one byte on a stream.
    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
    tx.write_all(b"p").await.unwrap();
    let mut one = [0u8; 1];
    rx.read_exact(&mut one).await.unwrap();
    let mut lat = Vec::with_capacity(PINGS);
    for _ in 0..PINGS {
        let t = Instant::now();
        tx.write_all(b"p").await.unwrap();
        rx.read_exact(&mut one).await.unwrap();
        lat.push(t.elapsed());
    }
    println!(
        "stream ping-pong ({PINGS}): p50 {:?}, p99 {:?}, p99.9 {:?}",
        pct(&mut lat, 0.5),
        pct(&mut lat, 0.99),
        pct(&mut lat, 0.999)
    );
    tx.finish().await.unwrap();

    let c = client.loop_stats().counts();
    let s = server.loop_stats().counts();
    println!("client driver: {c:?}");
    println!("server driver: {s:?}");
    println!("load average after: {}", loadavg());
}
