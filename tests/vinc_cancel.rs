//! Cancel safety: futures of the facade are dropped after every number of polls while other traffic runs, then the
//! endpoint is checked and the next operation must work.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::zombie_processes,
    clippy::useless_conversion,
    clippy::manual_assert_eq,
    clippy::items_after_statements,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod vinc_common;

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use nuclei::Task;
use nuclei::sync::oneshot;
use vinc::{Discovery, Endpoint, Hosted, NodeAddr};
use vinc_common::{ECHO, bind, client, eventually, node, pattern, poll_drop, within};

async fn echo_once<H: Hosted + 'static, D: Discovery + 'static>(client: &Endpoint<H, D>, addr: &NodeAddr) {
    let conn = client.connect(addr.clone(), ECHO).await.unwrap();
    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
    tx.write_all(b"alive").await.unwrap();
    tx.finish().await.unwrap();
    assert_eq!(rx.read_to_end(100).await.unwrap(), b"alive");
}

/// Background traffic that must not be disturbed by the dropped futures; resolves to its rounds when stopped.
fn load<H: Hosted + 'static, D: Discovery + 'static>(
    client: &Endpoint<H, D>,
    addr: &NodeAddr,
    stop: &Arc<AtomicBool>,
) -> Task<u64> {
    let (client, addr, stop) = (client.clone(), addr.clone(), Arc::clone(stop));
    nuclei::spawn_local(async move {
        let conn = client.connect(addr, ECHO).await.unwrap();
        let mut rounds = 0;
        while !stop.load(Ordering::Relaxed) {
            let (mut tx, mut rx) = conn.open_bi().await.unwrap();
            let payload = vec![rounds as u8; 20_000];
            tx.write_all(&payload).await.unwrap();
            tx.finish().await.unwrap();
            assert_eq!(rx.read_to_end(1 << 20).await.unwrap(), payload);
            rounds += 1;
        }
        rounds
    })
}

#[nuclei::test]
async fn dropped_connect_leaves_nothing_open() {
    within(200, async {
        let (server, client) = (node().await, client().await);
        let addr = server.addr();
        let stop = Arc::new(AtomicBool::new(false));
        let bg = load(&client, &addr, &stop);
        eventually(10, "load connected", || async {
            client.peers().await.unwrap().len() == 1
        })
        .await;
        let base = client.node_stats().await.unwrap().sessions;
        // Sub-sessions of the load's connection, dropped at every poll count: the client's own table comes back to base.
        for polls in 0..12 {
            for _ in 0..4 {
                let _ = poll_drop(client.connect(addr.clone(), ECHO), polls).await;
            }
        }
        eventually(20, "abandoned sub-sessions closed", || async {
            client.node_stats().await.unwrap().sessions <= base
        })
        .await;
        // Full handshakes from fresh nodes, dropped at every poll count: their own tables come back to empty at once.
        let server2 = node().await;
        let addr2 = server2.addr();
        let mut fresh = Vec::new();
        for _ in 0..12 {
            fresh.push(bind(vinc_common::builder().alpn(ECHO)).await);
        }
        for (polls, f) in fresh.iter().enumerate() {
            let _ = poll_drop(f.connect(addr2.clone(), ECHO), polls).await;
        }
        eventually(20, "abandoned dials closed", || async {
            for f in &fresh {
                if f.node_stats().await.unwrap().sessions != 0 {
                    return false;
                }
            }
            true
        })
        .await;
        stop.store(true, Ordering::Relaxed);
        assert!(bg.await > 0);
        echo_once(&client, &addr).await;
        // The server hears a CLOSE from every dial that was closed after the handshake; one closed before the server's
        // side finished is dropped by the half-open timer (30 s). Once the last handle is gone nothing is left.
        drop(fresh);
        eventually(90, "server table empty", || async {
            server2.node_stats().await.unwrap().sessions == 0
        })
        .await;
    })
    .await;
}

#[nuclei::test]
#[ignore = "waits on the facade rework: an open that finds no stream credit or pool room must wait, not fail"]
async fn dropped_open_accept_and_stats_lose_no_stream() {
    within(120, async {
        let (server, client) = (node().await, client().await);
        let addr = server.addr();
        let stop = Arc::new(AtomicBool::new(false));
        let bg = load(&client, &addr, &stop);
        let conn = client.connect(addr.clone(), ECHO).await.unwrap();
        // Streams opened with dropped futures: those that finished are real and work, the rest do not exist.
        let mut opened = Vec::new();
        for polls in 0..8 {
            if let Some(Ok(s)) = poll_drop(conn.open_bi(), polls).await {
                opened.push(s);
            }
            let _ = poll_drop(conn.stats(), polls).await;
        }
        for (mut tx, mut rx) in opened {
            tx.write_all(b"x").await.unwrap();
            tx.finish().await.unwrap();
            assert_eq!(rx.read_to_end(10).await.unwrap(), b"x");
        }
        echo_once(&client, &addr).await;

        // accept_bi dropped at every poll count loses no stream: a peer opens five, the other side collects them all.
        let b = bind(vinc_common::builder().alpn(ECHO)).await;
        let (a, addr_b) = (client.clone(), b.addr());
        let sender = nuclei::spawn_local(async move {
            let conn = a.connect(addr_b, ECHO).await.unwrap();
            let mut keep = Vec::new();
            for i in 0..5u8 {
                let (mut tx, rx) = conn.open_bi().await.unwrap();
                tx.write_all(&[i]).await.unwrap();
                tx.finish().await.unwrap();
                keep.push(rx);
            }
            // Hold the streams open until the other side has them.
            nuclei::time::sleep(Duration::from_millis(1500)).await;
            drop(keep);
        });
        let theirs = b.accept().await.unwrap().into_connection();
        let mut got = Vec::new();
        let mut round = 0;
        while got.len() < 5 {
            if let Some(Ok((_tx, mut rx))) = poll_drop(theirs.accept_bi(), round % 4).await {
                got.push(rx.read_to_end(4).await.unwrap()[0]);
            }
            round += 1;
        }
        got.sort_unstable();
        assert_eq!(got, [0, 1, 2, 3, 4], "a stream was lost to a dropped accept");
        sender.await;
        stop.store(true, Ordering::Relaxed);
        bg.await;
    })
    .await;
}

#[nuclei::test]
async fn dropped_write_accepts_exactly_what_it_reported() {
    within(120, async {
        let server = bind(vinc_common::builder().alpn(ECHO)).await;
        let client = client().await;
        let s = server.clone();
        // The server accepts a stream and does not read it until told to: the writer stalls on flow control.
        let (go_tx, go_rx) = oneshot::channel::<()>();
        let reader = nuclei::spawn_local(async move {
            let conn = s.accept().await.unwrap().into_connection();
            let (_tx, mut rx) = conn.accept_bi().await.unwrap();
            go_rx.await.unwrap();
            let mut got = Vec::new();
            while let Some(c) = rx.read_chunk(64 * 1024).await.unwrap() {
                got.extend_from_slice(&c);
            }
            got
        });
        let mut accepted: u64 = 0;
        let mut dropped = 0;
        let conn = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, _rx) = conn.open_bi().await.unwrap();
        let mut buf = vec![0u8; 16 * 1024];
        let end = Instant::now() + Duration::from_secs(4);
        while Instant::now() < end && dropped < 40 {
            pattern(3, accepted, &mut buf);
            // Usually Ready while there is room, Pending once the window and the channel are full.
            match poll_drop(tx.write(&buf), 2).await {
                Some(Ok(n)) => accepted += n as u64,
                Some(Err(e)) => panic!("{e}"),
                None => dropped += 1,
            }
        }
        assert!(
            dropped > 0,
            "the writer never stalled; the test did not exercise a pending write"
        );
        go_tx.send(()).unwrap();
        // Every write that reported bytes is delivered; the dropped ones delivered none.
        loop {
            pattern(3, accepted, &mut buf);
            if accepted >= 4 << 20 {
                break;
            }
            match poll_drop(tx.write(&buf), 50).await {
                Some(Ok(n)) => accepted += n as u64,
                Some(Err(e)) => panic!("{e}"),
                None => {}
            }
        }
        tx.finish().await.unwrap();
        // The connection closes when the last handle goes, so hold it until the reader has everything.
        let got = reader.await;
        assert_eq!(got.len() as u64, accepted);
        let mut want = vec![0u8; got.len()];
        // Rebuild the expected stream: each reported write started at its offset in the pattern.
        pattern(3, 0, &mut want);
        assert!(got == want, "the delivered bytes differ from the reported ones");
    })
    .await;
}

#[nuclei::test]
async fn dropped_read_loses_no_bytes() {
    within(120, async {
        let (server, client) = (node().await, client().await);
        let conn = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        let payload: Vec<u8> = (0..300_000u32).map(|i| (i % 253) as u8).collect();
        let sent = payload.clone();
        let writer = nuclei::spawn_local(async move {
            tx.write_all(&sent).await.unwrap();
            tx.finish().await.unwrap();
        });
        let mut got = Vec::new();
        let mut buf = vec![0u8; 1000];
        let end = Instant::now() + Duration::from_secs(60);
        let mut polls = 0;
        loop {
            polls = (polls + 1) % 4;
            match poll_drop(rx.read(&mut buf), polls).await {
                Some(Ok(Some(n))) => got.extend_from_slice(&buf[..n]),
                Some(Ok(None)) => break,
                Some(Err(e)) => panic!("{e}"),
                None => {}
            }
            assert!(
                Instant::now() < end,
                "stalled with {} of {} bytes",
                got.len(),
                payload.len()
            );
        }
        writer.await;
        assert_eq!(got, payload);
    })
    .await;
}
