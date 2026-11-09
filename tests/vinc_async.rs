//! The async API, driven by the test executor in `vinc_common`, against a peer in another process.
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

use futures_io::{AsyncRead, AsyncWrite};
use std::future::poll_fn;
use std::pin::Pin;

use vinc::{ErrorKind, Vinc};
use vinc_common::{ECHO, Exec, GEN, SINK, lo, pattern, pattern_hash, spawn_peer, watchdog};

const BIG: u64 = 4 << 20;

#[test]
fn child_async() {
    if vinc_common::is_child() {
        vinc_common::run_child(true);
    }
}

#[test]
fn many_streams_datagrams_and_reconnect() {
    watchdog(120);
    let peer = spawn_peer("child_async");
    let exec = Exec::new(4);
    let ep = Vinc::builder()
        .alpn(ECHO)
        .bind_addr(lo())
        .spawn_on(exec.clone())
        .unwrap();
    let addr = peer.addr.clone();
    exec.block_on(async move {
        let conn = ep.connect(addr.clone(), ECHO).await.unwrap();

        let jobs: Vec<Pin<Box<dyn std::future::Future<Output = ()> + Send>>> = (0..40u8)
            .map(|i| {
                let conn = conn.clone();
                Box::pin(async move {
                    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
                    let payload: Vec<u8> = (0..5000 + usize::from(i) * 977)
                        .map(|k| (k as u8).wrapping_add(i))
                        .collect();
                    tx.write_all(&payload).await.unwrap();
                    tx.finish().await.unwrap();
                    assert_eq!(rx.read_to_end(1 << 20).await.unwrap(), payload);
                }) as Pin<Box<dyn std::future::Future<Output = ()> + Send>>
            })
            .collect();
        vinc_common::join_all(jobs).await;

        conn.send_datagram(&[1u8; 100]).await.unwrap();
        assert_eq!(
            conn.send_datagram(&vec![0u8; 100_000]).await.unwrap_err().kind(),
            ErrorKind::TooLarge
        );

        for round in 0..2u64 {
            let c = ep.connect(addr.clone(), ECHO).await.unwrap();
            let (mut tx, mut rx) = c.open_bi().await.unwrap();
            tx.write_all(b"before").await.unwrap();
            let mut got = [0u8; 6];
            rx.read_exact(&mut got).await.unwrap();
            c.close(50 + round);
            let why = c.closed().await;
            assert!(
                matches!(why.kind(), ErrorKind::Closed { code, by_peer: false } if code == 50 + round),
                "{why:?}"
            );
            assert!(tx.write_all(b"after").await.is_err() || rx.read_to_end(10).await.is_err());
        }
        let again = ep.connect(addr, ECHO).await.unwrap();
        let (mut tx, mut rx) = again.open_bi().await.unwrap();
        tx.write_all(b"again").await.unwrap();
        tx.finish().await.unwrap();
        assert_eq!(rx.read_to_end(100).await.unwrap(), b"again");
    });
}

#[test]
fn large_transfer_with_futures_io() {
    watchdog(240);
    let peer = spawn_peer("child_async");
    let exec = Exec::new(2);
    let ep = Vinc::builder()
        .alpn(SINK)
        .bind_addr(lo())
        .spawn_on(exec.clone())
        .unwrap();
    let addr = peer.addr.clone();
    exec.block_on(async move {
        // Upload through the AsyncWrite trait object.
        let up = ep.connect(addr.clone(), SINK).await.unwrap();
        let (mut tx, mut rx) = up.open_bi().await.unwrap();
        let mut buf = vec![0u8; 64 * 1024];
        let mut at = 0;
        while at < BIG {
            let n = buf.len().min((BIG - at) as usize);
            pattern(7, at, &mut buf[..n]);
            let mut chunk = &buf[..n];
            while !chunk.is_empty() {
                let w = poll_fn(|cx| Pin::new(&mut tx).poll_write(cx, chunk)).await.unwrap();
                chunk = &chunk[w..];
            }
            at += n as u64;
        }
        poll_fn(|cx| Pin::new(&mut tx).poll_close(cx)).await.unwrap();
        let reply = rx.read_to_end(1 << 10).await.unwrap();
        assert_eq!(u64::from_le_bytes(reply[..8].try_into().unwrap()), BIG);
        assert_eq!(&reply[8..], &pattern_hash(7, BIG));

        // Download through the AsyncRead trait.
        let down = ep.connect(addr, GEN).await.unwrap();
        let (mut tx, mut rx) = down.open_bi().await.unwrap();
        let mut req = 9u64.to_le_bytes().to_vec();
        req.extend_from_slice(&BIG.to_le_bytes());
        tx.write_all(&req).await.unwrap();
        let mut h = blake3::Hasher::new();
        let mut total = 0u64;
        loop {
            let n = poll_fn(|cx| Pin::new(&mut rx).poll_read(cx, &mut buf)).await.unwrap();
            if n == 0 {
                break;
            }
            h.update(&buf[..n]);
            total += n as u64;
        }
        assert_eq!(total, BIG);
        assert_eq!(h.finalize().as_bytes(), &pattern_hash(9, BIG));
    });
}
