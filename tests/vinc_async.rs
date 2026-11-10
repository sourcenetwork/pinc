//! The async API on nuclei, between two endpoints of one process over loopback.
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

use vinc::{ErrorKind, Limits};
use vinc_common::{ECHO, GEN, SINK, bind, client, join_all, node, pattern, pattern_hash, serve_conn, within};

const BIG: u64 = 4 << 20;

#[nuclei::test]
async fn many_streams_datagrams_and_reconnect() {
    within(120, async {
        let peer = node().await;
        let ep = client().await;
        let addr = peer.addr();
        let conn = ep.connect(addr.clone(), ECHO).await.unwrap();

        let jobs = (0..40u8).map(|i| {
            let conn = conn.clone();
            async move {
                let (mut tx, mut rx) = conn.open_bi().await.unwrap();
                let payload: Vec<u8> = (0..5000 + usize::from(i) * 977)
                    .map(|k| (k as u8).wrapping_add(i))
                    .collect();
                tx.write_all(&payload).await.unwrap();
                tx.finish().await.unwrap();
                assert_eq!(rx.read_to_end(1 << 20).await.unwrap(), payload);
            }
        });
        join_all(jobs).await;

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
            c.close(50 + round).await;
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
    })
    .await;
}

/// A peer whose pool covers the windows of only a few streams: the streams opened beyond that wait for room instead
/// of failing, and every stream's bytes arrive once and in order.
#[nuclei::test]
#[ignore = "waits on the receiver-advertised stream credit of the transport: an open that finds no room must wait"]
async fn streams_beyond_the_peer_pool_are_delivered() {
    within(120, async {
        let small = Limits {
            pool_chunks: 8,
            stream_window: 64 * 1024,
            ..Limits::default()
        };
        let peer = bind(vinc_common::builder().alpn(ECHO).limits(small)).await;
        let s = peer.clone();
        nuclei::spawn_local(async move {
            while let Some(i) = s.accept().await {
                nuclei::spawn_local(serve_conn(i.into_connection())).detach();
            }
        })
        .detach();
        let ep = client().await;
        let conn = ep.connect(peer.addr(), ECHO).await.unwrap();
        let jobs = (0..24u8).map(|i| {
            let conn = conn.clone();
            async move {
                let (mut tx, mut rx) = conn.open_bi().await.unwrap();
                let payload: Vec<u8> = (0..20_000 + usize::from(i) * 1301)
                    .map(|k| (k as u8).wrapping_mul(3).wrapping_add(i))
                    .collect();
                tx.write_all(&payload).await.unwrap();
                tx.finish().await.unwrap();
                assert_eq!(rx.read_to_end(1 << 20).await.unwrap(), payload);
            }
        });
        join_all(jobs).await;
    })
    .await;
}

#[nuclei::test]
async fn large_transfer_in_both_directions() {
    within(240, async {
        let peer = node().await;
        let ep = client().await;
        let addr = peer.addr();
        let up = ep.connect(addr.clone(), SINK).await.unwrap();
        let (mut tx, mut rx) = up.open_bi().await.unwrap();
        let mut buf = vec![0u8; 64 * 1024];
        let mut at = 0;
        while at < BIG {
            let n = buf.len().min((BIG - at) as usize);
            pattern(7, at, &mut buf[..n]);
            tx.write_all(&buf[..n]).await.unwrap();
            at += n as u64;
        }
        tx.finish().await.unwrap();
        let reply = rx.read_to_end(1 << 10).await.unwrap();
        assert_eq!(u64::from_le_bytes(reply[..8].try_into().unwrap()), BIG);
        assert_eq!(&reply[8..], &pattern_hash(7, BIG));

        let down = ep.connect(addr, GEN).await.unwrap();
        let (mut tx, mut rx) = down.open_bi().await.unwrap();
        let mut req = 9u64.to_le_bytes().to_vec();
        req.extend_from_slice(&BIG.to_le_bytes());
        tx.write_all(&req).await.unwrap();
        let mut h = blake3::Hasher::new();
        let mut total = 0u64;
        while let Some(n) = rx.read(&mut buf).await.unwrap() {
            h.update(&buf[..n]);
            total += n as u64;
        }
        assert_eq!(total, BIG);
        assert_eq!(h.finalize().as_bytes(), &pattern_hash(9, BIG));
    })
    .await;
}
