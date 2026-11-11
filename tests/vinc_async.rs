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

/// On a link slower than the application writes, a stream made urgent overtakes a bulk transfer already in flight and
/// a less urgent stream that was opened and written before it.
#[nuclei::test]
async fn an_urgent_stream_overtakes_bulk_and_a_less_urgent_stream() {
    use std::cell::{Cell, RefCell};
    use std::net::{SocketAddr, UdpSocket};
    use std::rc::Rc;
    use std::sync::Arc;
    use std::time::{Duration, Instant};

    const TOTAL: u64 = 2 << 20;
    within(120, async {
        // The receiving side counts the bulk stream's bytes and notes how many had arrived when each control message
        // was complete.
        let peer = bind(vinc_common::builder().alpn(ECHO)).await;
        let bulk = Rc::new(Cell::new(0u64));
        let order = Rc::new(RefCell::new(Vec::<(u8, u64)>::new()));
        let (s, b, o) = (peer.clone(), Rc::clone(&bulk), Rc::clone(&order));
        nuclei::spawn_local(async move {
            while let Some(i) = s.accept().await {
                let conn = i.into_connection();
                let (b, o) = (Rc::clone(&b), Rc::clone(&o));
                nuclei::spawn_local(async move {
                    while let Ok((_tx, mut rx)) = conn.accept_bi().await {
                        let (b, o) = (Rc::clone(&b), Rc::clone(&o));
                        nuclei::spawn_local(async move {
                            let mut buf = vec![0u8; 64 * 1024];
                            let mut tag = None;
                            while let Ok(Some(n)) = rx.read(&mut buf).await {
                                if n == 0 {
                                    continue;
                                }
                                if *tag.get_or_insert(buf[0]) == b'B' {
                                    b.set(b.get() + n as u64);
                                }
                            }
                            if let Some(t) = tag.filter(|t| *t != b'B') {
                                o.borrow_mut().push((t, b.get()));
                            }
                        })
                        .detach();
                    }
                })
                .detach();
            }
        })
        .detach();

        // The sending side's link is slow: its host waits before every datagram, so data queues in the connection.
        let sock = Arc::new(nuclei::Handle::<UdpSocket>::bind(vinc_common::lo()).await.unwrap());
        let (r, tx) = (Arc::clone(&sock), Arc::clone(&sock));
        let ep = vinc_common::builder()
            .alpn(ECHO)
            .local_addr(sock.local_addr().unwrap())
            .build(
                async move |buf: &mut [u8]| r.recv_from(buf).await,
                async move |pkt: &[u8], to: SocketAddr| {
                    nuclei::time::sleep(Duration::from_micros(500)).await;
                    tx.send_to(pkt, to).await
                },
                async |at: Instant| nuclei::time::sleep_until_precise(at).await,
            )
            .unwrap();
        let driver = ep.clone();
        nuclei::spawn_local(async move {
            let _ = driver.run().await;
        })
        .detach();

        let conn = ep.connect(peer.addr(), ECHO).await.unwrap();
        let (mut btx, _brx) = conn.open_bi().await.unwrap();
        let writer = nuclei::spawn_local(async move {
            let chunk = vec![b'B'; 64 * 1024];
            let mut sent = 0;
            while sent < TOTAL {
                btx.write_all(&chunk).await.unwrap();
                sent += chunk.len() as u64;
            }
            btx.finish().await.unwrap();
        });
        vinc_common::eventually(60, "the bulk transfer is under way", || {
            let b = Rc::clone(&bulk);
            async move { b.get() >= 128 * 1024 }
        })
        .await;

        // The less urgent stream is opened and written first.
        let (mut low, _lr) = conn.open_bi().await.unwrap();
        let (mut high, _hr) = conn.open_bi().await.unwrap();
        low.set_urgency(7).await.unwrap();
        high.set_urgency(0).await.unwrap();
        low.write_all(&[b'L'; 1024]).await.unwrap();
        low.finish().await.unwrap();
        high.write_all(&[b'H'; 1024]).await.unwrap();
        high.finish().await.unwrap();

        vinc_common::eventually(100, "both control messages arrive", || {
            let o = Rc::clone(&order);
            async move { o.borrow().len() == 2 }
        })
        .await;
        writer.await;
        let got = order.borrow().clone();
        assert_eq!(got[0].0, b'H', "the urgent stream arrives first: {got:?}");
        assert!(
            got[0].1 < TOTAL,
            "the urgent stream overtakes the bulk transfer: {got:?}"
        );
        assert!(
            got[1].1 > got[0].1,
            "the less urgent stream waits behind the bulk transfer: {got:?}"
        );

        // A stream of an ended connection takes no urgency.
        let (mut late, _r) = conn.open_bi().await.unwrap();
        conn.close(0).await;
        assert!(late.set_urgency(1).await.is_err());
    })
    .await;
}
