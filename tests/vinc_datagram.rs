//! Received datagrams through the facade: in order, bounded, a large burst, on nuclei.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::zombie_processes,
    clippy::useless_conversion,
    clippy::manual_assert_eq,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod vinc_common;

use std::time::Duration;

use vinc::{Connection, Endpoint, ErrorKind, Hosted};
use vinc_common::{ECHO, bind, poll_drop, within};

/// A datagram of `seq` and padding to `len` bytes.
fn dgram(seq: u32, len: usize) -> Vec<u8> {
    let mut d = vec![(seq % 251) as u8; len.max(4)];
    d[..4].copy_from_slice(&seq.to_le_bytes());
    d
}

fn seq(d: &[u8]) -> u32 {
    u32::from_le_bytes(d[..4].try_into().unwrap())
}

/// A connected pair; the endpoints are returned so they live as long as the connections.
async fn pair() -> (
    Endpoint<impl Hosted>,
    Endpoint<impl Hosted>,
    Connection<impl Hosted>,
    Connection<impl Hosted>,
) {
    let server = bind(vinc_common::builder().alpn(ECHO)).await;
    let client = bind(vinc_common::builder().alpn(ECHO)).await;
    let c = client.connect(server.addr(), ECHO).await.unwrap();
    // The session reaches the server's queue once the client opened a stream.
    let (mut tx, _rx) = c.open_bi().await.unwrap();
    tx.write_all(b"hi").await.unwrap();
    let s = server.accept().await.unwrap().into_connection();
    (server, client, c, s)
}

#[nuclei::test]
async fn datagrams_arrive_in_order_with_their_bytes() {
    within(60, async {
        let (_server, _client, c, s) = pair().await;
        for i in 0..50u32 {
            c.send_datagram(&dgram(i, 20 + i as usize * 7)).await.unwrap();
        }
        for i in 0..50u32 {
            let d = s.read_datagram().await.unwrap();
            assert_eq!(d, dgram(i, 20 + i as usize * 7), "datagram {i}");
        }
        // A datagram sent the other way arrives too, and one that ends the connection ends the wait.
        s.send_datagram(&dgram(9, 30)).await.unwrap();
        assert_eq!(c.read_datagram().await.unwrap(), dgram(9, 30));
        c.close(5).await;
        assert!(s.read_datagram().await.is_err());
    })
    .await;
}

#[nuclei::test]
async fn a_large_burst_arrives_in_order_and_what_is_lost_is_lost_whole() {
    within(120, async {
        let (_server, _client, c, s) = pair().await;
        const N: u32 = 5000;
        let reader = nuclei::spawn_local(async move {
            let (mut prev, mut got): (Option<u32>, usize) = (None, 0);
            while let Ok(d) = s.read_datagram().await {
                let n = seq(&d);
                assert!(prev.is_none_or(|p| n > p), "datagram {n} came after {prev:?}");
                assert_eq!(d.len(), 100 + (n as usize % 50));
                prev = Some(n);
                got += 1;
            }
            got
        });
        for i in 0..N {
            c.send_datagram(&dgram(i, 100 + (i as usize % 50))).await.unwrap();
            if i % 64 == 63 {
                nuclei::time::sleep(Duration::from_micros(200)).await;
            }
        }
        nuclei::time::sleep(Duration::from_secs(2)).await;
        c.close(0).await;
        let n = reader.await;
        assert!(n > 0 && n <= N as usize, "{n} datagrams of {N}");
    })
    .await;
}

#[nuclei::test]
async fn a_session_holds_a_bounded_number_of_unread_datagrams() {
    within(120, async {
        let (_server, _client, c, s) = pair().await;
        for i in 0..3000u32 {
            c.send_datagram(&dgram(i, 200)).await.unwrap();
            if i % 32 == 31 {
                nuclei::time::sleep(Duration::from_micros(300)).await;
            }
        }
        nuclei::time::sleep(Duration::from_secs(1)).await;
        // Nothing was read: now read what is held. The session holds its channel (64) and the endpoint's queue (64), no more.
        let mut seqs = Vec::new();
        while let Ok(Ok(d)) = nuclei::time::timeout(Duration::from_secs(1), s.read_datagram()).await {
            seqs.push(seq(&d));
        }
        assert!((1..=128).contains(&seqs.len()), "{} datagrams were held", seqs.len());
        assert!(seqs.windows(2).all(|w| w[0] < w[1]), "out of order: {seqs:?}");
    })
    .await;
}

#[nuclei::test]
async fn datagrams_arrive_in_order_and_a_dropped_read_loses_nothing() {
    within(120, async {
        let (_server, _client, c, s) = pair().await;
        // A read that is dropped before a datagram exists consumes nothing.
        assert!(poll_drop(s.read_datagram(), 1).await.is_none());
        for i in 0..40u32 {
            c.send_datagram(&dgram(i, 64)).await.unwrap();
        }
        for i in 0..40u32 {
            assert_eq!(s.read_datagram().await.unwrap(), dgram(i, 64));
        }
        c.close(3).await;
        assert!(matches!(
            s.read_datagram().await.unwrap_err().kind(),
            ErrorKind::Closed { .. }
        ));
    })
    .await;
}
