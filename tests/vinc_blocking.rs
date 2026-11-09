//! The blocking API against a peer in another process, over real UDP sockets on loopback.
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

use std::io::{Read, Write};
use std::thread;

use vinc::{ErrorKind, Vinc};
use vinc_common::{ECHO, GEN, SINK, lo, pattern, pattern_hash, spawn_peer, watchdog};

const BIG: u64 = 4 << 20;

#[test]
fn child_blocking() {
    if vinc_common::is_child() {
        vinc_common::run_child(false);
    }
}

fn client() -> vinc::blocking::Endpoint {
    Vinc::builder()
        .alpn(ECHO)
        .bind_addr(lo())
        .bind_blocking()
        .unwrap()
        .blocking()
}

#[test]
fn many_streams_datagrams_and_reconnect() {
    watchdog(120);
    let peer = spawn_peer("child_blocking");
    let ep = client();
    let conn = ep.connect(peer.addr.clone(), ECHO).unwrap();
    assert_eq!(conn.remote(), peer.addr.node);
    assert_eq!(conn.alpn(), ECHO);

    // Many streams at once, each with its own payload.
    let streams: Vec<_> = (0..40u8)
        .map(|i| {
            let conn = conn.clone();
            thread::spawn(move || {
                let (mut tx, mut rx) = conn.open_bi().unwrap();
                let payload: Vec<u8> = (0..5000 + usize::from(i) * 977)
                    .map(|k| (k as u8).wrapping_add(i))
                    .collect();
                tx.write_all(&payload).unwrap();
                tx.finish().unwrap();
                assert_eq!(rx.read_to_end(1 << 20).unwrap(), payload);
            })
        })
        .collect();
    for s in streams {
        s.join().unwrap();
    }

    // Datagrams: sending works; reading them waits for the endpoint's read call.
    conn.send_datagram(&[1u8; 100]).unwrap();
    let too_big = vec![0u8; 100_000];
    assert_eq!(conn.send_datagram(&too_big).unwrap_err().kind(), ErrorKind::TooLarge);

    // The stats are live.
    let st = conn.stats().unwrap();
    assert!(st.bytes_sent > 0 && st.bytes_received > 0 && st.dialed_by_us);
    assert_eq!(ep.peers().unwrap(), vec![peer.addr.node]);

    // Close and reconnect, twice: the peer sees the code, the old streams fail, the new connection works.
    for round in 0..2u8 {
        let c = ep.connect(peer.addr.clone(), ECHO).unwrap();
        let (mut tx, mut rx) = c.open_bi().unwrap();
        tx.write_all(b"before").unwrap();
        let mut got = [0u8; 6];
        rx.read_exact(&mut got).unwrap();
        assert_eq!(&got, b"before");
        c.close(40 + u64::from(round));
        let why = c.closed();
        assert!(
            matches!(why.kind(), ErrorKind::Closed { code, by_peer: false } if code == 40 + u64::from(round)),
            "{why:?}"
        );
        assert!(tx.write_all(b"after").is_err() || rx.read_to_end(10).is_err());
    }
    let again = ep.connect(peer.addr.clone(), ECHO).unwrap();
    let (mut tx, mut rx) = again.open_bi().unwrap();
    tx.write_all(b"again").unwrap();
    tx.finish().unwrap();
    assert_eq!(rx.read_to_end(100).unwrap(), b"again");
}

#[test]
fn large_transfer_both_ways_with_std_io() {
    watchdog(240);
    let peer = spawn_peer("child_blocking");
    let ep = client();

    // Upload to the sink; the peer answers with the length and the hash.
    let up = ep.connect(peer.addr.clone(), SINK).unwrap();
    let (mut tx, mut rx) = up.open_bi().unwrap();
    let mut buf = vec![0u8; 64 * 1024];
    let mut at = 0;
    while at < BIG {
        let n = buf.len().min((BIG - at) as usize);
        pattern(7, at, &mut buf[..n]);
        tx.write_all(&buf[..n]).unwrap();
        at += n as u64;
    }
    tx.finish().unwrap();
    let mut reply = Vec::new();
    rx.read_to_end(1 << 10).map(|r| reply = r).unwrap();
    assert_eq!(u64::from_le_bytes(reply[..8].try_into().unwrap()), BIG);
    assert_eq!(&reply[8..], &pattern_hash(7, BIG));

    // Download from the generator through std::io::Read.
    let down = ep.connect(peer.addr.clone(), GEN).unwrap();
    let (mut tx, mut rx) = down.open_bi().unwrap();
    let mut req = 9u64.to_le_bytes().to_vec();
    req.extend_from_slice(&BIG.to_le_bytes());
    tx.write_all(&req).unwrap();
    tx.flush().unwrap();
    let mut h = blake3::Hasher::new();
    let mut total = 0u64;
    loop {
        let n = rx.read(&mut buf).unwrap();
        if n == 0 {
            break;
        }
        h.update(&buf[..n]);
        total += n as u64;
    }
    assert_eq!(total, BIG);
    assert_eq!(h.finalize().as_bytes(), &pattern_hash(9, BIG));
}
