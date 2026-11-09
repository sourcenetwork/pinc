//! Received datagrams through the facade: in order, bounded, a large burst, with the blocking and the async API.
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

use std::sync::Arc;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::thread;
use std::time::Duration;

use vinc::{ErrorKind, Vinc};
use vinc_common::{ECHO, Exec, lo, watchdog};

fn node() -> vinc::blocking::Endpoint {
    Vinc::builder()
        .alpn(ECHO)
        .bind_addr(lo())
        .bind_blocking()
        .unwrap()
        .blocking()
}

/// A datagram of `seq` and padding to `len` bytes.
fn dgram(seq: u32, len: usize) -> Vec<u8> {
    let mut d = vec![(seq % 251) as u8; len.max(4)];
    d[..4].copy_from_slice(&seq.to_le_bytes());
    d
}

fn seq(d: &[u8]) -> u32 {
    u32::from_le_bytes(d[..4].try_into().unwrap())
}

fn pair() -> (
    vinc::blocking::Endpoint,
    vinc::blocking::Connection,
    vinc::blocking::Connection,
) {
    let (server, client) = (node(), node());
    let c = client.connect(server.addr(), ECHO).unwrap();
    // The session reaches the server's queue once the client opened a stream.
    let (mut tx, _rx) = c.open_bi().unwrap();
    tx.write_all(b"hi").unwrap();
    let (_, _, s) = server.accept().unwrap();
    // Keep the endpoints alive with the connections.
    std::mem::forget(client);
    (server, c, s)
}

#[test]
fn blocking_datagrams_arrive_in_order_with_their_bytes() {
    watchdog(60);
    let (_server, c, s) = pair();
    for i in 0..50u32 {
        c.send_datagram(&dgram(i, 20 + i as usize * 7)).unwrap();
    }
    for i in 0..50u32 {
        let d = s.read_datagram().unwrap();
        assert_eq!(d, dgram(i, 20 + i as usize * 7), "datagram {i}");
    }
    // A datagram sent the other way arrives too, and one that ends the connection ends the wait.
    s.send_datagram(&dgram(9, 30)).unwrap();
    assert_eq!(c.read_datagram().unwrap(), dgram(9, 30));
    c.close(5);
    assert!(s.read_datagram().is_err());
}

#[test]
fn a_large_burst_arrives_in_order_and_what_is_lost_is_lost_whole() {
    watchdog(120);
    let (_server, c, s) = pair();
    const N: u32 = 5000;
    let got = Arc::new(AtomicUsize::new(0));
    let last = Arc::new(AtomicU32::new(0));
    let (g, l) = (Arc::clone(&got), Arc::clone(&last));
    let reader = thread::spawn(move || {
        let mut prev: Option<u32> = None;
        while let Ok(d) = s.read_datagram() {
            let n = seq(&d);
            assert!(prev.is_none_or(|p| n > p), "datagram {n} came after {prev:?}");
            assert_eq!(d.len(), 100 + (n as usize % 50));
            prev = Some(n);
            l.store(n, Ordering::SeqCst);
            g.fetch_add(1, Ordering::SeqCst);
        }
    });
    for i in 0..N {
        c.send_datagram(&dgram(i, 100 + (i as usize % 50))).unwrap();
        if i % 64 == 63 {
            thread::sleep(Duration::from_micros(200));
        }
    }
    thread::sleep(Duration::from_secs(2));
    let n = got.load(Ordering::SeqCst);
    assert!(n > 0 && n <= N as usize, "{n} datagrams of {N}");
    c.close(0);
    reader.join().unwrap();
}

#[test]
fn a_session_holds_a_bounded_number_of_unread_datagrams() {
    watchdog(120);
    let (_server, c, s) = pair();
    for i in 0..3000u32 {
        c.send_datagram(&dgram(i, 200)).unwrap();
        if i % 32 == 31 {
            thread::sleep(Duration::from_micros(300));
        }
    }
    thread::sleep(Duration::from_secs(1));
    // Nothing was read: now read what is held. The session holds its channel (64) and the endpoint's queue (64), no more.
    let got = Arc::new(AtomicUsize::new(0));
    let g = Arc::clone(&got);
    let seqs = Arc::new(std::sync::Mutex::new(Vec::new()));
    let sq = Arc::clone(&seqs);
    thread::spawn(move || {
        while let Ok(d) = s.read_datagram() {
            sq.lock().unwrap().push(seq(&d));
            g.fetch_add(1, Ordering::SeqCst);
        }
    });
    thread::sleep(Duration::from_secs(1));
    let n = got.load(Ordering::SeqCst);
    assert!((1..=128).contains(&n), "{n} datagrams were held");
    let v = seqs.lock().unwrap().clone();
    assert!(v.windows(2).all(|w| w[0] < w[1]), "out of order: {v:?}");
}

#[test]
fn async_datagrams_arrive_in_order_and_a_dropped_read_loses_nothing() {
    watchdog(120);
    let exec = Exec::new(2);
    let (server, client) = (
        Vinc::builder().alpn(ECHO).bind_addr(lo()).bind_blocking().unwrap(),
        Vinc::builder().alpn(ECHO).bind_addr(lo()).bind_blocking().unwrap(),
    );
    let to = server.addr();
    exec.block_on(async move {
        let c = client.connect(to, ECHO).await.unwrap();
        let (mut tx, _rx) = c.open_bi().await.unwrap();
        tx.write_all(b"hi").await.unwrap();
        let s = server.accept().await.unwrap().into_connection();
        // A read that is dropped before a datagram exists consumes nothing.
        let mut early = Box::pin(s.read_datagram());
        assert!(futures_poll_once(early.as_mut()).is_none());
        drop(early);
        for i in 0..40u32 {
            c.send_datagram(&dgram(i, 64)).await.unwrap();
        }
        for i in 0..40u32 {
            assert_eq!(s.read_datagram().await.unwrap(), dgram(i, 64));
        }
        c.close(3);
        assert!(matches!(
            s.read_datagram().await.unwrap_err().kind(),
            ErrorKind::Closed { .. }
        ));
    });
}

fn futures_poll_once<F: std::future::Future>(f: std::pin::Pin<&mut F>) -> Option<F::Output> {
    use std::task::{Context, Poll, Waker};
    match f.poll(&mut Context::from_waker(Waker::noop())) {
        Poll::Ready(v) => Some(v),
        Poll::Pending => None,
    }
}
