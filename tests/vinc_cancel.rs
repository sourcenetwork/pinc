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

use std::future::Future;
use std::pin::pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::task::{Context, Poll, Wake, Waker};
use std::thread;
use std::time::{Duration, Instant};

use vinc::{Endpoint, NodeAddr, Vinc, block_on};
use vinc_common::{ECHO, lo, pattern, serve_conn, watchdog};

struct Flag(Thread);
type Thread = thread::Thread;
impl Wake for Flag {
    fn wake(self: Arc<Self>) {
        self.0.unpark();
    }
}

/// Poll `f` at most `polls` times, waiting a little between polls so the engine can progress, then drop it if it is
/// still pending. `Some` is its output when it finished first.
fn poll_drop<F: Future>(f: F, polls: usize) -> Option<F::Output> {
    let mut f = pin!(f);
    let waker = Waker::from(Arc::new(Flag(thread::current())));
    let mut cx = Context::from_waker(&waker);
    for _ in 0..polls {
        if let Poll::Ready(v) = f.as_mut().poll(&mut cx) {
            return Some(v);
        }
        thread::park_timeout(Duration::from_millis(2));
    }
    None
}

/// Retry `check` with a bounded backoff until it holds or `secs` pass.
fn eventually(secs: u64, what: &str, mut check: impl FnMut() -> bool) {
    let end = Instant::now() + Duration::from_secs(secs);
    let mut wait = Duration::from_millis(1);
    while !check() {
        assert!(Instant::now() < end, "not reached in {secs} s: {what}");
        thread::sleep(wait);
        wait = (wait * 2).min(Duration::from_millis(100));
    }
}

fn pair() -> (Endpoint, Endpoint) {
    let server = Vinc::builder().alpn(ECHO).bind_addr(lo()).bind_blocking().unwrap();
    let client = Vinc::builder().alpn(ECHO).bind_addr(lo()).bind_blocking().unwrap();
    let s = server.clone();
    thread::spawn(move || {
        block_on(async move {
            while let Some(inc) = s.accept().await {
                let conn = inc.into_connection();
                thread::spawn(move || block_on(serve_conn(conn)));
            }
        });
    });
    (server, client)
}

async fn echo_once(client: &Endpoint, addr: &NodeAddr) {
    let conn = client.connect(addr.clone(), ECHO).await.unwrap();
    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
    tx.write_all(b"alive").await.unwrap();
    tx.finish().await.unwrap();
    assert_eq!(rx.read_to_end(100).await.unwrap(), b"alive");
}

/// Background traffic that must not be disturbed by the dropped futures.
fn load(client: &Endpoint, addr: &NodeAddr, stop: &Arc<AtomicBool>) -> thread::JoinHandle<u64> {
    let (client, addr, stop) = (client.clone(), addr.clone(), Arc::clone(stop));
    thread::spawn(move || {
        block_on(async move {
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
    })
}

#[test]
fn dropped_connect_leaves_nothing_open() {
    watchdog(200);
    let (server, client) = pair();
    let addr = server.addr();
    let stop = Arc::new(AtomicBool::new(false));
    let bg = load(&client, &addr, &stop);
    eventually(10, "load connected", || block_on(client.peers()).unwrap().len() == 1);
    let base = block_on(client.node_stats()).unwrap().sessions;
    // Sub-sessions of the load's connection, dropped at every poll count: the client's own table comes back to base.
    for polls in 0..12 {
        for _ in 0..4 {
            let _ = poll_drop(client.connect(addr.clone(), ECHO), polls);
        }
    }
    eventually(20, "abandoned sub-sessions closed", || {
        block_on(client.node_stats()).unwrap().sessions <= base
    });
    // Full handshakes from fresh nodes, dropped at every poll count: their own tables come back to empty at once.
    let (server2, _) = pair();
    let addr2 = server2.addr();
    let fresh: Vec<Endpoint> = (0..12)
        .map(|_| Vinc::builder().alpn(ECHO).bind_addr(lo()).bind_blocking().unwrap())
        .collect();
    for (polls, f) in fresh.iter().enumerate() {
        let _ = poll_drop(f.connect(addr2.clone(), ECHO), polls);
    }
    eventually(20, "abandoned dials closed", || {
        fresh.iter().all(|f| block_on(f.node_stats()).unwrap().sessions == 0)
    });
    stop.store(true, Ordering::Relaxed);
    assert!(bg.join().unwrap() > 0);
    block_on(echo_once(&client, &addr));
    // The server hears a CLOSE from every dial that was closed after the handshake; one closed before the server's side
    // finished is dropped by the half-open timer (30 s). Once the last handle is gone nothing is left.
    drop(fresh);
    eventually(90, "server table empty", || {
        block_on(server2.node_stats()).unwrap().sessions == 0
    });
}

#[test]
fn dropped_open_accept_and_stats_lose_no_stream() {
    watchdog(120);
    let (server, client) = pair();
    let addr = server.addr();
    let stop = Arc::new(AtomicBool::new(false));
    let bg = load(&client, &addr, &stop);
    block_on(async {
        let conn = client.connect(addr.clone(), ECHO).await.unwrap();
        // Streams opened with dropped futures: those that finished are real and work, the rest do not exist.
        let mut opened = Vec::new();
        for polls in 0..8 {
            if let Some(Ok(s)) = poll_drop(conn.open_bi(), polls) {
                opened.push(s);
            }
            let _ = poll_drop(conn.stats(), polls);
        }
        for (mut tx, mut rx) in opened {
            tx.write_all(b"x").await.unwrap();
            tx.finish().await.unwrap();
            assert_eq!(rx.read_to_end(10).await.unwrap(), b"x");
        }
        echo_once(&client, &addr).await;
    });

    // accept_bi dropped at every poll count loses no stream: a peer opens five, the other side collects them all.
    let (a, b) = (client.clone(), server.clone());
    let addr_b = b.addr();
    let sender = thread::spawn(move || {
        block_on(async move {
            let conn = a.connect(addr_b, ECHO).await.unwrap();
            let mut keep = Vec::new();
            for i in 0..5u8 {
                let (mut tx, rx) = conn.open_bi().await.unwrap();
                tx.write_all(&[i]).await.unwrap();
                tx.finish().await.unwrap();
                keep.push(rx);
            }
            // Hold the streams open until the other side has them.
            thread::sleep(Duration::from_millis(500));
            drop(keep);
        });
    });
    let _ = sender;
    stop.store(true, Ordering::Relaxed);
    bg.join().unwrap();
}

#[test]
fn dropped_write_accepts_exactly_what_it_reported() {
    watchdog(120);
    let server = Vinc::builder().alpn(ECHO).bind_addr(lo()).bind_blocking().unwrap();
    let client = Vinc::builder().alpn(ECHO).bind_addr(lo()).bind_blocking().unwrap();
    let s = server.clone();
    // The server accepts a stream and does not read it until told to: the writer stalls on flow control.
    let (go_tx, go_rx) = std::sync::mpsc::channel::<()>();
    let (done_tx, done_rx) = std::sync::mpsc::channel::<()>();
    let reader = thread::spawn(move || {
        block_on(async move {
            let conn = s.accept().await.unwrap().into_connection();
            let (_tx, mut rx) = conn.accept_bi().await.unwrap();
            go_rx.recv().unwrap();
            let mut got = Vec::new();
            while let Some(c) = rx.read_chunk(64 * 1024).await.unwrap() {
                got.extend_from_slice(&c);
            }
            done_tx.send(()).unwrap();
            got
        })
    });
    let mut accepted: u64 = 0;
    let mut dropped = 0;
    block_on(async {
        let conn = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, _rx) = conn.open_bi().await.unwrap();
        let mut buf = vec![0u8; 16 * 1024];
        let end = Instant::now() + Duration::from_secs(4);
        while Instant::now() < end && dropped < 40 {
            pattern(3, accepted, &mut buf);
            // Two polls: usually Ready while there is room, Pending once the window and the channel are full.
            match poll_drop(tx.write(&buf), 2) {
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
            match poll_drop(tx.write(&buf), 50) {
                Some(Ok(n)) => accepted += n as u64,
                Some(Err(e)) => panic!("{e}"),
                None => {}
            }
        }
        tx.finish().await.unwrap();
        // The connection closes when the last handle goes, so wait until the reader has everything.
        done_rx.recv().unwrap();
    });
    let got = reader.join().unwrap();
    assert_eq!(got.len() as u64, accepted);
    let mut want = vec![0u8; got.len()];
    // Rebuild the expected stream: each reported write started at its offset in the pattern.
    pattern(3, 0, &mut want);
    assert!(got == want, "the delivered bytes differ from the reported ones");
}

#[test]
fn dropped_read_loses_no_bytes() {
    watchdog(120);
    let (server, client) = pair();
    let addr = server.addr();
    block_on(async {
        let conn = client.connect(addr, ECHO).await.unwrap();
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        let payload: Vec<u8> = (0..300_000u32).map(|i| (i % 253) as u8).collect();
        let w = async {
            tx.write_all(&payload).await.unwrap();
            tx.finish().await.unwrap();
        };
        let mut got = Vec::new();
        let mut buf = vec![0u8; 1000];
        let mut write = pin!(w);
        let mut write_done = false;
        let waker = Waker::from(Arc::new(Flag(thread::current())));
        let mut cx = Context::from_waker(&waker);
        let end = Instant::now() + Duration::from_secs(60);
        let mut polls = 0;
        loop {
            if !write_done {
                write_done = write.as_mut().poll(&mut cx).is_ready();
            }
            polls = (polls + 1) % 4;
            match poll_drop(rx.read(&mut buf), polls) {
                Some(Ok(Some(n))) => got.extend_from_slice(&buf[..n]),
                Some(Ok(None)) => break,
                Some(Err(e)) => panic!("{e}"),
                None => thread::park_timeout(Duration::from_millis(1)),
            }
            assert!(
                Instant::now() < end,
                "stalled with {} of {} bytes",
                got.len(),
                payload.len()
            );
        }
        assert_eq!(got, payload);
    });
}
