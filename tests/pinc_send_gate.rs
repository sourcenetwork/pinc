//! A call that takes its value out of the endpoint (a read, an accept, an open, a dial) returns it in the poll that
//! took it, before anything is sent (pinc#636, pinc#702): a future dropped after its attempt finished keeps its
//! result, and what the attempt queued leaves with the next poll of any future on the endpoint. A call whose payload
//! is the send (a write, a datagram, a close) sends first and returns after, as before those issues, so the
//! endpoint's last packets never wait for a poll that never comes.
//!
//! The client of every test is an endpoint whose send closure parks each datagram while the gate is armed and sends
//! it once the gate opens, or, with `once` set, is pending once at every send (a socket buffer full for a moment);
//! its receive is never gated, so the peer's traffic arrives as usual. On the code before the fix of pinc#636 a
//! value-taking call waited for the flush of what its attempt owed before it returned, and a future dropped in that
//! wait lost what it had taken: `a_read_dropped_in_the_send_after_it_loses_no_bytes` fails on that code (bytes
//! lost). The datagram-read, open and allocation tests pass on that code too: they guard the fix, they do not
//! witness the bug.
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
    clippy::cast_possible_truncation,
    missing_docs
)]

#[macro_use]
mod pinc_common;

use std::cell::Cell;
use std::net::{SocketAddr, UdpSocket};
use std::rc::Rc;
use std::sync::Arc;

use crate::pinc_common::poll_drop;
use std::future::poll_fn;
use std::task::{Context, Poll, Waker};

use nuclei::Handle;
use pinc::{Builder, Endpoint, Hosted};
use pinc_common::{builder, within};

pinc_tests::install_counting_allocator!();

/// The bytes one pattern write of the peer tests carries.
const SIZE: usize = 512;

/// The send gate of the test client: while armed, the client's send closure parks the datagram until it opens.
struct Gate {
    on: Cell<bool>,
    /// Send-closure entries that found the gate armed.
    held: Cell<u64>,
    /// Datagrams the closure sent, held or not.
    passed: Cell<u64>,
    waker: std::cell::RefCell<Option<Waker>>,
    /// Every send is pending once (it wakes its task at once and completes when polled again), as on a host whose
    /// socket buffer is full for a moment at each send.
    once: Cell<bool>,
}

impl Gate {
    fn new() -> Rc<Self> {
        Rc::new(Self {
            on: Cell::new(false),
            held: Cell::new(0),
            passed: Cell::new(0),
            waker: std::cell::RefCell::new(None),
            once: Cell::new(false),
        })
    }

    fn arm(&self) {
        self.on.set(true);
    }

    fn open(&self) {
        self.on.set(false);
        if let Some(w) = self.waker.borrow_mut().take() {
            w.wake();
        }
    }
}

/// The test client: a loopback endpoint whose send parks while the gate is armed. Nothing drives it but the futures
/// the test awaits.
async fn gated(gate: Rc<Gate>, b: Builder) -> Endpoint<impl Hosted> {
    let sock = Arc::new(Handle::<UdpSocket>::bind(pinc_common::lo()).await.unwrap());
    let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
    b.local_addr(sock.local_addr().unwrap())
        .build(
            async move |buf: &mut [u8]| r.recv_from(buf).await,
            async move |pkt: &[u8], to: SocketAddr| {
                if gate.once.get() {
                    gate.held.set(gate.held.get() + 1);
                    let mut first = true;
                    poll_fn(|cx: &mut Context<'_>| {
                        if std::mem::take(&mut first) {
                            cx.waker().wake_by_ref();
                            Poll::Pending
                        } else {
                            Poll::Ready(())
                        }
                    })
                    .await;
                }
                if gate.on.get() {
                    gate.held.set(gate.held.get() + 1);
                    poll_fn(|cx: &mut Context<'_>| {
                        if gate.on.get() {
                            *gate.waker.borrow_mut() = Some(cx.waker().clone());
                            Poll::Pending
                        } else {
                            Poll::Ready(())
                        }
                    })
                    .await;
                }
                gate.passed.set(gate.passed.get() + 1);
                s.send_to(pkt, to).await
            },
            async |at: std::time::Instant| nuclei::time::sleep_until_precise(at).await,
        )
        .unwrap()
}

/// `recv_datagram` returns in the poll that took the datagram, although every send of the endpoint parks: the answer
/// the datagrams' arrival owed is left for the next poll of a future, and the read does not wait for it. The
/// endpoint's driver receives the datagrams and parks in the flush of the answer they owed, so the read's own poll
/// finds them queued and takes one out. A guard: it passes on the code before the fix too, whose read found nothing
/// left to send here.
#[nuclei::test]
async fn a_datagram_read_returns_while_the_answers_are_owed() {
    within(120, async {
        let server = pinc_common::bind(builder().alpn(pinc_common::ECHO)).await;
        let gate = Gate::new();
        let client = gated(Rc::clone(&gate), builder().alpn(pinc_common::ECHO)).await;
        // A driver, so the datagrams are received by its polls and the read only takes them out.
        let drive = client.clone();
        nuclei::spawn_local(async move {
            let _ = drive.run().await;
        })
        .detach();
        let conn = client.connect(server.addr(), pinc_common::ECHO).await.unwrap();
        let (go_tx, go_rx) = nuclei::sync::oneshot::channel::<()>();
        nuclei::spawn_local({
            let server = server.clone();
            async move {
                let c = server.accept().await.unwrap().into_connection();
                let _ = go_rx.await;
                // Four datagrams: the endpoint answers every second packet it hears, so answers are owed from the
                // second on. The driver parks in the flush of the first.
                c.send_datagram(b"first").await.unwrap();
                c.send_datagram(b"second").await.unwrap();
                c.send_datagram(b"third").await.unwrap();
                c.send_datagram(b"fourth").await.unwrap();
                // The session stays up until the test is done: a dropped connection ends it.
                let _ = c.closed().await;
            }
        })
        .detach();
        // Let the connect's own timers be serviced before the gate closes, so no timer of theirs falls due inside a
        // read.
        nuclei::time::sleep(std::time::Duration::from_millis(100)).await;
        gate.arm();
        let _ = go_tx.send(());
        let mut buf = vec![0u8; 64];
        let n = poll_drop(conn.recv_datagram(&mut buf), 8)
            .await
            .unwrap_or_else(|| panic!("the read waited on the answer it owed"))
            .unwrap();
        assert_eq!(&buf[..n], b"first", "the read did not return the first datagram");
        let n = poll_drop(conn.recv_datagram(&mut buf), 8)
            .await
            .unwrap_or_else(|| panic!("the read waited on the answer it owed"))
            .unwrap();
        assert_eq!(&buf[..n], b"second", "the read did not return the second datagram");
        // The answers leave with the next poll that sends: the gate opens, and the stats call after it flushes what
        // the reads left owed.
        gate.open();
        let _ = conn.stats().await;
        assert!(gate.passed.get() > 0, "the answers never left");
    })
    .await;
}

/// An open returns in the poll that took the stream's handles, although every send of the endpoint parks: the
/// answers the peer's datagrams owed are left for the next poll of a future, and the open does not wait for them.
/// The endpoint's driver receives the datagrams and parks in the flush of the first answer they owed, so one answer
/// may still be queued when the open runs. A guard: it passes on the code before the fix too.
#[nuclei::test]
async fn an_open_returns_while_the_answers_are_owed() {
    within(120, async {
        let server = pinc_common::bind(builder().alpn(pinc_common::ECHO)).await;
        let gate = Gate::new();
        let client = gated(Rc::clone(&gate), builder().alpn(pinc_common::ECHO)).await;
        let drive = client.clone();
        nuclei::spawn_local(async move {
            let _ = drive.run().await;
        })
        .detach();
        let conn = client.connect(server.addr(), pinc_common::ECHO).await.unwrap();
        let (go_tx, go_rx) = nuclei::sync::oneshot::channel::<()>();
        nuclei::spawn_local({
            let server = server.clone();
            async move {
                let c = server.accept().await.unwrap().into_connection();
                let _ = go_rx.await;
                // Four datagrams: the endpoint answers every second packet it hears, so answers are owed from the
                // second on. The driver parks in the flush of the first, and the second is still queued when the
                // open runs.
                for _ in 0..4 {
                    c.send_datagram(b"more").await.unwrap();
                }
                // The session stays up until the test is done: a dropped connection ends it.
                let _ = c.closed().await;
            }
        })
        .detach();
        // Let the connect's own timers be serviced before the gate closes, so no timer of theirs falls due inside a
        // call.
        nuclei::time::sleep(std::time::Duration::from_millis(100)).await;
        gate.arm();
        let _ = go_tx.send(());
        // The datagrams reach the driver and its flush parks on the first answer they owed.
        nuclei::time::sleep(std::time::Duration::from_millis(200)).await;
        let (tx, _rx) = poll_drop(conn.open_bi(), 8)
            .await
            .unwrap_or_else(|| panic!("the open waited on the answers it owed"))
            .unwrap();
        // The answers leave with the next poll that sends: the gate opens, and the stats call after it flushes what
        // the open left owed.
        gate.open();
        let _ = conn.stats().await;
        assert!(gate.passed.get() > 0, "the answers never left");
        drop(tx);
    })
    .await;
}

/// Steady traffic through a call whose payload is the send allocates nothing: rounds of write, the write's flush
/// (which sends the queued packet inside the call) and the stats call that follows move no heap memory once the
/// endpoint is set up.
#[nuclei::test]
async fn steady_rounds_through_the_gated_send_allocate_nothing() {
    within(60, async {
        let server = pinc_common::bind(builder().alpn(pinc_common::ECHO)).await;
        let gate = Gate::new();
        let client = gated(Rc::clone(&gate), builder().alpn(pinc_common::ECHO)).await;
        let conn = client.connect(server.addr(), pinc_common::ECHO).await.unwrap();
        // The peer takes the stream and reads only what the client wrote, after the measured window: the window runs
        // on the test thread only.
        let (go_tx, go_rx) = nuclei::sync::oneshot::channel::<()>();
        nuclei::spawn_local({
            let server = server.clone();
            async move {
                let c = server.accept().await.unwrap().into_connection();
                // The signal goes up before the accept: the stream is announced only with the client's first
                // write, which waits for this signal.
                let _ = go_tx.send(());
                let (_t, mut r) = c.accept_bi().await.unwrap();
                // One read per round, so the peer's buffers reach their steady size inside the warmup and the
                // measured window sees no growth on either side.
                let mut got = 0usize;
                for _ in 0..10 {
                    let mut chunk = vec![0u8; SIZE];
                    r.read_exact(&mut chunk).await.unwrap();
                    got += SIZE;
                }
                let rest = r.read_to_end(1 << 20).await.unwrap();
                got += rest.len();
                assert_eq!(got, 10 * SIZE, "bytes were lost to the gated sends");
            }
        })
        .detach();
        let (mut tx, _rx) = conn.open_bi().await.unwrap();
        let _ = go_rx.await;
        // Warm up: two rounds of write, whose flush sends the queued packet inside the call, and the stats call.
        let buf = vec![0u8; SIZE];
        for _ in 0..2 {
            assert_eq!(tx.write(&buf).await.unwrap(), SIZE);
            let _ = conn.stats().await;
        }
        let before = pinc_tests::AllocStats::now();
        for _ in 0..8 {
            assert_eq!(tx.write(&buf).await.unwrap(), SIZE);
            let _ = conn.stats().await;
        }
        let after = pinc_tests::AllocStats::now();
        let stats = pinc_tests::AllocStats {
            allocs: after.allocs - before.allocs,
            reallocs: after.reallocs - before.reallocs,
            bytes: after.bytes - before.bytes,
        };
        assert_eq!(stats.count(), 0, "the gated rounds allocated: {stats:?}");
        tx.finish().await.unwrap();
    })
    .await;
}

/// A read dropped while the send after it is pending loses no bytes: every send of the client is pending once, a
/// driver receives the stream, and every other read is dropped after its first poll, so a read whose attempt took
/// bytes and then flushed what the take owed (the stream's credit) is dropped in that flush; the bytes come back in
/// order from the reads that follow. On the code before the fix of pinc#636 and pinc#702 the read took the bytes,
/// then waited in that flush, and the dropped future took them with it.
#[nuclei::test]
async fn a_read_dropped_in_the_send_after_it_loses_no_bytes() {
    within(120, async {
        let server = pinc_common::bind(builder().alpn(pinc_common::ECHO)).await;
        let gate = Gate::new();
        let client = gated(Rc::clone(&gate), builder().alpn(pinc_common::ECHO)).await;
        let drive = client.clone();
        nuclei::spawn_local(async move {
            let _ = drive.run().await;
        })
        .detach();
        let conn = client.connect(server.addr(), pinc_common::ECHO).await.unwrap();
        gate.once.set(true);
        let payload: Vec<u8> = (0..1_000_000u32).map(|i| (i % 251) as u8).collect();
        let sent = payload.clone();
        nuclei::spawn_local({
            let server = server.clone();
            async move {
                let c = server.accept().await.unwrap().into_connection();
                let mut tx = c.open_uni().await.unwrap();
                tx.write_all(&sent).await.unwrap();
                tx.finish().await.unwrap();
                let _ = c.closed().await;
            }
        })
        .detach();
        let mut rx = conn.accept_uni().await.unwrap();
        let (mut got, mut buf, mut round) = (Vec::new(), vec![0u8; 1000], 0usize);
        loop {
            round += 1;
            match poll_drop(rx.read(&mut buf), round % 2 * 4).await {
                Some(Ok(Some(n))) => got.extend_from_slice(&buf[..n]),
                Some(Ok(None)) => break,
                Some(Err(e)) => panic!("{e}"),
                None => {}
            }
        }
        assert!(gate.held.get() > 0, "no send was pending");
        assert_eq!(got.len(), payload.len(), "bytes were lost");
        assert!(got == payload, "the bytes differ");
    })
    .await;
}
