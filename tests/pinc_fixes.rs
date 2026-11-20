//! Regressions of the facade: a stream dropped past the list of 128 gives its place back, a reset stream answers with
//! the reset, a reset or a stop cancelled before it ran is still the caller's to make, a dropped send stream ends its
//! stream at once, a refused stream keeps the entry of a stopped one, and a deadline added by a waiting future wakes
//! the driver.
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

mod pinc_common;

use std::cell::Cell;
use std::future::Future;
use std::net::{SocketAddr, UdpSocket};
use std::pin::Pin;
use std::rc::Rc;
use std::sync::Arc;
use std::task::{Context, Poll, Waker};
use std::time::{Duration, Instant};

use nuclei::Handle;
use pinc::{Endpoint, ErrorKind, Hosted, Limits, SendStream};
use pinc_common::{ECHO, bind, bind_idle, within};

#[nuclei::test]
async fn a_stream_dropped_past_128_gives_back_its_place() {
    within(60, async {
        // One chunk per first charge, so the pool never binds.
        let limits = Limits {
            stream_window: 16 * 1024,
            ..Limits::default()
        };
        let server = bind(pinc_common::builder().alpn(ECHO).limits(limits)).await;
        let client = bind(pinc_common::builder().alpn(ECHO)).await;
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        let s = server.accept().await.unwrap().into_connection();
        // 29 local bidirectional streams whose receive half is dropped at once: they stay open and listed.
        let mut local = Vec::new();
        for _ in 0..29 {
            let (tx, rx) = s.open_bi().await.unwrap();
            drop(rx);
            local.push(tx);
        }
        let mut held = Vec::new();
        for _ in 0..100 {
            let (mut tx, rx) = c.open_bi().await.unwrap();
            tx.write_all(b"x").await.unwrap();
            held.push((tx, rx));
        }
        // 100 peer streams accepted and dropped: with the 29, past the 128 the list once held.
        for _ in 0..100 {
            let (tx, rx) = s.accept_bi().await.unwrap();
            drop((tx, rx));
        }
        for (tx, _) in &mut held {
            tx.finish().await.unwrap();
        }
        drop(held);
        // The credit of all 100 comes back: 100 more streams open.
        let mut more = Vec::new();
        for i in 0..100 {
            let opened = nuclei::time::timeout(Duration::from_secs(10), c.open_bi()).await;
            assert!(
                matches!(opened, Ok(Ok(_))),
                "stream credit does not return in time (open {i})"
            );
            more.push(opened);
        }
        drop((local, more));
    })
    .await;
}

/// A connected pair and one stream opened by the client with its first bytes written, as the server sees it.
macro_rules! stream_pair {
    () => {{
        let server = bind(pinc_common::builder().alpn(ECHO)).await;
        let client = bind(pinc_common::builder().alpn(ECHO)).await;
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, rx) = c.open_bi().await.unwrap();
        tx.write_all(b"hi").await.unwrap();
        let s = server.accept().await.unwrap().into_connection();
        (server, client, c, s, tx, rx)
    }};
}

#[nuclei::test]
async fn a_reset_stream_answers_write_and_finish_with_the_reset() {
    within(60, async {
        let (_server, _client, _c, _s, mut tx, _rx) = stream_pair!();
        tx.reset(7).await;
        assert_eq!(tx.write(b"x").await.unwrap_err().kind(), ErrorKind::Stopped(7));
        assert_eq!(tx.finish().await.unwrap_err().kind(), ErrorKind::Stopped(7));
    })
    .await;
}

/// Returns `Pending` once, after waking itself.
#[derive(Default)]
struct YieldOnce(bool);

impl Future for YieldOnce {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.0 {
            return Poll::Ready(());
        }
        self.0 = true;
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}

/// A client endpoint with no run future whose next send, once `hold` is set, returns `Pending` once: a host whose
/// socket is busy, the point where a future dropped in the flush of a call leaves the call's work undone.
async fn bind_gated(hold: Rc<Cell<bool>>) -> Endpoint<impl Hosted> {
    let sock = Arc::new(Handle::<UdpSocket>::bind(pinc_common::lo()).await.unwrap());
    let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
    pinc_common::builder()
        .alpn(ECHO)
        .local_addr(sock.local_addr().unwrap())
        .build(
            async move |buf: &mut [u8]| r.recv_from(buf).await,
            async move |pkt: &[u8], to: SocketAddr| {
                if hold.take() {
                    YieldOnce::default().await;
                }
                s.send_to(pkt, to).await
            },
            async |at: Instant| nuclei::time::sleep_until_precise(at).await,
        )
        .unwrap()
}

/// A server, a gated client connected to it, a stream the client opened with its bytes written and the server's
/// halves of it; then a second of nothing, so the client's loss timer is due and its socket holds unread
/// acknowledgements, which its next call serves before it runs.
macro_rules! gated_pair {
    () => {{
        let hold = Rc::new(Cell::new(false));
        let server = bind(pinc_common::builder().alpn(ECHO)).await;
        let client = bind_gated(Rc::clone(&hold)).await;
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, rx) = c.open_bi().await.unwrap();
        tx.write_all(b"hi").await.unwrap();
        let s = server.accept().await.unwrap().into_connection();
        let (stx, srx) = s.accept_bi().await.unwrap();
        tx.write_all(&[3u8; 4096]).await.unwrap();
        nuclei::time::sleep(Duration::from_secs(1)).await;
        (server, client, c, s, tx, rx, stx, srx, hold)
    }};
}

/// Write to `tx` until the peer's stop with `code` is what the write answers.
async fn until_stopped<H: Hosted>(tx: &mut SendStream<H>, code: u64) {
    let end = Instant::now() + Duration::from_secs(10);
    loop {
        if let Err(e) = tx.write(b"y").await {
            return assert_eq!(e.kind(), ErrorKind::Stopped(code));
        }
        assert!(Instant::now() < end, "the stop did not reach the writer in 10 s");
        nuclei::time::sleep(Duration::from_millis(5)).await;
    }
}

/// Poll `f` once and drop it: it must be pending, or the setup did not reach the cancel point.
fn poll_once_and_drop<F: Future>(f: F) {
    let mut f = Box::pin(f);
    let polled = f.as_mut().poll(&mut Context::from_waker(Waker::noop()));
    assert!(polled.is_pending(), "the setup did not reach the cancel point");
}

#[nuclei::test]
async fn a_reset_cancelled_before_it_ran_leaves_the_stream_writable() {
    within(60, async {
        let (_server, _client, c, _s, mut tx, _rx, _stx, mut srx, hold) = gated_pair!();
        hold.set(true);
        poll_once_and_drop(tx.reset(9));
        nuclei::spawn_local(async move {
            c.closed().await;
        })
        .detach();
        assert_eq!(tx.write(b"x").await.unwrap(), 1);
        drop(tx);
        let got = within(10, srx.read_to_end(1 << 20)).await.unwrap();
        assert_eq!(got.len(), 2 + 4096 + 1);
    })
    .await;
}

#[nuclei::test]
async fn a_stream_the_server_refused_keeps_the_entry_of_a_stream_the_peer_stopped() {
    within(120, async {
        let limits = Limits {
            accept_streams: 1,
            ..Limits::default()
        };
        let server = bind(pinc_common::builder().alpn(ECHO).limits(limits)).await;
        let client = bind(pinc_common::builder().alpn(ECHO)).await;
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        let s = server.accept().await.unwrap().into_connection();
        let (mut stx, _srx) = s.open_bi().await.unwrap();
        stx.write_all(b"x").await.unwrap();
        let (_ctx, mut crx) = c.accept_bi().await.unwrap();
        crx.stop(5).await;
        until_stopped(&mut stx, 5).await;
        // More refused streams than the table of stopped streams holds; the first one stays in the accept queue.
        let mut refused = 0;
        while refused < 130 {
            let mut batch = Vec::new();
            for _ in 0..90 {
                let (mut tx, rx) = c.open_bi().await.unwrap();
                tx.write_all(b"x").await.unwrap();
                batch.push((tx, rx));
            }
            for (tx, _) in &mut batch {
                let end = nuclei::time::timeout(Duration::from_secs(2), async {
                    while tx.write(b"y").await.is_ok() {
                        nuclei::time::sleep(Duration::from_millis(5)).await;
                    }
                })
                .await;
                refused += usize::from(end.is_ok());
            }
        }
        let err = stx.write(b"z").await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Stopped(5));
    })
    .await;
}

#[nuclei::test]
async fn a_publish_waiting_for_a_neighbour_times_out_on_time_while_another_future_drives() {
    within(30, async {
        let ep = bind_idle(pinc_common::builder().alpn(ECHO)).await;
        // This future drives the endpoint and waits for ever.
        let driver = ep.clone();
        nuclei::spawn_local(async move {
            let _ = driver.accept().await;
        })
        .detach();
        nuclei::time::sleep(Duration::from_millis(50)).await;
        let started = Instant::now();
        let err = ep
            .publish(b"topic", b"x", Some(Duration::from_millis(50)))
            .await
            .unwrap_err();
        assert_eq!(err.kind(), ErrorKind::TimedOut);
        assert!(
            started.elapsed() < Duration::from_millis(500),
            "the timeout fired after {:?}",
            started.elapsed()
        );
    })
    .await;
}
