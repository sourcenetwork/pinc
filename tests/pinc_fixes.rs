//! Regressions of the facade: a dropped stream past the list of 128 is still drained, a reset stream answers with the
//! reset and a cancelled reset still ends the stream, and a deadline added by a waiting future wakes the driver.
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

use std::future::Future;
use std::task::{Context, Waker};
use std::time::{Duration, Instant};

use pinc::{ErrorKind, Limits};
use pinc_common::{ECHO, bind, bind_idle, pattern, within};

/// Streams each side keeps open with data on them: 196 in all, past the 128 the engine once listed.
const OPEN: usize = 98;

#[nuclei::test]
async fn streams_dropped_past_128_are_still_drained() {
    within(60, async {
        let limits = Limits {
            pool_chunks: 800,
            stream_window: 16 * 1024,
            accept_streams: 200,
            ..Limits::default()
        };
        let server = bind(pinc_common::builder().alpn(ECHO).limits(limits)).await;
        let client = bind(pinc_common::builder().alpn(ECHO)).await;
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        let mut held = Vec::new();
        for _ in 0..OPEN {
            let (mut tx, rx) = c.open_bi().await.unwrap();
            tx.write_all(&[1u8; 4096]).await.unwrap();
            held.push((tx, rx));
        }
        let s = server.accept().await.unwrap().into_connection();
        let mut kept = Vec::new();
        for _ in 0..OPEN {
            // The receive half is dropped at once: what the peer sends on it is thrown away.
            let (tx, rx) = s.accept_bi().await.unwrap();
            drop(rx);
            kept.push(tx);
        }
        for _ in 0..OPEN {
            let (mut tx, rx) = s.open_bi().await.unwrap();
            tx.write_all(b"x").await.unwrap();
            drop(rx);
            kept.push(tx);
            let (mut ctx, crx) = c.accept_bi().await.unwrap();
            ctx.write_all(&[2u8; 4096]).await.unwrap();
            held.push((ctx, crx));
        }
        // One more stream, read in full: the discarded bytes must not hold the window.
        let (mut tx, mut rx) = s.open_bi().await.unwrap();
        tx.write_all(b"x").await.unwrap();
        let (mut ctx, _held) = c.accept_bi().await.unwrap();
        const LEN: usize = 1 << 20;
        let writer = nuclei::spawn_local(async move {
            let mut buf = vec![0u8; LEN];
            pattern(7, 0, &mut buf);
            ctx.write_all(&buf).await.unwrap();
            ctx.finish().await.unwrap();
        });
        let got = rx.read_to_end(LEN + 1).await.unwrap();
        assert_eq!(got.len(), LEN);
        writer.await;
        drop((held, kept));
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

#[nuclei::test]
async fn a_reset_cancelled_before_it_ran_still_ends_the_stream() {
    within(60, async {
        let (_server, _client, _c, s, mut tx, _rx) = stream_pair!();
        let (_stx, mut srx) = s.accept_bi().await.unwrap();
        // Bytes are queued, so the first poll of the reset sends them and waits for the socket before it resets.
        tx.write_all(&[3u8; 4096]).await.unwrap();
        {
            let mut cx = Context::from_waker(Waker::noop());
            let mut reset = Box::pin(tx.reset(9));
            let _ = reset.as_mut().poll(&mut cx);
        }
        drop(tx);
        // The stream ends either way: with the end after its bytes, or with the reset; it never hangs.
        let end = srx.read_to_end(1 << 20).await;
        match end {
            Ok(b) => assert_eq!(b.len(), 2 + 4096),
            Err(e) => assert_eq!(e.kind(), ErrorKind::Reset(9)),
        }
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
