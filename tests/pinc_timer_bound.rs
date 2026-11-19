//! A layer whose deadline stays due after its timer was served neither keeps `Endpoint::close` from returning nor makes
//! the endpoint spin (pinc#569): each timer call that does not move the deadline is counted against the layer, and
//! the future that drives the endpoint sleeps a tick before the next. The layer here is a deadline of the endpoint that no
//! call moves (`Endpoint::stick_timer`).
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod pinc_common;

use std::time::{Duration, Instant};

use pinc::Timed;
use pinc_common::{ECHO, bind_idle, node, within};

/// The most timer calls that fit in the time since `start`, a tick apart.
fn ticks_since(start: Instant) -> u64 {
    start.elapsed().as_millis() as u64 + 1
}

/// A future that waits drives the endpoint for a while with the timer due, then the endpoint closes; the closing
/// future is the only one that drives it by then (the host of pinc#551 had aborted its `run` task).
#[nuclei::test]
async fn close_returns_while_a_timer_stays_due_and_the_loop_yields_between_its_calls() {
    within(60, async {
        let server = bind_idle(pinc_common::builder().alpn(ECHO)).await;
        let client = bind_idle(pinc_common::builder().alpn(ECHO)).await;
        let s = server.clone();
        let accepted = nuclei::spawn_local(async move { s.accept().await.map(pinc::Incoming::into_connection) });
        let conn = client.connect(server.addr(), ECHO).await.unwrap();
        // The server is driven until it accepted, and by nothing after that.
        let _held = accepted.await.unwrap();
        assert_eq!(
            client.timer_stats().total(),
            0,
            "a timer was left due before any was stuck"
        );

        let start = Instant::now();
        client.stick_timer();
        let waited = nuclei::time::timeout(Duration::from_millis(50), client.accept()).await;
        assert!(waited.is_err(), "nobody dials the client");
        client.close().await;
        let (stats, most) = (client.timer_stats(), ticks_since(start));
        let calls = stats.stuck(Timed::Endpoint);
        assert!(calls > 1, "the timer left due was counted {calls} times in 50 ms");
        assert_eq!(stats.total(), calls, "a layer other than the stuck one was named");
        assert!(
            calls <= most,
            "{calls} timer calls where {most} fit a tick apart: the loop did not yield between them"
        );
        drop(conn);
    })
    .await;
}

/// The endpoint goes on working with the timer due: a stream opens and echoes, and the calls are counted a tick apart.
#[nuclei::test]
async fn an_endpoint_whose_timer_stays_due_keeps_working() {
    within(60, async {
        let server = node().await;
        let client = bind_idle(pinc_common::builder().alpn(ECHO)).await;
        let conn = client.connect(server.addr(), ECHO).await.unwrap();

        let start = Instant::now();
        client.stick_timer();
        for round in 0..20u8 {
            let (mut tx, mut rx) = conn.open_bi().await.unwrap();
            tx.write_all(&[round; 64]).await.unwrap();
            tx.finish().await.unwrap();
            let mut got = [0u8; 64];
            rx.read_exact(&mut got).await.unwrap();
            assert_eq!(got, [round; 64]);
        }
        let (calls, most) = (client.timer_stats().stuck(Timed::Endpoint), ticks_since(start));
        assert!(calls > 0, "the timer left due was not counted");
        assert!(
            calls <= most,
            "{calls} timer calls where {most} fit a tick apart: the loop did not yield between them"
        );
        client.close().await;
    })
    .await;
}
