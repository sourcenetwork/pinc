//! A dial to a peer that stopped fails within the bound of the path the dialing node takes, and a redial reaches the
//! peer once it restarted on the same address, with and without a hub named as relay. On a node that is not thin the
//! connection handed over early ends when the resend timer fires after 4 unanswered first flights: 6 first delays for
//! a resume, 15 for a full handshake, the first delay being 500 ms unless the round trip remembered for the peer or
//! the node's handshake floor is longer (3 s and 7.5 s on a quiet host). A thin node (one that measured a round trip
//! of 250 ms or more, as one first handshake slowed by a stalled host makes it) keeps its 60 s handshake limit. Each
//! resend is scheduled from the moment its timer ran, so time in which the test's thread could not run moves the end
//! by as much: the test measures that time and adds it to the bound.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::needless_continue,
    clippy::too_many_lines
)]

#[macro_use]
mod pinc_common;

use std::cell::Cell;
use std::net::SocketAddr;
use std::rc::Rc;
use std::time::{Duration, Instant};

use pinc::{NodeAddr, Relay};
use pinc_common::{ECHO, echo_stream, eventually, within};
use pinc_transport::conn::connect_limit;

/// The shortest first resend delay of a dial.
const FIRST_DELAY: Duration = Duration::from_millis(500);
/// Slack for a loaded host.
const SLACK: Duration = Duration::from_millis(1_500);
/// How often the stall meter reads the clock.
const TICK: Duration = Duration::from_millis(10);

/// When a connection handed over early to a peer that stopped ends on a node that is not thin: 15 first delays (a
/// full handshake's flights go at 0, 1, 3 and 7 first delays and it ends at 15; a resume ends at 6), never past the
/// handshake limit. The first delay is `max(500 ms, 2 x r, floor)`, `r` the peer's remembered round trip, else the
/// node average; on a node that is not thin the average is under 250 ms, so only the peer's can raise the delay, and
/// that is the first dial's own handshake sample, which the first dial's time bounds from above.
fn early_bound(first_dial: Duration, floor: Duration) -> Duration {
    let first = FIRST_DELAY.max(first_dial.saturating_mul(2)).max(floor);
    first.saturating_mul(15).min(Duration::from_nanos(connect_limit(false)))
}

/// An endpoint bound at `addr`, so a restarted peer can come back on the same address.
macro_rules! endpoint_at {
    ($builder:expr, $addr:expr) => {{
        let sock = ::std::sync::Arc::new(::nuclei::Handle::<::std::net::UdpSocket>::bind($addr).await.unwrap());
        let (r, s) = (::std::sync::Arc::clone(&sock), ::std::sync::Arc::clone(&sock));
        $builder
            .local_addr(sock.local_addr().unwrap())
            .build(
                async move |buf: &mut [u8]| r.recv_from(buf).await,
                async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
                async |at: ::std::time::Instant| ::nuclei::time::sleep_until_precise(at).await,
            )
            .unwrap()
    }};
}

/// Run `ep` and echo every stream of every session it accepts.
macro_rules! serve_echo {
    ($ep:expr) => {{
        let (run, acc) = ($ep.clone(), $ep.clone());
        nuclei::spawn_local(async move {
            let serve = async move {
                let mut open = Vec::new();
                while let Some(inc) = acc.accept().await {
                    let conn = inc.into_connection();
                    if let Ok((tx, rx)) = conn.accept_bi().await {
                        echo_stream(tx, rx).await;
                    }
                    open.push(conn);
                }
            };
            nuclei::select! {
                _r = run.run() => {},
                () = serve => {},
            }
        })
    }};
}

/// Dial `to` and echo one message on a fresh stream; whether the echo came back within 3 s.
macro_rules! echoes {
    ($a:expr, $to:expr) => {{
        nuclei::time::timeout(Duration::from_secs(3), async {
            let conn = $a.connect($to, ECHO).await?;
            let (mut tx, mut rx) = conn.open_bi().await?;
            tx.write_all(b"ping").await?;
            tx.finish().await?;
            let mut got = [0u8; 4];
            rx.read_exact(&mut got).await?;
            Ok::<_, pinc::Error>(got == *b"ping")
        })
        .await
        .map_or(false, |r| r.inspect_err(|e| eprintln!("echo: {e}")).unwrap_or(false))
    }};
}

async fn redial_after_restart(hub: bool) -> bool {
    let relays = if hub {
        let h = endpoint_at!(pinc_common::builder().seed(&[10; 32]).unwrap().hub(), pinc_common::lo());
        let relay = Relay::new(h.id()).with_udp(h.local_addr());
        let run = h.clone();
        nuclei::spawn_local(async move {
            let _ = run.run().await;
        })
        .detach();
        std::mem::forget(h);
        vec![relay]
    } else {
        Vec::new()
    };
    let b = endpoint_at!(
        pinc_common::builder()
            .seed(&[2; 32])
            .unwrap()
            .alpn(ECHO)
            .relays(relays.clone()),
        pinc_common::lo()
    );
    let b_addr = b.local_addr();
    let b_id = b.id();
    let b_task = serve_echo!(b);
    let a = endpoint_at!(
        pinc_common::builder()
            .seed(&[1; 32])
            .unwrap()
            .alpn(ECHO)
            .relays(relays.clone()),
        pinc_common::lo()
    );
    let run = a.clone();
    nuclei::spawn_local(async move {
        let _ = run.run().await;
    })
    .detach();
    let mut to = NodeAddr::new(b_id);
    to.direct = vec![b_addr];
    // As a node does: a topic both joined.
    let t = Instant::now();
    assert!(echoes!(a, to.clone()), "the first dial echoes");
    let first_dial = t.elapsed();
    if hub {
        a.join(b"t", &[]).await.unwrap();
        b.join(b"t", &[]).await.unwrap();
        a.publish(b"t", b"x", None).await.unwrap();
        nuclei::time::sleep(Duration::from_secs(1)).await;
    }
    // The peer stops without a word, as a process that is killed.
    drop(b_task);
    drop(b);
    // A dial while the peer is down, as a replicator's retry makes. It fails, or the connection it hands back (reported
    // early, with a cached allow) ends within the bound of the node's path and fails what was written on it.
    let st = a.node_stats().await.unwrap();
    let early = early_bound(first_dial, Duration::from_nanos(st.hs_floor));
    // How long this thread could not run while the dial was pending: every endpoint of the test runs on it.
    let stalled = Rc::new(Cell::new(Duration::ZERO));
    let meter = nuclei::spawn_local({
        let stalled = Rc::clone(&stalled);
        async move {
            loop {
                let due = Instant::now() + TICK;
                nuclei::time::sleep_until_precise(due).await;
                stalled.set(stalled.get() + due.elapsed());
            }
        }
    });
    let at = Instant::now();
    // The test's own limit stops a dial that never ends.
    let down = async {
        let conn = a.connect(to.clone(), ECHO).await?;
        let (mut tx, mut rx) = conn.open_bi().await?;
        tx.write_all(b"ping").await?;
        let mut got = [0u8; 4];
        let read = rx.read_exact(&mut got).await;
        // What was written before the connection failed is reported as failed, not taken as sent.
        if read.is_err() {
            assert!(tx.finish().await.is_err(), "the stream of a failed connection finished");
        }
        read
    }
    .await;
    let took = at.elapsed();
    // A stall that ended as the dial did is counted once the meter has run.
    nuclei::time::sleep(TICK * 2).await;
    drop(meter);
    // The limit follows the node's round trips while the dial runs: a node thin at its start, or thin by its end,
    // keeps the thin limit.
    let thin = st.thin || a.node_stats().await.unwrap().thin;
    let (path, limit) = if thin {
        ("thin", Duration::from_nanos(connect_limit(true)))
    } else {
        ("early", early)
    };
    let bound = limit + SLACK + stalled.get();
    eprintln!(
        "down: {down:?} after {took:?} on the {path} path (bound {bound:?}, stalled {:?}, first dial {first_dial:?}, \
         lrtt {} us, tgr {} us, floor {} us)",
        stalled.get(),
        st.lrtt / 1_000,
        st.tgr / 1_000,
        st.hs_floor / 1_000
    );
    assert!(
        matches!(&down, Err(e) if matches!(e.kind(), pinc::ErrorKind::TimedOut | pinc::ErrorKind::Unreachable)),
        "a dial to a peer that stopped did not fail with TimedOut or Unreachable: {down:?}"
    );
    assert!(
        took <= bound,
        "a dial to a peer that stopped failed after {took:?}, past the bound of the {path} path, {bound:?}"
    );
    // The same peer comes back on the same address.
    let b = endpoint_at!(
        pinc_common::builder().seed(&[2; 32]).unwrap().alpn(ECHO).relays(relays),
        b_addr
    );
    let _b_task = serve_echo!(b);
    if hub {
        b.join(b"t", &[]).await.unwrap();
    }
    // Retried with a bounded backoff, as a replicator retries.
    eventually(20, "the redial echoes", || {
        let (a, to) = (a.clone(), to.clone());
        async move { echoes!(a, to) }
    })
    .await;
    a.close().await;
    b.close().await;
    true
}

#[nuclei::test]
async fn a_redial_reaches_a_restarted_peer_without_a_hub() {
    within(120, async { assert!(redial_after_restart(false).await) }).await;
}

#[nuclei::test]
async fn a_redial_reaches_a_restarted_peer_with_a_hub_named() {
    within(120, async {
        assert!(
            redial_after_restart(true).await,
            "the redial did not reach the restarted peer"
        );
    })
    .await;
}
