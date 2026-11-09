//! The driver: the engine to quiescence after every input on virtual time, and the driver future's wakeups.
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
    clippy::needless_continue,
    clippy::cast_possible_truncation
)]

mod vinc_common;

use std::future::Future;
use std::net::SocketAddr;
use std::pin::pin;
use std::sync::Arc;
use std::time::Duration;

use vinc::Vinc;
use vinc_common::{ECHO, bind, within};
use vinc_driver::{AllowAll, Engine, EngineConfig, Identity, Item, Limits, Request, SessionShared, chan, plane, run};
use vinc_keystore::KeyStore;

const A: &str = "10.0.0.1:4433";
const B: &str = "10.0.0.2:4433";

fn cfg(seed: u8, local: &str) -> EngineConfig<vinc_keystore::SoftwareStore, AllowAll> {
    EngineConfig {
        identity: Identity::from_seed(&[seed; 32]).unwrap(),
        alpns: vec![ECHO.to_vec()],
        limits: Limits {
            pool_chunks: 256,
            ..Limits::default()
        },
        admit: AllowAll,
        max_gso: 4,
        locals: vec![local.parse().unwrap()],
    }
}

/// Carry everything `from` wants to send to `to`; returns whether anything moved.
fn pump<S: KeyStore>(
    from: &mut Engine<'_, '_, S, AllowAll>,
    to: &mut Engine<'_, '_, S, AllowAll>,
    (fa, ta): (SocketAddr, SocketAddr),
    now: u64,
    inputs: &mut u64,
) -> bool {
    let mut buf = vec![0u8; 65_536];
    let mut moved = false;
    from.service(now);
    while let Some(t) = from.poll_transmit(now, &mut buf) {
        for seg in buf[..t.len].chunks(t.segment_size) {
            let mut d = seg.to_vec();
            to.handle_datagram(now, ta, fa, &mut d);
            *inputs += 1;
            to.service(now);
            moved = true;
        }
    }
    moved
}

fn quiescent<S: KeyStore>(e: &mut Engine<'_, '_, S, AllowAll>, now: u64) {
    let mut buf = vec![0u8; 65_536];
    assert_eq!(e.service(now), 0, "not quiescent: work left after settling");
    assert!(
        e.poll_transmit(now, &mut buf).is_none(),
        "not quiescent: a datagram is left to send"
    );
    assert!(
        e.poll_timeout().is_none_or(|d| d > now),
        "a deadline is in the past: the loop would spin"
    );
}

/// Run both engines to quiescence at `now`, carrying datagrams between them at once, then check the invariant: nothing
/// left to service or send, and the next deadline lies in the future.
fn settle<S: KeyStore>(
    a: &mut Engine<'_, '_, S, AllowAll>,
    b: &mut Engine<'_, '_, S, AllowAll>,
    now: u64,
    inputs: &mut u64,
) {
    let (aa, ba): (SocketAddr, SocketAddr) = (A.parse().unwrap(), B.parse().unwrap());
    for _ in 0..10_000 {
        let x = pump(a, b, (aa, ba), now, inputs);
        let y = pump(b, a, (ba, aa), now, inputs);
        if !x && !y {
            break;
        }
    }
    quiescent(a, now);
    quiescent(b, now);
}

/// Await `fut` while running `step` between its polls: the test's own loop, on the nuclei task that polls it.
async fn until<T>(fut: impl Future<Output = T>, mut step: impl FnMut()) -> T {
    let mut fut = pin!(fut);
    loop {
        nuclei::select! {
            biased;
            r = fut.as_mut() => return r,
            () = nuclei::task::yield_now() => step(),
        }
    }
}

/// A runtime whose workers have the stack an engine of 1024 sessions is built with.
fn big_stack() -> nuclei::Builder {
    nuclei::Builder::new().thread_stack_size(64 << 20)
}

#[allow(clippy::too_many_lines)]
#[nuclei::test(builder = "big_stack")]
async fn engines_are_quiescent_after_every_input_and_honour_deadlines() {
    // The engines are built on a worker of the runtime above, whose stack holds them.
    nuclei::spawn(engines_body()).await;
}

#[allow(clippy::too_many_lines)]
async fn engines_body() {
    let (ra, pa) = plane(64);
    let (rb, pb) = plane(64);
    let (qa, _qa_rx) = chan::<Arc<SessionShared>>(8);
    let (qb, qb_rx) = chan::<Arc<SessionShared>>(8);
    let node_b = Identity::from_seed(&[2; 32]).unwrap().node_id();
    run(cfg(1, A), pa, qa, 10_000_000_000, async |a| {
        run(cfg(2, B), pb, qb, 10_000_000_000, async |b| {
            let mut now = 10_000_000_000u64;
            let mut inputs = 0;
            settle(a, b, now, &mut inputs);

            // Dial, and let virtual time pass to the next deadline until the answer arrives.
            let addr: SocketAddr = B.parse().unwrap();
            let dial = ra.call(|reply| Request::Connect {
                node: node_b,
                alpn: ECHO.to_vec(),
                addrs: vec![addr],
                reply,
            });
            let mut settled = false;
            let conn = until(dial, || {
                if settled {
                    let next = [a.poll_timeout(), b.poll_timeout()].into_iter().flatten().min();
                    now = next.map_or(now + 1_000_000, |d| d.max(now + 1));
                    assert!(now < 40_000_000_000, "the handshake did not finish");
                    a.handle_timeout(now);
                    b.handle_timeout(now);
                } else {
                    settle(a, b, now, &mut inputs);
                }
                settled = !settled;
            })
            .await
            .unwrap()
            .unwrap();
            let inc = qb_rx.try_recv().expect("the peer saw the session");
            assert_eq!(conn.node, node_b);
            assert_eq!(inc.alpn.as_bytes(), ECHO);

            // A stream and 300 KB across it, in order.
            let open = ra.call(|reply| Request::Open {
                session: conn.id,
                bidi: true,
                reply,
            });
            let ns = until(open, || settle(a, b, now, &mut inputs)).await.unwrap().unwrap();
            let tx = ns.tx.unwrap();
            let payload: Vec<u8> = (0..300_000u32).map(|i| (i % 251) as u8).collect();
            let mut sent = 0;
            let mut got = Vec::new();
            let mut peer_rx = None;
            while got.len() < payload.len() {
                while sent < payload.len() && !tx.is_full() {
                    let n = 16_384.min(payload.len() - sent);
                    tx.send(Item::Data(payload[sent..sent + n].to_vec()));
                    sent += n;
                    ra.nudge(&ns.shared);
                }
                settle(a, b, now, &mut inputs);
                if peer_rx.is_none() {
                    peer_rx = inc.accept_bi.try_recv();
                }
                if let Some(p) = &peer_rx {
                    let rx = p.rx.as_ref().unwrap();
                    while let Some(chunk) = rx.try_recv() {
                        got.extend_from_slice(&chunk);
                        rb.nudge(&p.shared);
                    }
                }
                now += 1_000_000;
                a.handle_timeout(now);
                b.handle_timeout(now);
                assert!(now < 60_000_000_000, "the transfer did not finish");
            }
            assert_eq!(got, payload);
            assert!(inputs > 100);

            // Three streams opened in order, the last written first: the endpoint reports only the first frame's stream
            // as opened, and the peer must still see all three.
            let mut streams = Vec::new();
            for _ in 0..3 {
                let open = ra.call(|reply| Request::Open {
                    session: conn.id,
                    bidi: true,
                    reply,
                });
                streams.push(until(open, || settle(a, b, now, &mut inputs)).await.unwrap().unwrap());
            }
            for i in [2usize, 0, 1] {
                streams[i].tx.as_ref().unwrap().send(Item::Data(vec![i as u8; 100]));
                ra.nudge(&streams[i].shared);
                settle(a, b, now, &mut inputs);
            }
            let mut seen = Vec::new();
            while let Some(p) = inc.accept_bi.try_recv() {
                seen.push(p.rx.as_ref().unwrap().try_recv().map(|d| d[0]));
            }
            seen.sort();
            assert_eq!(
                seen,
                vec![Some(0), Some(1), Some(2)],
                "a stream opened out of order was lost"
            );
        })
        .await
        .unwrap();
    })
    .await
    .unwrap();
}

#[nuclei::test]
async fn an_idle_driver_sleeps_and_a_quiet_connection_wakes_only_for_its_timers() {
    within(60, async {
        let a = bind(Vinc::builder().alpn(ECHO)).await;
        let b = bind(Vinc::builder().alpn(ECHO)).await;

        // Nothing queued and no sessions: the driver is parked on its await and wakes for nothing.
        nuclei::time::sleep(Duration::from_millis(200)).await;
        let before = a.loop_stats().counts();
        nuclei::time::sleep(Duration::from_millis(800)).await;
        let idle = a.loop_stats().counts();
        assert_eq!(idle.wakeups, before.wakeups, "an idle driver woke up");
        assert_eq!(idle.timeouts, before.timeouts);

        // A connected, quiet pair: only keepalive timers run. A busy driver would wake thousands of times.
        let s = b.clone();
        nuclei::spawn(async move {
            while let Some(i) = s.accept().await {
                std::mem::forget(i);
            }
        })
        .detach();
        let conn = a.connect(b.addr(), ECHO).await.unwrap();
        nuclei::time::sleep(Duration::from_millis(500)).await;
        let t0 = (a.loop_stats().counts(), b.loop_stats().counts());
        nuclei::time::sleep(Duration::from_secs(4)).await;
        let t1 = (a.loop_stats().counts(), b.loop_stats().counts());
        for (x, y, who) in [(t0.0, t1.0, "dialer"), (t0.1, t1.1, "acceptor")] {
            let wakes = y.wakeups - x.wakeups;
            assert!(wakes <= 40, "{who}: {wakes} wakeups in 4 s of quiet");
            assert!(y.early - x.early <= 2, "{who}: the wait ended early too often");
        }
        // A timer ran late by no more than the machine's scheduling allows (generous: the test machine may be loaded).
        assert!(
            t1.0.max_late_ns < 500_000_000,
            "a timer ran {} ms late",
            t1.0.max_late_ns / 1_000_000
        );
        drop(conn);
        eprintln!(
            "quiet wakeups: dialer {}, acceptor {}",
            t1.0.wakeups - t0.0.wakeups,
            t1.1.wakeups - t0.1.wakeups
        );
    })
    .await;
}
