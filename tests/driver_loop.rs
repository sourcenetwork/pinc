//! The driver: the engine to quiescence after every input on virtual time, and the socket loop's wakeups.
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
use std::net::SocketAddr;
use std::pin::{Pin, pin};
use std::sync::Arc;
use std::task::{Context, Poll, Waker};
use std::thread;
use std::time::Duration;

use vinc::{NodeAddr, Vinc, block_on};
use vinc_common::{ECHO, lo};
use vinc_driver::{
    Engine, EngineConfig, Identity, Item, Limits, Remote, Request, SessionShared, Wake, chan, plane, run,
};

struct Nop;
impl Wake for Nop {
    fn wake(&self) {}
}

const A: &str = "10.0.0.1:4433";
const B: &str = "10.0.0.2:4433";

fn cfg(seed: u8, local: &str) -> EngineConfig {
    EngineConfig {
        identity: Identity::from_seed(&[seed; 32]).unwrap(),
        alpns: vec![ECHO.to_vec()],
        limits: Limits {
            pool_chunks: 256,
            ..Limits::default()
        },
        admit: None,
        max_gso: 4,
        locals: vec![local.parse().unwrap()],
    }
}

/// Carry everything `from` wants to send to `to`; returns whether anything moved.
fn pump(
    from: &mut Engine<'_, '_>,
    to: &mut Engine<'_, '_>,
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

fn quiescent(e: &mut Engine<'_, '_>, now: u64) {
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
fn settle(a: &mut Engine<'_, '_>, b: &mut Engine<'_, '_>, now: u64, inputs: &mut u64) {
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

fn poll_once<F: Future>(f: Pin<&mut F>) -> Poll<F::Output> {
    f.poll(&mut Context::from_waker(Waker::noop()))
}

#[test]
fn engines_are_quiescent_after_every_input_and_honour_deadlines() {
    // The endpoint is built on the calling thread's stack, as the driver thread does with 16 MiB.
    thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(engines_body)
        .unwrap()
        .join()
        .unwrap();
}

#[allow(clippy::too_many_lines)]
fn engines_body() {
    let (ra, pa) = plane(64, Arc::new(Nop));
    let (rb, pb) = plane(64, Arc::new(Nop));
    let (qa, _qa_rx) = chan::<Arc<SessionShared>>(8);
    let (qb, qb_rx) = chan::<Arc<SessionShared>>(8);
    let node_b = Identity::from_seed(&[2; 32]).unwrap().node_id();
    run(cfg(1, A), pa, qa, 10_000_000_000, |a| {
        run(cfg(2, B), pb, qb, 10_000_000_000, |b| {
            let mut now = 10_000_000_000u64;
            let mut inputs = 0;
            settle(a, b, now, &mut inputs);

            // Dial, and let virtual time pass to the next deadline until the answer arrives.
            let addr: SocketAddr = B.parse().unwrap();
            let remote: Remote = ra.clone();
            let dial = remote.call(|reply| Request::Connect {
                node: node_b,
                alpn: ECHO.to_vec(),
                addrs: vec![addr],
                reply,
            });
            let mut dial = pin!(dial);
            let conn = loop {
                if let Poll::Ready(r) = poll_once(dial.as_mut()) {
                    break r.unwrap().unwrap();
                }
                settle(a, b, now, &mut inputs);
                if let Poll::Ready(r) = poll_once(dial.as_mut()) {
                    break r.unwrap().unwrap();
                }
                let next = [a.poll_timeout(), b.poll_timeout()].into_iter().flatten().min();
                now = next.map_or(now + 1_000_000, |d| d.max(now + 1));
                assert!(now < 40_000_000_000, "the handshake did not finish");
                a.handle_timeout(now);
                b.handle_timeout(now);
            };
            let inc = qb_rx.try_recv().expect("the peer saw the session");
            assert_eq!(conn.node, node_b);
            assert_eq!(inc.alpn.as_bytes(), ECHO);

            // A stream and 300 KB across it, in order.
            let open = ra.call(|reply| Request::Open {
                session: conn.id,
                bidi: true,
                reply,
            });
            let mut open = pin!(open);
            assert!(poll_once(open.as_mut()).is_pending());
            settle(a, b, now, &mut inputs);
            let ns = match poll_once(open.as_mut()) {
                Poll::Ready(r) => r.unwrap().unwrap(),
                Poll::Pending => panic!("open was not answered after one settle"),
            };
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
                let mut open = pin!(open);
                assert!(poll_once(open.as_mut()).is_pending());
                settle(a, b, now, &mut inputs);
                match poll_once(open.as_mut()) {
                    Poll::Ready(r) => streams.push(r.unwrap().unwrap()),
                    Poll::Pending => panic!("open was not answered"),
                }
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
        .unwrap();
    })
    .unwrap();
}

#[test]
fn an_idle_loop_sleeps_and_a_quiet_connection_wakes_only_for_its_timers() {
    let a = Vinc::builder().alpn(ECHO).bind_addr(lo()).bind_blocking().unwrap();
    let b = Vinc::builder().alpn(ECHO).bind_addr(lo()).bind_blocking().unwrap();

    // Nothing queued and no sessions: the loop is blocked in the kernel and wakes for nothing.
    thread::sleep(Duration::from_millis(200));
    let before = a.loop_stats().counts();
    thread::sleep(Duration::from_millis(800));
    let idle = a.loop_stats().counts();
    assert_eq!(idle.wakeups, before.wakeups, "an idle loop woke up");
    assert_eq!(idle.timeouts, before.timeouts);

    // A connected, quiet pair: only keepalive timers run. A busy loop would wake thousands of times.
    let s = b.clone();
    thread::spawn(move || {
        block_on(async move {
            while let Some(i) = s.accept().await {
                std::mem::forget(i);
            }
        })
    });
    let conn = block_on(a.connect(NodeAddr::from(b.addr()), ECHO)).unwrap();
    thread::sleep(Duration::from_millis(500));
    let t0 = (a.loop_stats().counts(), b.loop_stats().counts());
    thread::sleep(Duration::from_secs(4));
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
}
