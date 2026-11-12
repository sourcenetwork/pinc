//! How the futures of the facade drive the endpoint: the driving role is handed over when its holder is dropped, a task
//! that only writes or only reads moves the endpoint, an idle endpoint is kept alive by `Endpoint::run`, one request
//! and its response cost a bounded number of polls and no timer, and no future holds a large frame.
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

#[macro_use]
mod vinc_common;

use std::net::{SocketAddr, UdpSocket};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use nuclei::Handle;
use vinc_common::{ECHO, SINK, bind, bind_idle, client, join_all, node, pattern, pattern_hash, poll_drop, within};

vinc_tests::install_counting_allocator!();

/// The driving future is dropped after every number of polls while a second task waits on another stream of the same
/// endpoint: the second task must still get its bytes, so the role passes on, and the first loses nothing.
#[nuclei::test]
async fn the_driving_future_dropped_at_every_poll_count_hands_the_role_on() {
    within(120, async {
        let server = node().await;
        let client = bind_idle(vinc_common::builder().alpn(ECHO)).await;
        let conn = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx1, mut rx1) = conn.open_bi().await.unwrap();
        let (mut tx2, mut rx2) = conn.open_bi().await.unwrap();

        let waiter = nuclei::spawn_local(async move {
            let mut got = Vec::new();
            while got.len() < 30 {
                let mut b = [0u8; 8];
                let n = rx2.read(&mut b).await.unwrap().unwrap();
                got.extend_from_slice(&b[..n]);
            }
            got
        });

        let mut got = Vec::new();
        for round in 0..30u8 {
            tx1.write_all(&[round]).await.unwrap();
            tx2.write_all(&[round]).await.unwrap();
            let mut b = [0u8; 1];
            // The first stream's reader is the driver most of the time; it is dropped after 1..4 rounds and retried.
            loop {
                if let Some(r) = poll_drop(rx1.read(&mut b), 1 + usize::from(round) % 4).await {
                    assert_eq!(r.unwrap(), Some(1));
                    got.push(b[0]);
                    break;
                }
            }
        }
        assert_eq!(got, (0..30u8).collect::<Vec<_>>());
        assert_eq!(waiter.await, (0..30u8).collect::<Vec<_>>());
    })
    .await;
}

/// Two tasks each read their own stream; the endpoint has no `run` and no other future.
#[nuclei::test]
async fn two_tasks_reading_two_streams_both_make_progress() {
    within(120, async {
        let server = node().await;
        let client = bind_idle(vinc_common::builder().alpn(ECHO)).await;
        let conn = client.connect(server.addr(), ECHO).await.unwrap();
        let jobs = (0..2u8).map(|i| {
            let conn = conn.clone();
            async move {
                let (mut tx, mut rx) = conn.open_bi().await.unwrap();
                for k in 0..200u8 {
                    tx.write_all(&[i, k]).await.unwrap();
                    let mut b = [0u8; 2];
                    rx.read_exact(&mut b).await.unwrap();
                    assert_eq!(b, [i, k]);
                }
            }
        });
        join_all(jobs).await;
    })
    .await;
}

/// A task that only writes (megabytes, through flow control) moves the endpoint by itself.
#[nuclei::test]
async fn a_task_that_only_writes_moves_the_endpoint() {
    within(120, async {
        let server = node().await;
        let client = bind_idle(vinc_common::builder().alpn(SINK)).await;
        let conn = client.connect(server.addr(), SINK).await.unwrap();
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        let len = 3u64 << 20;
        let writer = nuclei::spawn_local(async move {
            let mut buf = vec![0u8; 32 * 1024];
            let mut at = 0;
            while at < len {
                let n = buf.len().min((len - at) as usize);
                pattern(5, at, &mut buf[..n]);
                tx.write_all(&buf[..n]).await.unwrap();
                at += n as u64;
            }
            tx.finish().await.unwrap();
        });
        writer.await;
        let reply = rx.read_to_end(64).await.unwrap();
        assert_eq!(u64::from_le_bytes(reply[..8].try_into().unwrap()), len);
        assert_eq!(&reply[8..], &pattern_hash(5, len));
    })
    .await;
}

/// An idle connection is kept alive by `run`, which sends the keepalives with nothing else pending.
#[nuclei::test]
async fn an_idle_endpoint_is_kept_alive_by_run() {
    within(60, async {
        let server = node().await;
        let client = bind_idle(vinc_common::builder().alpn(ECHO)).await;
        let runner = client.clone();
        let run = nuclei::spawn_local(async move { runner.run().await });
        let conn = client.connect(server.addr(), ECHO).await.unwrap();
        let before = conn.stats().await.unwrap().packets_sent;
        nuclei::time::sleep(Duration::from_secs(12)).await;
        let after = conn.stats().await.unwrap().packets_sent;
        assert!(after > before, "no keepalive left in 12 s: {before} then {after}");
        assert!(conn.close_reason().is_none());
        client.close().await;
        assert!(run.await.is_ok());
    })
    .await;
}

/// The host's closures, counted: receives started, datagrams sent, sleeps that ran to their end.
#[derive(Default)]
struct Counts {
    recvs: AtomicUsize,
    sends: AtomicUsize,
    timers: AtomicUsize,
}

macro_rules! counted_endpoint {
    ($builder:expr, $counts:expr) => {{
        let sock = Arc::new(Handle::<UdpSocket>::bind(vinc_common::lo()).await.unwrap());
        let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
        let (cr, cs, cz) = (Arc::clone(&$counts), Arc::clone(&$counts), Arc::clone(&$counts));
        $builder
            .local_addr(sock.local_addr().unwrap())
            .build(
                async move |buf: &mut [u8]| {
                    cr.recvs.fetch_add(1, Ordering::Relaxed);
                    r.recv_from(buf).await
                },
                async move |pkt: &[u8], to: SocketAddr| {
                    cs.sends.fetch_add(1, Ordering::Relaxed);
                    s.send_to(pkt, to).await
                },
                async move |at: Instant| {
                    nuclei::time::sleep_until_precise(at).await;
                    cz.timers.fetch_add(1, Ordering::Relaxed);
                },
            )
            .unwrap()
    }};
}

/// One request and its response on an established connection: the client's future starts a bounded number of receives,
/// sends the request in one datagram, and no timer runs to its end.
#[nuclei::test]
async fn a_request_and_response_cost_a_bounded_number_of_polls_and_no_timer() {
    within(60, async {
        let server = node().await;
        let counts = Arc::new(Counts::default());
        let ep = counted_endpoint!(vinc_common::builder().alpn(ECHO), counts);
        let conn = ep.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        let mut buf = [0u8; 64];
        // Warm up: the handshake's acknowledgements and the first round trips settle.
        for _ in 0..50 {
            tx.write_all(&[7u8; 64]).await.unwrap();
            rx.read_exact(&mut buf).await.unwrap();
        }
        let c = |f: fn(&Counts) -> &AtomicUsize| f(&counts).load(Ordering::Relaxed);
        let (r0, s0, t0) = (c(|x| &x.recvs), c(|x| &x.sends), c(|x| &x.timers));
        const N: usize = 200;
        for _ in 0..N {
            tx.write_all(&[7u8; 64]).await.unwrap();
            rx.read_exact(&mut buf).await.unwrap();
        }
        let (r, s, t) = (c(|x| &x.recvs) - r0, c(|x| &x.sends) - s0, c(|x| &x.timers) - t0);
        // One receive that gets the response and one that finds nothing more (the driver reads until the host has nothing); one datagram sent per request
        // plus the acknowledgements; no timer fires.
        assert!(r <= 2 * N + N / 10, "{r} receives for {N} requests");
        assert!(s <= 2 * N, "{s} datagrams for {N} requests");
        assert!(t <= N / 20, "{t} timers ran for {N} requests");
    })
    .await;
}

/// An endpoint none of whose futures is polled makes no progress: while its host polls nothing of it, it neither
/// receives, sends nor sleeps, though the peer's echo arrives at its socket meanwhile. Once polled again it loses nothing:
/// every byte of the echo is read back in order.
#[nuclei::test]
async fn an_endpoint_no_one_polls_makes_no_progress_and_loses_nothing() {
    within(60, async {
        let server = node().await;
        let counts = Arc::new(Counts::default());
        let ep = counted_endpoint!(vinc_common::builder().alpn(ECHO), counts);
        let conn = ep.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        let mut data = vec![0u8; 64 * 1024];
        pattern(5, 0, &mut data);
        tx.write_all(&data).await.unwrap();
        tx.finish().await.unwrap();

        let c = |f: fn(&Counts) -> &AtomicUsize| f(&counts).load(Ordering::Relaxed);
        let before = (c(|x| &x.recvs), c(|x| &x.sends), c(|x| &x.timers));
        // Only the server's tasks run: the echo leaves for this endpoint's socket, and nothing of the endpoint runs.
        nuclei::time::sleep(Duration::from_millis(500)).await;
        let after = (c(|x| &x.recvs), c(|x| &x.sends), c(|x| &x.timers));
        assert_eq!(
            before, after,
            "the endpoint ran its host's calls (receives, sends, sleeps) with no future polled"
        );

        let back = rx.read_to_end(data.len()).await.unwrap();
        assert_eq!(back.len(), data.len());
        assert!(back == data, "the echo came back changed");
    })
    .await;
}

/// The CPU time of a round trip on an established connection is bounded: no per-poll cost that grows with the
/// endpoint's size (such as a large frame probed on every poll).
#[nuclei::test]
async fn a_round_trip_costs_bounded_cpu() {
    fn cpu_ticks() -> u64 {
        let stat = std::fs::read_to_string("/proc/self/stat").unwrap();
        let rest = &stat[stat.rfind(')').unwrap() + 2..];
        let f: Vec<&str> = rest.split(' ').collect();
        f[11].parse::<u64>().unwrap() + f[12].parse::<u64>().unwrap()
    }
    within(120, async {
        let server = bind(vinc_common::builder().alpn(ECHO)).await;
        let s = server.clone();
        nuclei::spawn_local(async move {
            while let Some(i) = s.accept().await {
                nuclei::spawn_local(vinc_common::serve_conn(i.into_connection())).detach();
            }
        })
        .detach();
        let ep = bind_idle(vinc_common::builder().alpn(ECHO)).await;
        let conn = ep.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        let mut buf = [0u8; 64];
        for _ in 0..100 {
            tx.write_all(&[1u8; 64]).await.unwrap();
            rx.read_exact(&mut buf).await.unwrap();
        }
        const N: u64 = 5000;
        let t0 = cpu_ticks();
        for _ in 0..N {
            tx.write_all(&[1u8; 64]).await.unwrap();
            rx.read_exact(&mut buf).await.unwrap();
        }
        let ticks = cpu_ticks() - t0;
        // Both endpoints and the socket calls are in this process; a tick is 10 ms.
        let per_trip_us = ticks * 10_000 / N;
        assert!(per_trip_us < 400, "{per_trip_us} us of CPU per round trip");
    })
    .await;
}

/// Steady-state messages allocate nothing in the facade: a stream write and read, and a datagram send and receive, cost
/// no more allocations than the same exchange over the bare sockets does.
#[nuclei::test]
async fn messages_allocate_nothing_in_the_facade() {
    use vinc_tests::AllocStats;
    fn used(from: AllocStats) -> u64 {
        AllocStats::now().count() - from.count()
    }
    within(120, async {
        // The bare exchange: the allocations of the socket layer alone.
        let a = Handle::<UdpSocket>::bind(vinc_common::lo()).await.unwrap();
        let b = Handle::<UdpSocket>::bind(vinc_common::lo()).await.unwrap();
        let (aa, ba) = (a.local_addr().unwrap(), b.local_addr().unwrap());
        let mut buf = [0u8; 128];
        for _ in 0..20 {
            a.send_to(&[1u8; 64], ba).await.unwrap();
            b.recv_from(&mut buf).await.unwrap();
            b.send_to(&[1u8; 64], aa).await.unwrap();
            a.recv_from(&mut buf).await.unwrap();
        }
        const N: u64 = 200;
        let from = AllocStats::now();
        for _ in 0..N {
            a.send_to(&[1u8; 64], ba).await.unwrap();
            b.recv_from(&mut buf).await.unwrap();
            b.send_to(&[1u8; 64], aa).await.unwrap();
            a.recv_from(&mut buf).await.unwrap();
        }
        let bare = used(from);

        let server = node().await;
        let ep = bind_idle(vinc_common::builder().alpn(ECHO)).await;
        let conn = ep.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        let mut sbuf = [0u8; 64];
        for _ in 0..100 {
            tx.write_all(&[1u8; 64]).await.unwrap();
            rx.read_exact(&mut sbuf).await.unwrap();
        }
        let from = AllocStats::now();
        for _ in 0..N {
            tx.write_all(&[1u8; 64]).await.unwrap();
            rx.read_exact(&mut sbuf).await.unwrap();
        }
        let stream = used(from);
        // The echo server's side runs on this thread too and is counted: it is the same facade code, so the budget is
        // the bare exchange's allocations (one request and one response per round) plus nothing per message.
        assert!(
            stream <= bare,
            "stream: {stream} allocations for {N} round trips against {bare} bare"
        );

        // Datagrams: both ends are in the test, each sends one datagram per round and reads the other's.
        let dserver = bind(vinc_common::builder().alpn(ECHO)).await;
        let dclient = bind(vinc_common::builder().alpn(ECHO)).await;
        let c = dclient.connect(dserver.addr(), ECHO).await.unwrap();
        // The session reaches the server's accept queue once the client sent something on it.
        let (mut hi, _hi_rx) = c.open_bi().await.unwrap();
        hi.write_all(b"hi").await.unwrap();
        let s = dserver.accept().await.unwrap().into_connection();
        let mut dbuf = [0u8; 128];
        let round = async |c: &vinc::Connection<_>, s: &vinc::Connection<_>, dbuf: &mut [u8]| {
            c.send_datagram(&[1u8; 64]).await.unwrap();
            assert_eq!(s.recv_datagram(dbuf).await.unwrap(), 64);
            s.send_datagram(&[2u8; 64]).await.unwrap();
            assert_eq!(c.recv_datagram(dbuf).await.unwrap(), 64);
        };
        // A session's buffers are allocated a segment at a time until they hold what the session works with; this
        // exchange comes to need a second segment after about a hundred rounds, and nothing after that.
        for _ in 0..400 {
            round(&c, &s, &mut dbuf).await;
        }
        let from = AllocStats::now();
        for _ in 0..N {
            round(&c, &s, &mut dbuf).await;
        }
        let datagram = used(from);
        assert!(
            datagram <= bare,
            "datagram: {datagram} allocations for {N} round trips against {bare} bare"
        );
    })
    .await;
}

/// Two endpoints are built, connected, used and dropped on one thread with a small stack: no poll function and no drop
/// holds an endpoint's tables on its stack.
fn on_a_stack(kib: usize) {
    std::thread::Builder::new()
        .stack_size(kib << 10)
        .spawn(|| {
            nuclei::block_on(async move {
                let server = lo_endpoint!(vinc_common::builder().alpn(ECHO));
                let ep = lo_endpoint!(vinc_common::builder().alpn(ECHO));
                let to = server.addr();
                let s = server.clone();
                nuclei::spawn_local(async move {
                    while let Some(i) = s.accept().await {
                        nuclei::spawn_local(vinc_common::serve_conn(i.into_connection())).detach();
                    }
                })
                .detach();
                let conn = ep.connect(to, ECHO).await.unwrap();
                let (mut tx, mut rx) = conn.open_bi().await.unwrap();
                tx.write_all(b"small stack").await.unwrap();
                tx.finish().await.unwrap();
                assert_eq!(rx.read_to_end(100).await.unwrap(), b"small stack");
                conn.close(0).await;
                drop((tx, rx, conn));
                drop(ep);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Endpoints of the default 1024 sessions are built, connected, used and dropped on a 1 MiB stack. The endpoint is far
/// larger than that, so any frame that held it would overflow this stack at once.
#[test]
fn a_default_endpoint_builds_drives_and_drops_on_a_one_mebibyte_stack() {
    on_a_stack(1024);
}

#[allow(dead_code)]
fn unused() {
    let _ = client;
}
