//! How the futures of the facade drive the endpoint: the driving role is handed over when its holder is dropped, a task
//! that only writes or only reads moves the endpoint, an idle endpoint is kept alive by `Endpoint::run`, one request
//! and its response cost a bounded number of polls and no timer, no future holds a large frame, and a host whose last
//! act is a call loses nothing when it drops the endpoint after.
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
mod pinc_common;

use std::cell::Cell;
use std::net::{SocketAddr, UdpSocket};
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use nuclei::Handle;
use nuclei::sync::oneshot;
use pinc::{Discovery, Endpoint, Error, ErrorKind, Hosted, Pinc, Platform};
use pinc_common::{ECHO, SINK, bind, bind_idle, client, join_all, node, pattern, pattern_hash, poll_drop, within};

pinc_tests::install_counting_allocator!();

/// The driving future is dropped after every number of polls while a second task waits on another stream of the same
/// endpoint: the second task must still get its bytes, so the role passes on, and the first loses nothing.
#[nuclei::test]
async fn the_driving_future_dropped_at_every_poll_count_hands_the_role_on() {
    within(120, async {
        let server = node().await;
        let client = bind_idle(pinc_common::builder().alpn(ECHO)).await;
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
        let client = bind_idle(pinc_common::builder().alpn(ECHO)).await;
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
        let client = bind_idle(pinc_common::builder().alpn(SINK)).await;
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
        let client = bind_idle(pinc_common::builder().alpn(ECHO)).await;
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
        let sock = Arc::new(Handle::<UdpSocket>::bind(pinc_common::lo()).await.unwrap());
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
        let ep = counted_endpoint!(pinc_common::builder().alpn(ECHO), counts);
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
        let ep = counted_endpoint!(pinc_common::builder().alpn(ECHO), counts);
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
        let server = bind(pinc_common::builder().alpn(ECHO)).await;
        let s = server.clone();
        nuclei::spawn_local(async move {
            while let Some(i) = s.accept().await {
                nuclei::spawn_local(pinc_common::serve_conn(i.into_connection())).detach();
            }
        })
        .detach();
        let ep = bind_idle(pinc_common::builder().alpn(ECHO)).await;
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
    use pinc_tests::AllocStats;
    fn used(from: AllocStats) -> u64 {
        AllocStats::now().count() - from.count()
    }
    within(120, async {
        // The bare exchange: the allocations of the socket layer alone.
        let a = Handle::<UdpSocket>::bind(pinc_common::lo()).await.unwrap();
        let b = Handle::<UdpSocket>::bind(pinc_common::lo()).await.unwrap();
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
        let ep = bind_idle(pinc_common::builder().alpn(ECHO)).await;
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
        let dserver = bind(pinc_common::builder().alpn(ECHO)).await;
        let dclient = bind(pinc_common::builder().alpn(ECHO)).await;
        let c = dclient.connect(dserver.addr(), ECHO).await.unwrap();
        // The session reaches the server's accept queue once the client sent something on it.
        let (mut hi, _hi_rx) = c.open_bi().await.unwrap();
        hi.write_all(b"hi").await.unwrap();
        let s = dserver.accept().await.unwrap().into_connection();
        let mut dbuf = [0u8; 128];
        let round = async |c: &pinc::Connection<_>, s: &pinc::Connection<_>, dbuf: &mut [u8]| {
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
                let server = lo_endpoint!(pinc_common::builder().alpn(ECHO));
                let ep = lo_endpoint!(pinc_common::builder().alpn(ECHO));
                let to = server.addr();
                let s = server.clone();
                nuclei::spawn_local(async move {
                    while let Some(i) = s.accept().await {
                        nuclei::spawn_local(pinc_common::serve_conn(i.into_connection())).detach();
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

/// The last call of a host sends what it queued before its value returns, although no future is polled after it and
/// the endpoint is dropped at once: a datagram sent as the endpoint's last act reaches the peer. On the code that
/// returned every call before its send, what the call queued waited for a later poll that never came, and a host
/// whose last act is the call lost it when it dropped the endpoint (pinc#636).
#[nuclei::test]
async fn the_last_datagram_of_an_endpoint_leaves_with_its_call() {
    within(30, async {
        let server = bind(pinc_common::builder().alpn(ECHO)).await;
        // No task drives the client: its calls are the only futures on it, and the last one is the endpoint's last
        // act.
        let client = bind_idle(pinc_common::builder().alpn(ECHO)).await;
        let conn = client.connect(server.addr(), ECHO).await.unwrap();
        let (got_tx, got_rx) = nuclei::sync::oneshot::channel::<Vec<u8>>();
        nuclei::spawn_local({
            let server = server.clone();
            async move {
                let c = server.accept().await.unwrap().into_connection();
                let _ = got_tx.send(c.read_datagram().await.unwrap_or_default());
            }
        })
        .detach();
        conn.send_datagram(b"the last call").await.unwrap();
        drop(conn);
        drop(client);
        assert_eq!(within(5, got_rx).await, Ok(b"the last call".to_vec()));
    })
    .await;
}

/// The last call of a host is its close, and the peer sees the code although no future is polled after the close and
/// the endpoint is dropped at once. On the code that returned every call before its send, the close frame waited for
/// a later poll that never came, and the peer's session hung until its idle timeout (pinc#636). The client closes
/// once the server has accepted: a dial whose handshake round trip is 20 ms or more reports before the server's host
/// has the session, and a session that ended before its host read it is never offered on accept (pinc#436).
#[nuclei::test]
async fn the_last_close_of_an_endpoint_reaches_the_peer() {
    within(30, async {
        let server = bind(pinc_common::builder().alpn(ECHO)).await;
        let client = bind_idle(pinc_common::builder().alpn(ECHO)).await;
        let conn = client.connect(server.addr(), ECHO).await.unwrap();
        let (why_rx, accepted) = closed_on_accept(&server);
        within(20, accepted).await.unwrap();
        conn.close(0).await;
        drop(conn);
        drop(client);
        let why = within(20, why_rx).await.unwrap();
        assert!(
            matches!(why.kind(), pinc::ErrorKind::Closed { code: 0, by_peer: true }),
            "the peer did not see the close: {why:?}"
        );
    })
    .await;
}

/// Accept the next session of `server` in a task of its own: the second receiver fires once it is accepted, the first
/// with the reason it closed.
fn closed_on_accept<H: Hosted + 'static, D: Discovery + 'static>(
    server: &Endpoint<H, D>,
) -> (oneshot::Receiver<Error>, oneshot::Receiver<()>) {
    let (why_tx, why_rx) = oneshot::channel::<Error>();
    let (up_tx, up_rx) = oneshot::channel::<()>();
    let server = server.clone();
    nuclei::spawn_local(async move {
        let c = server.accept().await.unwrap().into_connection();
        let _ = up_tx.send(());
        let _ = why_tx.send(c.closed().await);
    })
    .detach();
    (why_rx, up_rx)
}

/// A platform on the system's clock that, once armed, reads normally once and then jumps 2 s ahead: a host held up
/// between the close (the first read) and its next drive.
#[derive(Clone)]
struct Stalled {
    origin: Instant,
    reads_left: Rc<Cell<u8>>,
    skew: Rc<Cell<u64>>,
}

impl Platform for Stalled {
    type Instant = u64;
    type Error = Error;

    fn now(&self) -> u64 {
        match self.reads_left.get() {
            2 => self.reads_left.set(1),
            1 => {
                self.reads_left.set(0);
                self.skew.set(2_000_000_000);
            }
            _ => {}
        }
        u64::try_from(self.origin.elapsed().as_nanos()).unwrap_or(u64::MAX) + self.skew.get()
    }

    fn wall_ns(&self) -> u64 {
        0
    }

    fn random(&self, out: &mut [u8]) -> Result<(), Error> {
        pinc_keystore::os_random(out).map_err(|_| Error::new(ErrorKind::Config, "no randomness"))
    }
}

/// The close of an endpoint whose host was held up for longer than the close's grace between the close and the next
/// drive still reaches the peer: the grace does not free a session whose CLOSE the host has not been offered.
#[nuclei::test]
async fn a_close_reaches_the_peer_though_the_host_was_held_past_the_grace() {
    within(30, async {
        let server = bind(pinc_common::builder().alpn(ECHO)).await;
        let clock = Stalled {
            origin: Instant::now(),
            reads_left: Rc::default(),
            skew: Rc::default(),
        };
        let sock = Arc::new(Handle::<UdpSocket>::bind(pinc_common::lo()).await.unwrap());
        let (r, s, origin) = (Arc::clone(&sock), Arc::clone(&sock), clock.origin);
        let failed = |_: std::io::Error| Error::new(ErrorKind::Unreachable, "the socket failed");
        let client = Pinc::builder_on(clock.clone())
            .alpn(ECHO)
            .local_addr(sock.local_addr().unwrap())
            .build(
                async move |buf: &mut [u8]| r.recv_from(buf).await.map_err(failed),
                async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await.map_err(failed),
                async move |at: u64| nuclei::time::sleep_until_precise(origin + Duration::from_nanos(at)).await,
            )
            .unwrap();
        let conn = client.connect(server.addr(), ECHO).await.unwrap();
        let (why_rx, accepted) = closed_on_accept(&server);
        within(20, accepted).await.unwrap();
        clock.reads_left.set(2);
        conn.close(0).await;
        drop(conn);
        drop(client);
        let why = within(20, why_rx).await.unwrap();
        assert!(
            matches!(why.kind(), pinc::ErrorKind::Closed { code: 0, by_peer: true }),
            "the peer did not see the close: {why:?}"
        );
    })
    .await;
}

#[allow(dead_code)]
fn unused() {
    let _ = client;
}
