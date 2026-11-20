//! The host's clock, error type and randomness come through one platform type: a host with an instant of its own and
//! the facade's own error runs an echo; every deadline is the platform's, in virtual time; a busy receive is transient
//! and an unreachable one stops the endpoint; a record's sequence is the platform's wall clock; a relay role needs a
//! wall clock; and the relay binary's chain, with std closures, builds unchanged. On nuclei.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    missing_docs
)]

mod pinc_common;

use std::cell::{Cell, RefCell};
use std::future::{pending, poll_fn};
use std::net::{SocketAddr, UdpSocket};
use std::rc::Rc;
use std::sync::Arc;
use std::task::Poll;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use nuclei::Handle;
use pinc::relay::{Carriers as RelayCarriers, Completion, Peer, Relay as RelayHost, Tag};
use pinc::{
    CarrierKind, Discovery, Endpoint, Error, ErrorKind, Hosted, LOOKUP_WAIT, Limits, NodeAddr, NodeId, Pinc, Platform,
    Records, Rendezvous,
};
use pinc_common::{ECHO, lo, poll_drop, serve_conn, within};
use pinc_connect::record::Record;
use pinc_crypto::IdentityAlg;

/// The wall clock the fake platform reports, in milliseconds: a time the system's clock is not at.
const WALL_MS: u64 = 1_700_000_000_000;

/// How long a prekey serves new dials, in nanoseconds: 10 minutes.
const PREKEY_LIFE: u64 = 600_000_000_000;

/// A platform whose instant is nanoseconds in a `u64` and whose error is the facade's own.
#[derive(Clone)]
struct Fake {
    now: Rc<Cell<u64>>,
    wall_ns: u64,
}

impl Fake {
    fn new(wall_ns: u64) -> Self {
        Self {
            now: Rc::default(),
            wall_ns,
        }
    }
}

impl Platform for Fake {
    type Instant = u64;
    type Error = Error;

    fn now(&self) -> u64 {
        self.now.get()
    }

    fn wall_ns(&self) -> u64 {
        self.wall_ns
    }

    fn random(&self, out: &mut [u8]) -> Result<(), Error> {
        pinc_keystore::os_random(out).map_err(|_| Error::new(ErrorKind::Config, "no randomness"))
    }
}

/// A platform on the system's monotonic clock, from an origin, with the facade's own error.
#[derive(Clone, Copy)]
struct Clock {
    origin: Instant,
}

impl Platform for Clock {
    type Instant = u64;
    type Error = Error;

    fn now(&self) -> u64 {
        u64::try_from(self.origin.elapsed().as_nanos()).unwrap_or(u64::MAX)
    }

    fn wall_ns(&self) -> u64 {
        u64::try_from(SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()).unwrap()
    }

    fn random(&self, out: &mut [u8]) -> Result<(), Error> {
        pinc_keystore::os_random(out).map_err(|_| Error::new(ErrorKind::Config, "no randomness"))
    }
}

fn failed(_: std::io::Error) -> Error {
    Error::new(ErrorKind::Unreachable, "the socket failed")
}

/// An endpoint of `clock` serving the echo protocol, over a loopback UDP socket of nuclei; `first` is what its first
/// receive returns instead of waiting for a datagram, if it is `Some`. Tasks drive it and serve its sessions.
async fn on_clock(clock: Clock, first: Option<Error>) -> Endpoint<impl Hosted> {
    on_clock_with(clock, first, Limits::default()).await
}

/// As [`on_clock`], with `limits`.
async fn on_clock_with(clock: Clock, first: Option<Error>, limits: Limits) -> Endpoint<impl Hosted> {
    let sock = Arc::new(Handle::<UdpSocket>::bind(lo()).await.unwrap());
    let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
    let first = Cell::new(first);
    let origin = clock.origin;
    let ep = Pinc::builder_on(clock)
        .limits(limits)
        .alpn(ECHO)
        .local_addr(sock.local_addr().unwrap())
        .build(
            async move |buf: &mut [u8]| -> pinc::Result<(usize, SocketAddr)> {
                if let Some(e) = first.take() {
                    return Err(e);
                }
                r.recv_from(buf).await.map_err(failed)
            },
            async move |pkt: &[u8], to: SocketAddr| -> pinc::Result<usize> { s.send_to(pkt, to).await.map_err(failed) },
            async move |at: u64| nuclei::time::sleep_until_precise(origin + Duration::from_nanos(at)).await,
        )
        .unwrap();
    let e = ep.clone();
    nuclei::spawn_local(async move {
        let _ = e.run().await;
    })
    .detach();
    let e = ep.clone();
    nuclei::spawn_local(async move {
        while let Some(i) = e.accept().await {
            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();
    ep
}

async fn echo<H: Hosted>(c: &pinc::Connection<H>) -> Vec<u8> {
    let (mut tx, mut rx) = c.open_bi().await.unwrap();
    tx.write_all(b"ping").await.unwrap();
    tx.finish().await.unwrap();
    rx.read_to_end(16).await.unwrap()
}

#[nuclei::test]
async fn an_echo_runs_on_a_platform_with_its_own_instant_and_error() {
    let clock = Clock { origin: Instant::now() };
    let server = on_clock(clock, None).await;
    let client = on_clock(clock, None).await;
    within(30, async {
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        assert_eq!(echo(&c).await, b"ping");
    })
    .await;
}

#[nuclei::test]
async fn two_endpoints_on_the_limits_of_a_32_bit_host_connect_and_echo() {
    let clock = Clock { origin: Instant::now() };
    let server = on_clock_with(clock, None, Limits::wasm()).await;
    let client = on_clock_with(clock, None, Limits::wasm()).await;
    within(30, async {
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        assert_eq!(echo(&c).await, b"ping");
    })
    .await;
}

/// Wait one turn of the executor: the first poll wakes itself and is pending.
async fn yield_once() {
    let mut first = true;
    poll_fn(|cx| {
        if std::mem::take(&mut first) {
            cx.waker().wake_by_ref();
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    })
    .await
}

/// A discovery whose lookup never answers.
struct Silent;

impl Discovery for Silent {
    fn lookup(&self, _node: &NodeId) -> impl Future<Output = Vec<SocketAddr>> {
        pending()
    }
}

fn node(byte: u8) -> NodeId {
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: [byte; 32],
    }
}

#[nuclei::test]
async fn every_deadline_goes_through_the_platform() {
    let pf = Fake::new(WALL_MS * 1_000_000);
    let clock = Rc::clone(&pf.now);
    let sleeper = Rc::clone(&clock);
    let ep = Pinc::builder_on(pf)
        .alpn(ECHO)
        .connect_timeout(Duration::from_secs(20))
        .discovery(Silent)
        .local_addr(([127, 0, 0, 1], 4433).into())
        .build(
            // Nothing is ever received, and a send goes nowhere.
            async |_buf: &mut [u8]| pending::<pinc::Result<(usize, SocketAddr)>>().await,
            async |pkt: &[u8], _to: SocketAddr| -> pinc::Result<usize> { Ok(pkt.len()) },
            // Time moves only when the endpoint sleeps: to the deadline, and never back.
            async move |at: u64| {
                sleeper.set(sleeper.get().max(at));
                yield_once().await;
            },
        )
        .unwrap();

    // A dial to an address nobody answers ends at its 20 s timeout, in virtual time.
    let to = NodeAddr {
        node: node(7),
        direct: vec![([127, 0, 0, 1], 9).into()],
        relays: Vec::new(),
    };
    let t = Instant::now();
    let e = within(10, ep.connect(to, ECHO)).await.unwrap_err();
    assert_eq!(e.kind(), ErrorKind::TimedOut);
    assert!(t.elapsed() < Duration::from_secs(1), "{:?}", t.elapsed());

    // A dial by node id alone waits for discovery, which the platform's clock bounds.
    let (t, before) = (Instant::now(), clock.get());
    let e = within(10, ep.connect(node(8), ECHO)).await.unwrap_err();
    let moved = Duration::from_nanos(clock.get() - before);
    assert_eq!(e.kind(), ErrorKind::TimedOut);
    assert!(moved >= LOOKUP_WAIT, "the virtual clock moved {moved:?}");
    assert!(t.elapsed() < Duration::from_secs(1), "{:?}", t.elapsed());
}

#[nuclei::test]
async fn a_busy_receive_keeps_running_and_an_unreachable_one_stops() {
    let clock = Clock { origin: Instant::now() };
    // The server's first receive is busy: the endpoint goes on, and an echo works afterwards.
    let server = on_clock(clock, Some(Error::new(ErrorKind::Busy, "busy"))).await;
    let client = on_clock(clock, None).await;
    within(30, async {
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        assert_eq!(echo(&c).await, b"ping");
    })
    .await;

    // A receive that is unreachable ends `run` with the socket's failure.
    let ep = Pinc::builder_on(clock)
        .local_addr(lo())
        .build(
            async |_buf: &mut [u8]| -> pinc::Result<(usize, SocketAddr)> {
                Err(Error::new(ErrorKind::Unreachable, "gone"))
            },
            async |pkt: &[u8], _to: SocketAddr| -> pinc::Result<usize> { Ok(pkt.len()) },
            async |_at: u64| pending::<()>().await,
        )
        .unwrap();
    let e = within(10, ep.run()).await.unwrap_err();
    assert_eq!(e.kind(), ErrorKind::Unreachable);
    assert_eq!(e.to_string(), "the socket failed");
}

/// A rendezvous that keeps nothing.
struct Nowhere;

impl Rendezvous for Nowhere {
    fn publish(&self, _record: &[u8]) -> impl Future<Output = pinc::Result<()>> {
        std::future::ready(Ok(()))
    }

    fn fetch(&self, _node: &NodeId) -> impl Future<Output = Option<Vec<u8>>> {
        std::future::ready(None)
    }
}

#[nuclei::test]
async fn a_record_sequence_is_the_platform_wall_clock_in_milliseconds() {
    let ep = Pinc::builder_on(Fake::new(WALL_MS * 1_000_000 + 999_999))
        .discovery(Records::new(Nowhere))
        .build(
            async |_buf: &mut [u8]| pending::<pinc::Result<(usize, SocketAddr)>>().await,
            async |pkt: &[u8], _to: SocketAddr| -> pinc::Result<usize> { Ok(pkt.len()) },
            async |_at: u64| pending::<()>().await,
        )
        .unwrap();
    let rec = within(30, ep.signed_record()).await.unwrap();
    assert_eq!(Record::parse_verified(&rec).unwrap().seq, WALL_MS);
}

/// Relay carriers that submit nothing and complete nothing.
struct Idle;

impl RelayCarriers for Idle {
    type Stream = ();

    fn submit_accept(&self, _tag: Tag) {}

    fn submit_open(&self, _tag: Tag, _peer: &Peer, _kind: CarrierKind) {}

    fn submit_read(&self, _stream: &Rc<()>, _tag: Tag, _buf: Vec<u8>) {}

    fn submit_write(&self, _stream: &Rc<()>, _tag: Tag, _buf: Vec<u8>, _from: usize) {}

    fn close(&self, _tag: Tag, _stream: Rc<()>) {}

    fn poll_completed(&self, _cx: &mut std::task::Context<'_>) -> Poll<Completion<()>> {
        Poll::Pending
    }

    fn drive(&self) -> impl Future<Output = ()> {
        pending()
    }
}

#[nuclei::test]
async fn a_relay_role_needs_a_wall_clock() {
    let build = |pf: Fake, relay: bool| {
        let b = Pinc::builder_on(pf).hub().local_addr(([127, 0, 0, 1], 4434).into());
        let recv = async |_buf: &mut [u8]| pending::<pinc::Result<(usize, SocketAddr)>>().await;
        let send = async |pkt: &[u8], _to: SocketAddr| -> pinc::Result<usize> { Ok(pkt.len()) };
        let sleep = async |_at: u64| pending::<()>().await;
        if relay {
            b.relay_role(RelayHost::builder(), Idle)
                .build(recv, send, sleep)
                .map(drop)
        } else {
            b.build(recv, send, sleep).map(drop)
        }
    };
    let e = build(Fake::new(0), true).unwrap_err();
    assert_eq!(e.kind(), ErrorKind::Config);
    assert_eq!(e.to_string(), "the relay role needs the platform's wall clock");
    build(Fake::new(0), false).unwrap();
    build(Fake::new(WALL_MS * 1_000_000), true).unwrap();
}

#[nuclei::test]
async fn the_relay_binary_chain_builds_unchanged() {
    let sock = Arc::new(Handle::<UdpSocket>::bind(lo()).await.unwrap());
    let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
    let ep = Pinc::builder()
        .seed(&[0x71; 32])
        .unwrap()
        .local_addr(sock.local_addr().unwrap())
        .hub()
        .relay_role(RelayHost::builder(), Idle)
        .build(
            async move |buf: &mut [u8]| r.recv_from(buf).await,
            async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
            async |at: Instant| nuclei::time::sleep_until_precise(at).await,
        )
        .unwrap();
    // `run` starts and keeps running: it is still pending after some turns of the executor.
    assert!(poll_drop(ep.run(), 10).await.is_none());
    assert!(ep.relay_stats().is_some());
}

/// A platform whose randomness is a stream from `entropy` (an error if there is none), on the system's clock or on a
/// virtual one; it records the length of every draw.
#[derive(Clone)]
struct Gen {
    origin: Option<Instant>,
    now: Rc<Cell<u64>>,
    entropy: Option<u8>,
    draws: Rc<RefCell<Vec<usize>>>,
}

impl Gen {
    fn new(entropy: Option<u8>, origin: Option<Instant>) -> Self {
        Self {
            origin,
            now: Rc::default(),
            entropy,
            draws: Rc::default(),
        }
    }
}

impl Platform for Gen {
    type Instant = u64;
    type Error = Error;

    fn now(&self) -> u64 {
        self.origin.map_or_else(
            || self.now.get(),
            |o| u64::try_from(o.elapsed().as_nanos()).unwrap_or(u64::MAX),
        )
    }

    fn wall_ns(&self) -> u64 {
        WALL_MS * 1_000_000
    }

    fn random(&self, out: &mut [u8]) -> Result<(), Error> {
        let e = self.entropy.ok_or(Error::new(ErrorKind::Config, "no randomness"))?;
        let mut draws = self.draws.borrow_mut();
        for (i, b) in out.iter_mut().enumerate() {
            *b = e.wrapping_add(i as u8).wrapping_add(draws.len() as u8);
        }
        draws.push(out.len());
        Ok(())
    }
}

#[nuclei::test]
async fn a_platform_without_randomness_gives_no_identity() {
    let e = Pinc::builder_on(Gen::new(None, None))
        .build(
            async |_buf: &mut [u8]| pending::<pinc::Result<(usize, SocketAddr)>>().await,
            async |pkt: &[u8], _to: SocketAddr| -> pinc::Result<usize> { Ok(pkt.len()) },
            async |_at: u64| pending::<()>().await,
        )
        .map(drop)
        .unwrap_err();
    assert_eq!(e.kind(), ErrorKind::Config);
}

/// An endpoint on `pf`, with the identity of `seed`, serving the echo protocol on a loopback UDP socket of nuclei.
async fn on_gen(pf: Gen, origin: Instant, seed: [u8; 32]) -> Endpoint<impl Hosted> {
    let sock = Arc::new(Handle::<UdpSocket>::bind(lo()).await.unwrap());
    let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
    let ep = Pinc::builder_on(pf)
        .seed(&seed)
        .unwrap()
        .alpn(ECHO)
        .local_addr(sock.local_addr().unwrap())
        .build(
            async move |buf: &mut [u8]| -> pinc::Result<(usize, SocketAddr)> { r.recv_from(buf).await.map_err(failed) },
            async move |pkt: &[u8], to: SocketAddr| -> pinc::Result<usize> { s.send_to(pkt, to).await.map_err(failed) },
            async move |at: u64| nuclei::time::sleep_until_precise(origin + Duration::from_nanos(at)).await,
        )
        .unwrap();
    let e = ep.clone();
    nuclei::spawn_local(async move {
        let _ = e.run().await;
    })
    .detach();
    let e = ep.clone();
    nuclei::spawn_local(async move {
        while let Some(i) = e.accept().await {
            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();
    ep
}

#[nuclei::test]
async fn two_endpoints_with_one_seed_and_different_entropy_connect() {
    let origin = Instant::now();
    let a = on_gen(Gen::new(Some(1), Some(origin)), origin, [0x42; 32]).await;
    let b = on_gen(Gen::new(Some(2), Some(origin)), origin, [0x42; 32]).await;
    assert_eq!(a.addr().node, b.addr().node);
    let third = on_clock(Clock { origin }, None).await;
    within(30, async {
        for server in [&a, &b] {
            let c = third.connect(server.addr(), ECHO).await.unwrap();
            assert_eq!(echo(&c).await, b"ping");
        }
    })
    .await;
}

#[nuclei::test]
async fn a_prekey_rotation_asks_the_platform_for_fresh_entropy() {
    let pf = Gen::new(Some(5), None);
    let (clock, draws) = (Rc::clone(&pf.now), Rc::clone(&pf.draws));
    let waker: Rc<RefCell<Option<std::task::Waker>>> = Rc::default();
    let (parked, once) = (Rc::clone(&waker), Cell::new(true));
    let wake_clock = Rc::clone(&clock);
    let ep = Pinc::builder_on(pf)
        .seed(&[9; 32])
        .unwrap()
        .local_addr(([127, 0, 0, 1], 4435).into())
        .build(
            // Quiet until the clock is past the prekey's life, then one busy receive, then quiet again.
            async move |_buf: &mut [u8]| {
                poll_fn(|cx| {
                    if wake_clock.get() > PREKEY_LIFE && once.take() {
                        return Poll::Ready(Err(Error::new(ErrorKind::Busy, "busy")));
                    }
                    *parked.borrow_mut() = Some(cx.waker().clone());
                    Poll::Pending
                })
                .await
            },
            async |pkt: &[u8], _to: SocketAddr| -> pinc::Result<usize> { Ok(pkt.len()) },
            async |_at: u64| pending::<()>().await,
        )
        .unwrap();
    let before = draws.borrow().len();
    let e = ep.clone();
    nuclei::spawn_local(async move {
        let _ = e.run().await;
    })
    .detach();
    for _ in 0..8 {
        yield_once().await;
    }
    assert_eq!(draws.borrow().len(), before, "nothing is drawn while no prekey is due");
    clock.set(PREKEY_LIFE + 1);
    waker.borrow_mut().take().unwrap().wake();
    for _ in 0..8 {
        yield_once().await;
    }
    let fresh = draws.borrow()[before..].iter().filter(|n| **n == 32).count();
    assert!(fresh >= 1, "draws since build: {:?}", &draws.borrow()[before..]);
}

/// The sizes of the default builder, of the built endpoint and of its `run` future, in an unoptimised build, as they
/// were before the platform parameter existed; the builder is one word larger since its limits name the slots of the
/// spill arena.
const BUILDER: usize = 408;
const ENDPOINT: usize = 8;
const RUN: usize = 1072;

#[test]
fn the_sizes_of_the_builder_the_endpoint_and_its_run_future_are_not_larger_than_before() {
    let builder = Pinc::builder();
    let b = std::mem::size_of_val(&builder);
    let ep = builder
        .build(
            async |_buf: &mut [u8]| pending::<std::io::Result<(usize, SocketAddr)>>().await,
            async |pkt: &[u8], _to: SocketAddr| Ok(pkt.len()),
            async |_at: Instant| {},
        )
        .unwrap();
    let e = std::mem::size_of_val(&ep);
    let r = std::mem::size_of_val(&ep.run());
    println!("sizes: builder {b} (was {BUILDER}), endpoint {e} (was {ENDPOINT}), run {r} (was {RUN})");
    assert!(b <= BUILDER, "the builder is {b} bytes, was {BUILDER}");
    assert!(e <= ENDPOINT, "the endpoint is {e} bytes, was {ENDPOINT}");
    assert!(r <= RUN, "the run future is {r} bytes, was {RUN}");
}
