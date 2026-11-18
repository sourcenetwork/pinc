//! The relay role of an endpoint: three facade endpoints and nothing else. One is the relay and the hub of the other two,
//! on one identity, one socket and one `run`; the other two know only it. They reach each other through it (an echo over
//! a stream), exchange topic messages through it as their hub, and a record one publishes is found by the other. The
//! same again with the two members behind addresses that cannot reach each other, so the bytes go through the relay.
//!
//! The network is in memory: a UDP send puts the datagram in the inbox of the address it names unless the link is cut,
//! and a carrier is a pair of byte pipes whose server end the relay accepts.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::items_after_statements,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::type_complexity,
    clippy::large_futures
)]

#[macro_use]
mod vinc_common;

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::io;
use std::net::SocketAddr;
use std::rc::Rc;
use std::time::{Duration, Instant};

use smol::channel::{Receiver, Sender, unbounded};
use vinc::relay::{CarrierFns, Peer, Relay as RelayHost};
use vinc::{CarrierKind, Endpoint, Error, ErrorKind, Event, Hosted, Relay};
use vinc_common::{ECHO, eventually, serve_conn, within};

const RELAY_ADDR: &str = "10.0.0.1:7000";
const A_ADDR: &str = "10.0.0.2:7001";
const B_ADDR: &str = "10.0.0.3:7002";
/// Where B appears from after its NAT rebinds it.
const B_MOVED: &str = "10.0.0.4:7002";

fn addr(s: &str) -> SocketAddr {
    s.parse().unwrap()
}

/// UDP between addresses in memory; a cut link loses what crosses it, in both directions.
struct Net {
    inbox: RefCell<HashMap<SocketAddr, Sender<(Vec<u8>, SocketAddr)>>>,
    cut: RefCell<HashSet<(SocketAddr, SocketAddr)>>,
    /// Addresses a NAT rebound: what the owner sends from `old` arrives from the new address.
    moved: RefCell<HashMap<SocketAddr, SocketAddr>>,
    lost: Cell<usize>,
}

impl Net {
    fn new() -> Rc<Self> {
        Rc::new(Self {
            inbox: RefCell::new(HashMap::new()),
            cut: RefCell::new(HashSet::new()),
            moved: RefCell::new(HashMap::new()),
            lost: Cell::new(0),
        })
    }

    fn attach(&self, at: SocketAddr) -> Receiver<(Vec<u8>, SocketAddr)> {
        let (tx, rx) = unbounded();
        self.inbox.borrow_mut().insert(at, tx);
        rx
    }

    fn cut(&self, a: SocketAddr, b: SocketAddr) {
        self.cut.borrow_mut().extend([(a, b), (b, a)]);
    }

    /// The owner of `old` is rebound to `new`: it still receives on its socket, and the others see it at `new`.
    fn rebind(&self, old: SocketAddr, new: SocketAddr) {
        let tx = self.inbox.borrow().get(&old).cloned();
        if let Some(tx) = tx {
            self.inbox.borrow_mut().insert(new, tx);
        }
        self.moved.borrow_mut().insert(old, new);
    }

    fn send(&self, from: SocketAddr, to: SocketAddr, pkt: &[u8]) {
        if self.cut.borrow().contains(&(from, to)) {
            self.lost.set(self.lost.get() + 1);
        } else if let Some(tx) = self.inbox.borrow().get(&to) {
            let seen = self.moved.borrow().get(&from).copied().unwrap_or(from);
            let _ = tx.try_send((pkt.to_vec(), seen));
        }
    }
}

/// One end of an in-memory carrier.
struct Pipe {
    tx: Sender<Vec<u8>>,
    rx: Receiver<Vec<u8>>,
    left: RefCell<Vec<u8>>,
}

impl Pipe {
    fn pair() -> (Self, Self) {
        let ((t1, r1), (t2, r2)) = (unbounded(), unbounded());
        let end = |tx, rx| Self {
            tx,
            rx,
            left: RefCell::new(Vec::new()),
        };
        (end(t1, r2), end(t2, r1))
    }

    /// Fill at most `buf.len()` bytes; zero when the other end closed.
    async fn read(&self, mut buf: Vec<u8>) -> (usize, Vec<u8>) {
        let empty = self.left.borrow().is_empty();
        if empty {
            match self.rx.recv().await {
                Ok(d) => *self.left.borrow_mut() = d,
                Err(_) => return (0, buf),
            }
        }
        let mut left = self.left.borrow_mut();
        let n = left.len().min(buf.len());
        buf[..n].copy_from_slice(&left[..n]);
        left.drain(..n);
        (n, buf)
    }

    async fn write(&self, bytes: &[u8]) -> bool {
        self.tx.send(bytes.to_vec()).await.is_ok()
    }
}

fn broken() -> io::Error {
    io::ErrorKind::BrokenPipe.into()
}

/// A member: it knows only `relay`, reaches it by UDP and by a carrier opened to the relay's accept queue, and serves
/// the echo protocol.
fn member(
    net: Rc<Net>,
    at: SocketAddr,
    seed: u8,
    relay: Relay,
    to_relay: Sender<(Pipe, CarrierKind)>,
) -> Endpoint<impl Hosted> {
    member_with(net, at, seed, relay, to_relay, Rc::new(Cell::new(true)))
}

/// As [`member`]; while `carrier_up` is false the member cannot open a carrier.
fn member_with(
    net: Rc<Net>,
    at: SocketAddr,
    seed: u8,
    relay: Relay,
    to_relay: Sender<(Pipe, CarrierKind)>,
    carrier_up: Rc<Cell<bool>>,
) -> Endpoint<impl Hosted> {
    let rx = net.attach(at);
    let n = net;
    vinc_common::builder()
        .seed(&[seed; 32])
        .unwrap()
        .alpn(ECHO)
        .relays([relay])
        .local_addr(at)
        .carriers(
            async move |_relay: &Relay, kind: CarrierKind| -> io::Result<Pipe> {
                if !carrier_up.get() {
                    return Err(broken());
                }
                let (mine, theirs) = Pipe::pair();
                to_relay.send((theirs, kind)).await.map_err(|_| broken())?;
                Ok(mine)
            },
            async |p: &Pipe, buf: Vec<u8>| {
                let (n, buf) = p.read(buf).await;
                (Ok(n), buf)
            },
            async |p: &Pipe, buf: Vec<u8>, from: usize| {
                let r = if p.write(&buf[from..]).await {
                    Ok(buf.len() - from)
                } else {
                    Err(broken())
                };
                (r, buf)
            },
            async |_p: Pipe| {},
        )
        .build(
            async move |buf: &mut [u8]| {
                let (d, from) = rx.recv().await.map_err(|_| broken())?;
                buf[..d.len()].copy_from_slice(&d);
                Ok((d.len(), from))
            },
            async move |pkt: &[u8], to: SocketAddr| {
                n.send(at, to, pkt);
                Ok(pkt.len())
            },
            async |at: Instant| nuclei::time::sleep_until_precise(at).await,
        )
        .unwrap()
}

/// The endpoint that is the relay and the hub: its members' carriers arrive on `accepted`.
fn relay_endpoint(net: Rc<Net>, at: SocketAddr, accepted: Receiver<(Pipe, CarrierKind)>) -> Endpoint<impl Hosted> {
    let rx = net.attach(at);
    let n = net;
    let carriers = CarrierFns::new(
        async move || -> vinc::Result<(Pipe, CarrierKind)> {
            accepted
                .recv()
                .await
                .map_err(|_| Error::new(ErrorKind::Shutdown, "the relay stopped"))
        },
        async |_peer: &Peer, _kind: CarrierKind| -> vinc::Result<Pipe> {
            Err(Error::new(ErrorKind::Unreachable, "the relay has no peers"))
        },
        async |p: &Pipe, buf: Vec<u8>| {
            let (n, buf) = p.read(buf).await;
            (Ok(n), buf)
        },
        async |p: &Pipe, buf: Vec<u8>, from: usize| {
            let r = if p.write(&buf[from..]).await {
                Ok(buf.len() - from)
            } else {
                Err(Error::new(ErrorKind::Unreachable, "the carrier is closed"))
            };
            (r, buf)
        },
        async |_p: Pipe| {},
    );
    vinc_common::builder()
        .seed(&[0x70; 32])
        .unwrap()
        .hub()
        .local_addr(at)
        .relay_role(RelayHost::builder(), carriers)
        .build(
            async move |buf: &mut [u8]| {
                let (d, from) = rx.recv().await.map_err(|_| broken())?;
                buf[..d.len()].copy_from_slice(&d);
                Ok((d.len(), from))
            },
            async move |pkt: &[u8], to: SocketAddr| {
                n.send(at, to, pkt);
                Ok(pkt.len())
            },
            async |at: Instant| nuclei::time::sleep_until_precise(at).await,
        )
        .unwrap()
}

/// What the tests run on: the network, the relay endpoint and the two members, all driven.
struct Rig<R: Hosted, A: Hosted, B: Hosted> {
    net: Rc<Net>,
    relay: Endpoint<R>,
    a: Endpoint<A>,
    b: Endpoint<B>,
    b_carrier_up: Rc<Cell<bool>>,
}

fn drive<H: Hosted + 'static>(ep: &Endpoint<H>) {
    let ep = ep.clone();
    nuclei::spawn_local(async move {
        let _ = ep.run().await;
    })
    .detach();
}

/// The relay and two members that know only it; with `apart` the two members cannot reach each other.
fn rig(apart: bool) -> Rig<impl Hosted + 'static, impl Hosted + 'static, impl Hosted + 'static> {
    let net = Net::new();
    if apart {
        net.cut(addr(A_ADDR), addr(B_ADDR));
    }
    let (to_relay, accepted) = unbounded();
    let relay = relay_endpoint(Rc::clone(&net), addr(RELAY_ADDR), accepted);
    let known = Relay::new(relay.id())
        .with_udp(addr(RELAY_ADDR))
        .with_tcp(addr(RELAY_ADDR));
    let a = member(Rc::clone(&net), addr(A_ADDR), 1, known, to_relay.clone());
    let b_carrier_up = Rc::new(Cell::new(true));
    let b = member_with(
        Rc::clone(&net),
        addr(B_ADDR),
        2,
        known,
        to_relay,
        Rc::clone(&b_carrier_up),
    );
    drive(&relay);
    drive(&a);
    drive(&b);
    let server = b.clone();
    nuclei::spawn_local(async move {
        while let Some(i) = server.accept().await {
            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();
    Rig {
        net,
        relay,
        a,
        b,
        b_carrier_up,
    }
}

/// The next message of `ep` within `ms`, skipping the other events.
async fn next_message<H: Hosted + 'static>(ep: &Endpoint<H>, ms: u64) -> Option<(Vec<u8>, NodeIdOf, Vec<u8>)> {
    let ep = ep.clone();
    nuclei::time::timeout(Duration::from_millis(ms), async move {
        loop {
            match ep.event().await {
                Some(Event::Message {
                    topic, hop, payload, ..
                }) => break Some((topic, hop, payload)),
                Some(_) => {}
                None => break None,
            }
        }
    })
    .await
    .ok()
    .flatten()
}

type NodeIdOf = vinc::NodeId;

/// An echo over a stream from A to B by B's id alone.
async fn echo<R: Hosted, A: Hosted + 'static, B: Hosted>(rig: &Rig<R, A, B>) -> vinc::Connection<A> {
    let conn = rig.a.connect(rig.b.id(), ECHO).await.unwrap();
    assert_eq!(conn.remote(), rig.b.id());
    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
    tx.write_all(b"through the relay").await.unwrap();
    let mut got = [0u8; 17];
    rx.read_exact(&mut got).await.unwrap();
    assert_eq!(&got, b"through the relay");
    conn
}

/// A topic message from A reaches B and comes back the other way, through the relay as the hub.
async fn topics<R: Hosted, A: Hosted + 'static, B: Hosted + 'static>(rig: &Rig<R, A, B>) {
    assert!(rig.b.join(b"relay/topic", &[]).await.unwrap());
    assert!(rig.a.join(b"relay/topic", &[]).await.unwrap());
    // A subscription takes a moment to reach the hub: publish until the other end hears it.
    let mut got = None;
    for _ in 0..200 {
        rig.a.publish(b"relay/topic", b"from a", None).await.unwrap();
        if let Some(m) = next_message(&rig.b, 300).await {
            got = Some(m);
            break;
        }
    }
    let (topic, hop, payload) = got.expect("no message reached the other member");
    assert_eq!(topic, b"relay/topic");
    assert_eq!(payload, b"from a");
    assert_eq!(hop, rig.relay.id(), "it came through the relay's hub");
    let mut back = None;
    for _ in 0..200 {
        rig.b.publish(b"relay/topic", b"from b", None).await.unwrap();
        if let Some(m) = next_message(&rig.a, 300).await {
            back = Some(m);
            break;
        }
    }
    assert_eq!(back.expect("no message came back").2, b"from b");
}

/// A record B publishes is found by A at the relay, hints included.
async fn records<R: Hosted, A: Hosted + 'static, B: Hosted>(rig: &Rig<R, A, B>) {
    let pointer = [0xAB; 38];
    rig.b.set_hints(&pointer).unwrap();
    let (a, bid) = (rig.a.clone(), rig.b.id());
    eventually(60, "the relay holds B's record with its hints", || {
        let a = a.clone();
        async move {
            a.lookup(&bid)
                .await
                .is_ok_and(|r| r.is_some_and(|r| r.hints == pointer && r.node == bid))
        }
    })
    .await;
}

/// The relay's own counters, read from its endpoint.
fn carried<R: Hosted>(relay: &Endpoint<R>) -> u64 {
    let s = relay.relay_stats().expect("the endpoint has the relay role");
    s.machine.carrier + s.machine.tunnel
}

async fn both_carriers_open<R: Hosted + 'static, A: Hosted, B: Hosted>(rig: &Rig<R, A, B>) {
    let relay = rig.relay.clone();
    eventually(60, "both members hold a carrier at the relay", || {
        let relay = relay.clone();
        async move { relay.relay_stats().is_some_and(|s| s.carriers >= 2) }
    })
    .await;
}

#[nuclei::test]
async fn two_members_reach_each_other_through_an_endpoint_that_is_their_relay_and_hub() {
    let rig = rig(false);
    within(120, async {
        both_carriers_open(&rig).await;
        echo(&rig).await;
        topics(&rig).await;
        records(&rig).await;
        let s = rig.relay.relay_stats().unwrap();
        assert!(s.records >= 2, "the relay stored the members' records: {s:?}");
        assert!(s.machine.lookups >= 1, "the relay answered a lookup: {s:?}");
    })
    .await;
}

#[nuclei::test]
async fn the_same_with_members_that_cannot_reach_each_other_so_the_bytes_go_through_the_relay() {
    let rig = rig(true);
    within(120, async {
        both_carriers_open(&rig).await;
        let conn = echo(&rig).await;
        let (_, remote) = conn.stats().await.unwrap().route.expect("the connection has a path");
        assert!(
            vinc_core::is_relay_addr(&remote),
            "the path is the relay's, not a direct address: {remote}"
        );
        assert!(carried(&rig.relay) > 0, "the relay carried the members' packets");
        topics(&rig).await;
        records(&rig).await;
        assert!(
            rig.net.lost.get() > 0,
            "the members tried the direct link and it lost the datagrams"
        );
        let s = rig.relay.relay_stats().unwrap();
        assert!(
            s.datagrams_in > 0 && s.datagrams_out > 0,
            "the relay used the endpoint's socket: {s:?}"
        );
    })
    .await;
}

#[nuclei::test]
async fn an_endpoint_without_the_role_has_no_relay_counters() {
    let net = Net::new();
    let (to_relay, _accepted) = unbounded();
    let relay = Relay::new(vinc::Identity::from_seed(&[9; 32]).unwrap().node_id()).with_udp(addr(RELAY_ADDR));
    let a = member(net, addr(A_ADDR), 1, relay, to_relay);
    assert!(a.relay_stats().is_none());
    assert!(a.next_relay_event().is_none());
    assert!(!a.close_relay_carrier(&relay.id));
}

#[nuclei::test]
async fn the_relay_reports_a_carrier_that_closes_and_ends_one_on_request() {
    let rig = rig(false);
    within(60, async {
        both_carriers_open(&rig).await;
        assert!(rig.relay.close_relay_carrier(&rig.a.id()), "A held a carrier here");
        assert!(
            !rig.relay
                .close_relay_carrier(&vinc::Identity::from_seed(&[8; 32]).unwrap().node_id())
        );
        let relay = rig.relay.clone();
        eventually(30, "the relay counts the carrier it ended", || {
            let relay = relay.clone();
            async move { relay.relay_stats().is_some_and(|s| s.carriers_closed >= 1) }
        })
        .await;
        let (mut up, mut down) = (false, false);
        while let Some(e) = rig.relay.next_relay_event() {
            up |= matches!(e, vinc::relay::Event::CarrierUp { .. });
            down |= matches!(
                e,
                vinc::relay::Event::CarrierDown {
                    why: vinc::relay::Closed::Revoked,
                    ..
                }
            );
        }
        assert!(
            up && down,
            "the relay's events name the carriers that came up and the one it ended"
        );
    })
    .await;
}

/// Wait up to `secs` for `f` to hold of the relay's counters; a miss prints them.
async fn settle<R: Hosted + 'static>(relay: &Endpoint<R>, secs: u64, what: &str, f: fn(&vinc::relay::Stats) -> bool) {
    let end = Instant::now() + Duration::from_secs(secs);
    let mut wait = Duration::from_millis(1);
    loop {
        let s = relay.relay_stats().expect("the endpoint has the relay role");
        if f(&s) {
            return;
        }
        assert!(Instant::now() < end, "not reached in {secs} s: {what}: {s:?}");
        nuclei::time::sleep(wait).await;
        wait = (wait * 2).min(Duration::from_millis(100));
    }
}

/// A message held for a sleeping member is handed over when the member's route validates after its return. The
/// rig has no way to read what member B receives from the relay, so this checks the relay's own counters (held and
/// handed over), not the arrival.
#[nuclei::test]
async fn mail_held_for_a_member_that_returns_on_an_unvalidated_route_is_handed_over_when_the_route_validates() {
    let rig = rig(true);
    within(120, async {
        both_carriers_open(&rig).await;
        // B holds a UDP session to the relay's hub, then suspends: the relay keeps its sleep notice
        assert!(rig.b.join(b"relay/topic", &[]).await.unwrap());
        settle(&rig.relay, 30, "the hub holds B's session", |s| s.hub_sessions >= 1).await;
        rig.b_carrier_up.set(false);
        rig.b.suspend().await;
        settle(&rig.relay, 30, "B's carrier closed", |s| s.carriers == 1).await;
        // the relay tunnels to a member it heard within the freshness bound (20 s): wait it out so the mail is held
        nuclei::time::sleep(Duration::from_secs(21)).await;
        // A dials B: its first packets are held at the relay
        let (a, b_id) = (rig.a.clone(), rig.b.id());
        nuclei::spawn_local(async move {
            let _ = a.connect(b_id, ECHO).await;
        })
        .detach();
        settle(&rig.relay, 30, "the relay holds mail for B", |s| s.mailbox_members == 1).await;
        // B returns from a rebound address (an unvalidated route) and cannot open a carrier
        rig.net.rebind(addr(B_ADDR), addr(B_MOVED));
        rig.b.resume(false).await;
        settle(&rig.relay, 60, "the held mail is handed over", |s| {
            s.mailbox.delivered >= 1 && s.mailbox_members == 0
        })
        .await;
    })
    .await;
}
