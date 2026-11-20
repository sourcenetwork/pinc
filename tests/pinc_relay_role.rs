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
    clippy::large_futures,
    clippy::unused_async_trait_impl
)]

#[macro_use]
mod pinc_common;

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::io;
use std::net::SocketAddr;
use std::rc::Rc;
use std::time::{Duration, Instant};

use pinc::relay::{CarrierFns, MemStore, Peer, Relay as RelayHost};
use pinc::{
    CarrierKind, Discovery, Endpoint, Error, ErrorKind, Event, Hosted, NoDiscovery, NodeId, PeerRecord, Records, Relay,
    Rendezvous,
};
use pinc_common::{ECHO, eventually, serve_conn, within};
use pinc_connect::relay::rule::HUB_TUNNEL_FRESH_NS;
use smol::channel::{Receiver, Sender, unbounded};

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
    member_with(net, at, seed, relay, to_relay, Rc::new(Cell::new(true)), NoDiscovery)
}

/// As [`member`]; while `carrier_up` is false the member cannot open a carrier, and it finds records by `discovery`.
fn member_with<D: Discovery + 'static>(
    net: Rc<Net>,
    at: SocketAddr,
    seed: u8,
    relay: Relay,
    to_relay: Sender<(Pipe, CarrierKind)>,
    carrier_up: Rc<Cell<bool>>,
    discovery: D,
) -> Endpoint<impl Hosted, D> {
    let rx = net.attach(at);
    let n = net;
    pinc_common::builder()
        .seed(&[seed; 32])
        .unwrap()
        .discovery(discovery)
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
fn relay_endpoint(
    net: Rc<Net>,
    at: SocketAddr,
    accepted: Receiver<(Pipe, CarrierKind)>,
    store: MemStore,
) -> Endpoint<impl Hosted> {
    let rx = net.attach(at);
    let n = net;
    let carriers = CarrierFns::new(
        async move || -> pinc::Result<(Pipe, CarrierKind)> {
            accepted
                .recv()
                .await
                .map_err(|_| Error::new(ErrorKind::Shutdown, "the relay stopped"))
        },
        async |_peer: &Peer, _kind: CarrierKind| -> pinc::Result<Pipe> {
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
    pinc_common::builder()
        .seed(&[0x70; 32])
        .unwrap()
        .hub()
        .local_addr(at)
        .relay_role(RelayHost::builder().store(store), carriers)
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

/// The relay tunnels to a member it heard within the hub's freshness bound: wait the bound out, and a second more, so
/// that the packets for a member that left are held. The platform of these endpoints is the system's, so its clock
/// cannot be moved and the wait is real time.
const FRESH_WAIT: Duration = Duration::from_nanos(HUB_TUNNEL_FRESH_NS + 1_000_000_000);

/// What the tests run on: the network, the relay endpoint and the two members, all driven.
struct Rig<R: Hosted, A: Hosted, B: Hosted> {
    net: Rc<Net>,
    relay: Endpoint<R>,
    a: Endpoint<A>,
    b: Endpoint<B>,
    b_carrier_up: Rc<Cell<bool>>,
    /// The relay endpoint's run: dropping it ends the run, and spawning [`run_task`] again starts the next one.
    relay_run: RefCell<Option<nuclei::Task<()>>>,
}

fn run_task<H: Hosted + 'static, D: Discovery + 'static>(ep: &Endpoint<H, D>) -> nuclei::Task<()> {
    let ep = ep.clone();
    nuclei::spawn_local(async move {
        let _ = ep.run().await;
    })
}

fn drive<H: Hosted + 'static, D: Discovery + 'static>(ep: &Endpoint<H, D>) {
    run_task(ep).detach();
}

/// The relay and two members that know only it; with `apart` the two members cannot reach each other.
fn rig(apart: bool) -> Rig<impl Hosted + 'static, impl Hosted + 'static, impl Hosted + 'static> {
    rig_with(apart, MemStore::new())
}

/// [`rig`] with the relay's record store given, so a test can read what it holds.
fn rig_with(apart: bool, store: MemStore) -> Rig<impl Hosted + 'static, impl Hosted + 'static, impl Hosted + 'static> {
    let net = Net::new();
    if apart {
        net.cut(addr(A_ADDR), addr(B_ADDR));
    }
    let (to_relay, accepted) = unbounded();
    let relay = relay_endpoint(Rc::clone(&net), addr(RELAY_ADDR), accepted, store);
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
        NoDiscovery,
    );
    let relay_run = RefCell::new(Some(run_task(&relay)));
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
        relay_run,
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

type NodeIdOf = pinc::NodeId;

/// An echo over a stream from A to B by B's id alone.
async fn echo<R: Hosted, A: Hosted + 'static, B: Hosted>(rig: &Rig<R, A, B>) -> pinc::Connection<A> {
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
            pinc_core::is_relay_addr(&remote),
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
    let relay = Relay::new(pinc::Identity::from_seed(&[9; 32]).unwrap().node_id()).with_udp(addr(RELAY_ADDR));
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
                .close_relay_carrier(&pinc::Identity::from_seed(&[8; 32]).unwrap().node_id())
        );
        let relay = rig.relay.clone();
        eventually(30, "the relay counts the carrier it ended", || {
            let relay = relay.clone();
            async move { relay.relay_stats().is_some_and(|s| s.carriers_closed >= 1) }
        })
        .await;
        let (mut up, mut down) = (false, false);
        while let Some(e) = rig.relay.next_relay_event() {
            up |= matches!(e, pinc::relay::Event::CarrierUp { .. });
            down |= matches!(
                e,
                pinc::relay::Event::CarrierDown {
                    why: pinc::relay::Closed::Revoked,
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
async fn settle<R: Hosted + 'static>(relay: &Endpoint<R>, secs: u64, what: &str, f: fn(&pinc::relay::Stats) -> bool) {
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
        nuclei::time::sleep(FRESH_WAIT).await;
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

/// A second run of the relay endpoint takes the role as the first left it: the packets held for a sleeping member are
/// restored once, not once for each run, so a member that returns is handed each of them exactly once.
#[nuclei::test]
async fn a_second_run_of_the_relay_endpoint_holds_a_packet_once() {
    let store = MemStore::new();
    let rig = rig_with(true, store.clone());
    within(150, async {
        both_carriers_open(&rig).await;
        assert!(rig.b.join(b"relay/topic", &[]).await.unwrap());
        settle(&rig.relay, 30, "the hub holds B's session", |s| s.hub_sessions >= 1).await;
        rig.b_carrier_up.set(false);
        rig.b.suspend().await;
        settle(&rig.relay, 30, "B's carrier closed", |s| s.carriers == 1).await;
        nuclei::time::sleep(FRESH_WAIT).await;
        let (a, b_id) = (rig.a.clone(), rig.b.id());
        nuclei::spawn_local(async move {
            let _ = a.connect(b_id, ECHO).await;
        })
        .detach();
        settle(&rig.relay, 30, "the relay holds mail for B", |s| s.mailbox_members == 1).await;
        eventually(30, "the held packets are in the store", || {
            let store = store.clone();
            async move { store.mailboxes() == 1 }
        })
        .await;
        let held = rig.relay.relay_stats().unwrap().mailbox.stored;
        // the run ends and the next one starts on the same endpoint
        drop(rig.relay_run.borrow_mut().take());
        *rig.relay_run.borrow_mut() = Some(run_task(&rig.relay));
        settle(&rig.relay, 60, "A holds a carrier again", |s| s.carriers == 1).await;
        // B returns from a rebound address (an unvalidated route) and cannot open a carrier
        rig.net.rebind(addr(B_ADDR), addr(B_MOVED));
        rig.b.resume(false).await;
        settle(&rig.relay, 60, "the held mail is handed over", |s| {
            s.mailbox.delivered >= 1 && s.mailbox_members == 0
        })
        .await;
        let s = rig.relay.relay_stats().unwrap();
        assert_eq!(s.mailbox.stored, held, "the second run held the packets again: {s:?}");
        // the member's mailbox is empty, and nothing expired or was pushed out of it: each held packet was handed
        // over, once
        assert_eq!(
            (s.mailbox.delivered, s.mailbox.expired, s.mailbox.dropped_oldest),
            (held, 0, 0),
            "the held packets were not each handed over exactly once: {s:?}"
        );
    })
    .await;
}

/// A rendezvous that holds the one record it is given and checks nothing.
#[derive(Clone, Default)]
struct Held(Rc<RefCell<Option<Vec<u8>>>>);

impl Rendezvous for Held {
    async fn publish(&self, record: &[u8]) -> pinc::Result<()> {
        *self.0.borrow_mut() = Some(record.to_vec());
        Ok(())
    }

    async fn fetch(&self, _node: &NodeId) -> Option<Vec<u8>> {
        self.0.borrow().clone()
    }
}

/// The record of `node` that `a` looks up until its hints are `hints`.
async fn lookup_hints<H: Hosted + 'static>(a: &Endpoint<H, Records<Held>>, node: NodeId, hints: u8) -> PeerRecord {
    let got = Rc::new(RefCell::new(None));
    eventually(60, "the lookup answers the record with the hints", || {
        let (a, got) = (a.clone(), Rc::clone(&got));
        async move {
            let Ok(Some(r)) = a.lookup(&node).await else {
                return false;
            };
            let hit = r.hints == [hints; 38];
            if hit {
                *got.borrow_mut() = Some(r);
            }
            hit
        }
    })
    .await;
    got.take().unwrap()
}

#[nuclei::test]
async fn a_record_a_relay_answered_is_not_replaced_by_an_older_one_from_the_store() {
    let net = Net::new();
    let (to_relay, accepted) = unbounded();
    let relay = relay_endpoint(Rc::clone(&net), addr(RELAY_ADDR), accepted, MemStore::new());
    let known = Relay::new(relay.id())
        .with_udp(addr(RELAY_ADDR))
        .with_tcp(addr(RELAY_ADDR));
    let store = Held::default();
    let a = member_with(
        Rc::clone(&net),
        addr(A_ADDR),
        1,
        known,
        to_relay.clone(),
        Rc::new(Cell::new(true)),
        Records::new(store.clone()),
    );
    let b = member(net, addr(B_ADDR), 2, known, to_relay);
    let _relay_run = run_task(&relay);
    drive(&a);
    drive(&b);
    within(120, async {
        // An earlier record of B's identity, signed before the hints change.
        let old = pinc_common::bind_idle(
            pinc_common::builder()
                .seed(&[2; 32])
                .unwrap()
                .discovery(Records::new(Held::default()))
                .alpn(ECHO),
        )
        .await;
        old.set_hints(&[1; 38]).unwrap();
        let older = old.signed_record().await.unwrap();
        nuclei::time::sleep(Duration::from_millis(50)).await;
        b.set_hints(&[2; 38]).unwrap();
        let first = lookup_hints(&a, b.id(), 2).await;
        // The store now holds the older record; the relay's answer that A kept is newer.
        *store.0.borrow_mut() = Some(older);
        let second = a.lookup(&b.id()).await.unwrap().unwrap();
        assert_eq!((second.seq, second.hints), (first.seq, first.hints));
    })
    .await;
}
