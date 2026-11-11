//! The relay host on real loopback sockets, on nuclei: members that speak the carrier reach each other through it.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::type_complexity,
    clippy::items_after_statements,
    clippy::large_futures,
    clippy::many_single_char_names,
    clippy::needless_continue,
    clippy::single_match,
    missing_docs
)]

mod relay_members;
mod vinc_common;

use std::cell::RefCell;
use std::collections::VecDeque;
use std::net::{SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::rc::Rc;
use std::time::{Duration, Instant};

use nuclei::Handle;
use relay_members::{Member, decode, on_big_stack, wall_ns};
use vinc::relay::{CarrierFns, Clock, Event, Limits, MemStore, Peer, Reason, Relay, Stats, Store, Udp};
use vinc::{CarrierKind, Error, ErrorKind, Identity};
use vinc_common::{client, eventually, within};
use vinc_connect::carrier::session::{ALPN, PEER_ALPN};
use vinc_connect::carrier::{DnsAnswer, Frame};
use vinc_connect::record::{self, Reach, RecordFields};
use vinc_connect::relay::datagram::Datagram;
use vinc_connect::relay::{Quota, sleep};
use vinc_crypto::{IdentityAlg, Keypair, NodeId};

const HUB: &[u8] = b"t/hub";

fn io_err(_: std::io::Error) -> Error {
    Error::new(ErrorKind::Unreachable, "the socket failed")
}

/// The sockets of a relay on loopback; a restarted relay is built on the same ones, so its address stays.
#[derive(Clone)]
struct Ports {
    listener: Rc<Handle<TcpListener>>,
    sock: Rc<Handle<UdpSocket>>,
    addr: SocketAddr,
}

async fn bind_ports() -> Ports {
    // the UDP port of the same number may be taken by another test process: try another number
    for _ in 0..50 {
        let listener = Rc::new(Handle::<TcpListener>::bind(vinc_common::lo()).await.unwrap());
        let addr = listener.get_ref().local_addr().unwrap();
        if let Ok(sock) = Handle::<UdpSocket>::bind(addr).await {
            return Ports {
                listener,
                sock: Rc::new(sock),
                addr,
            };
        }
    }
    panic!("no port is free for both TCP and UDP");
}

/// A relay on loopback, run as a local task; dropping `task` drops the run.
struct TestRelay {
    addr: SocketAddr,
    id: NodeId,
    kinds: Rc<RefCell<VecDeque<CarrierKind>>>,
    stats: Box<dyn Fn() -> Stats>,
    events: Box<dyn Fn() -> Option<Event>>,
    stop: Box<dyn Fn()>,
    task: Option<nuclei::Task<vinc::Result<()>>>,
}

async fn start(seed: u8, limits: Limits, store: MemStore) -> TestRelay {
    start_with(seed, limits, store, &[]).await
}

async fn start_with(seed: u8, limits: Limits, store: MemStore, peers: &[Peer]) -> TestRelay {
    start_on(&bind_ports().await, seed, limits, store, peers)
}

fn start_on(ports: &Ports, seed: u8, limits: Limits, store: MemStore, peers: &[Peer]) -> TestRelay {
    let addr = ports.addr;
    let kinds = Rc::new(RefCell::new(VecDeque::new()));
    let t0 = Instant::now();
    let base = wall_ns();
    let (k, l) = (Rc::clone(&kinds), Rc::clone(&ports.listener));
    let (s1, s2) = (Rc::clone(&ports.sock), Rc::clone(&ports.sock));
    let mut builder = Relay::builder()
        .identity(Identity::from_seed(&[seed; 32]).unwrap())
        .limits(limits);
    for p in peers {
        builder = builder.peer(*p);
    }
    let relay = builder
        .store(store)
        .hub(addr, &[HUB])
        .build(
            Udp::new(
                async move |buf: &mut [u8]| s1.recv_from(buf).await.map_err(io_err),
                async move |pkt: &[u8], to| s2.send_to(pkt, to).await.map_err(io_err),
            ),
            CarrierFns::new(
                async move || {
                    let (s, _) = l.accept().await.map_err(io_err)?;
                    let kind = k.borrow_mut().pop_front().unwrap_or(CarrierKind::Tcp);
                    Ok((s, kind))
                },
                async |p: &Peer, _kind: CarrierKind| {
                    let to = p
                        .tcp
                        .ok_or_else(|| Error::new(ErrorKind::Unreachable, "the peer has no address"))?;
                    Handle::<TcpStream>::connect(to).await.map_err(io_err)
                },
                async |s: &Handle<TcpStream>, mut buf: Vec<u8>| {
                    let r = s.recv(&mut buf).await.map_err(io_err);
                    (r, buf)
                },
                async |s: &Handle<TcpStream>, buf: Vec<u8>, from: usize| {
                    let r = s.send(&buf[from..]).await.map_err(io_err);
                    (r, buf)
                },
                async |_s: Handle<TcpStream>| {},
            ),
            Clock::new(
                move || base + u64::try_from(t0.elapsed().as_nanos()).unwrap(),
                async move |at: u64| {
                    nuclei::time::sleep_until_precise(t0 + Duration::from_nanos(at.saturating_sub(base))).await;
                },
            ),
        )
        .unwrap();
    let (r1, r2, r3, r4) = (relay.clone(), relay.clone(), relay.clone(), relay.clone());
    let task = nuclei::spawn_local(async move { r1.run().await });
    TestRelay {
        addr,
        id: r4.node_id(),
        kinds,
        stats: Box::new(move || r2.stats()),
        events: Box::new(move || r3.next_event()),
        stop: Box::new(move || relay.stop()),
        task: Some(task),
    }
}

impl Member {
    async fn connect(r: &TestRelay, tag: u8, kind: CarrierKind) -> Self {
        Self::connect_as(r, tag, kind, ALPN).await
    }

    /// Connect with the carrier protocol name of a member (`ALPN`) or of a peer relay (`PEER_ALPN`).
    async fn connect_as(r: &TestRelay, tag: u8, kind: CarrierKind, alpn: &'static [u8]) -> Self {
        r.kinds.borrow_mut().push_back(kind);
        Self::connect_to(r.addr, r.id, [tag; 32], kind, alpn).await
    }
}

async fn stats_where(r: &TestRelay, what: &str, f: impl Fn(&Stats) -> bool) {
    eventually(10, what, || async { f(&(r.stats)()) }).await;
}

#[test]
fn members_of_every_kind_reach_each_other_through_the_relay() {
    on_big_stack(|| {
        within(60, async {
            let r = start(0x71, Limits::default(), MemStore::new()).await;
            let mut a = Member::connect(&r, 0x11, CarrierKind::Tcp).await;
            let mut b = Member::connect(&r, 0x12, CarrierKind::Ws).await;
            let mut c = Member::connect(&r, 0x13, CarrierKind::WsMessages).await;
            a.publish(1).await;
            let rec_b = b.publish(1).await;
            stats_where(&r, "two records stored", |s| s.records == 2).await;

            // lookup
            c.send(&Frame::DnsQuery { peer: b.id }).await;
            let reply = c.recv().await.unwrap();
            match decode(&reply) {
                Frame::DnsReply { peer, answer } => {
                    assert_eq!(peer, b.id);
                    assert_eq!(answer, DnsAnswer::Record(&rec_b));
                }
                other => panic!("{other:?}"),
            }

            // the first flight and then data, both ways
            a.send(&Frame::Send {
                dst: b.id,
                flag: 1,
                packet: b"first flight",
            })
            .await;
            match decode(&b.recv().await.unwrap()) {
                Frame::Recv { src, flag, packet } | Frame::RecvNew { src, flag, packet, .. } => {
                    assert_eq!((src, flag, packet), (a.id, 1, &b"first flight"[..]));
                }
                other => panic!("{other:?}"),
            }
            b.send(&Frame::Send {
                dst: a.id,
                flag: 0,
                packet: b"data back",
            })
            .await;
            match decode(&a.recv().await.unwrap()) {
                Frame::Recv { src, packet, .. } | Frame::RecvNew { src, packet, .. } => {
                    assert_eq!((src, packet), (b.id, &b"data back"[..]));
                }
                other => panic!("{other:?}"),
            }
            let s = (r.stats)();
            assert_eq!(s.carriers, 3);
            assert_eq!(s.carriers_opened, 3);
            assert_eq!(s.machine.lookups, 1);
            assert!(s.machine.carrier >= 2);
            assert!(matches!((r.events)(), Some(Event::CarrierUp { .. })));
        })
    });
}

#[test]
fn a_restart_keeps_the_records() {
    on_big_stack(|| {
        within(60, async {
            let store = MemStore::new();
            let mut r = start(0x72, Limits::default(), store.clone()).await;
            let mut a = Member::connect(&r, 0x21, CarrierKind::Tcp).await;
            let rec_a = a.publish(7).await;
            eventually(10, "the record reaches the store", || async { store.len() == 1 }).await;
            drop(r.task.take());
            assert!(a.recv().await.is_none(), "dropping the run closed the carrier");

            let r2 = start(0x72, Limits::default(), store.clone()).await;
            assert_eq!(r2.id, r.id);
            let mut b = Member::connect(&r2, 0x22, CarrierKind::Tcp).await;
            stats_where(&r2, "the record is restored", |s| s.records == 1).await;
            b.send(&Frame::DnsQuery { peer: a.id }).await;
            match decode(&b.recv().await.unwrap()) {
                Frame::DnsReply { answer, .. } => assert_eq!(answer, DnsAnswer::Record(&rec_a)),
                other => panic!("{other:?}"),
            }
        })
    });
}

#[test]
fn a_full_table_refuses_only_the_extra_member() {
    on_big_stack(|| {
        within(60, async {
            let limits = Limits {
                carriers: 2,
                ..Limits::default()
            };
            let r = start(0x73, limits, MemStore::new()).await;
            let mut a = Member::connect(&r, 0x31, CarrierKind::Tcp).await;
            let mut b = Member::connect(&r, 0x32, CarrierKind::Tcp).await;
            a.publish(1).await;
            b.publish(1).await;
            stats_where(&r, "records", |s| s.records == 2).await;
            let mut c = Member::connect(&r, 0x33, CarrierKind::Tcp).await;
            assert!(c.recv().await.is_none(), "the third member is closed");
            let s = (r.stats)();
            assert_eq!((s.carriers, s.refused_carriers_full), (2, 1));
            a.send(&Frame::Send {
                dst: b.id,
                flag: 0,
                packet: b"still works",
            })
            .await;
            match decode(&b.recv().await.unwrap()) {
                Frame::Recv { packet, .. } | Frame::RecvNew { packet, .. } => assert_eq!(packet, b"still works"),
                other => panic!("{other:?}"),
            }
            // a node that reconnects replaces its own carrier and is not counted twice
            let mut a2 = Member::connect(&r, 0x31, CarrierKind::Tcp).await;
            assert!(a.recv().await.is_none(), "the older carrier of the node is closed");
            a2.send(&Frame::Ping).await;
            assert_eq!(decode(&a2.recv().await.unwrap()), Frame::Pong);
            assert_eq!((r.stats)().refused_carriers_full, 1);
        })
    });
}

#[test]
fn packets_for_a_sleeping_member_are_held_within_the_bound_and_delivered_on_wake() {
    on_big_stack(|| {
        within(60, async {
            let r = start(0x74, Limits::default(), MemStore::new()).await;
            let mut a = Member::connect(&r, 0x41, CarrierKind::Tcp).await;
            let mut b = Member::connect(&r, 0x42, CarrierKind::Tcp).await;
            a.publish(1).await;
            b.publish(1).await;
            stats_where(&r, "records", |s| s.records == 2).await;
            let mut notice = [0u8; 512];
            let n = sleep::sign(&b.kp, &r.id, wall_ns() / 1_000_000, &mut notice).unwrap();
            b.send(&Frame::Sleep { notice: &notice[..n] }).await;
            b.flush().await;
            // the notice is processed before the close because the relay reads in order
            let bid = b.id;
            drop(b);
            stats_where(&r, "member b gone", |s| s.carriers == 1).await;

            let body = [9u8; 1000];
            for i in 0..20u8 {
                let mut p = body;
                p[0] = i;
                a.send(&Frame::Send {
                    dst: bid,
                    flag: 0,
                    packet: &p,
                })
                .await;
            }
            stats_where(&r, "all stored", |s| s.mailbox.stored == 20).await;
            let s = (r.stats)();
            let held = s.mailbox.stored - s.mailbox.dropped_oldest;
            assert!(s.mailbox.dropped_oldest > 0, "the bound pushed packets out: {s:?}");
            assert!(held * 1000 <= vinc::relay::MAILBOX_BYTES as u64, "held {held} packets");
            assert_eq!(s.mailbox_members, 1);
            let mut woke = false;
            while let Some(e) = (r.events)() {
                woke |= matches!(e, Event::Wake { node } if node == bid);
            }
            assert!(woke, "a wake-up was requested");

            let kp_seed = 0x42;
            let mut b2 = Member::connect(&r, kp_seed, CarrierKind::Tcp).await;
            let mut got = 0;
            let mut first = None;
            while got < held {
                match decode(&b2.recv().await.unwrap()) {
                    Frame::Recv { packet, .. } | Frame::RecvNew { packet, .. } | Frame::RecvAlias { packet, .. } => {
                        first.get_or_insert(packet[0]);
                        got += 1;
                    }
                    other => panic!("{other:?}"),
                }
            }
            assert_eq!(
                first,
                Some(u8::try_from(20 - held).unwrap()),
                "the newest packets survive, oldest first"
            );
            assert_eq!((r.stats)().mailbox.delivered, held);
        })
    });
}

#[test]
fn a_stalled_reader_is_closed_and_the_others_keep_working() {
    on_big_stack(|| {
        within(120, async {
            let limits = Limits {
                write_backlog: 64 * 1024,
                quota: Quota {
                    bytes: u64::MAX / 2,
                    ..Quota::DEFAULT
                },
                ..Limits::default()
            };
            let r = start(0x75, limits, MemStore::new()).await;
            let mut a = Member::connect(&r, 0x51, CarrierKind::Tcp).await;
            let mut b = Member::connect(&r, 0x52, CarrierKind::Tcp).await;
            a.publish(1).await;
            b.publish(1).await;
            stats_where(&r, "records", |s| s.records == 2).await;
            // b never reads again; a floods it
            let p = [7u8; 1400];
            let end = Instant::now() + Duration::from_secs(100);
            let mut sent = 0u64;
            while (r.stats)().slow_closed == 0 {
                assert!(Instant::now() < end, "the stalled reader was never closed");
                for _ in 0..64 {
                    a.send(&Frame::Send {
                        dst: b.id,
                        flag: 0,
                        packet: &p,
                    })
                    .await;
                    sent += 1;
                }
                nuclei::time::sleep(Duration::from_millis(1)).await;
            }
            assert!(sent > 0);
            // a's own carrier still answers while b's was stalled and closed
            a.send(&Frame::DnsQuery { peer: b.id }).await;
            loop {
                match decode(&a.recv().await.unwrap()) {
                    Frame::DnsReply { .. } => break,
                    _ => {}
                }
            }
            assert_eq!((r.stats)().slow_closed, 1);
            let _ = b;
        })
    });
}

#[test]
fn stopping_the_relay_closes_every_carrier_and_the_run_returns() {
    on_big_stack(|| {
        within(60, async {
            let mut r = start(0x76, Limits::default(), MemStore::new()).await;
            let mut a = Member::connect(&r, 0x61, CarrierKind::Tcp).await;
            let mut b = Member::connect(&r, 0x62, CarrierKind::Ws).await;
            (r.stop)();
            let task = r.task.take().unwrap();
            assert!(task.await.is_ok());
            assert!(a.recv().await.is_none());
            assert!(b.recv().await.is_none());
        })
    });
}

#[test]
fn a_member_with_a_udp_session_to_the_hub_is_counted_and_released() {
    on_big_stack(|| {
        within(60, async {
            let r = start(0x77, Limits::default(), MemStore::new()).await;
            let ep = client().await;
            let conn = ep
                .connect(vinc::NodeAddr::new(r.id).with_direct(r.addr), HUB)
                .await
                .unwrap();
            stats_where(&r, "the hub holds the session", |s| s.hub_sessions == 1).await;
            conn.close(0).await;
            stats_where(&r, "the session is released", |s| s.hub_sessions == 0).await;
        })
    });
}

fn signed_record(tag: u8, relay: NodeId, seq: u64) -> (NodeId, Vec<u8>) {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[tag; 32]).unwrap();
    let mut out = vec![0u8; record::MAX_RECORD_LEN];
    let n = record::sign(
        &kp,
        &RecordFields {
            home: relay,
            seq,
            reach: Reach::UdpBlocked,
            addrs: &[],
            hints: &[],
        },
        &mut out,
    )
    .unwrap();
    out.truncate(n);
    (kp.node_id(), out)
}

#[test]
fn the_packets_held_for_a_sleeping_member_survive_a_restart() {
    on_big_stack(|| {
        within(60, async {
            let store = MemStore::new();
            let mut r = start(0x78, Limits::default(), store.clone()).await;
            let mut a = Member::connect(&r, 0x81, CarrierKind::Tcp).await;
            let mut b = Member::connect(&r, 0x82, CarrierKind::Tcp).await;
            a.publish(1).await;
            b.publish(1).await;
            eventually(10, "both records kept", || async { store.len() == 2 }).await;
            let mut notice = [0u8; 512];
            let n = sleep::sign(&b.kp, &r.id, wall_ns() / 1_000_000, &mut notice).unwrap();
            b.send(&Frame::Sleep { notice: &notice[..n] }).await;
            let (bid, aid) = (b.id, a.id);
            drop(b);
            stats_where(&r, "member b gone", |s| s.carriers == 1).await;
            for i in 0..3u8 {
                a.send(&Frame::Send {
                    dst: bid,
                    flag: i,
                    packet: &[i; 1000],
                })
                .await;
            }
            stats_where(&r, "three packets held", |s| s.mailbox.stored == 3).await;
            let entry = 33 + 1 + 8 + 2 + 1000;
            eventually(10, "the held packets are kept", || async {
                store.mailbox_bytes() == 3 * entry
            })
            .await;

            // the relay restarts between the packets and the member's wake
            drop(r.task.take());
            assert!(a.recv().await.is_none());
            let r2 = start(0x78, Limits::default(), store.clone()).await;
            let mut b2 = Member::connect(&r2, 0x82, CarrierKind::Tcp).await;
            for i in 0..3u8 {
                match decode(&b2.recv().await.unwrap()) {
                    Frame::Recv { src, flag, packet } | Frame::RecvNew { src, flag, packet, .. } => {
                        assert_eq!((flag, packet), (i, &[i; 1000][..]));
                        assert_eq!(src, aid);
                    }
                    Frame::RecvAlias { flag, packet, .. } => assert_eq!((flag, packet), (i, &[i; 1000][..])),
                    other => panic!("{other:?}"),
                }
            }
            // exactly those three, and nothing more is held or kept
            b2.send(&Frame::Ping).await;
            assert_eq!(decode(&b2.recv().await.unwrap()), Frame::Pong);
            assert_eq!((r2.stats)().mailbox.delivered, 3);
            eventually(10, "the store forgets the delivered packets", || async {
                store.mailboxes() == 0
            })
            .await;
        })
    });
}

#[test]
fn a_restored_record_keeps_its_remaining_lifetime_and_a_dropped_one_leaves_the_store() {
    on_big_stack(|| {
        within(60, async {
            let relay_id = Identity::from_seed(&[0x79; 32]).unwrap().node_id();
            let ttl = vinc_connect::relay::rule::RECORD_TTL_NS;
            let now = wall_ns();
            let store = MemStore::new();
            let (almost, rec_almost) = signed_record(0x91, relay_id, 1);
            let (expired, rec_expired) = signed_record(0x92, relay_id, 1);
            let (fresh, rec_fresh) = signed_record(0x93, relay_id, 1);
            let fresh_at = now - 10_000_000_000;
            store
                .put(&almost, &rec_almost, now - ttl + 2_500_000_000)
                .await
                .unwrap();
            store
                .put(&expired, &rec_expired, now - ttl - 1_000_000_000)
                .await
                .unwrap();
            store.put(&fresh, &rec_fresh, fresh_at).await.unwrap();
            let r = start(0x79, Limits::default(), store.clone()).await;
            assert_eq!(r.id, relay_id);
            eventually(10, "the expired record leaves the store", || async {
                store.received(&expired).is_none()
            })
            .await;
            // the one with 2.5 s left was restored with them, and is dropped by lifetime a few seconds later
            eventually(15, "the almost expired record is dropped and removed", || async {
                store.received(&almost).is_none()
            })
            .await;
            assert_eq!(
                store.received(&fresh),
                Some(fresh_at),
                "a live record is kept as it was received"
            );
            assert_eq!((r.stats)().records, 1);
        })
    });
}

#[test]
fn the_relay_holds_as_many_members_and_records_as_the_state_machine_allows() {
    on_big_stack(|| {
        within(120, async {
            let r = start(0x7a, Limits::default(), MemStore::new()).await;
            let mut members = Vec::new();
            for tag in 1..=150u8 {
                let mut m = Member::connect(&r, tag, CarrierKind::Tcp).await;
                m.publish(1).await;
                members.push(m);
            }
            stats_where(&r, "150 carriers and records", |s| {
                s.carriers == 150 && s.records == 150
            })
            .await;
            let last = members.last().map(|m| m.id).unwrap();
            let first = members.first_mut().unwrap();
            first.send(&Frame::DnsQuery { peer: last }).await;
            match decode(&first.recv().await.unwrap()) {
                Frame::DnsReply {
                    answer: DnsAnswer::Record(_),
                    ..
                } => {}
                other => panic!("{other:?}"),
            }
            assert_eq!((r.stats)().refused_carriers_full, 0);
        })
    });
}

#[test]
fn a_packet_crosses_between_a_member_and_a_peer_relay_both_ways() {
    on_big_stack(|| {
        within(60, async {
            // the peer relay is played by a node the relay trusts as a relay; its member is a record homed there
            let peer_kp = Keypair::from_seed(IdentityAlg::Ed25519, &[0xb1; 32]).unwrap();
            let r = start_with(
                0x7b,
                Limits::default(),
                MemStore::new(),
                &[Peer::new(peer_kp.node_id())],
            )
            .await;
            let mut peer = Member::connect_as(&r, 0xb1, CarrierKind::Tcp, PEER_ALPN).await;
            let mut a = Member::connect(&r, 0xa1, CarrierKind::Tcp).await;
            a.publish(1).await;
            let (far, far_record) = signed_record(0xb2, peer.id, 1);
            peer.send(&Frame::Sync { record: &far_record }).await;
            stats_where(&r, "both records stored", |s| s.records == 2).await;

            // a member of this relay writes to a node homed at the peer: the relay forwards one hop
            a.send(&Frame::Send {
                dst: far,
                flag: 5,
                packet: b"to the far side",
            })
            .await;
            // (the relay also replicates the record `a` published to its peer; that arrives first)
            let forwarded = loop {
                let frame = peer.recv().await.unwrap();
                if matches!(decode(&frame), Frame::Forward { .. }) {
                    break frame;
                }
            };
            match decode(&forwarded) {
                Frame::Forward { src, dst, flag, packet } => {
                    assert_eq!((src, dst, flag, packet), (a.id, far, 5, &b"to the far side"[..]));
                }
                other => panic!("{other:?}"),
            }
            // and the peer forwards a packet for this relay's member, who receives it from the far node
            peer.send(&Frame::Forward {
                src: far,
                dst: a.id,
                flag: 6,
                packet: b"from the far side",
            })
            .await;
            match decode(&a.recv().await.unwrap()) {
                Frame::Recv { src, flag, packet } | Frame::RecvNew { src, flag, packet, .. } => {
                    assert_eq!((src, flag, packet), (far, 6, &b"from the far side"[..]));
                }
                other => panic!("{other:?}"),
            }
            let s = (r.stats)();
            assert_eq!(s.machine.peer, 1);

            // a packet that came from a peer is never sent on to another relay
            peer.send(&Frame::Forward {
                src: far,
                dst: far,
                flag: 0,
                packet: b"loop",
            })
            .await;
            stats_where(&r, "the loop is refused", |s| s.refused(Reason::NoRoute) == 1).await;
            // a member may not speak the relay-to-relay frames
            a.send(&Frame::Forward {
                src: far,
                dst: a.id,
                flag: 0,
                packet: b"forged",
            })
            .await;
            stats_where(&r, "a member's forward is refused", |s| {
                s.refused(Reason::UnexpectedFrame) == 1
            })
            .await;
        })
    });
}

#[test]
fn packets_cross_the_hub_tunnel_up_and_down_between_a_udp_session_and_a_carrier() {
    on_big_stack(|| {
        within(60, async {
            let r = start(0x7c, Limits::default(), MemStore::new()).await;
            // member `a` is a facade endpoint with a validated UDP session to the relay; its socket is also used for
            // the tunnel datagrams, and the datagrams the relay tunnels down to it are set aside
            let sock = Rc::new(Handle::<UdpSocket>::bind(vinc_common::lo()).await.unwrap());
            let down: Rc<RefCell<VecDeque<Vec<u8>>>> = Rc::default();
            let (rs, ss, rd) = (Rc::clone(&sock), Rc::clone(&sock), Rc::clone(&down));
            let ep = vinc::Vinc::builder()
                .alpn(HUB)
                .local_addr(sock.local_addr().unwrap())
                .build(
                    async move |buf: &mut [u8]| loop {
                        let (n, from) = rs.recv_from(buf).await?;
                        if buf.first().is_some_and(|b| *b < 0x40) {
                            rd.borrow_mut().push_back(buf[..n].to_vec());
                        } else {
                            return Ok((n, from));
                        }
                    },
                    async move |pkt: &[u8], to: SocketAddr| ss.send_to(pkt, to).await,
                    async |at: Instant| nuclei::time::sleep_until_precise(at).await,
                )
                .unwrap();
            let runner = ep.clone();
            nuclei::spawn_local(async move {
                let _ = runner.run().await;
            })
            .detach();
            let _session = ep
                .connect(vinc::NodeAddr::new(r.id).with_direct(r.addr), HUB)
                .await
                .unwrap();
            stats_where(&r, "the hub holds the session", |s| s.hub_sessions == 1).await;
            let mut b = Member::connect(&r, 0xc1, CarrierKind::Tcp).await;
            b.publish(1).await;
            stats_where(&r, "the carrier is up and its record stored", |s| {
                s.carriers == 1 && s.records == 1
            })
            .await;

            // up: a datagram on the session reaches the carrier of the destination
            let mut buf = [0u8; 256];
            let n = Datagram::Spu {
                dst: b.id,
                flag: 3,
                packet: b"up the tunnel",
            }
            .encode(&mut buf)
            .unwrap();
            sock.send_to(&buf[..n], r.addr).await.unwrap();
            let up = vinc_common::poll_drop(b.recv(), 2500)
                .await
                .unwrap_or_else(|| panic!("nothing came up the tunnel: {:?}", (r.stats)()))
                .unwrap();
            match decode(&up) {
                Frame::Recv { src, flag, packet } | Frame::RecvNew { src, flag, packet, .. } => {
                    assert_eq!((src, flag, packet), (ep.id(), 3, &b"up the tunnel"[..]));
                }
                other => panic!("{other:?}"),
            }
            // down: a packet for the member, who has no carrier, comes down the session as a tunnel datagram
            b.send(&Frame::Send {
                dst: ep.id(),
                flag: 4,
                packet: b"down the tunnel",
            })
            .await;
            eventually(10, "the tunnelled packet reaches the session", || async {
                !down.borrow().is_empty()
            })
            .await;
            let got = down.borrow_mut().pop_front().unwrap();
            match Datagram::decode(&got).unwrap() {
                Datagram::Spl { src, flag, packet } => {
                    assert_eq!((src, flag, packet), (b.id, 4, &b"down the tunnel"[..]));
                }
                other => panic!("{other:?}"),
            }
            assert!((r.stats)().machine.tunnel >= 1);
        })
    });
}

/// A packet from `from` to `to`, received as a packet from `from`.
async fn deliver(from: &mut Member, to: &mut Member, tag: u8) {
    let (src, dst) = (from.id, to.id);
    from.send(&Frame::Send {
        dst,
        flag: tag,
        packet: &[tag; 64],
    })
    .await;
    match decode(&to.recv().await.unwrap()) {
        Frame::Recv { src: s, flag, packet }
        | Frame::RecvNew {
            src: s, flag, packet, ..
        } => {
            assert_eq!((s, flag, packet), (src, tag, &[tag; 64][..]));
        }
        Frame::RecvAlias { flag, packet, .. } => assert_eq!((flag, packet), (tag, &[tag; 64][..])),
        other => panic!("{other:?}"),
    }
}

/// A packet from `a` to `b` and one back.
async fn cross(a: &mut Member, b: &mut Member, tag: u8) {
    deliver(a, b, tag).await;
    deliver(b, a, tag).await;
}

#[test]
fn two_relay_hosts_form_a_mesh_by_themselves_and_it_comes_back_after_each_restarts() {
    on_big_stack(|| {
        within(120, async {
            let (pa, pb) = (bind_ports().await, bind_ports().await);
            let ids = [
                Identity::from_seed(&[0x51; 32]).unwrap().node_id(),
                Identity::from_seed(&[0x52; 32]).unwrap().node_id(),
            ];
            // the whole list goes to both relays; each skips itself, and the one with the lower node id dials
            let list = [Peer::new(ids[0]).with_tcp(pa.addr), Peer::new(ids[1]).with_tcp(pb.addr)];
            let (sa, sb) = (MemStore::new(), MemStore::new());
            let mut ra = start_on(&pa, 0x51, Limits::default(), sa.clone(), &list);
            let mut rb = start_on(&pb, 0x52, Limits::default(), sb.clone(), &list);
            stats_where(&ra, "the mesh is up at a", |s| s.peers_up == 1).await;
            stats_where(&rb, "the mesh is up at b", |s| s.peers_up == 1).await;

            let mut ma = Member::connect(&ra, 0x61, CarrierKind::Tcp).await;
            let mut mb = Member::connect(&rb, 0x62, CarrierKind::Tcp).await;
            ma.publish(1).await;
            mb.publish(1).await;
            stats_where(&ra, "both records at a", |s| s.records == 2).await;
            stats_where(&rb, "both records at b", |s| s.records == 2).await;
            cross(&mut ma, &mut mb, 1).await;
            assert!((ra.stats)().machine.peer >= 1 && (rb.stats)().machine.peer >= 1);

            // b restarts on its sockets and its store; the mesh comes back by itself
            drop(rb.task.take());
            assert!(mb.recv().await.is_none());
            rb = start_on(&pb, 0x52, Limits::default(), sb.clone(), &list);
            stats_where(&ra, "the mesh is back at a", |s| s.peers_up == 1).await;
            stats_where(&rb, "the mesh is back at b", |s| s.peers_up == 1).await;
            let mut mb = Member::connect(&rb, 0x62, CarrierKind::Tcp).await;
            mb.publish(1).await;
            cross(&mut ma, &mut mb, 2).await;

            // and a restarts
            drop(ra.task.take());
            assert!(ma.recv().await.is_none());
            ra = start_on(&pa, 0x51, Limits::default(), sa.clone(), &list);
            stats_where(&ra, "the mesh is back at a again", |s| s.peers_up == 1).await;
            stats_where(&rb, "the mesh is back at b again", |s| s.peers_up == 1).await;
            let mut ma = Member::connect(&ra, 0x61, CarrierKind::Tcp).await;
            ma.publish(1).await;
            cross(&mut ma, &mut mb, 3).await;
            assert_eq!((ra.stats)().peer_dial_failures + (rb.stats)().peer_dial_failures, 0);
        })
    });
}

#[test]
fn a_relay_never_peers_with_itself_and_an_unlisted_relay_is_refused() {
    on_big_stack(|| {
        within(60, async {
            let me = Identity::from_seed(&[0x53; 32]).unwrap().node_id();
            let ports = bind_ports().await;
            // listing itself, with its own address, changes nothing: nothing is dialed
            let r = start_on(
                &ports,
                0x53,
                Limits::default(),
                MemStore::new(),
                &[Peer::new(me).with_tcp(ports.addr)],
            );
            nuclei::time::sleep(Duration::from_millis(300)).await;
            let s = (r.stats)();
            assert_eq!((s.peers_up, s.carriers_opened, s.peer_dial_failures), (0, 0, 0));
            // a node that asks for the peer protocol without being listed is closed, not made a peer
            let mut stranger = Member::connect_as(&r, 0x54, CarrierKind::Tcp, PEER_ALPN).await;
            assert!(stranger.recv().await.is_none());
            assert_eq!((r.stats)().peers_up, 0);
        })
    });
}

#[test]
fn a_relay_that_joins_the_mesh_late_receives_the_records_homed_at_the_others() {
    on_big_stack(|| {
        within(60, async {
            let (pa, pb) = (bind_ports().await, bind_ports().await);
            let ids = [
                Identity::from_seed(&[0x55; 32]).unwrap().node_id(),
                Identity::from_seed(&[0x56; 32]).unwrap().node_id(),
            ];
            let list = [Peer::new(ids[0]).with_tcp(pa.addr), Peer::new(ids[1]).with_tcp(pb.addr)];
            // a is alone when its member publishes
            let ra = start_on(&pa, 0x55, Limits::default(), MemStore::new(), &list);
            let mut ma = Member::connect(&ra, 0x71, CarrierKind::Tcp).await;
            ma.publish(1).await;
            stats_where(&ra, "the record is stored", |s| s.records == 1).await;
            // b starts later and learns it when the mesh forms
            let rb = start_on(&pb, 0x56, Limits::default(), MemStore::new(), &list);
            stats_where(&rb, "the record reached the relay that joined late", |s| {
                s.records == 1 && s.peers_up == 1
            })
            .await;
            let mut mb = Member::connect(&rb, 0x72, CarrierKind::Tcp).await;
            mb.send(&Frame::DnsQuery { peer: ma.id }).await;
            match decode(&mb.recv().await.unwrap()) {
                Frame::DnsReply {
                    answer: DnsAnswer::Record(_),
                    ..
                } => {}
                other => panic!("{other:?}"),
            }
        })
    });
}
