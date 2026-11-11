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

mod vinc_common;

use std::cell::RefCell;
use std::collections::VecDeque;
use std::net::{SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::rc::Rc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use nuclei::Handle;
use vinc::relay::{Carriers, Clock, Event, Limits, MemStore, Relay, Stats, Store, Udp};
use vinc::{CarrierKind, Error, ErrorKind, Identity};
use vinc_common::{client, eventually, within};
use vinc_connect::carrier::session::{ALPN, Poll};
use vinc_connect::carrier::ws::{self, Decoder, Opcode, Role, WsFrame};
use vinc_connect::carrier::{DnsAnswer, Frame, MAX_FRAME_LEN, ProtectedCarrier};
use vinc_connect::record::{self, Reach, RecordFields};
use vinc_connect::relay::{Quota, sleep};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use vinc_security::{
    ConnId, CreditRecord, Env, InitiatorParams, KeyHandle, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys,
};

const HUB: &[u8] = b"t/hub";

/// Run `make`'s future on the nuclei runtime in a thread with a large stack: the handshake types of the dialing side
/// are generic over the provider and so are built unoptimised here, with frames far larger than a test thread's.
fn on_big_stack<F: Future<Output = ()> + 'static>(make: impl FnOnce() -> F + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || nuclei::block_on(make()))
        .unwrap()
        .join()
        .unwrap();
}

fn io_err(_: std::io::Error) -> Error {
    Error::new(ErrorKind::Unreachable, "the socket failed")
}

fn wall_ns() -> u64 {
    u64::try_from(SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()).unwrap()
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
    let listener = Rc::new(Handle::<TcpListener>::bind(vinc_common::lo()).await.unwrap());
    let addr = listener.get_ref().local_addr().unwrap();
    let sock = Rc::new(Handle::<UdpSocket>::bind(addr).await.unwrap());
    let kinds = Rc::new(RefCell::new(VecDeque::new()));
    let t0 = Instant::now();
    let base = wall_ns();
    let (k, l) = (Rc::clone(&kinds), Rc::clone(&listener));
    let (s1, s2) = (Rc::clone(&sock), Rc::clone(&sock));
    let relay = Relay::builder()
        .identity(Identity::from_seed(&[seed; 32]).unwrap())
        .limits(limits)
        .store(store)
        .hub(addr, &[HUB])
        .build(
            Udp::new(
                async move |buf: &mut [u8]| s1.recv_from(buf).await.map_err(io_err),
                async move |pkt: &[u8], to| s2.send_to(pkt, to).await.map_err(io_err),
            ),
            Carriers::new(
                async move || {
                    let (s, _) = l.accept().await.map_err(io_err)?;
                    let kind = k.borrow_mut().pop_front().unwrap_or(CarrierKind::Tcp);
                    Ok((s, kind))
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

/// The dialing carrier and its key material; a function of its own so the large values live in its frame only.
#[inline(never)]
fn dial_carrier(
    kp: &Keypair,
    tag: u8,
    relay: NodeId,
) -> (Box<ProtectedCarrier<Software>>, Drbg, Box<SoftPrekeys<Software>>) {
    let identity = LocalIdentity::from_keypair(kp, KeyHandle(1)).unwrap();
    let mut drbg = Drbg::new(&[tag ^ 0x55; 32]);
    let prov = Software;
    let mut env = Env {
        provider: &prov,
        now: wall_ns(),
        drbg: &mut drbg,
    };
    let mut prekeys = Box::new(SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap());
    let prekey = prekeys.acquire(&mut env).unwrap();
    let carrier = Box::new(
        ProtectedCarrier::dial(
            &mut env,
            InitiatorParams {
                peer: relay,
                alpn: ALPN,
                scid: ConnId::new(&[tag; 8]).unwrap(),
                identity: &identity,
                prekey: &prekey,
                peer_has_prekey: false,
                ticket: None,
                credit: CreditRecord::NONE,
            },
        )
        .unwrap(),
    );
    (carrier, drbg, prekeys)
}

/// A member: the carrier handshake and frames over a real TCP stream, with optional WebSocket framing.
struct Member {
    kp: Keypair,
    id: NodeId,
    relay: NodeId,
    stream: Handle<TcpStream>,
    carrier: Box<ProtectedCarrier<Software>>,
    drbg: Drbg,
    stores: Box<vinc_security::ResponderStores<4, 4>>,
    ws: Option<Decoder>,
    ws_in: Vec<u8>,
    eof: bool,
}

impl Member {
    async fn connect(r: &TestRelay, tag: u8, kind: CarrierKind) -> Self {
        r.kinds.borrow_mut().push_back(kind);
        let stream = Handle::<TcpStream>::connect(r.addr).await.unwrap();
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[tag; 32]).unwrap();
        let (carrier, drbg, prekeys) = dial_carrier(&kp, tag, r.id);
        let mut m = Self {
            id: kp.node_id(),
            kp,
            relay: r.id,
            stream,
            carrier,
            drbg,
            stores: Box::default(),
            ws: (kind == CarrierKind::Ws).then(|| Decoder::new(Role::Server)),
            ws_in: Vec::new(),
            eof: false,
        };
        m.handshake(&prekeys).await;
        m
    }

    async fn write_all(&self, bytes: &[u8]) {
        let wrapped;
        let bytes = if self.ws.is_some() {
            let mut f = vec![0u8; bytes.len() + ws::MAX_HEADER];
            let n = ws::encode(Opcode::Binary, bytes, Some([1, 2, 3, 4]), &mut f).unwrap();
            f.truncate(n);
            wrapped = f;
            &wrapped[..]
        } else {
            bytes
        };
        let mut sent = 0;
        while sent < bytes.len() {
            sent += self.stream.send(&bytes[sent..]).await.unwrap();
        }
    }

    async fn flush(&mut self) {
        let mut buf = vec![0u8; 32 * 1024];
        while self.carrier.pending_transmit() > 0 {
            let n = self.carrier.transmit(&mut buf);
            self.write_all(&buf[..n]).await;
        }
    }

    /// Read from the stream into the carrier; false at end of stream.
    async fn fill(&mut self) -> bool {
        let mut buf = vec![0u8; 16 * 1024];
        let n = match self.stream.recv(&mut buf).await {
            Ok(n) if n > 0 => n,
            _ => {
                self.eof = true;
                return false;
            }
        };
        let mut payloads: Vec<Vec<u8>> = Vec::new();
        if let Some(dec) = self.ws.as_mut() {
            self.ws_in.extend_from_slice(&buf[..n]);
            let mut pos = 0;
            while let Ok(Some((frame, used))) = dec.decode(&mut self.ws_in[pos..]) {
                if let WsFrame::Data(p) = frame {
                    payloads.push(p.to_vec());
                }
                pos += used;
            }
            self.ws_in.drain(..pos);
        } else {
            payloads.push(buf[..n].to_vec());
        }
        for p in payloads {
            let mut rest = &p[..];
            while !rest.is_empty() {
                let used = self.carrier.receive(rest);
                rest = &rest[used..];
                if used == 0 {
                    break;
                }
                // make room: the caller polls between fills, and a unit is far below the buffer
            }
        }
        true
    }

    async fn handshake(&mut self, prekeys: &SoftPrekeys<Software>) {
        loop {
            self.flush().await;
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &self.kp)),
                prekeys: Some(prekeys),
            };
            let prov = Software;
            let mut env = Env {
                provider: &prov,
                now: wall_ns(),
                drbg: &mut self.drbg,
            };
            if self.carrier.key_request().is_some() {
                if let Poll::Open(_) = self.carrier.answer_soft(&mut env, &soft).unwrap() {
                    self.flush().await;
                    return;
                }
                continue;
            }
            let pr = self.carrier.poll(&mut env, &mut self.stores).unwrap();
            match pr {
                Poll::Open(peer) => {
                    assert_eq!(peer, self.relay, "the relay proved its identity");
                    return;
                }
                Poll::KeyRequest => {
                    if let Poll::Open(_) = self.carrier.answer_soft(&mut env, &soft).unwrap() {
                        self.flush().await;
                        return;
                    }
                }
                Poll::Handshake | Poll::Frame(_) => {}
                Poll::Idle => {
                    self.flush().await;
                    assert!(self.fill().await, "the relay closed during the handshake");
                }
            }
        }
    }

    async fn send(&mut self, f: &Frame<'_>) {
        let mut out = vec![0u8; MAX_FRAME_LEN + 64];
        let n = self.carrier.seal(&Software, f, &mut out).unwrap();
        self.write_all(&out[..n]).await;
    }

    /// The next frame, encoded; `None` once the relay closed the stream.
    async fn recv(&mut self) -> Option<Vec<u8>> {
        loop {
            let prov = Software;
            let mut env = Env {
                provider: &prov,
                now: wall_ns(),
                drbg: &mut self.drbg,
            };
            match self.carrier.poll(&mut env, &mut self.stores) {
                Ok(Poll::Frame(f)) => {
                    let mut b = vec![0u8; MAX_FRAME_LEN];
                    let n = f.encode(&mut b).unwrap();
                    b.truncate(n);
                    return Some(b);
                }
                Ok(Poll::Idle) | Err(_) if !self.eof => {
                    if !self.fill().await {
                        continue;
                    }
                }
                _ => return None,
            }
        }
    }

    fn record(&self, seq: u64) -> Vec<u8> {
        let mut out = vec![0u8; record::MAX_RECORD_LEN];
        let n = record::sign(
            &self.kp,
            &RecordFields {
                home: self.relay,
                seq,
                reach: Reach::UdpBlocked,
                addrs: &[],
                hints: &[],
            },
            &mut out,
        )
        .unwrap();
        out.truncate(n);
        out
    }

    async fn publish(&mut self, seq: u64) -> Vec<u8> {
        let rec = self.record(seq);
        self.send(&Frame::Publish { record: &rec }).await;
        rec
    }
}

fn decode(bytes: &[u8]) -> Frame<'_> {
    Frame::decode(bytes).unwrap()
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
