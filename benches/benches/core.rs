//! Benchmarks of the `vinc-core` endpoint: the cost of one datagram in (demultiplexing to its session, opening it and
//! settling the session) and of one datagram out, with 1, 100 and 10,000 connections in the table, and the cost of one
//! operation on the deadline heap.
//!
//! The table of a rig holds one real handshake and sessions opened over it (a sub-session needs no handshake), so even
//! 10,000 connections are quick to build; each datagram the receive benchmark feeds is a fresh packet of one
//! connection, chosen in turn, built outside the timed section. Two endpoints exchange datagrams directly with no
//! delay. The numbers are the cost of the endpoint and the crypto on this machine, not of a network.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::type_complexity,
    clippy::many_single_char_names,
    clippy::cast_precision_loss,
    clippy::large_stack_arrays
)]

use std::hint::black_box;
use std::net::SocketAddr;

use std::time::{Duration, Instant};

use criterion::{Criterion, Throughput};
use vinc_core::{Answer, Command, DeadlineHeap, Endpoint, EndpointConfig, Event, Query, Role, SessionId, Slot};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use vinc_security::{Env, KeyHandle, KeyResponse, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys};
use vinc_transport::conn::{Resources, Tables};
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::BufferPool;
use vinc_transport::stream::{self, NoSource, Streams};

const ALPN: &[u8] = b"vinc/1";
const CHUNKS: usize = 3;

type Ep<const K: usize, const D: usize> = Endpoint<'static, 'static, Software, NoSource, 2, 2, 16, 1, K, D, 4, 4, 2>;

fn memory() -> Resources<'static, NoSource, 2, 2, 16> {
    let pool = BufferPool::new_boxed(CHUNKS);
    let streams: &'static mut Streams<NoSource, 2, 2> =
        Box::leak(Box::new(Streams::new(&stream::Config::new(false), &pool)));
    Resources {
        pool,
        streams: streams.into(),
        loss: (&*Box::leak(Box::new(LossEstimate::new()))).into(),
        tables: Tables::new(),
    }
}

struct Host<const K: usize, const D: usize> {
    ep: Box<Ep<K, D>>,
    addr: SocketAddr,
    drbg: Drbg,
    kp: Keypair,
    prekeys: SoftPrekeys<Software>,
    node: vinc_crypto::NodeId,
}

impl<const K: usize, const D: usize> Host<K, D> {
    fn new(tag: u8) -> Self {
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[tag; 32]).unwrap();
        let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
        let slots: Box<[Slot<'static, Software, NoSource, 2, 2, 16, 1>; K]> = (0..K)
            .map(|_| Slot::new(memory()))
            .collect::<Vec<_>>()
            .into_boxed_slice()
            .try_into()
            .ok()
            .unwrap();
        let mut cfg = EndpointConfig::new(u64::from(tag));
        cfg.conn.max_gso = 1;
        let mut ep = Box::new(Endpoint::new(
            1_000_000_000,
            Software,
            Drbg::new(&[tag ^ 0x3c; 32]),
            id,
            cfg,
            Box::leak(slots),
        ));
        let mut drbg = Drbg::new(&[tag ^ 0xc3; 32]);
        let mut env = Env {
            provider: &Software,
            now: 1_000_000_000,
            drbg: &mut drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
        ep.set_prekey(prekeys.acquire(&mut env).unwrap());
        assert!(ep.register_alpn(ALPN));
        let addr: SocketAddr = ([10, 0, 0, tag], 4433).into();
        ep.add_iface(addr).unwrap();
        Self {
            ep,
            addr,
            drbg,
            kp,
            prekeys,
            node: id.node_id(),
        }
    }

    /// Answer the key operations a session waits for, until it waits for none.
    fn answer_keys(&mut self, session: SessionId, now: u64) {
        loop {
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &self.kp)),
                prekeys: Some(&self.prekeys),
            };
            let mut env = Env {
                provider: &Software,
                now,
                drbg: &mut self.drbg,
            };
            let mut sig = [0u8; vinc_crypto::identity::MAX_SIGNATURE_LEN];
            let answer = match self.ep.query(Query::KeyRequest(session)) {
                Answer::KeyRequest(req) => match soft.answer(&mut env, &req, &mut sig) {
                    KeyResponse::Signature(s) => KeyResponse::Signature(s),
                    KeyResponse::SharedSecret(s) => KeyResponse::SharedSecret(s),
                    KeyResponse::Failed => KeyResponse::Failed,
                },
                _ => return,
            };
            let reply = self
                .ep
                .command(
                    now,
                    Command::KeyResponse {
                        session,
                        response: answer,
                    },
                )
                .unwrap();
            for e in reply.events.iter() {
                self.react(*e, now);
            }
        }
    }

    fn react(&mut self, ev: Event, now: u64) {
        match ev {
            Event::KeyRequest { session } => self.answer_keys(session, now),
            Event::AcpCheck { check, .. } => {
                let rep = self.ep.command(now, Command::AcpAnswer { check, allow: true }).unwrap();
                for e in rep.events.iter() {
                    self.react(*e, now);
                }
            }
            _ => {}
        }
    }

    /// Host duties for the events waiting: key operations and access checks.
    fn service(&mut self, now: u64) {
        while let Some(ev) = self.ep.poll_event() {
            self.react(ev, now);
        }
    }
}

/// Move datagrams between the two hosts until neither has more to send.
fn pump<const K: usize, const D: usize>(c: &mut Host<K, D>, s: &mut Host<K, D>, now: u64) {
    let mut buf = vec![0u8; 65_536];
    for _ in 0..64 {
        let mut moved = false;
        c.ep.handle_timeout(now);
        s.ep.handle_timeout(now);
        c.service(now);
        s.service(now);
        while let Some(t) = c.ep.poll_transmit(now, &mut buf) {
            moved = true;
            for seg in buf[..t.len].chunks_mut(t.segment_size) {
                s.ep.handle_datagram(now, t.remote, t.local, seg);
            }
        }
        while let Some(t) = s.ep.poll_transmit(now, &mut buf) {
            moved = true;
            for seg in buf[..t.len].chunks_mut(t.segment_size) {
                c.ep.handle_datagram(now, t.remote, t.local, seg);
            }
        }
        if !moved {
            break;
        }
    }
}

struct Rig<const K: usize, const D: usize> {
    c: Host<K, D>,
    s: Host<K, D>,
    sessions: Vec<SessionId>,
    now: u64,
    next: usize,
}

fn rig<const K: usize, const D: usize>(n: usize) -> Rig<K, D> {
    let (mut c, mut s) = (Host::<K, D>::new(1), Host::<K, D>::new(2));
    let mut now = 2_000_000_000u64;
    let (peer, to) = (s.node, s.addr);
    let parent = {
        let rep =
            c.ep.command(
                now,
                Command::Connect {
                    node: peer,
                    alpn: ALPN,
                    addrs: &[to],
                    role: Role::Other,
                },
            )
            .unwrap();
        match rep.value {
            vinc_core::Value::Session(id) => id,
            v => panic!("{v:?}"),
        }
    };
    for _ in 0..16 {
        pump(&mut c, &mut s, now);
        now += 30_000_000;
    }
    let mut sessions = vec![parent];
    while sessions.len() < n {
        for _ in 0..8.min(n - sessions.len()) {
            let rep =
                c.ep.command(
                    now,
                    Command::Connect {
                        node: peer,
                        alpn: ALPN,
                        addrs: &[to],
                        role: Role::Other,
                    },
                )
                .unwrap();
            if let vinc_core::Value::Session(id) = rep.value {
                sessions.push(id);
            }
        }
        pump(&mut c, &mut s, now);
        now += 30_000_000;
    }
    for _ in 0..4 {
        pump(&mut c, &mut s, now);
        now += 30_000_000;
    }
    assert_eq!(c.ep.node_stats().sessions, n);
    assert_eq!(s.ep.node_stats().sessions, n, "the server did not accept every session");
    Rig {
        c,
        s,
        sessions,
        now,
        next: 0,
    }
}

impl<const K: usize, const D: usize> Rig<K, D> {
    /// Queue a datagram on the next connection (in turn) of the client.
    fn queue_one(&mut self) {
        let session = self.sessions[self.next % self.sessions.len()];
        self.next += 1;
        self.now += 1_000;
        self.c
            .ep
            .command(
                self.now,
                Command::SendDatagram {
                    session,
                    data: &[0x5a; 64],
                },
            )
            .unwrap();
    }

    /// Let both sides settle (acknowledgements, events) outside the timed section.
    fn settle(&mut self) {
        self.now += 30_000_000;
        pump(&mut self.c, &mut self.s, self.now);
    }
}

/// Datagrams prepared and timed together, so the clock is read once per batch.
const BATCH: usize = 64;

fn bench_size<const K: usize, const D: usize>(
    g: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    n: usize,
) {
    let mut r = rig::<K, D>(n);
    g.throughput(Throughput::Elements(1));
    g.bench_function(format!("receive_{n}"), |b| {
        let mut buf = vec![0u8; 65_536];
        b.iter_custom(|iters| {
            let (mut spent, mut done) = (Duration::ZERO, 0usize);
            while done < iters as usize {
                let mut batch = Vec::with_capacity(BATCH);
                for _ in 0..BATCH.min(iters as usize - done) {
                    r.queue_one();
                    if let Some(t) = r.c.ep.poll_transmit(r.now, &mut buf) {
                        batch.push((t, buf[..t.len].to_vec()));
                    }
                }
                let at = r.now;
                let start = Instant::now();
                for (t, d) in &mut batch {
                    r.s.ep.handle_datagram(at, t.remote, t.local, black_box(d));
                }
                spent += start.elapsed();
                done += batch.len().max(1);
                r.settle();
            }
            spent.mul_f64(iters as f64 / done as f64)
        });
    });
    g.bench_function(format!("send_{n}"), |b| {
        let mut buf = vec![0u8; 65_536];
        b.iter_custom(|iters| {
            let (mut spent, mut done) = (Duration::ZERO, 0usize);
            while done < iters as usize {
                let count = BATCH.min(iters as usize - done);
                for _ in 0..count {
                    r.queue_one();
                }
                let at = r.now;
                let mut produced = 0;
                let start = Instant::now();
                for _ in 0..count {
                    produced += usize::from(black_box(r.c.ep.poll_transmit(at, black_box(&mut buf))).is_some());
                }
                spent += start.elapsed();
                done += produced.max(1);
                r.settle();
            }
            spent.mul_f64(iters as f64 / done as f64)
        });
    });
    g.bench_function(format!("poll_timeout_and_idle_handle_timeout_{n}"), |b| {
        b.iter(|| {
            let t = black_box(r.s.ep.poll_timeout());
            r.s.ep.handle_timeout(black_box(r.now));
            t
        });
    });
}

fn bench_endpoint(c: &mut Criterion) {
    let mut g = c.benchmark_group("core_endpoint");
    g.sample_size(30);
    bench_size::<1, 16>(&mut g, 1);
    bench_size::<100, 1_000>(&mut g, 100);
    bench_size::<10_000, 100_000>(&mut g, 10_000);
    g.finish();
}

fn bench_heap(c: &mut Criterion) {
    let mut g = c.benchmark_group("core_timer_heap");
    g.throughput(Throughput::Elements(1));
    for n in [1usize, 100, 10_000] {
        g.bench_function(format!("set_{n}"), |b| {
            let mut h: Box<DeadlineHeap<10_000>> = Box::new(DeadlineHeap::new());
            let mut x = 0x9E37_79B9_7F4A_7C15u64;
            for id in 0..n {
                x = x.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                h.set(id, Some(x >> 20));
            }
            b.iter(|| {
                x = x
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                h.set(black_box((x >> 40) as usize % n), Some(black_box(x >> 20)));
            });
        });
        g.bench_function(format!("pop_and_reinsert_{n}"), |b| {
            let mut h: Box<DeadlineHeap<10_000>> = Box::new(DeadlineHeap::new());
            for id in 0..n {
                h.set(id, Some((id as u64).wrapping_mul(2_654_435_761) >> 8));
            }
            let mut clock = 1u64 << 40;
            b.iter(|| {
                let (t, id) = h.peek().unwrap();
                clock += 1;
                h.set(id, Some(t.max(clock) + 1_000));
            });
        });
    }
    g.finish();
}

/// The rigs hold large values; run the benchmarks on a thread with a big stack.
fn main() {
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(|| {
            let mut c = Criterion::default().configure_from_args();
            bench_heap(&mut c);
            bench_endpoint(&mut c);
            c.final_summary();
        })
        .unwrap()
        .join()
        .unwrap();
}
