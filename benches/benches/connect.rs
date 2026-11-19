//! Benchmarks of `pinc-connect`: the decision the client makes for every datagram it routes onto a relay carrier, the
//! throughput of the protected carrier (seal and open), and the throughput of the relay forwarding between two
//! carrier sessions.
//!
//! The carrier pair completes a real handshake in memory first; every benchmark then measures steady state. The
//! numbers are the cost of the state machines and the crypto on this machine, not of a network.
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

use criterion::{BatchSize, Criterion, Throughput};
use pinc_connect::carrier::session::{self, ALPN, Poll, ProtectedCarrier};
use pinc_connect::carrier::{Frame, MAX_FRAME_LEN};
use pinc_connect::client::{Config as ClientConfig, Connectivity, Io, RelayCfg};
use pinc_connect::relay::datagram::Datagram;
use pinc_connect::relay::{Config, Effect, Relay, Sink};
use pinc_core::{Endpoint, EndpointConfig, Slot};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use pinc_security::{
    ConnId, CreditRecord, Env, InitiatorParams, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys,
    SoftPrekeys,
};
use pinc_transport::conn::{Resources, Tables};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{self, NoSource, Streams};

const NOW: u64 = 1_000_000_000_000;
const PACKET: usize = 1200;

fn kp(tag: u8) -> Keypair {
    Keypair::from_seed(IdentityAlg::Ed25519, &[tag; 32]).unwrap()
}

/// A dialer and a listener that completed the handshake in memory.
struct Pair {
    client: Box<ProtectedCarrier<Software>>,
    relay: Box<ProtectedCarrier<Software>>,
}

/// Poll a carrier until idle, answering every key request from software keys; true once it opened.
fn step(
    c: &mut ProtectedCarrier<Software>,
    env: &mut Env<'_, Software>,
    stores: &mut ResponderStores<2, 2>,
    soft: &SoftKeys<'_, Software>,
) -> bool {
    let mut opened = false;
    let mut next = c.poll(env, stores).unwrap();
    loop {
        match next {
            Poll::KeyRequest => next = c.answer_soft(env, soft).unwrap(),
            Poll::Open(_) => {
                opened = true;
                next = c.poll(env, stores).unwrap();
            }
            Poll::Idle => return opened,
            _ => next = c.poll(env, stores).unwrap(),
        }
    }
}

fn pair() -> Pair {
    let (ckp, rkp) = (kp(0x31), kp(0x32));
    let cid = LocalIdentity::from_keypair(&ckp, KeyHandle(1)).unwrap();
    let rid = LocalIdentity::from_keypair(&rkp, KeyHandle(1)).unwrap();
    let (mut cd, mut rd) = (Drbg::new(&[1; 32]), Drbg::new(&[2; 32]));
    let mut env = Env {
        provider: &Software,
        now: NOW,
        drbg: &mut cd,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
    let mut client = Box::new(
        ProtectedCarrier::dial(
            &mut env,
            InitiatorParams {
                peer: rid.node_id(),
                alpn: ALPN,
                scid: ConnId::new(b"client00").unwrap(),
                identity: &cid,
                prekey: &prekey,
                peer_has_prekey: false,
                ticket: None,
                credit: CreditRecord::NONE,
            },
        )
        .unwrap(),
    );
    let mut relay = Box::new(ProtectedCarrier::accept(
        session::responder_config(rid, ConnId::new(b"relay000").unwrap()).unwrap(),
    ));
    let mut stores = ResponderStores::<2, 2>::default();
    let mut cstores = ResponderStores::<2, 2>::default();
    let csoft = SoftKeys {
        signer: Some((KeyHandle(1), &ckp)),
        prekeys: Some(&prekeys),
    };
    let rsoft = SoftKeys::<Software> {
        signer: Some((KeyHandle(1), &rkp)),
        prekeys: None,
    };
    let mut buf = vec![0u8; 32 * 1024];
    let (mut c_open, mut r_open) = (false, false);
    for _ in 0..64 {
        let n = client.transmit(&mut buf);
        let mut rest = &buf[..n];
        while !rest.is_empty() {
            let took = relay.receive(rest);
            rest = &rest[took..];
            if took == 0 {
                break;
            }
        }
        let mut renv = Env {
            provider: &Software,
            now: NOW,
            drbg: &mut rd,
        };
        r_open |= step(&mut relay, &mut renv, &mut stores, &rsoft);
        let n = relay.transmit(&mut buf);
        let mut rest = &buf[..n];
        while !rest.is_empty() {
            let took = client.receive(rest);
            rest = &rest[took..];
            if took == 0 {
                break;
            }
        }
        c_open |= step(&mut client, &mut env, &mut cstores, &csoft);
        if c_open && r_open {
            return Pair { client, relay };
        }
    }
    panic!("the carrier handshake did not complete");
}

fn bench_carrier(c: &mut Criterion) {
    let mut g = c.benchmark_group("connect_carrier");
    let packet = [0x41u8; PACKET];
    let src = NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: [7; 32],
    };
    g.throughput(Throughput::Bytes(PACKET as u64));
    g.bench_function("seal_1200", |b| {
        let mut p = pair();
        let mut out = vec![0u8; MAX_FRAME_LEN + 64];
        b.iter(|| {
            let f = Frame::Recv {
                src,
                flag: 0,
                packet: black_box(&packet),
            };
            black_box(p.client.seal(&Software, &f, &mut out).unwrap())
        });
    });
    g.bench_function("open_1200", |b| {
        let mut p = pair();
        let mut stores = ResponderStores::<2, 2>::default();
        let mut drbg = Drbg::new(&[3; 32]);
        let mut sealed = vec![0u8; MAX_FRAME_LEN + 64];
        b.iter_batched(
            || {
                let f = Frame::Recv {
                    src,
                    flag: 0,
                    packet: &packet,
                };
                let n = p.relay.seal(&Software, &f, &mut sealed).unwrap();
                sealed[..n].to_vec()
            },
            |unit| {
                let mut env = Env {
                    provider: &Software,
                    now: NOW,
                    drbg: &mut drbg,
                };
                let took = p.client.receive(&unit);
                assert_eq!(took, unit.len());
                match black_box(p.client.poll(&mut env, &mut stores).unwrap()) {
                    Poll::Frame(f) => f.packet().map(<[u8]>::len),
                    _ => None,
                }
            },
            BatchSize::SmallInput,
        );
    });
    g.finish();
}

#[derive(Default)]
struct Count(u64, u64);

impl Sink for Count {
    fn emit(&mut self, e: Effect<'_>) {
        if let Effect::Carrier { frame, .. } = e {
            self.0 += 1;
            self.1 += frame.packet().map_or(0, <[u8]>::len) as u64;
        }
    }
}

fn bench_relay(c: &mut Criterion) {
    let mut g = c.benchmark_group("connect_relay");
    let node = |t: u8| NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: [t; 32],
    };
    let (a, b) = (node(0xa1), node(0xb2));
    // The measured loop sends far more than the default per-minute quota; lift it so the bench times forwarding.
    let mut cfg = Config::new(node(0x10), 9);
    cfg.quota.bytes = u64::MAX;
    let mut relay: Box<Relay<16, 16, 4, 2048>> = Box::new(Relay::new(cfg));
    let mut sink = Count::default();
    let sa = relay.carrier_opened(0, a, &mut sink).unwrap();
    relay.carrier_opened(0, b, &mut sink).unwrap();
    let packet = [0x41u8; PACKET];
    g.throughput(Throughput::Bytes(PACKET as u64));
    g.bench_function("forward_carrier_to_carrier_1200", |bench| {
        let mut now = 0u64;
        bench.iter(|| {
            now += 1_000;
            relay
                .carrier_frame(
                    now,
                    &a,
                    sa,
                    &Frame::Send {
                        dst: b,
                        flag: 0,
                        packet: black_box(&packet),
                    },
                    &mut sink,
                )
                .unwrap();
        });
    });
    g.bench_function("answer_qad", |bench| {
        let mut buf = [0u8; 64];
        let n = Datagram::Qad { nonce: [3; 8] }.encode(&mut buf).unwrap();
        let src: SocketAddr = "198.51.100.9:4000".parse().unwrap();
        let mut now = 0u64;
        bench.iter(|| {
            now += 1_000;
            relay.datagram(now, src, None, black_box(&buf[..n]), &mut sink).unwrap();
        });
    });
    g.finish();
    assert!(sink.0 > 0);
}

type Ep = Endpoint<'static, 'static, Software, NoSource, 2, 2, 16, 1, 2, 24, 4, 4, 2>;

fn endpoint(tag: u8) -> (Box<Ep>, LocalIdentity) {
    let kpair = kp(tag);
    let id = LocalIdentity::from_keypair(&kpair, KeyHandle(1)).unwrap();
    let slots: Box<[Slot<'static, Software, NoSource, 2, 2, 16, 1>; 2]> = (0..2)
        .map(|_| {
            let pool = BufferPool::new_boxed(3);
            let streams: &'static mut Streams<NoSource, 2, 2> =
                Box::leak(Box::new(Streams::new(&stream::Config::new(false), &pool)));
            Slot::new(Resources {
                pool,
                streams: streams.into(),
                loss: (&*Box::leak(Box::new(LossEstimate::new()))).into(),
                tables: Tables::new(),
            })
        })
        .collect::<Vec<_>>()
        .into_boxed_slice()
        .try_into()
        .ok()
        .unwrap();
    let ep = Box::new(Endpoint::new(
        NOW,
        Software,
        Drbg::new(&[9; 32]),
        id,
        EndpointConfig::new(1),
        Box::leak(slots),
    ));
    (ep, id)
}

/// The client's decision for a datagram the endpoint transmitted to a relay path: which carrier, whether to tunnel,
/// the alias and the batch. Measured with an open carrier and no session, the steady state of a relayed packet.
fn bench_route(c: &mut Criterion) {
    let mut g = c.benchmark_group("connect_client");
    let (ep, identity) = endpoint(0x31);
    let mut drbg = Drbg::new(&[4; 32]);
    let mut env = Env {
        provider: &Software,
        now: NOW,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
    let rkp = kp(0x32);
    let rid = LocalIdentity::from_keypair(&rkp, KeyHandle(1)).unwrap();
    let mut relays = [None; 1];
    relays[0] = Some(RelayCfg {
        id: rid.node_id(),
        udp: Some("203.0.113.10:4433".parse().unwrap()),
        tcp: Some("203.0.113.10:443".parse().unwrap()),
        ws: None,
    });
    let mut conn: Box<Connectivity<Software, 1, 4>> = Box::new(Connectivity::new(
        ClientConfig {
            me: identity.node_id(),
            identity,
            relays,
            phone: false,
            restarted: false,
            start: NOW,
            v6: false,
            keep_learn: false,
        },
        prekey,
        Software,
        1,
    ));
    // Open the carrier against a real listener.
    let ckp = kp(0x31);
    let mut stores = ResponderStores::<2, 2>::default();
    let mut rd = Drbg::new(&[5; 32]);
    let mut relay_side = Box::new(ProtectedCarrier::accept(
        session::responder_config(rid, ConnId::new(b"relay000").unwrap()).unwrap(),
    ));
    let csoft = SoftKeys {
        signer: Some((KeyHandle(1), &ckp)),
        prekeys: Some(&prekeys),
    };
    let rsoft = SoftKeys::<Software> {
        signer: Some((KeyHandle(1), &rkp)),
        prekeys: None,
    };
    let mut now = NOW;
    conn.set_local(&["192.168.1.2:4433".parse().unwrap()]);
    conn.probe_all(now, &mut env);
    let mut buf = vec![0u8; 32 * 1024];
    let (_, n) = conn.poll_udp(&mut buf).unwrap();
    let nonce: [u8; 8] = match Datagram::decode(&buf[..n]).unwrap() {
        Datagram::Qad { nonce } => nonce,
        _ => panic!("not a probe"),
    };
    let mut reply = [0u8; 64];
    let m = Datagram::Qadr {
        nonce,
        addr: "198.51.100.5:20000".parse().unwrap(),
    }
    .encode(&mut reply)
    .unwrap();
    assert!(conn.handle_udp(now, "203.0.113.10:4433".parse().unwrap(), &reply[..m]));
    now += 1_000_000_000;
    conn.tick(now, &mut env, None);
    assert!(matches!(conn.poll_io(), Some(Io::Open { .. })));
    conn.stream_opened(now, &mut env, 0);
    for _ in 0..40 {
        loop {
            let ans = conn.key_request(0).map(|r| {
                csoft
                    .answer(&mut env, &r, &mut [0u8; pinc_crypto::identity::MAX_SIGNATURE_LEN])
                    .clone_response()
            });
            let Some(ans) = ans else { break };
            conn.key_response(now, &mut env, 0, ans.get());
        }
        let n = conn.poll_stream(0, &mut buf);
        let mut rest = &buf[..n];
        while !rest.is_empty() {
            let took = relay_side.receive(rest);
            rest = &rest[took..];
            let mut renv = Env {
                provider: &Software,
                now,
                drbg: &mut rd,
            };
            loop {
                match relay_side.poll(&mut renv, &mut stores).unwrap() {
                    Poll::KeyRequest => {
                        relay_side.answer_soft(&mut renv, &rsoft).unwrap();
                    }
                    Poll::Idle => break,
                    _ => {}
                }
            }
            if took == 0 {
                break;
            }
        }
        let mut back = vec![0u8; 32 * 1024];
        let k = relay_side.transmit(&mut back);
        if k > 0 {
            conn.stream_data(now, &mut env, 0, &back[..k]);
        }
        if conn.carrier_state(0) == pinc_connect::client::link::State::Open {
            break;
        }
    }
    assert_eq!(
        conn.carrier_state(0),
        pinc_connect::client::link::State::Open,
        "the carrier opened"
    );
    let peer = NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: [0xb7; 32],
    };
    let to = conn.path_addr(0, &peer);
    let packet = [0x41u8; PACKET];
    let mut out = vec![0u8; 32 * 1024];
    g.throughput(Throughput::Elements(1));
    g.bench_function("route_open_carrier_1200", |b| {
        let mut t = now;
        b.iter(|| {
            t += 1_000;
            black_box(conn.route(t, &*ep, to, black_box(&packet)));
            // keep the write buffer drained, as the host does after each step
            if t.is_multiple_of(16_000) {
                black_box(conn.poll_stream(0, &mut out));
            }
        });
    });
    g.finish();
}

/// The owned form of a key answer, so the request that produced it can be dropped before it is delivered.
trait CloneResponse {
    fn clone_response(self) -> Owned;
}

enum Owned {
    Sig(Vec<u8>),
    Secret(pinc_crypto::Secret<32>),
}

impl Owned {
    fn get(&self) -> pinc_security::KeyResponse<'_> {
        match self {
            Self::Sig(s) => pinc_security::KeyResponse::Signature(s),
            Self::Secret(s) => pinc_security::KeyResponse::SharedSecret(pinc_crypto::Secret::new(*s.expose())),
        }
    }
}

impl CloneResponse for pinc_security::KeyResponse<'_> {
    fn clone_response(self) -> Owned {
        match self {
            Self::Signature(s) => Owned::Sig(s.to_vec()),
            Self::SharedSecret(s) => Owned::Secret(s),
            Self::Failed => panic!("the software keys failed"),
        }
    }
}

/// The values the benchmarks build are large; run them on a thread with a big stack.
fn main() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut c = Criterion::default().configure_from_args();
            bench_carrier(&mut c);
            bench_relay(&mut c);
            bench_route(&mut c);
            c.final_summary();
        })
        .unwrap()
        .join()
        .unwrap();
}
