//! Benchmarks of `vinc-broadcast`: a message from the publisher through a hub to a subscriber, end to end - the
//! publisher signs and sends it, the hub verifies, logs and pushes it and acknowledges it, the subscriber verifies
//! and delivers it, and the publisher takes the acknowledgement.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use vinc_broadcast::wire::ty;
use vinc_broadcast::{Config, Event, Host, IdKey, Lane, Topics};
use vinc_crypto::{IdentityAlg, Keypair};

type NodeId = [u8; 32];

const T: &[u8] = b"bench";
const STEP: u64 = 100_000_000;
const WALL: u64 = 1_700_000_000_000;

/// The secrets of the id tables of the benchmarked nodes, full width as the key store draws them.
const MAP_SECRETS: [u64; 7] = [
    0x9e37_79b9_7f4a_7c15,
    0xbf58_476d_1ce4_e5b9,
    0x94d0_49bb_1331_11eb,
    0x2545_f491_4f6c_dd1d,
    0xd6e8_feb8_6659_fd93,
    0xff51_afd7_ed55_8ccd,
    0xc4ce_b9fe_1a85_ec53,
];

/// A host that keeps the frames it is handed, in slots it reuses, so a round allocates nothing.
#[derive(Default)]
struct Pipe {
    out: Vec<(NodeId, Vec<u8>)>,
    used: usize,
    delivered: u64,
    ask: Option<u32>,
    wall: u64,
}

impl Host for Pipe {
    fn send(&mut self, peer: &NodeId, _lane: Lane, frame: &[u8]) -> bool {
        if self.used == self.out.len() {
            self.out.push((*peer, Vec::new()));
        }
        let (to, buf) = &mut self.out[self.used];
        *to = *peer;
        buf.clear();
        buf.extend_from_slice(frame);
        self.used += 1;
        true
    }
    fn send_member(&mut self, peer: &NodeId, frame: &[u8]) -> bool {
        self.send(peer, Lane::Main, frame)
    }
    fn hub_up(&self, _hub: &NodeId) -> bool {
        true
    }
    fn in_view(&self, _member: &NodeId) -> bool {
        true
    }
    fn wall_ms(&self) -> u64 {
        self.wall
    }
    fn event(&mut self, event: Event<'_>) {
        match event {
            Event::Message { .. } => self.delivered += 1,
            Event::AcpCheck { id, .. } => self.ask = Some(id),
            _ => {}
        }
    }
}

fn parts(f: &[u8]) -> (u8, &[u8], &[u8]) {
    let tl = usize::from(f[5]);
    (f[4], &f[6..6 + tl], &f[6 + tl..])
}

struct Rig {
    hub: Topics,
    hh: Pipe,
    sub: Topics,
    sh: Pipe,
    publisher: Topics,
    ph: Pipe,
    ids: [NodeId; 3],
    now: u64,
}

impl Rig {
    fn new(alg: IdentityAlg) -> Self {
        let keys: Vec<Keypair> = (1..=3u8)
            .map(|t| Keypair::from_seed(alg, &vec![t; alg.seed_len()]).unwrap())
            .collect();
        let ids = [
            keys[0].node_id().bytes,
            keys[1].node_id().bytes,
            keys[2].node_id().bytes,
        ];
        let hubs = [ids[0]];
        let mut it = keys.into_iter();
        let mut mk = |i: usize| {
            let cfg = Config {
                me: ids[i],
                is_hub: i == 0,
                hubs: &hubs,
                incarnation: 1 << 16,
                trace: false,
                limits: vinc_broadcast::Limits::default(),
                map_keys: IdKey::new(0x5eed, &MAP_SECRETS).unwrap(),
            };
            Topics::start(&cfg, Box::new(it.next().unwrap()), 1_000_000_000, WALL).unwrap()
        };
        let (hub, sub, publisher) = (mk(0), mk(1), mk(2));
        let pipe = || Pipe {
            wall: WALL,
            ..Pipe::default()
        };
        let mut r = Self {
            hub,
            hh: pipe(),
            sub,
            sh: pipe(),
            publisher,
            ph: pipe(),
            ids,
            now: 1_000_000_000,
        };
        let mut floor = [0u8; 4096];
        for who in [1, 2] {
            let n = r.hub.floor(&ids[who], &mut floor);
            let (t, h) = if who == 1 {
                (&mut r.sub, &mut r.sh)
            } else {
                (&mut r.publisher, &mut r.ph)
            };
            t.frame(h, r.now, &ids[0], ty::FLOOR, &[], &floor[..n]);
            t.primary_changed(h, r.now, None, &ids[0]);
        }
        r.sub.subscribe(&mut r.sh, r.now, T).unwrap();
        let (_, sub_frame) = (r.sh.out[0].0, r.sh.out[0].1.clone());
        let (t, topic, rest) = parts(&sub_frame);
        r.hub.frame(&mut r.hh, r.now, &ids[1], t, topic, rest);
        r.sh.used = 0;
        r.hh.used = 0;
        r.round(b"warm up");
        r
    }

    /// One message, end to end.
    fn round(&mut self, body: &[u8]) {
        self.now += STEP;
        for h in [&mut self.hh, &mut self.sh, &mut self.ph] {
            h.wall += STEP / 1_000_000;
        }
        self.publisher.publish(&mut self.ph, self.now, T, body).unwrap();
        for k in 0..self.ph.used {
            let (t, topic, rest) = parts(&self.ph.out[k].1);
            self.hub.frame(&mut self.hh, self.now, &self.ids[2], t, topic, rest);
        }
        self.ph.used = 0;
        for k in 0..self.hh.used {
            let (to, f) = &self.hh.out[k];
            let (t, topic, rest) = parts(f);
            if *to == self.ids[1] {
                self.sub.frame(&mut self.sh, self.now, &self.ids[0], t, topic, rest);
                if let Some(id) = self.sh.ask.take() {
                    self.sub.acp_answer(&mut self.sh, self.now, id, true);
                }
            } else if *to == self.ids[2] {
                self.publisher
                    .frame(&mut self.ph, self.now, &self.ids[0], t, topic, rest);
            }
        }
        self.hh.used = 0;
        self.sh.used = 0;
        self.ph.used = 0;
    }

    fn tick(&mut self) {
        self.hub.on_timer(&mut self.hh, self.now);
        self.sub.on_timer(&mut self.sh, self.now);
        self.publisher.on_timer(&mut self.ph, self.now);
        self.hh.used = 0;
        self.sh.used = 0;
        self.ph.used = 0;
    }
}

fn bench_through_hub(c: &mut Criterion) {
    let mut g = c.benchmark_group("broadcast_through_hub");
    for (name, alg) in [("ed25519", IdentityAlg::Ed25519), ("p256", IdentityAlg::EcdsaP256)] {
        for len in [100usize, 4096] {
            let body = vec![0xA5u8; len];
            let mut rig = Rig::new(alg);
            let before = rig.sh.delivered;
            g.throughput(Throughput::Bytes(len as u64));
            let mut n = 0u32;
            g.bench_function(format!("{name}_{len}B"), |b| {
                b.iter(|| {
                    rig.round(black_box(&body));
                    n += 1;
                    if n.is_multiple_of(256) {
                        rig.tick();
                    }
                });
            });
            assert!(rig.sh.delivered > before, "the benchmark delivers what it measures");
        }
    }
    g.finish();
}

criterion_group!(benches, bench_through_hub);
criterion_main!(benches);
