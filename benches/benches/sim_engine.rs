//! Benchmark of the `pinc-sim` engine: events per second with 1,000 nodes.
//!
//! 500 client and server pairs of toy echo nodes run to completion over links with delay, jitter and 1% loss. The
//! reported throughput is engine events (timers, arrivals, commands) per second, including the toy nodes' own work.
//! A second group runs 200 pairs that move 1 MB each over a TCP carrier on a link with 1% loss, which exercises the
//! stream model (segments, ACKs, retransmission timers).
#![allow(missing_docs, clippy::unwrap_used, clippy::cast_possible_truncation)]

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use pinc_sim::toy::{Toy, ToyCmd, ToyConfig};
use pinc_sim::toy_stream::{StreamCmd, StreamProbe};
use pinc_sim::{LinkConfig, Loss, MS, SEC, Sim, SimConfig, StreamId, StreamKind};

const PAIRS: u32 = 500;

fn build() -> Sim<Toy> {
    let link = LinkConfig {
        delay: 5 * MS,
        jitter: MS,
        loss: Loss::Bernoulli(0.01),
        ..LinkConfig::default()
    };
    let mut sim = Sim::with_config(
        42,
        SimConfig {
            default_link: Some(link),
            ..SimConfig::default()
        },
    );
    let addr = |i: u32, port| SocketAddr::new(IpAddr::V4(Ipv4Addr::from(0x0a00_0000 + i)), port);
    for p in 0..PAIRS {
        let (c, s) = (addr(2 * p, 5000), addr(2 * p + 1, 443));
        let base = ToyConfig {
            local: c,
            peer: Some(s),
            total: 200,
            window: 16,
            msg_len: 1200,
            rto: 60 * MS,
        };
        let client = sim.add_node_at(Toy::new(base), c.ip());
        sim.add_node_at(
            Toy::new(ToyConfig {
                local: s,
                peer: None,
                ..base
            }),
            s.ip(),
        );
        sim.command(0, client, ToyCmd::Start);
    }
    sim
}

fn engine(c: &mut Criterion) {
    let mut probe = build();
    assert!(probe.run_idle(600 * SEC));
    let events = probe.events_processed();
    let mut g = c.benchmark_group("sim_engine");
    g.sample_size(10).throughput(Throughput::Elements(events));
    g.bench_function("1000_nodes_events", |b| {
        b.iter_batched(
            build,
            |mut sim| {
                sim.run_idle(600 * SEC);
                sim.events_processed()
            },
            BatchSize::LargeInput,
        );
    });
    g.finish();
}

const STREAM_PAIRS: u32 = 200;

fn build_streams() -> Sim<StreamProbe> {
    let link = LinkConfig {
        delay: 5 * MS,
        loss: Loss::Bernoulli(0.01),
        ..LinkConfig::default()
    };
    let mut sim = Sim::with_config(
        42,
        SimConfig {
            default_link: Some(link),
            ..SimConfig::default()
        },
    );
    let addr = |i: u32, port| SocketAddr::new(IpAddr::V4(Ipv4Addr::from(0x0a00_0000 + i)), port);
    for p in 0..STREAM_PAIRS {
        let (c, s) = (addr(2 * p, 5000), addr(2 * p + 1, 443));
        let client = sim.add_node_at(StreamProbe::new(), c.ip());
        let server = sim.add_node_at(StreamProbe::new(), s.ip());
        sim.listen(server, s, StreamKind::Tcp);
        sim.command(
            0,
            client,
            StreamCmd::Connect {
                local: c,
                remote: s,
                kind: StreamKind::Tcp,
                simultaneous: false,
            },
        );
        sim.command(
            SEC,
            client,
            StreamCmd::SendMany {
                stream: StreamId(1),
                count: 1000,
                len: 1000,
            },
        );
    }
    sim
}

fn carrier(c: &mut Criterion) {
    let mut probe = build_streams();
    assert!(probe.run_idle(600 * SEC));
    let events = probe.events_processed();
    let mut g = c.benchmark_group("sim_carrier");
    g.sample_size(10).throughput(Throughput::Elements(events));
    g.bench_function("200_pairs_1mb_events", |b| {
        b.iter_batched(
            build_streams,
            |mut sim| {
                sim.run_idle(600 * SEC);
                sim.events_processed()
            },
            BatchSize::LargeInput,
        );
    });
    g.finish();
}

criterion_group!(benches, engine, carrier);
criterion_main!(benches);
