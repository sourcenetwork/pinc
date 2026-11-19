//! Benchmarks of `pinc-transport` recovery: acknowledgement processing, sending and the pacer.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::single_range_in_vec_init
)]

use std::hint::black_box;
use std::time::{Duration, Instant};

use criterion::{Criterion, criterion_group, criterion_main};
use pinc_transport::recovery::{FrameRef, FrameRefs, MS, Pacer, Recovery, SECOND, Sent};

type Rec = Recovery<1024>;

fn packet(pn: u64) -> Sent {
    let mut frames = FrameRefs::new();
    frames
        .push(FrameRef::Stream {
            id: 4,
            offset: pn * 1200,
            len: 1200,
            fin: false,
        })
        .unwrap();
    Sent {
        pn,
        time: pn * 1000,
        size: 1200,
        path: 0,
        is_repair: false,
        is_mtu_probe: false,
        frames,
    }
}

/// Run `iters` rounds of sending `count` packets (untimed) and acknowledging `ranges` of them (timed).
fn timed_acks(iters: u64, count: u64, ranges: &[std::ops::RangeInclusive<u64>]) -> Duration {
    let mut rec = Box::new(Rec::new(1200));
    let mut total = Duration::ZERO;
    let mut pn = 0u64;
    // Each iteration is 5 s later, so packets left unacknowledged expire from the ring before it fills.
    let mut base = 0u64;
    for _ in 0..iters {
        for k in 0..count {
            let mut p = packet(pn + k);
            p.time = base + k * 1000;
            rec.on_packet_sent(p).unwrap();
        }
        let now = base + 50 * MS;
        let start = Instant::now();
        let mut acked = 0u32;
        rec.on_ack_received(
            black_box(now),
            ranges.iter().map(|r| pn + r.start()..=pn + r.end()),
            |_| acked += 1,
        )
        .unwrap();
        total += start.elapsed();
        black_box(acked);
        pn += count;
        base += 5 * SECOND;
    }
    total
}

fn bench_ack(c: &mut Criterion) {
    let mut g = c.benchmark_group("transport_recovery");
    g.bench_function("ack_10_packets", |b| {
        b.iter_custom(|iters| timed_acks(iters, 10, &[0..=9]));
    });
    g.bench_function("ack_100_packets_3_gaps", |b| {
        b.iter_custom(|iters| timed_acks(iters, 100, &[80..=99, 50..=77, 20..=47, 0..=17]));
    });
    g.bench_function("on_packet_sent", |b| {
        b.iter_custom(|iters| {
            let mut rec = Box::new(Rec::new(1200));
            let mut total = Duration::ZERO;
            let mut pn = 0u64;
            let mut left = iters;
            while left > 0 {
                let chunk = left.min(256);
                let start = Instant::now();
                for k in 0..chunk {
                    rec.on_packet_sent(black_box(packet(pn + k))).unwrap();
                }
                total += start.elapsed();
                rec.on_ack_received(pn * 1000 + SECOND, std::iter::once(pn..=pn + chunk - 1), |_| {})
                    .unwrap();
                pn += chunk;
                left -= chunk;
            }
            total
        });
    });
    g.bench_function("pacer_next_release", |b| {
        let mut p = Pacer::new();
        for _ in 0..10 {
            p.on_sent(0, 1200, 100 * MS, 120_000, true);
        }
        let mut now = 0u64;
        b.iter(|| {
            now += 100;
            black_box(p.next_release(black_box(now)))
        });
    });
    g.finish();
}

criterion_group!(benches, bench_ack);
criterion_main!(benches);
