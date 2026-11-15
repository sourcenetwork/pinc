//! Benchmarks of the `pinc-transport` stream layer: receiving and reading 1400-byte frames in order and with 10%
//! reordering, buffered writes through to acknowledgement, and building frames from a source-backed stream.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{Config, NoSource, PeerLimits, StreamSource, Streams};

const FRAME: usize = 1400;
/// Frames per received stream: about 700 KB, below the initial window.
const FRAMES: usize = 512;

fn peer() -> PeerLimits {
    PeerLimits {
        window: 1 << 60,
        max_streams: 100,
    }
}

fn config() -> Config {
    let mut c = Config::new(false);
    c.peer = peer();
    c
}

/// `(offset, fin)` of each frame in arrival order: in order, or with about 10% of the frames swapped with a neighbour.
fn arrival_order(reorder: bool) -> Vec<(u64, bool)> {
    let mut order: Vec<usize> = (0..FRAMES).collect();
    if reorder {
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        for i in 0..FRAMES - 3 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            if state.is_multiple_of(10) {
                order.swap(i, i + 1 + (state >> 8) as usize % 3);
            }
        }
    }
    order
        .into_iter()
        .map(|i| ((i * FRAME) as u64, i == FRAMES - 1))
        .collect()
}

fn bench_receive(c: &mut Criterion) {
    let mut g = c.benchmark_group("stream_recv");
    g.throughput(Throughput::Bytes((FRAMES * FRAME) as u64));
    let payload = [0x5Au8; FRAME];
    for (name, reorder) in [("in_order_1400", false), ("reorder_10pct_1400", true)] {
        let order = arrival_order(reorder);
        let mut pool = BufferPool::new_boxed(256);
        let mut table = Box::new(Streams::<NoSource, 4, 1025>::new(&config(), &pool));
        let mut next_id = 2u64;
        g.bench_function(name, |b| {
            b.iter(|| {
                let id = next_id;
                next_id += 4;
                let mut read = 0usize;
                for &(offset, fin) in &order {
                    table
                        .on_stream_frame(&mut pool, id, offset, black_box(&payload), fin)
                        .unwrap();
                    while let Some(chunk) = table.read_chunk(&pool, id) {
                        let n = chunk.len();
                        read += n;
                        table.consume(&mut pool, id, n, 0, 0).unwrap();
                    }
                }
                while table.pending_control().is_some() {}
                black_box(read)
            });
        });
    }
    g.finish();
}

fn bench_write(c: &mut Criterion) {
    let mut g = c.benchmark_group("stream_send");
    g.throughput(Throughput::Bytes(FRAME as u64));
    let payload = [0xA5u8; FRAME];
    let mut pool = BufferPool::new_boxed(256);
    let mut table = Box::new(Streams::<NoSource, 4, 1025>::new(&config(), &pool));
    let id = table.open_stream(&pool, false).unwrap();
    let mut out = [0u8; FRAME];
    g.bench_function("buffered_write_build_ack_1400", |b| {
        b.iter(|| {
            assert_eq!(
                table.write(&mut pool, id, black_box(&payload), u64::MAX).unwrap(),
                FRAME
            );
            let frame = table.next_stream_frame(&mut pool, FRAME).unwrap();
            table.copy_out(&mut pool, &frame, &mut out).unwrap();
            table.on_acked(&mut pool, id, frame.offset, frame.len as u64, false);
            black_box(out[0])
        });
    });
    g.finish();
}

struct Repeating<'a>(&'a [u8]);

impl StreamSource for Repeating<'_> {
    fn read_at(&mut self, offset: u64, dst: &mut [u8]) -> usize {
        let at = offset as usize % self.0.len();
        let n = dst.len().min(self.0.len() - at);
        dst[..n].copy_from_slice(&self.0[at..at + n]);
        n
    }
}

fn bench_source(c: &mut Criterion) {
    let mut g = c.benchmark_group("stream_send");
    g.throughput(Throughput::Bytes(FRAME as u64));
    // A length that keeps every read whole: the source repeats a block that is a multiple of the frame size.
    let block = vec![0x3Cu8; FRAME * 64];
    let mut pool = BufferPool::new_boxed(4);
    let mut table = Box::new(Streams::<Repeating<'_>, 2, 65>::new(&config(), &pool));
    let id = table.open_stream(&pool, false).unwrap();
    table.open_source(id, Repeating(&block), 1 << 50).unwrap();
    let mut out = [0u8; FRAME];
    g.bench_function("source_backed_build_1400", |b| {
        b.iter(|| {
            let frame = table.next_stream_frame(&mut pool, FRAME).unwrap();
            table.copy_out(&mut pool, &frame, &mut out).unwrap();
            black_box(out[0])
        });
    });
    g.finish();
}

criterion_group!(benches, bench_receive, bench_write, bench_source);
criterion_main!(benches);
