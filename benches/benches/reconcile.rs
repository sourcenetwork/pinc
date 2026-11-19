//! Benchmarks of `pinc-reconcile`: the time and the bytes of a reconciliation against the size of the difference, on
//! sets of 10^6 items of 40 bytes. Each session runs both sides in one thread over in-memory indexes, so the time is
//! the work of the protocol (fingerprints, splits, leaves, merges), without a network. Each difference runs under the
//! default message limit and under a 16 KiB limit, where a round is spread over many messages. The bytes and messages
//! of each run are printed, and the machine's load average before and after, since a loaded machine inflates the times.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::collections::BTreeSet;
use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use pinc_reconcile::{Initiator, Limits, MemIndex, Responder, Step};

const N: usize = 1_000_000;
const ITEM: usize = 40;
const DIFFS: [usize; 7] = [0, 1, 10, 100, 1000, 10_000, 100_000];
const LIMITS: [(&str, usize); 2] = [("default", 0x00ff_ffff), ("16k", 16_384)];

struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn item(&mut self) -> Vec<u8> {
        let mut v = vec![0u8; ITEM];
        for chunk in v.chunks_mut(8) {
            chunk.copy_from_slice(&self.next().to_le_bytes()[..chunk.len()]);
        }
        v
    }
}

fn load_average() -> String {
    std::fs::read_to_string("/proc/loadavg").map_or_else(
        |_| "not available".into(),
        |s| s.split_whitespace().take(3).collect::<Vec<_>>().join(" "),
    )
}

fn index(set: &[Vec<u8>]) -> MemIndex {
    MemIndex::from_sorted(set.iter().map(Vec::as_slice)).unwrap()
}

/// `base` with `d` changes, half removed and half added.
fn changed(rng: &mut SplitMix64, base: &[Vec<u8>], d: usize) -> Vec<Vec<u8>> {
    let mut gone = BTreeSet::new();
    while gone.len() < d / 2 {
        gone.insert((rng.next() as usize) % base.len());
    }
    let mut out: Vec<Vec<u8>> = base
        .iter()
        .enumerate()
        .filter(|(i, _)| !gone.contains(i))
        .map(|(_, x)| x.clone())
        .collect();
    out.extend((0..d - d / 2).map(|_| rng.item()));
    out.sort_unstable();
    out.dedup();
    out
}

/// One session; returns the bytes on the wire and the messages.
fn session(
    init: &mut Initiator,
    resp: &mut Responder,
    a: &MemIndex,
    b: &MemIndex,
    tx: &mut Vec<u8>,
    rx: &mut Vec<u8>,
) -> (usize, usize) {
    let (mut bytes, mut messages) = (0, 0);
    resp.reset();
    init.start(a, b"set", tx).unwrap();
    'session: loop {
        bytes += tx.len();
        messages += 1;
        let mut step = resp.handle(b, tx, rx).unwrap();
        loop {
            match step {
                Step::Send | Step::Last => {
                    bytes += rx.len();
                    messages += 1;
                    match init.handle(a, rx, tx).unwrap() {
                        Step::Send => continue 'session,
                        Step::Last => {
                            bytes += tx.len();
                            messages += 1;
                            return (bytes, messages);
                        }
                        _ => return (bytes, messages),
                    }
                }
                Step::Chunk => {
                    bytes += rx.len();
                    messages += 1;
                    init.handle(a, rx, tx).unwrap();
                    step = resp.resume(b, rx).unwrap();
                }
                Step::Done | Step::Wait => return (bytes, messages),
            }
        }
    }
}

fn reconcile(c: &mut Criterion) {
    eprintln!("load average (1, 5, 15 min) at start: {}", load_average());
    let mut rng = SplitMix64(0x5eed);
    let mut base: Vec<Vec<u8>> = (0..N).map(|_| rng.item()).collect();
    base.sort_unstable();
    base.dedup();
    let ia = index(&base);

    let mut group = c.benchmark_group("reconcile_1m");
    group.sample_size(10);
    for d in DIFFS {
        let other = changed(&mut rng, &base, d);
        let ib = index(&other);
        for (label, max_message) in LIMITS {
            let limits = Limits {
                max_message,
                ..Limits::default()
            };
            let (mut init, mut resp) = (Initiator::new(limits), Responder::new(limits));
            let (mut tx, mut rx) = (Vec::new(), Vec::new());
            let (bytes, messages) = session(&mut init, &mut resp, &ia, &ib, &mut tx, &mut rx);
            let found = init.report().map(|r| r.here_count() + r.there_count()).unwrap();
            eprintln!("{label:>7} d = {d:>6}: {bytes:>9} bytes, {messages:>4} messages, {found} items found");
            group.throughput(Throughput::Bytes(bytes as u64));
            group.bench_with_input(BenchmarkId::new(label, d), &d, |bench, _| {
                bench.iter(|| black_box(session(&mut init, &mut resp, &ia, &ib, &mut tx, &mut rx)));
            });
        }
    }
    group.finish();
    eprintln!("load average (1, 5, 15 min) at end: {}", load_average());
}

criterion_group!(benches, reconcile);
criterion_main!(benches);
