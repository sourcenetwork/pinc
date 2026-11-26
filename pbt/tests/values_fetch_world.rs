//! `pinc-values`: whole fetches over the project's in-memory multi-provider harness (`tests/values_support`, included
//! by path, unchanged), with generated values, providers (honest or lying, fast or slow, lossy, reordering, stalling),
//! stores that already hold some bytes, and requested ranges.
//!
//! Where the expected behaviour comes from (`crates/pinc-values/src/fetch/mod.rs`):
//! - "Only bytes that hashed to the value's root are written to the store, and a range is committed only after its
//!   bytes are written: a crash leaves the verified set a subset of the truth";
//! - "LIAR_EVICT: a provider whose bytes fail verification is cut off, its share goes back to the queue", and
//!   "Nothing else ends a fetch whose providers stop answering" (`FetchSpec::deadline`): with one honest provider that
//!   keeps answering, the fetch completes;
//! - "Resume: a fetch asks only for the bytes the store has not verified" and `Fetch::start`: "Bytes the store has
//!   verified are not asked for again"; `span::align`: requests are rounded "to whole groups";
//! - `FetchSpec::ranges`: "The byte ranges wanted; empty means the whole value";
//! - the tests `tests/values_fetch.rs` (`a_liar_is_evicted_nothing_bad_is_released_and_the_value_completes`,
//!   `resume_with_holes_requests_exactly_the_holes`, `every_provider_lying_fails_and_stores_nothing_bad`: "Bytes
//!   announced are bytes verified").
//!
//! The existing suite runs fixed worlds; these properties draw them.

#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::cast_possible_truncation)]

// The harness names `pinc_tests::SplitMix64`; this crate stands in for `pinc-tests` (whose features would change the
// code under test) with the same generator.
extern crate self as pinc_tests;

#[path = "../../tests/values_support/mod.rs"]
mod values_support;

use std::ops::{ControlFlow, Range};

use ephyra::prelude::*;
use ephyra::{check_generator, check_shrinker};
use pinc_values::knobs::GROUP;
use pinc_values::span::Span;
use pinc_values::trace::{Event, FailReason, Trace};
use values_support::{ClientStore, Lie, MS, PStore, ProvCfg, SEC, Sim};

/// The generator of `pinc_tests` (`tests/support/lib.rs`), bit for bit.
#[derive(Debug, Clone)]
pub struct SplitMix64(u64);

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn fill(&mut self, buf: &mut [u8]) {
        for chunk in buf.chunks_mut(8) {
            let v = self.next_u64().to_le_bytes();
            let n = chunk.len();
            chunk.copy_from_slice(&v[..n]);
        }
    }
}

/// One provider of the world. `lie` is a kind (0 flip a byte, 1 every group, 2 a bad pair) and a raw offset.
#[derive(Clone, Debug, PartialEq)]
struct Prov {
    lie: Option<(u8, u64)>,
    rate: u64,
    latency_ms: u64,
    loss: u64,
    reorder_ms: u64,
    stall: Option<u64>,
}

impl Prov {
    /// Honest, and answering for as long as the fetch runs.
    const fn keeps_answering(&self) -> bool {
        self.lie.is_none() && self.stall.is_none()
    }
}

/// A world. Spans are raw `(off, len)` pairs reduced modulo the value when run, so every shrink stays valid.
#[derive(Clone, Debug)]
struct World {
    len: u64,
    seed: u64,
    provs: Vec<Prov>,
    seeded: Vec<(u64, u64)>,
    ranges: Vec<(u64, u64)>,
    /// Session cuts: provider (modulo the count), when (ms), and for how long (ms) before it can be dialled again.
    cuts: Vec<(usize, u64, u64)>,
}

fn span_of(len: u64, (a, b): (u64, u64)) -> Range<u64> {
    let off = a % len;
    off..off + 1 + b % (len - off)
}

impl World {
    /// The seeded ranges, merged into disjoint ones (the harness keys stored pieces by offset).
    fn seeded_ranges(&self) -> Vec<Range<u64>> {
        let mut v: Vec<Range<u64>> = self.seeded.iter().map(|&p| span_of(self.len, p)).collect();
        v.sort_by_key(|r| r.start);
        let mut out: Vec<Range<u64>> = Vec::new();
        for r in v {
            match out.last_mut() {
                Some(l) if r.start <= l.end => l.end = l.end.max(r.end),
                _ => out.push(r),
            }
        }
        out
    }

    fn spans(&self) -> Vec<Span> {
        self.ranges
            .iter()
            .map(|&p| {
                let r = span_of(self.len, p);
                Span {
                    off: r.start,
                    len: r.end - r.start,
                }
            })
            .collect()
    }

    /// The wanted bytes: the ranges, or the whole value.
    fn wanted(&self) -> Vec<Range<u64>> {
        if self.ranges.is_empty() {
            vec![0..self.len]
        } else {
            self.spans().iter().map(|s| s.off..s.off + s.len).collect()
        }
    }
}

fn draw_prov(g: &mut Source) -> Prov {
    Prov {
        lie: if g.bool_with(0.3) {
            Some((g.int(0u8..=2), g.int(0u64..=u64::MAX / 2)))
        } else {
            None
        },
        rate: *g.pick(&[50u64, 300, 1000, 4000]),
        latency_ms: *g.pick(&[0u64, 1, 10, 80]),
        loss: *g.weighted(&[(6, 0u64), (1, 10), (1, 100)]),
        reorder_ms: *g.weighted(&[(6, 0u64), (1, 5)]),
        stall: if g.bool_with(0.15) { Some(g.int(0u64..=200_000)) } else { None },
    }
}

fn draw_world(g: &mut Source) -> World {
    let (few, many) = (g.int(2u64..=8), g.int(9u64..=40));
    let groups = *g.weighted(&[(3, 1u64), (4, few), (2, many)]);
    let some = g.int(1..=GROUP - 1);
    let tail = *g.weighted(&[(2, 0u64), (2, 1), (3, some)]);
    let len = ((groups - 1) * GROUP + if tail == 0 { GROUP } else { tail }).max(1);
    let n = *g.weighted(&[(3, 1usize), (3, 2), (2, 3), (1, 4), (1, 6)]);
    let provs = (0..n).map(|_| draw_prov(g)).collect();
    let seeded = (0..*g.weighted(&[(3, 0usize), (3, 1), (2, 3), (1, 8)]))
        .map(|_| {
            let (off, any) = (g.int(0..=len - 1), g.int(0..=len));
            (off, *g.weighted(&[(1, 0u64), (1, GROUP - 1), (2, any)]))
        })
        .collect();
    let ranges = (0..*g.weighted(&[(3, 0usize), (2, 1), (2, 3), (1, 6)]))
        .map(|_| {
            let (off, any) = (g.int(0..=len - 1), g.int(0..=len));
            (off, *g.weighted(&[(1, 0u64), (2, any)]))
        })
        .collect();
    let cuts = (0..*g.weighted(&[(4, 0usize), (2, 1), (1, 3)]))
        .map(|_| (g.index(n), g.int(0u64..=3000), *g.pick(&[0u64, 5, 500, 10_000])))
        .collect();
    World {
        len,
        seed: g.int(0u64..=1 << 40),
        provs,
        seeded,
        ranges,
        cuts,
    }
}

fn shrink_world(w: &World, visit: &mut dyn FnMut(World) -> ControlFlow<()>) -> ControlFlow<()> {
    for i in 0..w.provs.len() {
        if w.provs.len() > 1 {
            let mut provs = w.provs.clone();
            provs.remove(i);
            visit(World { provs, ..w.clone() })?;
        }
    }
    for i in 0..w.seeded.len() {
        let mut seeded = w.seeded.clone();
        seeded.remove(i);
        visit(World { seeded, ..w.clone() })?;
    }
    for i in 0..w.ranges.len() {
        let mut ranges = w.ranges.clone();
        ranges.remove(i);
        visit(World { ranges, ..w.clone() })?;
    }
    for i in 0..w.cuts.len() {
        let mut cuts = w.cuts.clone();
        cuts.remove(i);
        visit(World { cuts, ..w.clone() })?;
    }
    if w.len > 1 {
        visit(World { len: w.len / 2, ..w.clone() })?;
        visit(World { len: w.len - 1, ..w.clone() })?;
    }
    for i in 0..w.provs.len() {
        let p = &w.provs[i];
        let calm = Prov {
            loss: 0,
            reorder_ms: 0,
            latency_ms: 0,
            stall: None,
            ..p.clone()
        };
        if calm != *p {
            let mut provs = w.provs.clone();
            provs[i] = calm;
            visit(World { provs, ..w.clone() })?;
        }
    }
    ControlFlow::Continue(())
}

fn worlds() -> ephyra::BoxGen<World> {
    (|g: &mut Source| draw_world(g)).with_shrink(shrink_world).boxed()
}

fn world_size(w: &World) -> u64 {
    w.len
        + 100 * (w.provs.len() + w.seeded.len() + w.ranges.len() + w.cuts.len()) as u64
        + w
            .provs
            .iter()
            .map(|p| p.loss + p.reorder_ms + p.latency_ms + u64::from(p.stall.is_some()))
            .sum::<u64>()
}

/// The virtual time a world is given: far more than its slowest honest provider needs.
const LIMIT_S: u64 = 900;

struct Ran {
    sim: Sim,
    truth: PStore,
    done: bool,
}

fn run(w: &World) -> Ran {
    let truth = PStore::random(w.seed, w.len as usize);
    let outboard = truth.0.outboard.len() as u64;
    let cfgs = w
        .provs
        .iter()
        .map(|p| {
            let store = match p.lie {
                None => truth.clone(),
                Some((0, at)) => truth.lying(Lie::FlipByte(at % w.len)),
                Some((1, _)) => truth.lying(Lie::EveryGroup),
                Some((_, at)) => truth.lying(Lie::BadPair(if outboard == 0 { 0 } else { at % outboard })),
            };
            let mut c = ProvCfg::new(store, p.rate)
                .latency(p.latency_ms * MS)
                .loss(p.loss)
                .reorder(p.reorder_ms);
            if let Some(b) = p.stall {
                c = c.stall_after(b);
            }
            c
        })
        .collect();
    let store = ClientStore::seeded(truth.content(), &w.seeded_ranges());
    let mut sim = Sim::new(cfgs, store);
    let provs = sim.all_providers();
    sim.start_with(&w.spans(), &provs, None);
    // The cuts and revivals in time order: `true` cuts, `false` lets the provider be dialled again.
    let mut steps: Vec<(u64, bool, usize)> = w
        .cuts
        .iter()
        .flat_map(|&(i, at, down)| [(at * MS, true, i % w.provs.len()), ((at + down) * MS, false, i % w.provs.len())])
        .collect();
    steps.sort_unstable();
    for (t, cut, i) in steps {
        if sim.run_until(t, |s| s.fetch.is_done()) {
            break;
        }
        if cut && sim.provs[i].up {
            sim.cut(i);
        } else if !cut {
            sim.revive(i);
        }
    }
    let done = sim.run_until(LIMIT_S * SEC, |s| s.fetch.is_done());
    Ran { sim, truth, done }
}

/// Every verified byte is the truth, every announced byte is verified, and a fetch that completed holds every
/// wanted byte; with an honest provider that keeps answering the fetch completes, and with no honest provider at all
/// it either completes with the truth or fails because every provider lied.
#[ephyra::test(gen = worlds(), tests = 120)]
fn a_fetch_never_stores_a_wrong_byte_and_completes_while_an_honest_provider_answers(w: World) {
    let Ran { sim, truth, done } = run(&w);
    sim.store.assert_verified_is_true(truth.content());
    for (_, off, len) in sim.rec.readable() {
        assert!(sim.store.verified.contains_range(off..off + len), "announced {off}+{len} is not verified");
    }
    let honest = w.provs.iter().take(4).any(Prov::keeps_answering);
    ephyra::cover(honest, "an honest provider keeps answering");
    ephyra::cover(w.provs.iter().take(4).any(|p| p.lie.is_some()), "a liar");
    ephyra::cover(!w.seeded.is_empty(), "resumed");
    // Intended, and excluded narrowly: a provider whose link goes silent before the fetch's first verified granule is
    // waited for with no timer (`FetchSpec::deadline`: "one that is connected and sends nothing is waited for with no
    // timer"; `stall_base`: "a fetch that has not yet received one is never redialled by the stall rule"), and an idle
    // provider without a session never steals, so such a fetch waits for ever although another provider is honest.
    let verified_any = sim.rec.traces.iter().any(|(_, t)| matches!(t, Trace::Verified { .. }));
    let silent_first = !verified_any && w.provs.iter().take(4).any(|p| p.stall.is_some());
    ephyra::cover(silent_first && !done, "waited for a provider silent before the first granule");
    if honest && !silent_first {
        assert!(done, "the fetch did not finish in {LIMIT_S} s with an honest provider answering");
        assert!(sim.rec.complete(), "the fetch failed with an honest provider answering: {:?}", sim.rec.failed());
    }
    if done && sim.rec.complete() {
        for r in w.wanted() {
            assert!(sim.store.verified.contains_range(r.clone()), "a completed fetch lacks {r:?}");
        }
    }
    if done && !sim.rec.complete() {
        assert_eq!(sim.rec.failed(), Some(FailReason::EveryProviderLied), "why the fetch failed");
    }
}

/// The bytes a resumed fetch from one honest, lossless provider asks for are exactly the bytes of the wanted ranges,
/// rounded out to whole groups, that the store has not verified, each asked once.
#[ephyra::test(gen = worlds(), tests = 150)]
fn a_resumed_fetch_from_one_honest_provider_asks_exactly_for_the_missing_groups(w: World) {
    let w = World {
        provs: vec![Prov {
            lie: None,
            loss: 0,
            reorder_ms: 0,
            stall: None,
            ..w.provs[0].clone()
        }],
        cuts: Vec::new(),
        ..w
    };
    let Ran { sim, truth, done } = run(&w);
    assert!(done, "the fetch did not finish in {LIMIT_S} s");
    assert!(sim.rec.complete(), "the fetch failed: {:?}", sim.rec.failed());
    sim.store.assert_verified_is_true(truth.content());
    // The wanted ranges are rounded out to whole groups first (`Fetch::start` aligns each with `span::align`), then
    // only the bytes the store has not verified are asked for: a hole inside a group is asked as it is.
    let seeded = w.seeded_ranges();
    let mut want = vec![false; w.len as usize];
    for r in w.wanted() {
        let (a, b) = (r.start / GROUP * GROUP, r.end.div_ceil(GROUP).saturating_mul(GROUP).min(w.len));
        want[a as usize..b as usize].fill(true);
    }
    for s in &seeded {
        want[s.start as usize..s.end as usize].fill(false);
    }
    let missing = want.iter().filter(|x| **x).count() as u64;
    let requested: u64 = sim
        .rec
        .traces_of(|t| if let Trace::Requested { bytes, .. } = t { Some(*bytes) } else { None })
        .iter()
        .map(|x| x.1)
        .sum();
    ephyra::cover(!seeded.is_empty() && missing > 0, "a resume with holes");
    assert_eq!(requested, missing, "bytes requested against the missing bytes of the wanted groups");
    let readable: u64 = sim
        .rec
        .events
        .iter()
        .filter_map(|(_, e)| if let Event::Readable { len, .. } = e { Some(*len) } else { None })
        .sum();
    ephyra::cover(readable > 0, "bytes announced");
}

fn world_ok(w: &World) -> bool {
    w.len >= 1 && !w.provs.is_empty() && w.wanted().iter().all(|r| r.start < r.end && r.end <= w.len)
}

#[test]
fn the_world_generator_builds_valid_worlds_and_shrinks_within_them() {
    check_generator(&Config::default().tests(200), worlds(), world_ok).assert_passed();
    check_shrinker(&Config::default().tests(100), worlds(), world_ok, world_size).assert_passed();
}
