//! Trace generation for the work scheduler of the value fetch: real runs of `Fetch` over the in-memory multi-provider
//! harness (several providers of different speeds, ranges and resume, liars, a silent provider, a dropped one, more
//! providers than the fetch uses, no provider, a wrong root, nothing missing), recorded as ndjson
//! (`values_sched.ndjson`) for the TLA+ trace check (`TraceValuesSched.tla`) and the Lean replay
//! (`Pinc/TraceValuesSched.lean`).
//!
//! A run is one line `run` (the value length, the ranges asked, the verified intervals the store held at the start,
//! the providers the fetch takes in slot order), the transitions the fetch reports through its `Trace` log in order
//! (`start`, `topup`, `steal`, `ver`, `liar`; each with the time of the call) and one line `end` (how the fetch ended).
//! The checkers replay them on the scheduler model: the bytes of the wanted groups stay partitioned among the queue,
//! the providers' lists and the verified set; a top-up is the step of the target (ARRIVAL_CURVE), the tail shrink and
//! the group cut; a steal is the victim, the cut and the idle rules of the model; an eviction returns the share to the
//! queue and the evicted provider is never assigned again.
//!
//! The test asserts the conservation itself (a plain tracker written here), so it is meaningful without the proof
//! tools. What is not observable: the spans of the lists (the log carries byte counts, the ranges on the wire are
//! checked by the other value tests), so the checkers replay the byte accounting, the arithmetic and the order of the
//! transitions; the span-level behaviour is proved in Lean (`ValuesSchedList` ... `ValuesSchedCover`) and model
//! checked (`ValuesSchedList`, `ValuesSched`). The trace is written to the directory in `PINC_TRACE_DIR` when it is
//! set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::needless_pass_by_value,
    clippy::type_complexity,
    clippy::doc_markdown,
    unreachable_pub
)]

mod values_support;

use std::collections::BTreeSet;
use std::fmt::Write as _;

use values_support::*;
use pinc_tests::SplitMix64;
use pinc_values::session::Provider;
use pinc_values::span::Span;
use pinc_values::trace::{Event, FailReason, Trace};

const G: u64 = GROUP;

/// The ndjson being written and what the runs covered.
#[derive(Default)]
struct Rec2 {
    out: String,
    run: u32,
    runs_with: Cov,
}

#[derive(Default, Debug)]
struct Cov {
    topups: u32,
    tail_topups: u32,
    steals: u32,
    steals_moving: u32,
    liars: u32,
    all_lied: u32,
    resumes: u32,
    non_striped: u32,
    no_provider: u32,
    bad_root: u32,
    nothing_missing: u32,
}

/// The groups `[g * G, min((g + 1) * G, len))` of a value.
fn group_end(g: u64, len: u64) -> u64 {
    ((g + 1) * G).min(len)
}

fn groups_of(len: u64) -> u64 {
    len.div_ceil(G)
}

/// The groups a list of byte ranges covers once rounded out, as the fetch does.
fn wanted_groups(len: u64, ranges: &[Span]) -> BTreeSet<u64> {
    let whole = [Span { off: 0, len }];
    let asked: &[Span] = if ranges.is_empty() { &whole } else { ranges };
    let mut w = BTreeSet::new();
    for s in asked {
        if s.len > 0 {
            for g in s.off / G..(s.off + s.len).div_ceil(G).min(groups_of(len)) {
                w.insert(g);
            }
        }
    }
    w
}

fn bytes_of(gs: &BTreeSet<u64>, len: u64) -> u64 {
    gs.iter().map(|&g| group_end(g, len) - g * G).sum()
}

/// A plain tracker of the scheduler's byte accounting, written independently of the checkers: the asserts of the test.
struct Tracker {
    striped: bool,
    len: u64,
    wanted: BTreeSet<u64>,
    done: BTreeSet<u64>,
    q: u64,
    a: [u64; 4],
    in_assign: [bool; 4],
    pending_steal: Option<(usize, u64)>,
    evicted: [bool; 4],
}

impl Tracker {
    fn conserved(&self) -> bool {
        let verified_wanted: BTreeSet<u64> = self.wanted.intersection(&self.done).copied().collect();
        self.q + self.a.iter().sum::<u64>() + bytes_of(&verified_wanted, self.len) == bytes_of(&self.wanted, self.len)
    }
}

impl Rec2 {
    /// Record one run of a finished simulation.
    fn record(&mut self, sim: &Sim, ranges: &[Span], ver0: &[(u64, u64)], slots: &[u32], badroot: bool) {
        self.run += 1;
        let r = self.run;
        let len = sim.length;
        let ws = |l: &[(u64, u64)]| {
            l.iter()
                .map(|(a, b)| format!("[{a},{b}]"))
                .collect::<Vec<_>>()
                .join(",")
        };
        let want: Vec<(u64, u64)> = ranges.iter().map(|s| (s.off, s.len)).collect();
        let provs = slots.iter().map(u32::to_string).collect::<Vec<_>>().join(",");
        writeln!(
            self.out,
            "{{\"t\":\"vs\",\"op\":\"run\",\"run\":{r},\"len\":{len},\"want\":[{}],\"ver\":[{}],\"provs\":[{provs}],\"badroot\":{}}}",
            ws(&want),
            ws(ver0),
            u8::from(badroot)
        )
        .unwrap();

        // The plain tracker.
        let wanted = wanted_groups(len, ranges);
        let mut done: BTreeSet<u64> = BTreeSet::new();
        for &(a, b) in ver0 {
            for g in a / G..b.div_ceil(G) {
                done.insert(g);
            }
        }
        let mut tr = Tracker {
            striped: false,
            len,
            wanted: wanted.clone(),
            done,
            q: 0,
            a: [0; 4],
            in_assign: [false; 4],
            pending_steal: None,
            evicted: [false; 4],
        };
        let slot_of = |p: Provider| {
            slots
                .iter()
                .position(|&x| x == p.0)
                .expect("event of an unknown provider")
        };
        for (now, t) in &sim.rec.traces {
            let (ms, ns) = (*now / MS, *now % MS);
            match *t {
                Trace::FetchStart {
                    wanted: w,
                    providers,
                    striped,
                } => {
                    let missing: BTreeSet<u64> = wanted.difference(&tr.done).copied().collect();
                    assert_eq!(
                        w,
                        bytes_of(&missing, len),
                        "run {r}: the fetch wants its missing bytes, exactly once"
                    );
                    tr.striped = striped;
                    tr.q = if striped { w } else { 0 };
                    tr.a[0] = if striped { 0 } else { w };
                    for i in 0..usize::from(providers) {
                        tr.in_assign[i] = true;
                    }
                    assert!(tr.conserved() || !striped, "run {r}: start");
                    self.runs_with.resumes += u32::from(!ver0.is_empty());
                    self.runs_with.non_striped += u32::from(!striped);
                    writeln!(
                        self.out,
                        "{{\"t\":\"vs\",\"op\":\"start\",\"run\":{r},\"ms\":{ms},\"ns\":{ns},\"wanted\":{w},\"prov\":{providers},\"striped\":{}}}",
                        u8::from(striped)
                    )
                    .unwrap();
                }
                Trace::TopUp {
                    provider,
                    bytes,
                    target,
                } => {
                    let p = slot_of(provider);
                    assert!(
                        tr.in_assign[p] && !tr.evicted[p],
                        "run {r}: work for a provider that holds no share"
                    );
                    if let Some((to, b)) = tr.pending_steal.take() {
                        assert!(to == p && b == bytes, "run {r}: the tail of a steal goes to the thief");
                    } else {
                        assert!(bytes <= tr.q, "run {r}: more taken than queued");
                        tr.q -= bytes;
                        self.runs_with.tail_topups += u32::from(tr.q < 4 * 1_048_576 * 4);
                    }
                    tr.a[p] += bytes;
                    self.runs_with.topups += 1;
                    assert!(tr.conserved(), "run {r}: top-up broke the conservation");
                    writeln!(
                        self.out,
                        "{{\"t\":\"vs\",\"op\":\"topup\",\"run\":{r},\"ms\":{ms},\"ns\":{ns},\"p\":{p},\"bytes\":{bytes},\"tgt\":{target}}}"
                    )
                    .unwrap();
                }
                Trace::Steal { from, to, bytes } => {
                    let (f, t2) = (slot_of(from), slot_of(to));
                    assert!(f != t2, "run {r}: a provider stole from itself");
                    assert!(
                        tr.in_assign[f] && tr.in_assign[t2],
                        "run {r}: steal between non-holders"
                    );
                    assert!(tr.a[f] >= bytes, "run {r}: stole more than the victim held");
                    tr.a[f] -= bytes;
                    tr.pending_steal = (bytes > 0).then_some((t2, bytes));
                    self.runs_with.steals += 1;
                    self.runs_with.steals_moving += u32::from(bytes > 0);
                    writeln!(
                        self.out,
                        "{{\"t\":\"vs\",\"op\":\"steal\",\"run\":{r},\"ms\":{ms},\"ns\":{ns},\"from\":{f},\"to\":{t2},\"bytes\":{bytes}}}"
                    )
                    .unwrap();
                }
                Trace::Verified {
                    provider,
                    off,
                    len: l,
                    ahead,
                } => {
                    let p = slot_of(provider);
                    assert_eq!(off % G, 0, "run {r}: a verified group starts on a group boundary");
                    let g = off / G;
                    assert_eq!(l, group_end(g, len) - off, "run {r}: a verified group is a whole group");
                    assert!(tr.wanted.contains(&g), "run {r}: verified a group nobody wanted");
                    assert!(tr.done.insert(g), "run {r}: group {g} verified twice");
                    if tr.striped {
                        assert!(tr.a[p] >= l, "run {r}: verified bytes the provider was not assigned");
                        tr.a[p] -= l;
                        assert!(tr.conserved(), "run {r}: verification broke the conservation");
                    }
                    writeln!(
                        self.out,
                        "{{\"t\":\"vs\",\"op\":\"ver\",\"run\":{r},\"ms\":{ms},\"ns\":{ns},\"p\":{p},\"off\":{off},\"len\":{l},\"ahead\":{}}}",
                        u8::from(ahead)
                    )
                    .unwrap();
                }
                Trace::Liar { provider, .. } => {
                    let p = slot_of(provider);
                    assert!(tr.in_assign[p], "run {r}: a provider that holds no share lied");
                    tr.q += tr.a[p];
                    tr.a[p] = 0;
                    tr.in_assign[p] = false;
                    tr.evicted[p] = true;
                    self.runs_with.liars += 1;
                    assert!(
                        tr.conserved() || !tr.striped,
                        "run {r}: eviction broke the conservation"
                    );
                    writeln!(
                        self.out,
                        "{{\"t\":\"vs\",\"op\":\"liar\",\"run\":{r},\"ms\":{ms},\"ns\":{ns},\"p\":{p}}}"
                    )
                    .unwrap();
                }
                _ => {}
            }
        }
        let res = if sim.rec.complete() {
            assert!(
                tr.wanted.is_subset(&tr.done),
                "run {r}: complete with a wanted group missing"
            );
            "complete"
        } else {
            match sim.rec.failed() {
                Some(FailReason::EveryProviderLied) => {
                    self.runs_with.all_lied += 1;
                    "liar"
                }
                Some(FailReason::NoProvider) => {
                    self.runs_with.no_provider += 1;
                    "noprov"
                }
                Some(FailReason::BadRoot) => {
                    self.runs_with.bad_root += 1;
                    "badroot"
                }
                other => panic!("run {r}: ended with {other:?}"),
            }
        };
        if res == "complete"
            && sim
                .rec
                .traces
                .iter()
                .all(|(_, t)| !matches!(t, Trace::FetchStart { .. }))
        {
            self.runs_with.nothing_missing += 1;
        }
        assert!(
            sim.rec
                .events
                .iter()
                .filter(|(_, e)| matches!(e, Event::Complete | Event::Failed(_)))
                .count()
                == 1,
            "run {r}: the fetch ends once"
        );
        writeln!(
            self.out,
            "{{\"t\":\"vs\",\"op\":\"end\",\"run\":{r},\"res\":\"{res}\"}}"
        )
        .unwrap();
    }
}

fn verified0(st: &ClientStore) -> Vec<(u64, u64)> {
    st.verified.iter().map(|r| (r.start, r.end)).collect()
}

/// Run a simulation with `ranges` and `provs` (indices into its providers) and record it.
fn go(rec: &mut Rec2, mut sim: Sim, ranges: &[Span], provs: &[u32], limit_s: u64) -> Sim {
    let ver0 = verified0(&sim.store);
    let list: Vec<Provider> = provs.iter().map(|&i| Provider(i)).collect();
    sim.start_with(ranges, &list, None);
    sim.run(limit_s);
    let mut slots: Vec<u32> = Vec::new();
    for &p in provs {
        if slots.len() < 4 && !slots.contains(&p) {
            slots.push(p);
        }
    }
    let badroot = sim.rec.failed() == Some(FailReason::BadRoot);
    rec.record(&sim, ranges, &ver0, &slots, badroot);
    sim
}

fn all(n: u32) -> Vec<u32> {
    (0..n).collect()
}

fn cfgs(store: &PStore, rates: &[u64]) -> Vec<ProvCfg> {
    rates.iter().map(|&r| ProvCfg::new(store.clone(), r)).collect()
}

#[test]
fn the_scheduler_runs_are_recorded_and_conserve_the_work() {
    let mut rec = Rec2::default();

    // One provider: the work is not striped.
    let store = PStore::random(101, 3 * (1 << 20) + 123);
    let sim = go(
        &mut rec,
        Sim::new(cfgs(&store, &[2000]), ClientStore::new()),
        &[],
        &all(1),
        120,
    );
    sim.store.assert_verified_is_true(store.content());

    // Uniform providers, the whole value: tail shrink at the end.
    let store = PStore::random(102, 8 << 20);
    for n in [2u32, 3, 4] {
        let sim = go(
            &mut rec,
            Sim::new(cfgs(&store, &vec![3000; n as usize]), ClientStore::new()),
            &[],
            &all(n),
            200,
        );
        sim.store.assert_verified_is_true(store.content());
    }

    // Unequal speeds: fast, medium, slow, very slow.
    let store = PStore::random(103, 12 << 20);
    let sim = go(
        &mut rec,
        Sim::new(cfgs(&store, &[4000, 2500, 1500, 800]), ClientStore::new()),
        &[],
        &all(4),
        300,
    );
    sim.store.assert_verified_is_true(store.content());

    // A provider that goes silent with the session up is robbed after two seconds, whatever it still holds.
    let store = PStore::random(104, 3 << 20);
    let sim = Sim::new(
        vec![
            ProvCfg::new(store.clone(), 3000),
            ProvCfg::new(store.clone(), 3000).stall_after(1_400_000),
        ],
        ClientStore::new(),
    );
    let sim = go(&mut rec, sim, &[], &all(2), 200);
    sim.store.assert_verified_is_true(store.content());

    // Two providers go silent: two idle ones rob them one after the other, and the one robbed first (just handed work, its
    // last granule old) must not look idle to the second.
    let store = PStore::random(110, 5 << 20);
    for (c, d) in [(600_000, 700_000), (300_000, 1_200_000), (0, 900_000)] {
        let sim = Sim::new(
            vec![
                ProvCfg::new(store.clone(), 3000),
                ProvCfg::new(store.clone(), 3000),
                ProvCfg::new(store.clone(), 3000).stall_after(c),
                ProvCfg::new(store.clone(), 3000).stall_after(d),
            ],
            ClientStore::new(),
        );
        let sim = go(&mut rec, sim, &[], &all(4), 300);
        sim.store.assert_verified_is_true(store.content());
    }

    // The same with fast providers that finished long before: the first thief was idle for over two seconds when it was
    // handed work, and the second must not rob it.
    let store = PStore::random(111, 3 << 20);
    for (stall_c, stall_d) in [(450_000, 450_000), (400_000, 500_000)] {
        let sim = Sim::new(
            vec![
                ProvCfg::new(store.clone(), 6000),
                ProvCfg::new(store.clone(), 6000),
                ProvCfg::new(store.clone(), 600).stall_after(stall_c),
                ProvCfg::new(store.clone(), 600).stall_after(stall_d),
            ],
            ClientStore::new(),
        );
        let sim = go(&mut rec, sim, &[], &all(4), 300);
        sim.store.assert_verified_is_true(store.content());
    }

    // A provider dropped mid transfer; its work is taken by the others.
    let store = PStore::random(105, 6 << 20);
    let mut sim = Sim::new(cfgs(&store, &[2000, 2000, 2000]), ClientStore::new());
    let ver0 = verified0(&sim.store);
    sim.start();
    assert!(sim.run_until(60 * SEC, |s| s.store.covered() >= 1 << 20));
    sim.cut(1);
    sim.provs[1].up = false;
    sim.run(300);
    rec.record(&sim, &[], &ver0, &[0, 1, 2], false);
    sim.store.assert_verified_is_true(store.content());

    // A liar among honest providers: evicted, its share back in the queue, nothing it sent stored.
    let honest = PStore::random(106, 5 << 20);
    for lie in [Lie::EveryGroup, Lie::FlipByte(3 * G + 5), Lie::BadPair(0)] {
        let sim = Sim::new(
            vec![
                ProvCfg::new(honest.clone(), 2500),
                ProvCfg::new(honest.lying(lie), 2500),
                ProvCfg::new(honest.clone(), 2500),
            ],
            ClientStore::new(),
        );
        let sim = go(&mut rec, sim, &[], &all(3), 300);
        sim.store.assert_verified_is_true(honest.content());
        assert!(sim.rec.complete());
    }

    // Every provider lies: failed with EveryProviderLied, no bad byte stored.
    let sim = Sim::new(
        vec![
            ProvCfg::new(honest.lying(Lie::EveryGroup), 2000),
            ProvCfg::new(honest.lying(Lie::FlipByte(5)), 2000),
            ProvCfg::new(honest.lying(Lie::EveryGroup), 2000),
        ],
        ClientStore::new(),
    );
    let sim = go(&mut rec, sim, &[], &all(3), 120);
    assert_eq!(sim.rec.failed(), Some(FailReason::EveryProviderLied));
    sim.store.assert_matches(honest.content());
    // ... and a single lying provider.
    let sim = go(
        &mut rec,
        Sim::new(
            vec![ProvCfg::new(honest.lying(Lie::FlipByte(77)), 1000)],
            ClientStore::new(),
        ),
        &[],
        &all(1),
        120,
    );
    assert_eq!(sim.rec.failed(), Some(FailReason::EveryProviderLied));

    // Resume: the store holds verified groups; ranges are asked unordered, overlapping and not group aligned.
    let store = PStore::random(107, 40 * G as usize + 777);
    let seeded = |rs: &[std::ops::Range<u64>]| ClientStore::seeded(store.content(), rs);
    let sim = go(
        &mut rec,
        Sim::new(
            cfgs(&store, &[3000, 3000, 2000]),
            seeded(&[0..2 * G, 5 * G..9 * G, 15 * G..20 * G]),
        ),
        &[],
        &all(3),
        200,
    );
    sim.store.assert_verified_is_true(store.content());
    let ranges = [
        Span {
            off: 30 * G + 5,
            len: 3 * G,
        },
        Span { off: 4 * G, len: 1 },
        Span {
            off: 3 * G + 9,
            len: 2 * G,
        },
        Span { off: 31 * G, len: G },
        Span { off: 12 * G, len: 0 },
    ];
    let sim = go(
        &mut rec,
        Sim::new(cfgs(&store, &[3000, 1000]), seeded(&[8 * G..10 * G, 32 * G..33 * G])),
        &ranges,
        &all(2),
        200,
    );
    assert!(sim.rec.complete());

    // Six providers, one named twice: the first four distinct ones are used.
    let store = PStore::random(108, 2 << 20);
    let sim = Sim::new(cfgs(&store, &[2000; 6]), ClientStore::new());
    go(&mut rec, sim, &[], &[2, 2, 0, 1, 3, 4, 5], 200);

    // No provider; a wrong root for an empty value; everything already verified.
    go(&mut rec, Sim::uniform(1, 5000, 100), &[], &[], 5);
    let empty = PStore::bytes(Vec::new());
    go(
        &mut rec,
        Sim::new(cfgs(&empty, &[100]), ClientStore::new()),
        &[],
        &all(1),
        5,
    );
    let mut bad = Sim::new(cfgs(&empty, &[100]), ClientStore::new());
    bad.root = [9; 32];
    go(&mut rec, bad, &[], &all(1), 5);
    let store = PStore::random(109, 100_000);
    #[allow(clippy::single_range_in_vec_init, reason = "one verified interval")]
    let full = ClientStore::seeded(store.content(), &[0..100_000]);
    go(&mut rec, Sim::new(cfgs(&store, &[100]), full), &[], &all(1), 5);

    // Seeded random worlds.
    let mut rng = SplitMix64::traced(0x5C4ED);
    for seed in 0..48u64 {
        let mut next = |n: u64| rng.next_u64() % n;
        let nprov = 1 + next(4) as u32;
        let len = 1 + next(6 << 20) as usize;
        let store = PStore::random(200 + seed, len);
        let rates: Vec<u64> = (0..nprov).map(|_| 400 + next(5000)).collect();
        let mut cs: Vec<ProvCfg> = Vec::new();
        for (i, &r) in rates.iter().enumerate() {
            let mut c = ProvCfg::new(
                if i > 0 && next(4) == 0 {
                    store.lying(Lie::EveryGroup)
                } else {
                    store.clone()
                },
                r,
            );
            if next(3) == 0 {
                c = c.stall_after(next(2 << 20));
            }
            cs.push(c);
        }
        // Group aligned verified pieces and a few ranges.
        let ng = groups_of(len as u64);
        let mut seeded_rs: Vec<std::ops::Range<u64>> = Vec::new();
        for _ in 0..next(3) {
            let a = next(ng);
            let b = (a + 1 + next(6)).min(ng);
            seeded_rs.push(a * G..(b * G).min(len as u64));
        }
        seeded_rs.sort_by_key(|r| r.start);
        seeded_rs.dedup_by(|b, a| {
            b.start <= a.end && {
                a.end = a.end.max(b.end);
                true
            }
        });
        let mut ranges = Vec::new();
        for _ in 0..next(4) {
            let off = next(len as u64);
            ranges.push(Span {
                off,
                len: next((len as u64 - off).max(1) + 1).min(len as u64 - off),
            });
        }
        let st = ClientStore::seeded(store.content(), &seeded_rs);
        let sim = Sim::new(cs, st);
        let provs: Vec<u32> = all(nprov);
        let ver0 = verified0(&sim.store);
        let list: Vec<Provider> = provs.iter().map(|&i| Provider(i)).collect();
        let mut sim = sim;
        sim.start_with(&ranges, &list, None);
        // A stalled and lying world may not finish; run to a long limit and record what happened if it did.
        if sim.run_until(600 * SEC, |s| s.fetch.is_done()) {
            let ok = sim.rec.complete() || sim.rec.failed() == Some(FailReason::EveryProviderLied);
            if ok {
                rec.record(&sim, &ranges, &ver0, &provs, false);
            }
        }
    }

    let c = &rec.runs_with;
    eprintln!("values_sched trace coverage: {c:?}");
    assert!(c.topups > 20 && c.tail_topups > 0, "{c:?}");
    assert!(c.steals_moving > 0, "no steal moved bytes: {c:?}");
    assert!(c.liars > 0 && c.all_lied > 0, "{c:?}");
    assert!(
        c.resumes > 0 && c.non_striped > 0 && c.no_provider > 0 && c.bad_root > 0 && c.nothing_missing > 0,
        "{c:?}"
    );

    if let Some(dir) = std::env::var_os("PINC_TRACE_DIR") {
        std::fs::write(std::path::Path::new(&dir).join("values_sched.ndjson"), rec.out).unwrap();
    }
}
