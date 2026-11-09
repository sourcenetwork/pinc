//! Trace generation for the multi-provider value fetch: real runs of `Fetch` against real `Server`s through the
//! in-memory harness, recorded as ndjson (`values_sys.ndjson`) for the TLA+ trace check (`TraceValuesSys.tla`) and the
//! Lean replay (`Vinc.TraceValuesSys`).
//!
//! A run is one fetch: a `start` line with its parameters (the value in groups, the wanted groups, the groups the store
//! held, the providers named, the providers that lie, the deadline), then one line per event and per trace record the
//! fetcher reported, in the order it reported them (`Rec::log`), then an `end` line. The lines the checkers use:
//!
//! - `req`: a request went out; the groups it asks for are decoded from the REQ bytes the provider received.
//! - `ver`: a group verified and reached the store; `snap` is the store's verified set (in groups) right after the
//!   commit, `genuine` says the bytes written equal the true value (checked against the content after the run).
//! - `held`, `rel`, `liar`, `dial`, `retry`, `topup`, `steal`, `stall`, `proofrej`, `fstart`: the trace records.
//! - `ev`: an application event (`R` readable, `C` complete, `F` failed with a reason).
//!
//! Times are in microseconds, rounded up, so a deadline that passed by a nanosecond is later than the deadline.
//!
//! Every scenario is asserted here, so the test is meaningful without the proof tools. The trace is written to
//! `values_sys.ndjson` in the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
//!
//! The scenarios: 1, 2, 3 and 4 providers; a provider dropped mid-transfer (and one that returns); a slow provider
//! whose work is stolen; a liar among honest providers (bad group, bad proof); every provider lying; a restart in the
//! middle (the store survives, the new fetch asks only for what is missing); loss and reordering with write-through;
//! the deadline; a store that refuses; an empty value (right and wrong root); no provider; a fetch of ranges over a
//! store with holes.
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
    clippy::single_range_in_vec_init,
    unreachable_pub
)]

mod values_support;

use std::fmt::Write as _;
use std::ops::Range;

use values_support::*;
use vinc_values::session::Provider;
use vinc_values::span::Span;
use vinc_values::trace::{Event, FailReason, Release, Trace};
use vinc_values::wire::Req;

/// What the checkers need to know about a run besides what the fetcher reports.
struct Meta {
    /// The value length in bytes.
    len: u64,
    /// The wanted ranges as asked (empty: the whole value).
    ranges: Vec<Span>,
    /// The providers named, 0-based.
    listed: Vec<u32>,
    /// The providers whose store lies, 0-based.
    liars: Vec<u32>,
    /// The deadline in nanoseconds, if any.
    deadline: Option<u64>,
    /// The groups the store held when the run started.
    ver0: Vec<Range<u64>>,
    /// Whether the run was cut before its end (a restart), so no final event is expected.
    cut: bool,
    /// The root is not the hash of the empty value although the value is empty.
    bad_root: bool,
}

fn groups_of(len: u64) -> u64 {
    len.div_ceil(GROUP)
}

fn wanted(m: &Meta) -> Vec<u64> {
    let g = groups_of(m.len);
    if m.ranges.is_empty() {
        return (0..g).collect();
    }
    let mut out: Vec<u64> = Vec::new();
    for s in &m.ranges {
        if s.len == 0 {
            continue;
        }
        let (a, b) = (s.off / GROUP, (s.off + s.len).div_ceil(GROUP).min(g));
        out.extend(a..b);
    }
    out.sort_unstable();
    out.dedup();
    out
}

fn list(v: impl IntoIterator<Item = u64>) -> String {
    let mut s = String::from("[");
    for (i, x) in v.into_iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, "{x}").unwrap();
    }
    s.push(']');
    s
}

/// A verified set as `[[a,b),...]` pairs of groups.
fn pairs(ranges: &[Range<u64>]) -> String {
    let mut sorted: Vec<(u64, u64)> = ranges
        .iter()
        .map(|r| (r.start / GROUP, r.end.div_ceil(GROUP)))
        .collect();
    sorted.sort_unstable();
    let mut merged: Vec<(u64, u64)> = Vec::new();
    for (a, b) in sorted {
        match merged.last_mut() {
            Some(l) if a <= l.1 => l.1 = l.1.max(b),
            _ => merged.push((a, b)),
        }
    }
    let mut s = String::from("[");
    for (i, (a, b)) in merged.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, "[{a},{b}]").unwrap();
    }
    s.push(']');
    s
}

fn prov(p: Provider) -> u64 {
    u64::from(p.0) + 1
}

fn why(r: FailReason) -> &'static str {
    match r {
        FailReason::NoProvider => "NoProvider",
        FailReason::EveryProviderLied => "EveryProviderLied",
        FailReason::Deadline => "Deadline",
        FailReason::Store => "Store",
        FailReason::BadRoot => "BadRoot",
    }
}

/// Append the lines of one finished run.
fn dump(out: &mut String, id: u32, sim: &Sim, m: &Meta) {
    let content = sim.provs[0].cfg.store.content().clone();
    let want = wanted(m);
    let first = m.ranges.first().map_or(0, |s| s.off / GROUP);
    writeln!(
        out,
        "{{\"t\":\"vsys\",\"op\":\"start\",\"run\":{id},\"g\":{},\"want\":{},\"ver0\":{},\"np\":{},\"listed\":{},\"liars\":{},\"dl\":{},\"empty\":{},\"badroot\":{},\"first\":{first}}}",
        groups_of(m.len),
        list(want.iter().copied()),
        list(m.ver0.iter().flat_map(|r| (r.start / GROUP)..r.end.div_ceil(GROUP))),
        sim.provs.len(),
        list(m.listed.iter().map(|p| u64::from(*p) + 1)),
        list(m.liars.iter().map(|p| u64::from(*p) + 1)),
        m.deadline.map_or(-1, |d| i64::try_from(d / 1000).unwrap()),
        u8::from(m.len == 0),
        u8::from(m.bad_root),
    )
    .unwrap();
    // The k-th verified record is the k-th commit of the store.
    let mut commits = sim.store.commits.iter();
    let mut seen: Vec<Range<u64>> = m.ver0.clone();
    let line = |out: &mut String, now: u64, body: String| {
        writeln!(
            out,
            "{{\"t\":\"vsys\",\"op\":\"rec\",\"run\":{id},\"now\":{},{body}}}",
            now.div_ceil(1000)
        )
        .unwrap();
    };
    for item in &sim.rec.log {
        match *item {
            Logged::Tr(now, t) => match t {
                Trace::FetchStart {
                    wanted: _,
                    providers,
                    striped,
                } => line(
                    out,
                    now,
                    format!("\"k\":\"fstart\",\"n\":{providers},\"striped\":{}", u8::from(striped)),
                ),
                Trace::Dial(p) => line(out, now, format!("\"k\":\"dial\",\"p\":{}", prov(p))),
                Trace::Requested { provider, stream, .. } => {
                    let reqs = &sim.provs[provider.0 as usize].sess.reqs;
                    let bytes = reqs.get(&stream).expect("the provider received the request");
                    let (req, _) = Req::parse(bytes).expect("a well-formed request");
                    let mut gs: Vec<u64> = Vec::new();
                    for s in req.ranges() {
                        gs.extend((s.off / GROUP)..(s.off + s.len).div_ceil(GROUP));
                    }
                    line(
                        out,
                        now,
                        format!("\"k\":\"req\",\"p\":{},\"groups\":{}", prov(provider), list(gs)),
                    );
                }
                Trace::TopUp { provider, .. } => line(out, now, format!("\"k\":\"topup\",\"p\":{}", prov(provider))),
                Trace::Steal { from, to, .. } => {
                    line(
                        out,
                        now,
                        format!("\"k\":\"steal\",\"from\":{},\"to\":{}", prov(from), prov(to)),
                    );
                }
                Trace::Verified {
                    provider,
                    off,
                    len,
                    ahead,
                } => {
                    let c = commits.next().expect("a verified record has a commit");
                    assert_eq!(*c, off..off + len, "the commit is the verified group");
                    seen.push(c.clone());
                    let genuine = sim.store.read(off, len).as_slice() == content.bytes(off, len).as_slice();
                    line(
                        out,
                        now,
                        format!(
                            "\"k\":\"ver\",\"p\":{},\"g\":{},\"ahead\":{},\"genuine\":{},\"snap\":{}",
                            prov(provider),
                            off / GROUP,
                            u8::from(ahead),
                            u8::from(genuine),
                            pairs(&seen)
                        ),
                    );
                }
                Trace::Held { off } => line(out, now, format!("\"k\":\"held\",\"g\":{}", off / GROUP)),
                Trace::Released { off, why } => {
                    let w = match why {
                        Release::Buffered => "buffered",
                        Release::Tail => "tail",
                        Release::Granules => "granules",
                        Release::Timeout => "timeout",
                        Release::Done => "done",
                    };
                    line(out, now, format!("\"k\":\"rel\",\"g\":{},\"why\":\"{w}\"", off / GROUP));
                }
                Trace::Liar { provider, .. } => line(out, now, format!("\"k\":\"liar\",\"p\":{}", prov(provider))),
                Trace::Retry(p) => line(out, now, format!("\"k\":\"retry\",\"p\":{}", prov(p))),
                Trace::StallRedial { .. } => line(out, now, "\"k\":\"stall\"".to_string()),
                Trace::ProofRejected { .. } => line(out, now, "\"k\":\"proofrej\"".to_string()),
                Trace::Serving { .. } | Trace::Refused { .. } | Trace::ProofSent { .. } => {}
            },
            Logged::Ev(now, e) => match e {
                Event::Readable { off, len } => {
                    line(
                        out,
                        now,
                        format!("\"k\":\"ev\",\"e\":\"R\",\"g\":{},\"len\":{len}", off / GROUP),
                    );
                }
                Event::Complete => line(out, now, "\"k\":\"ev\",\"e\":\"C\"".to_string()),
                Event::Failed(r) => line(out, now, format!("\"k\":\"ev\",\"e\":\"F\",\"why\":\"{}\"", why(r))),
            },
        }
    }
    assert!(commits.next().is_none(), "every commit has a verified record");
    writeln!(
        out,
        "{{\"t\":\"vsys\",\"op\":\"end\",\"run\":{id},\"done\":{},\"snap\":{}}}",
        u8::from(!m.cut),
        pairs(
            &sim.store
                .commits
                .iter()
                .cloned()
                .chain(m.ver0.iter().cloned())
                .collect::<Vec<_>>()
        )
    )
    .unwrap();
}

fn meta(sim: &Sim, ranges: &[Span], provs: &[Provider], liars: &[u32], deadline: Option<u64>) -> Meta {
    Meta {
        len: sim.length,
        ranges: ranges.to_vec(),
        listed: provs.iter().map(|p| p.0).collect(),
        liars: liars.to_vec(),
        deadline,
        ver0: sim.store.verified.iter().collect(),
        cut: false,
        bad_root: false,
    }
}

/// Run `sim` to its end over `ranges` and `provs`, check the store holds only the truth, record the run.
fn run(
    out: &mut String,
    id: &mut u32,
    mut sim: Sim,
    ranges: &[Span],
    liars: &[u32],
    deadline: Option<u64>,
    limit: u64,
) -> Sim {
    let provs = sim.all_providers();
    let m = meta(&sim, ranges, &provs, liars, deadline);
    sim.start_with(ranges, &provs, deadline);
    sim.run(limit);
    finish(out, id, sim, m)
}

fn finish(out: &mut String, id: &mut u32, sim: Sim, m: Meta) -> Sim {
    // Every written byte is a byte of the true value, whatever happened.
    sim.store.assert_matches(sim.provs[0].cfg.store.content());
    sim.store.assert_verified_is_true(sim.provs[0].cfg.store.content());
    // Exactly one final event, and nothing after it.
    let finals: Vec<usize> = sim
        .rec
        .log
        .iter()
        .enumerate()
        .filter(|(_, l)| matches!(l, Logged::Ev(_, Event::Complete | Event::Failed(_))))
        .map(|(i, _)| i)
        .collect();
    assert_eq!(finals.len(), usize::from(!m.cut), "one final event");
    if let Some(i) = finals.first() {
        assert_eq!(*i + 1, sim.rec.log.len(), "nothing is reported after the final event");
    }
    *id += 1;
    dump(out, *id, &sim, &m);
    sim
}

fn uniform(n: usize, groups: usize, rate: u64, seed: u64) -> Sim {
    let store = PStore::random(seed, groups * GROUP as usize - 5);
    Sim::new(
        (0..n).map(|_| ProvCfg::new(store.clone(), rate)).collect(),
        ClientStore::new(),
    )
}

#[test]
fn value_fetch_traces() {
    let mut out = String::new();
    let mut id = 0u32;
    let g = GROUP as usize;

    // 1, 2, 3 and 4 providers.
    for (n, seed) in [(1, 101), (2, 102), (3, 103), (4, 104)] {
        let sim = run(&mut out, &mut id, uniform(n, 14, 3000, seed), &[], &[], None, 120);
        assert!(sim.rec.complete(), "{n} providers");
        assert_eq!(sim.store.covered(), sim.length);
    }
    // A bigger value over four providers: the queue, the targets and the steals get work to do.
    let sim = run(&mut out, &mut id, uniform(4, 160, 2500, 105), &[], &[], None, 300);
    assert!(sim.rec.complete());

    // A provider dropped mid-transfer for good: the others finish; a single provider that returns resumes.
    let store = PStore::random(106, 40 * g);
    let mut sim = Sim::new(
        vec![
            ProvCfg::new(store.clone(), 2000),
            ProvCfg::new(store.clone(), 2000),
            ProvCfg::new(store.clone(), 2000),
        ],
        ClientStore::new(),
    );
    let provs = sim.all_providers();
    let m = meta(&sim, &[], &provs, &[], None);
    sim.start();
    assert!(sim.run_until(60 * SEC, |s| s.store.covered() >= 8 * GROUP));
    sim.cut(1);
    sim.provs[1].up = false;
    sim.run(300);
    assert!(sim.rec.complete());
    assert!(
        sim.rec
            .traces
            .iter()
            .any(|(_, t)| matches!(t, Trace::Steal { from, .. } if from.0 == 1))
    );
    finish(&mut out, &mut id, sim, m);

    let store = PStore::random(107, 30 * g);
    let mut sim = Sim::new(vec![ProvCfg::new(store.clone(), 1500)], ClientStore::new());
    let provs = sim.all_providers();
    let m = meta(&sim, &[], &provs, &[], None);
    sim.start();
    assert!(sim.run_until(60 * SEC, |s| s.store.covered() >= 6 * GROUP));
    sim.cut(0);
    let down = sim.now + 3 * SEC;
    sim.run_until(down, |_| false);
    sim.revive(0);
    sim.run(300);
    assert!(sim.rec.complete());
    assert!(sim.rec.traces.iter().any(|(_, t)| matches!(t, Trace::Retry(_))));
    finish(&mut out, &mut id, sim, m);

    // A slow provider: it goes silent, the other takes its work.
    let store = PStore::random(108, 60 * g);
    let sim = Sim::new(
        vec![
            ProvCfg::new(store.clone(), 3000).stall_after(5 * GROUP),
            ProvCfg::new(store.clone(), 3000),
        ],
        ClientStore::new(),
    );
    let sim = run(&mut out, &mut id, sim, &[], &[], None, 300);
    assert!(sim.rec.complete());
    assert!(sim.rec.traces.iter().any(|(_, t)| matches!(t, Trace::Steal { .. })));

    // A silent provider that is robbed once it has been idle long enough, and a reconnecting thief.
    let store = PStore::random(109, 3 << 20);
    let mut sim = Sim::new(
        vec![
            ProvCfg::new(store.clone(), 1000).stall_after(0),
            ProvCfg::new(store.clone(), 8000),
        ],
        ClientStore::new(),
    );
    let provs = sim.all_providers();
    let m = meta(&sim, &[], &provs, &[], None);
    sim.start();
    sim.run_until(500 * MS, |_| false);
    sim.cut(1);
    sim.revive(1);
    sim.run(300);
    assert!(sim.rec.complete());
    finish(&mut out, &mut id, sim, m);

    // A liar among honest providers (a bad group, a bad proof, a bad byte), and every provider lying.
    let honest = PStore::random(110, 128 * g);
    for (lie, seed_rate) in [
        (Lie::EveryGroup, 6000),
        (Lie::BadPair(0), 6000),
        (Lie::FlipByte(70 * GROUP + 3), 6000),
    ] {
        let sim = Sim::new(
            vec![
                ProvCfg::new(honest.clone(), 3000),
                ProvCfg::new(honest.lying(lie), seed_rate),
            ],
            ClientStore::new(),
        );
        let sim = run(&mut out, &mut id, sim, &[], &[1], None, 200);
        assert!(sim.rec.complete(), "{:?}", sim.rec.failed());
        assert!(
            sim.rec.traces.iter().any(|(_, t)| matches!(t, Trace::Liar { .. })),
            "{lie:?}"
        );
    }
    let sim = Sim::new(
        vec![
            ProvCfg::new(honest.clone(), 3000),
            ProvCfg::new(honest.lying(Lie::EveryGroup), 5000),
            ProvCfg::new(honest.lying(Lie::BadPair(0)), 5000),
            ProvCfg::new(honest.clone(), 1000),
        ],
        ClientStore::new(),
    );
    let sim = run(&mut out, &mut id, sim, &[], &[1, 2], None, 300);
    assert!(sim.rec.complete());
    for liars in [vec![0u32, 1], vec![0]] {
        let cfgs: Vec<_> = liars
            .iter()
            .map(|_| ProvCfg::new(honest.lying(Lie::FlipByte(5)), 3000))
            .collect();
        let sim = run(
            &mut out,
            &mut id,
            Sim::new(cfgs, ClientStore::new()),
            &[],
            &liars,
            None,
            100,
        );
        assert_eq!(sim.rec.failed(), Some(FailReason::EveryProviderLied));
    }

    // Restart in the middle: the store survives, the new fetch asks only for what is missing.
    let store = PStore::random(111, 50 * g);
    let mut sim = Sim::new(
        vec![ProvCfg::new(store.clone(), 2500), ProvCfg::new(store.clone(), 2500)],
        ClientStore::new(),
    );
    let provs = sim.all_providers();
    let mut m = meta(&sim, &[], &provs, &[], None);
    sim.start();
    assert!(sim.run_until(300 * SEC, |s| s.store.covered() >= 20 * GROUP));
    m.cut = true;
    let kept = std::mem::take(&mut sim.store);
    let first_commits = kept.commits.len();
    // The commits of the cut run belong to its trace; the survivor store keeps the verified set only.
    let mut cut_sim = sim;
    cut_sim.store = ClientStore {
        pieces: kept.pieces.clone(),
        verified: kept.verified.clone(),
        written: kept.written,
        fail_writes: false,
        commits: kept.commits.clone(),
    };
    finish(&mut out, &mut id, cut_sim, m);
    let have = kept.covered();
    assert!(first_commits > 0 && have < sim_len(&store));
    let mut survivor = ClientStore {
        pieces: kept.pieces,
        verified: kept.verified,
        written: 0,
        fail_writes: false,
        commits: Vec::new(),
    };
    survivor.commits.clear();
    let again = Sim::new(
        vec![ProvCfg::new(store.clone(), 2500), ProvCfg::new(store.clone(), 2500)],
        survivor,
    );
    let again = run(&mut out, &mut id, again, &[], &[], None, 300);
    assert!(again.rec.complete());
    let requested: u64 = again
        .rec
        .traces_of(|t| {
            if let Trace::Requested { bytes, .. } = t {
                Some(*bytes)
            } else {
                None
            }
        })
        .iter()
        .map(|x| x.1)
        .sum();
    assert!(requested <= sim_len(&store) - have + 2 * GROUP);

    // Ranges over a store with holes, and a store that holds everything.
    let store = PStore::random(112, 20 * g);
    let seeded = ClientStore::seeded(
        store.content(),
        &[0..2 * GROUP, 5 * GROUP..9 * GROUP, 15 * GROUP..20 * GROUP],
    );
    let sim = run(
        &mut out,
        &mut id,
        Sim::new(vec![ProvCfg::new(store.clone(), 4000)], seeded),
        &[],
        &[],
        None,
        60,
    );
    assert!(sim.rec.complete());
    let seeded = ClientStore::seeded(store.content(), &[0..20 * GROUP]);
    let sim = run(
        &mut out,
        &mut id,
        Sim::new(vec![ProvCfg::new(store.clone(), 100)], seeded),
        &[],
        &[],
        None,
        10,
    );
    assert!(sim.rec.complete());
    let ranges = [
        Span {
            off: 3 * GROUP + 5,
            len: 10,
        },
        Span {
            off: 12 * GROUP,
            len: 2 * GROUP + 1,
        },
    ];
    let sim = Sim::new(
        vec![ProvCfg::new(store.clone(), 4000), ProvCfg::new(store.clone(), 4000)],
        ClientStore::new(),
    );
    let sim = run(&mut out, &mut id, sim, &ranges, &[], None, 60);
    assert!(sim.rec.complete());

    // Loss and reordering: out-of-order groups verify against range proofs and are written through.
    let store = PStore::random(113, 160 * g);
    let sim = Sim::new(vec![ProvCfg::new(store, 6000).loss(30).reorder(4)], ClientStore::new());
    let sim = run(&mut out, &mut id, sim, &[], &[], None, 400);
    assert!(sim.rec.complete());
    assert!(
        sim.rec
            .traces
            .iter()
            .any(|(_, t)| matches!(t, Trace::Verified { ahead: true, .. })),
        "no group was written through"
    );

    // The deadline ends a fetch that cannot finish; a store that refuses ends it with Store.
    let store = PStore::random(114, 30 * g);
    let sim = Sim::new(vec![ProvCfg::new(store.clone(), 10)], ClientStore::new());
    let sim = run(&mut out, &mut id, sim, &[], &[], Some(3 * SEC), 60);
    assert_eq!(sim.rec.failed(), Some(FailReason::Deadline));
    let mut cs = ClientStore::new();
    cs.fail_writes = true;
    let sim = run(
        &mut out,
        &mut id,
        Sim::new(vec![ProvCfg::new(store.clone(), 1000)], cs),
        &[],
        &[],
        None,
        30,
    );
    assert_eq!(sim.rec.failed(), Some(FailReason::Store));

    // An empty value with its root completes; with another root it fails; no provider fails at once.
    let empty = PStore::bytes(Vec::new());
    let sim = run(
        &mut out,
        &mut id,
        Sim::new(vec![ProvCfg::new(empty.clone(), 100)], ClientStore::new()),
        &[],
        &[],
        None,
        5,
    );
    assert!(sim.rec.complete());
    let mut sim = Sim::new(vec![ProvCfg::new(empty, 100)], ClientStore::new());
    sim.root = [9; 32];
    let provs = sim.all_providers();
    let mut m = meta(&sim, &[], &provs, &[], None);
    m.bad_root = true;
    sim.start();
    sim.run(5);
    assert_eq!(sim.rec.failed(), Some(FailReason::BadRoot));
    finish(&mut out, &mut id, sim, m);
    let mut sim = uniform(1, 3, 100, 115);
    let m = meta(&sim, &[], &[], &[], None);
    sim.start_with(&[], &[], None);
    assert_eq!(sim.rec.failed(), Some(FailReason::NoProvider));
    finish(&mut out, &mut id, sim, m);

    assert!(id >= 20);
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("values_sys.ndjson"), &out).unwrap();
    }
}

fn sim_len(store: &PStore) -> u64 {
    store.len()
}
