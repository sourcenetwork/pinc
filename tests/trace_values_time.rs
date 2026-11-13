//! Trace generation for the time rules of the value fetch (HEAD_HOLD, STALL_REDIAL, the deadline and the failure
//! reasons): real runs of `Fetch` in the deterministic multi-provider simulation of `values_support`, recorded as ndjson
//! (`values_time.ndjson`) for the TLA+ trace check (`TraceValuesTime.tla`) and the Lean replay
//! (`Vinc/ValuesTimeTrace.lean`).
//!
//! A run is one fetch: a header line (`vtrun`: the first request offset, the wanted groups and wanted spans, the groups
//! the store held at the start, the deadline, the providers, what `start` reported) and then one line per step of the
//! simulation (`vt`): a step is one queued event of the simulation or one `on_timeout` call, at the time `now`, with the
//! time state of the fetch before and after (`Fetch::timers`, `poll_timeout`), the records and events the fetch emitted
//! in order (`tr`), and, for a timer call, the answers of the sessions the stall rules read (`ss`) and the two waits
//! computed from them (`w`: STALL_RTT, `lv`: STALL_LIVE, by a plain restatement of the rules written here, which the
//! Lean replay holds to the model of `stall.rs`). Times are u64 nanoseconds written as four 16-bit limbs. A step that
//! changed nothing the models read and emitted nothing is not written.
//!
//! The scenarios are the ones of `values_rules` (first granule held and released for each cause, silent providers
//! that redial at 4 s, 8 s, 16 s, slow sessions that wait four round trips, live sessions) with deadlines before and
//! after each of those moments, liars, a store that refuses writes, no provider, a wrong root, a fetch that is done
//! at the start, and seeded random worlds. Every scenario is asserted here, so the test is meaningful without the proof
//! tools.
//!
//! The trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
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
    clippy::unreadable_literal,
    clippy::doc_markdown,
    clippy::assert_is_empty,
    clippy::single_range_in_vec_init,
    clippy::cast_possible_wrap,
    clippy::manual_is_multiple_of,
    unreachable_pub
)]

mod values_support;

use std::fmt::Write as _;

use values_support::*;
use vinc_tests::SplitMix64;
use vinc_values::fetch::Timers;
use vinc_values::knobs;
use vinc_values::session::Provider;
use vinc_values::span::{Span, align};
use vinc_values::trace::{Event, FailReason, Release, Trace};

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        (v >> 48) & 0xffff
    )
}

fn b(x: bool) -> &'static str {
    if x { "true" } else { "false" }
}

/// A time that may be absent, as `{"p":false}` or `{"p":true,"v":limbs}` (the TLA+ JSON reader has no null).
fn opt_limbs(v: Option<u64>) -> String {
    v.map_or_else(
        || "{\"p\":false}".to_string(),
        |x| format!("{{\"p\":true,\"v\":{}}}", limbs(x)),
    )
}

/// The time state of the fetch as one JSON object.
fn state(t: &Timers, poll: Option<u64>) -> String {
    let head = t.head.map_or_else(
        || "{\"h\":false}".to_string(),
        |(off, len, t0)| format!("{{\"h\":true,\"off\":{off},\"len\":{len},\"t0\":{}}}", limbs(t0)),
    );
    format!(
        "{{\"run\":{},\"sw\":{},\"lastp\":{},\"lastb\":{},\"treq\":{},\"tw\":{},\"head\":{head},\"rel\":{},\"nv\":{},\"poll\":{}}}",
        b(t.running),
        limbs(t.sw),
        limbs(t.lastp),
        limbs(t.lastb),
        limbs(t.treq),
        limbs(t.tw),
        b(t.released),
        t.nv,
        opt_limbs(poll)
    )
}

fn cause(c: Release) -> &'static str {
    match c {
        Release::Buffered => "buffered",
        Release::Tail => "tail",
        Release::Granules => "granules",
        Release::Timeout => "timeout",
        Release::Done => "done",
    }
}

fn reason(r: FailReason) -> &'static str {
    match r {
        FailReason::NoProvider => "NoProvider",
        FailReason::EveryProviderLied => "Lied",
        FailReason::Deadline => "Deadline",
        FailReason::Store => "Store",
        FailReason::BadRoot => "BadRoot",
    }
}

/// The records of the fetch since `from`, as the atoms the models compare.
fn atoms(sim: &Sim, from: usize) -> String {
    let mut out = Vec::new();
    for l in &sim.rec.log[from..] {
        match l {
            Logged::Tr(_, Trace::Verified { off, len, .. }) => out.push(format!("[\"ver\",{off},{len}]")),
            Logged::Tr(_, Trace::Held { off }) => out.push(format!("[\"held\",{off}]")),
            Logged::Tr(_, Trace::Released { off, why }) => out.push(format!("[\"rel\",{off},\"{}\"]", cause(*why))),
            Logged::Ev(_, Event::Readable { off, len }) => out.push(format!("[\"rd\",{off},{len}]")),
            Logged::Ev(_, Event::Complete) => out.push("[\"done\"]".to_string()),
            Logged::Ev(_, Event::Failed(r)) => out.push(format!("[\"fail\",\"{}\"]", reason(*r))),
            Logged::Tr(_, Trace::StallRedial { wait, next }) => {
                out.push(format!("[\"redial\",{},{}]", limbs(*wait), limbs(*next)));
            }
            Logged::Tr(_, Trace::Liar { .. }) => out.push("[\"liar\"]".to_string()),
            _ => {}
        }
    }
    format!("[{}]", out.join(","))
}

struct Snap {
    up: Vec<bool>,
    latency: Vec<u64>,
    last_rx: Vec<u64>,
    live: bool,
    pto: bool,
}

fn snap(sim: &Sim) -> Snap {
    Snap {
        up: sim.sess.up.clone(),
        latency: sim.sess.latency.clone(),
        last_rx: sim.sess.last_rx.clone(),
        live: sim.sess.live,
        pto: sim.sess.pto,
    }
}

/// What the stall rules read from the sessions, restated: the sessions as JSON, STALL_RTT and STALL_LIVE for the
/// providers (all of them assigned: no provider is evicted in the scenarios that reach a stall).
fn session_env(snap: &Snap, now: u64, lastp: u64) -> (String, u64, u64) {
    let mut ss = Vec::new();
    let mut rmax = 0u64;
    let mut live = Some(0u64);
    for i in 0..snap.up.len() {
        let up = snap.up[i];
        let rtt = up.then(|| 2 * snap.latency[i]);
        let last_rx = if snap.live { now } else { snap.last_rx[i] };
        ss.push(format!(
            "{{\"c\":{},\"r\":{},\"p\":{},\"x\":{}}}",
            b(up),
            rtt.map_or(-1, |r| r as i64),
            b(snap.pto),
            limbs(last_rx)
        ));
        if let Some(r) = rtt.filter(|&r| r != 0) {
            rmax = rmax.max(r);
        }
        live = live.and_then(|d| {
            if !up {
                return None;
            }
            let r = rtt.filter(|&r| r != 0).unwrap_or(knobs::ASSUMED_RTT);
            if r < knobs::SLOW_RTT
                || snap.pto
                || now.saturating_sub(last_rx) > (2 * knobs::NS).max(r.saturating_mul(2))
                || now.saturating_sub(lastp) > knobs::LIVE_CAP
            {
                None
            } else {
                Some(d.max(r.saturating_mul(2)).max(knobs::STALL_WAIT))
            }
        });
    }
    let w = knobs::STALL_RTT.saturating_mul(rmax).min(knobs::STALL_RTT_CAP);
    (format!("[{}]", ss.join(",")), w, live.unwrap_or(0))
}

/// The groups of a list of aligned spans, as `[off,len]` pairs.
fn groups(spans: &[Span]) -> Vec<(u64, u64)> {
    let mut v = Vec::new();
    for s in spans {
        let mut o = s.off;
        while o < s.end() {
            let l = (s.end() - o).min(knobs::GROUP);
            v.push((o, l));
            o += l;
        }
    }
    v
}

fn pairs(v: &[(u64, u64)]) -> String {
    format!(
        "[{}]",
        v.iter()
            .map(|(a, l)| format!("[{a},{l}]"))
            .collect::<Vec<_>>()
            .join(",")
    )
}

/// A run of steps in which only stream bytes arrived.
struct Pending {
    pre: String,
    t1: u64,
    tn: u64,
    n: u64,
    mg: u64,
}

impl Pending {
    fn write(&self, out: &mut String, run: u32, post: &str) {
        writeln!(
            out,
            "{{\"t\":\"vt\",\"run\":{run},\"k\":\"bs\",\"t1\":{},\"tn\":{},\"n\":{},\"mg\":{},\"pre\":{},\"post\":{post}}}",
            limbs(self.t1),
            limbs(self.tn),
            self.n,
            limbs(self.mg),
            self.pre
        )
        .unwrap();
    }
}

/// Everything one run needs: the simulation is started here and stepped one queued event or timer call at a time.
struct Run<'a> {
    out: &'a mut String,
    id: u32,
}

impl Run<'_> {
    /// Start `sim` and record the run until the fetch is done, nothing is left to do, or `limit` virtual time.
    fn go(&mut self, sim: &mut Sim, ranges: &[Span], provs: &[Provider], deadline: Option<u64>, limit: u64) {
        self.go_until(sim, ranges, provs, deadline, limit, &|_| false);
    }

    /// Like [`Run::go`], and stop recording as soon as `stop` holds (the run is a prefix of the fetch).
    fn go_until(
        &mut self,
        sim: &mut Sim,
        ranges: &[Span],
        provs: &[Provider],
        deadline: Option<u64>,
        limit: u64,
        stop: &dyn Fn(&Sim) -> bool,
    ) {
        let seeded: Vec<Span> = sim
            .store
            .verified
            .iter()
            .map(|r| Span {
                off: r.start,
                len: r.end - r.start,
            })
            .collect();
        let asked: Vec<Span> = if ranges.is_empty() {
            vec![Span {
                off: 0,
                len: sim.length,
            }]
        } else {
            ranges.to_vec()
        };
        let aligned: Vec<Span> = asked.iter().filter_map(|s| align(*s, sim.length)).collect();
        let empty_root = sim.root == *blake3::hash(b"").as_bytes();
        let from = sim.rec.log.len();
        sim.start_with(ranges, provs, deadline);
        let t0 = sim.fetch.timers();
        let nprov = {
            let mut seen = Vec::new();
            for p in provs {
                if !seen.contains(p) {
                    seen.push(*p);
                }
            }
            seen.len().min(knobs::MAX_PROVIDERS)
        };
        writeln!(
            self.out,
            "{{\"t\":\"vtrun\",\"run\":{},\"o0\":{},\"we\":{},\"len\":{},\"er\":{},\"wg\":{},\"want\":{},\"sto\":{},\"stoi\":{},\"hb\":{},\"nvl\":{},\"hasdl\":{},\"dl\":{},\"striped\":{},\"np\":{},\"post\":{},\"tr\":{}}}",
            self.id,
            asked.first().map_or(0, |s| s.off),
            t0.wend,
            sim.length,
            b(empty_root),
            pairs(&groups(&aligned)),
            pairs(&aligned.iter().map(|s| (s.off, s.end())).collect::<Vec<_>>()),
            pairs(&groups(&seeded)),
            pairs(&seeded.iter().map(|s| (s.off, s.end())).collect::<Vec<_>>()),
            knobs::HOLD_B,
            knobs::HOLD_NV,
            b(deadline.is_some()),
            limbs(deadline.unwrap_or(0)),
            b(provs.len() > 1),
            nprov,
            state(&t0, sim.fetch.poll_timeout()),
            atoms(sim, from)
        )
        .unwrap();
        let (mut steps, mut written) = (0usize, 0usize);
        // Consecutive steps in which only stream bytes arrived are written as one line (`bs`): the first and last
        // time, how many, and the longest gap between consecutive ones (BYTE_LIVE keeps the largest of its gaps).
        let mut pend: Option<Pending> = None;
        let mut last_post = String::new();
        while sim.fetch.is_running() && steps < 2_000_000 && written < 4000 && !stop(sim) {
            let pre = sim.fetch.timers();
            let pre_poll = sim.fetch.poll_timeout();
            let sn = snap(sim);
            let from = sim.rec.log.len();
            let mut calls = 0;
            let more = sim.run_until(limit, |_| {
                calls += 1;
                calls > 1
            });
            if !more && calls == 1 {
                break;
            }
            steps += 1;
            let now = sim.now;
            let post = sim.fetch.timers();
            let post_poll = sim.fetch.poll_timeout();
            let at = atoms(sim, from);
            if at == "[]" && pre == post && pre_poll == post_poll {
                continue;
            }
            let plain = at == "[]"
                && !sim.timed_out
                && pre.running == post.running
                && pre.lastp == post.lastp
                && pre.tw == post.tw
                && pre.treq == post.treq
                && pre.head == post.head
                && pre.released == post.released
                && pre.nv == post.nv
                && post.lastb == now
                && now != 0;
            if plain {
                match pend.as_mut() {
                    Some(p) => {
                        p.mg = p.mg.max(now - p.tn);
                        p.tn = now;
                        p.n += 1;
                    }
                    None => {
                        pend = Some(Pending {
                            pre: state(&pre, pre_poll),
                            t1: now,
                            tn: now,
                            n: 1,
                            mg: 0,
                        });
                    }
                }
                last_post = state(&post, post_poll);
                continue;
            }
            if let Some(p) = pend.take() {
                p.write(self.out, self.id, &last_post);
                written += 1;
            }
            written += 1;
            let (ss, w, lv) = if sim.timed_out {
                session_env(&sn, now, pre.lastp.max(pre.treq))
            } else {
                ("[]".to_string(), 0, 0)
            };
            writeln!(
                self.out,
                "{{\"t\":\"vt\",\"run\":{},\"k\":\"{}\",\"now\":{},\"pre\":{},\"post\":{},\"ss\":{ss},\"w\":{},\"lv\":{},\"tr\":{at}}}",
                self.id,
                if sim.timed_out { "to" } else { "ev" },
                limbs(now),
                state(&pre, pre_poll),
                state(&post, post_poll),
                limbs(w),
                limbs(lv),
            )
            .unwrap();
        }
        if let Some(p) = pend.take() {
            p.write(self.out, self.id, &last_post);
        }
        if std::env::var_os("VT_DEBUG").is_some() {
            eprintln!(
                "run {} steps {steps} running {} now {} s",
                self.id,
                sim.fetch.is_running(),
                sim.now / SEC
            );
        }
        self.id += 1;
    }
}

fn releases(sim: &Sim) -> Vec<(u64, Release)> {
    sim.rec
        .traces_of(|t| {
            if let Trace::Released { off, why } = t {
                Some((*off, *why))
            } else {
                None
            }
        })
        .into_iter()
        .map(|(_, r)| r)
        .collect()
}

fn redials(sim: &Sim) -> Vec<(u64, u64, u64)> {
    sim.rec
        .traces_of(|t| {
            if let Trace::StallRedial { wait, next } = t {
                Some((*wait, *next))
            } else {
                None
            }
        })
        .into_iter()
        .map(|(t, (w, n))| (t, w, n))
        .collect()
}

fn silent_sim(seed: u64, rate: u64, latency: u64, after: u64) -> Sim {
    let store = PStore::random(seed, 2 << 20);
    Sim::new(
        vec![ProvCfg::new(store, rate).latency(latency).stall_after(after)],
        ClientStore::new(),
    )
}

const G: u64 = GROUP;

#[test]
fn time_rules_trace() {
    let mut out = String::new();
    let mut run = Run { out: &mut out, id: 0 };

    // HEAD_HOLD, each cause.
    let mut sim = Sim::uniform(1, 1 << 20, 2000);
    run.go(&mut sim, &[], &[Provider(0)], None, 60 * SEC);
    assert_eq!(releases(&sim)[0].1, Release::Buffered);

    let mut sim = Sim::uniform(1, 3 * G as usize, 2000);
    run.go(&mut sim, &[], &[Provider(0)], None, 30 * SEC);
    assert_eq!(releases(&sim)[0].1, Release::Tail);

    let mut sim = Sim::new(
        vec![ProvCfg::new(PStore::random(45, 300 * G as usize), 4000)],
        ClientStore::new(),
    );
    let ranges = [
        Span { off: 0, len: G },
        Span {
            off: 100 * G,
            len: 60 * G,
        },
    ];
    run.go(&mut sim, &ranges, &[Provider(0)], None, 60 * SEC);
    assert_eq!(releases(&sim)[0].1, Release::Granules);

    let len = 300 * G as usize;
    let head_frame = vinc_values::plan::Plan::new(len as u64, &[Span { off: 0, len: G }])
        .unwrap()
        .total();
    let cfgs = vec![
        ProvCfg::new(PStore::random(46, len), 3000).stall_after(head_frame),
        ProvCfg::new(PStore::random(46, len), 100),
    ];
    let mut sim = Sim::new(cfgs, ClientStore::new());
    let ranges = [
        Span { off: 0, len: G },
        Span {
            off: 100 * G,
            len: 120 * G,
        },
    ];
    run.go_until(&mut sim, &ranges, &[Provider(0), Provider(1)], None, 30 * SEC, &|s| {
        !releases(s).is_empty()
    });
    assert_eq!(releases(&sim)[0].1, Release::Timeout);

    // The first request offset is mid-granule: the tail threshold is the end of the wanted ranges (the aligned
    // end), so the value ends in the buffer and the release is the tail.
    let mut sim = Sim::uniform(1, 40 * G as usize, 2000);
    run.go(
        &mut sim,
        &[Span { off: 100, len: 3 * G }],
        &[Provider(0)],
        None,
        30 * SEC,
    );
    assert_eq!(releases(&sim)[0].1, Release::Tail);

    // The first granule is in the store already: it is never held.
    let content = PStore::random(48, 8 * G as usize);
    let mut sim = Sim::new(
        vec![ProvCfg::new(content.clone(), 2000)],
        ClientStore::seeded(content.content(), &[0..G]),
    );
    run.go(&mut sim, &[], &[Provider(0)], None, 30 * SEC);
    assert!(releases(&sim).is_empty());
    assert!(sim.rec.complete());

    // STALL_REDIAL: 4 s, 8 s, 16 s, 16 s, and the deadline before, between and after those redials.
    for (k, dl) in [
        None,
        Some(3 * SEC),
        Some(9 * SEC),
        Some(14 * SEC),
        Some(30 * SEC),
        Some(60 * SEC),
    ]
    .into_iter()
    .enumerate()
    {
        let mut sim = silent_sim(100 + k as u64, 1000, 10 * MS, 400_000);
        run.go(
            &mut sim,
            &[],
            &[Provider(0)],
            dl,
            if dl.is_some() { 100 * SEC } else { 90 * SEC },
        );
        if dl.is_none() {
            let r = redials(&sim);
            assert!(r.len() >= 4, "redials {r:?} at {} s, steps", sim.now / SEC);
            assert_eq!((r[0].1, r[0].2), (4 * SEC, 8 * SEC));
            assert_eq!((r[1].1, r[1].2), (8 * SEC, 16 * SEC));
        } else {
            assert_eq!(sim.rec.failed(), Some(FailReason::Deadline));
        }
    }
    // ARK_PACE, STALL_RTT, STALL_LIVE (alone and with a probe timeout).
    let mut sim = silent_sim(110, 8, 10 * MS, 8 * 2048 * 6);
    run.go_until(&mut sim, &[], &[Provider(0)], None, 300 * SEC, &|s| {
        !redials(s).is_empty()
    });
    let mut sim = silent_sim(111, 1000, 1500 * MS, 300_000);
    run.go(&mut sim, &[], &[Provider(0)], Some(80 * SEC), 200 * SEC);
    let mut sim = silent_sim(112, 1000, 200 * MS, 300_000);
    sim.sess.live = true;
    run.go(&mut sim, &[], &[Provider(0)], Some(70 * SEC), 100 * SEC);
    let mut sim = silent_sim(114, 1000, 200 * MS, 300_000);
    sim.sess.live = true;
    sim.sess.pto = true;
    run.go(&mut sim, &[], &[Provider(0)], Some(60 * SEC), 100 * SEC);

    // Failure reasons.
    let honest = PStore::random(120, 200_000);
    let mut sim = Sim::new(
        vec![ProvCfg::new(honest.lying(Lie::FlipByte(77)), 1000)],
        ClientStore::new(),
    );
    run.go(&mut sim, &[], &[Provider(0)], Some(40 * SEC), 60 * SEC);
    assert_eq!(sim.rec.failed(), Some(FailReason::EveryProviderLied));
    let mut sim = Sim::new(
        vec![
            ProvCfg::new(honest.lying(Lie::EveryGroup), 3000),
            ProvCfg::new(honest.clone(), 3000),
        ],
        ClientStore::new(),
    );
    run.go(&mut sim, &[], &[Provider(0), Provider(1)], Some(40 * SEC), 60 * SEC);
    assert!(sim.rec.complete());
    let mut cs = ClientStore::new();
    cs.fail_writes = true;
    let mut sim = Sim::new(vec![ProvCfg::new(PStore::random(121, 100_000), 1000)], cs);
    run.go(&mut sim, &[], &[Provider(0)], Some(40 * SEC), 60 * SEC);
    assert_eq!(sim.rec.failed(), Some(FailReason::Store));
    let mut sim = Sim::uniform(1, 5000, 100);
    run.go(&mut sim, &[], &[], None, 10 * SEC);
    assert_eq!(sim.rec.failed(), Some(FailReason::NoProvider));
    let empty = PStore::bytes(Vec::new());
    let mut sim = Sim::new(vec![ProvCfg::new(empty.clone(), 100)], ClientStore::new());
    sim.root = [9; 32];
    run.go(&mut sim, &[], &[Provider(0)], None, 10 * SEC);
    assert_eq!(sim.rec.failed(), Some(FailReason::BadRoot));
    let mut sim = Sim::new(vec![ProvCfg::new(empty, 100)], ClientStore::new());
    run.go(&mut sim, &[], &[Provider(0)], Some(5 * SEC), 10 * SEC);
    assert!(sim.rec.complete());
    // Nothing missing at the start, with no provider named.
    let content = PStore::random(122, 4 * G as usize);
    let mut sim = Sim::new(
        vec![ProvCfg::new(content.clone(), 100)],
        ClientStore::seeded(content.content(), &[0..4 * G]),
    );
    run.go(&mut sim, &[], &[], None, 10 * SEC);
    assert!(sim.rec.complete());

    // A provider that goes silent and one that is slow, with a deadline.
    let store = PStore::random(130, 1 << 20);
    let mut sim = Sim::new(
        vec![
            ProvCfg::new(store.clone(), 800).stall_after(150_000),
            ProvCfg::new(store, 600).latency(40 * MS),
        ],
        ClientStore::new(),
    );
    run.go(&mut sim, &[], &[Provider(0), Provider(1)], Some(50 * SEC), 90 * SEC);

    // Seeded random worlds.
    let mut rng = SplitMix64::traced(0x7156_4EED);
    for k in 0..24u64 {
        let n = 1 + (rng.next_u64() % 3) as usize;
        let groups_n = 3 + rng.next_u64() % 14;
        let len = (groups_n * G) as usize - (rng.next_u64() % 5000) as usize;
        let store = PStore::random(200 + k, len);
        let cfgs: Vec<ProvCfg> = (0..n)
            .map(|_| {
                let mut c =
                    ProvCfg::new(store.clone(), 600 + rng.next_u64() % 3400).latency((1 + rng.next_u64() % 400) * MS);
                if rng.next_u64() % 3 == 0 {
                    c = c.stall_after(20_000 + rng.next_u64() % (len as u64 / 2 + 1));
                }
                c
            })
            .collect();
        let mut sim = Sim::new(cfgs, ClientStore::new());
        if rng.next_u64() % 4 == 0 {
            sim.sess.live = true;
        }
        let ps = sim.all_providers();
        let ranges: Vec<Span> = match rng.next_u64() % 3 {
            0 => Vec::new(),
            1 => vec![Span {
                off: 100 + rng.next_u64() % (G * 2),
                len: G * (1 + rng.next_u64() % 4),
            }],
            _ => vec![
                Span { off: 0, len: G },
                Span {
                    off: 2 * G,
                    len: G * (1 + rng.next_u64() % 2),
                },
            ],
        };
        let ranges: Vec<Span> = ranges.into_iter().filter(|s| s.end() <= len as u64).collect();
        let dl = (rng.next_u64() % 2 == 0).then(|| SEC * (1 + rng.next_u64() % 40));
        run.go(&mut sim, &ranges, &ps, dl, 120 * SEC);
    }

    if let Some(dir) = std::env::var_os("VINC_TRACE_DIR") {
        let path = std::path::Path::new(&dir).join("values_time.ndjson");
        std::fs::write(path, out).unwrap();
    }
}
