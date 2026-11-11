//! The 21 score terms of one finished run, by the current rule and by the fair rule.
//!
//! [`compute_terms`] is the live metric and decides validity and `is_better`. [`compute_fair_terms`]
//! replaces L1, L2, L4 and T4 from the same run: every intended receiver counts, must or not, a sample is bounded by
//! its deadline, and a stream fetch that never completes is fully stalled.
//!
//! What the host feeds: R1 is the recorder's `cpu_ns` (set in `Rec::finish`) over `app_bytes`; R2 is the mean of the
//! sampled state peaks (the recorder's samples, or [`super::NodeFacts::state_peak`] where larger); R3 is the mean over
//! all world nodes of [`super::NodeFacts::export_max`] (0 for a node with no entry). Every other term comes from the
//! recorder and the world alone.
//!
//! Invariant: a term with no samples is `None`; sums of integer nanoseconds and bytes are exact integers before the
//! single final division, as in the reference.

use std::collections::BTreeMap;

use super::gates::{echo_connected_in_time, matching};
use super::{RunFacts, Terms, p50, tail_mean};
use crate::suite::rec::{HOUR, MemberKind, Rec};
use crate::suite::world::model::{ChangeKind, IntentKind, World};

fn diff(a: u64, b: u64) -> i64 {
    (i128::from(a) - i128::from(b)) as i64
}

/// `deadline or end`: a missing or zero deadline stands for the end of the run, as Python's `or` does.
fn dl_or_end(deadline: Option<u64>, end: u64) -> u64 {
    deadline.filter(|&d| d != 0).unwrap_or(end)
}

/// The latency of a must echo or fetch that did not finish: until its deadline or the end of the run.
fn open_lat(deadline: Option<u64>, end: u64, t: u64) -> i64 {
    diff(dl_or_end(deadline, end).min(end), t)
}

fn mean_i(sum: i128, n: usize) -> f64 {
    sum as f64 / n as f64
}

/// The terms of one run by the current rule.
pub fn compute_terms(world: &World, rec: &Rec, facts: &RunFacts) -> Terms {
    let end = rec.end;
    let mut t = Terms::new();
    let (mut small, mut under_bulk) = (Vec::<i64>::new(), Vec::<i64>::new());
    for it in rec.intents.values().filter(|it| it.small && !it.receivers.is_empty()) {
        let dl = it.deadline.unwrap_or(end);
        for &r in it.receivers.iter().filter(|&&r| r != it.node) {
            let done = it.delivered.get(&r);
            let lat = done.map_or_else(|| diff(dl.min(end), it.t), |&d| diff(d, it.t));
            if done.is_none() && !it.must_set.contains(&r) {
                continue;
            }
            small.push(lat);
            if it.under_bulk {
                under_bulk.push(lat);
            }
        }
    }
    t.set("L1", p50(&small));
    t.set("L2", tail_mean(&small));
    let cold: Vec<i64> = rec
        .intents
        .values()
        .filter(|it| it.kind == IntentKind::Echo && it.must)
        .map(|it| {
            it.delivered
                .get(&it.node)
                .map_or_else(|| open_lat(it.deadline, end, it.t), |&d| diff(d, it.t))
        })
        .collect();
    t.set("L3", tail_mean(&cold));
    t.set(
        "L4",
        if under_bulk.len() >= 5 {
            tail_mean(&under_bulk)
        } else {
            None
        },
    );
    t.set("L5", awareness_lags(world, rec));
    throughput(rec, &mut t);
    continuation(world, rec, &mut t);
    cost(world, rec, facts, &mut t);
    t
}

fn throughput(rec: &Rec, t: &mut Terms) {
    let end = rec.end;
    let (mut bulk_ns, mut bulk_bytes, mut multi_ns, mut multi_bytes) = (0i128, 0u128, 0i128, 0u128);
    let (mut ttfb, mut stall) = (Vec::<i64>::new(), Vec::<f64>::new());
    for it in rec
        .intents
        .values()
        .filter(|it| it.kind == IntentKind::Fetch && it.must)
    {
        let dur = it
            .delivered
            .get(&it.node)
            .map_or_else(|| open_lat(it.deadline, end, it.t), |&d| diff(d, it.t));
        let nbytes = it.meta.req_bytes.unwrap_or(it.size);
        bulk_ns += i128::from(dur);
        bulk_bytes += u128::from(nbytes);
        if it.meta.providers.len() > 1 {
            multi_ns += i128::from(dur);
            multi_bytes += u128::from(nbytes);
        }
        if it.meta.stream_rate.is_some_and(|r| r != 0) {
            ttfb.push(
                it.meta
                    .first_byte
                    .map_or_else(|| open_lat(it.deadline, end, it.t), |fb| diff(fb, it.t)),
            );
            if let Some(st) = it.meta.stall_frac {
                stall.push(st);
            }
        }
    }
    t.set("T1", (bulk_bytes != 0).then(|| bulk_ns as f64 / bulk_bytes as f64));
    t.set("T2", (multi_bytes != 0).then(|| multi_ns as f64 / multi_bytes as f64));
    t.set("T3", p50(&ttfb));
    t.set("T4", mean_f(&stall));
}

fn mean_f(xs: &[f64]) -> Option<f64> {
    (!xs.is_empty()).then(|| xs.iter().sum::<f64>() / xs.len() as f64)
}

fn continuation(world: &World, rec: &Rec, t: &mut Terms) {
    let end = rec.end;
    if rec.resumes.is_empty() {
        t.set("C1", None);
        t.set("C2", None);
    } else {
        let n = rec.resumes.len();
        let bytes: i128 = rec.resumes.iter().map(|r| i128::from(r.bytes)).sum::<i128>() + i128::from(rec.redundant);
        t.set("C1", Some(mean_i(bytes, n)));
        let lat: i128 = rec
            .resumes
            .iter()
            .map(|r| i128::from(diff(r.first.unwrap_or(end), r.t)))
            .sum();
        t.set("C2", Some(mean_i(lat, n)));
    }
    let musts = rec.intents.values().any(|it| it.must);
    t.set("C3", None);
    if world.score_c3 && musts {
        let (mut und, mut tot) = (0u64, 0u64);
        for it in rec.intents.values().filter(|it| it.must) {
            for &r in &it.receivers {
                if r == it.node && it.kind != IntentKind::Fetch {
                    continue;
                }
                tot += 1;
                let late = match it.delivered.get(&r) {
                    None => true,
                    Some(&d) => it.deadline.is_some_and(|dl| d > dl),
                };
                und += u64::from(late);
            }
        }
        t.set("C3", (tot != 0).then(|| und as f64 / tot as f64));
    }
    let echo: Vec<u32> = rec
        .intents
        .values()
        .filter(|it| it.kind == IntentKind::Echo && it.must)
        .map(|it| it.iid)
        .collect();
    let c4 = (!echo.is_empty()).then(|| {
        let fails = echo
            .iter()
            .filter(|&&iid| !echo_connected_in_time(world, rec, iid))
            .count();
        fails as f64 / echo.len() as f64
    });
    t.set("C4", c4);
}

fn cost(world: &World, rec: &Rec, facts: &RunFacts, t: &mut Terms) {
    let app = rec.app_bytes;
    let ratio = |n: u64| (app != 0).then(|| n as f64 / app as f64);
    t.set("B1", ratio(rec.wire_bytes));
    let rc = &rec.reconcile_cost;
    t.set(
        "B2",
        (!rc.is_empty()).then(|| {
            let bytes: u128 = rc.iter().map(|&(b, _)| u128::from(b)).sum();
            let items: u128 = rc.iter().map(|&(_, n)| u128::from(n)).sum();
            bytes as f64 / items.max(1) as f64
        }),
    );
    if let Some((a, b)) = rec.idle {
        let hours = (b - a) as f64 / HOUR as f64;
        let live = (0..world.nodes.len()).filter(|&i| rec.alive_through(i, a, b)).count();
        let nh = live.max(1) as f64 * hours;
        t.set("B3", Some(rec.idle_bytes as f64 / nh));
        t.set("B4", Some(rec.idle_tx as f64 / nh));
    } else {
        t.set("B3", None);
        t.set("B4", None);
    }
    t.set("B5", ratio(rec.third_bytes));
    t.set("R1", (app != 0).then(|| rec.cpu_ns / app as f64));
    let peaks: Vec<u64> = (0..world.nodes.len())
        .filter_map(|i| facts.state_peak(rec, i))
        .collect();
    t.set(
        "R2",
        (!peaks.is_empty()).then(|| peaks.iter().map(|&p| u128::from(p)).sum::<u128>() as f64 / peaks.len() as f64),
    );
    let n = world.nodes.len();
    t.set(
        "R3",
        (n != 0).then(|| {
            (0..n)
                .map(|i| u128::from(facts.nodes.get(i).map_or(0, |f| f.export_max)))
                .sum::<u128>() as f64
                / n as f64
        }),
    );
}

/// L5: change to matching event at every affected live node; the slowest 5%.
fn awareness_lags(world: &World, rec: &Rec) -> Option<f64> {
    let lags: Vec<i64> = aware_samples(world, rec).iter().map(|s| s.lag).collect();
    tail_mean(&lags)
}

/// One L5 sample: a change, a live node that should notice it, and how long that took (capped, the run's end when
/// it never did).
struct AwareSample {
    kind: ChangeKind,
    member: usize,
    node: usize,
    t0: u64,
    lag: i64,
    seen: bool,
}

fn aware_samples(world: &World, rec: &Rec) -> Vec<AwareSample> {
    let end = rec.end;
    let mut by = BTreeMap::<(usize, usize), Vec<(u64, MemberKind, Option<u64>)>>::new();
    for m in &rec.membership {
        if let Some(member) = m.member {
            by.entry((m.node, member)).or_default().push((m.t, m.kind, m.extra));
        }
    }
    let cap = i64::try_from(world.awareness_bound_cap_ns.saturating_mul(2)).unwrap_or(i64::MAX);
    let mut out = Vec::new();
    for ch in &rec.changes {
        let (t0, kind, idx) = (ch.t, ch.kind, ch.node);
        for j in 0..world.nodes.len() {
            if j == idx || rec.denied.contains(&j) || rec.denied.contains(&idx) {
                continue;
            }
            if !rec.alive_through(j, t0, end.min(t0 + 1)) || rec.revoked.get(&j).copied().unwrap_or(end + 1) <= t0 {
                continue;
            }
            if kind == ChangeKind::Join && !rec.alive_at(j, t0) {
                continue;
            }
            let first = by.get(&(j, idx)).and_then(|evs| {
                evs.iter()
                    .find(|&&(t, k, ex)| {
                        t >= t0 && matching(kind, k) && (kind != ChangeKind::Stack || ex == ch.version)
                    })
                    .map(|&(t, _, _)| t)
            });
            out.push(AwareSample {
                kind,
                member: idx,
                node: j,
                t0,
                lag: diff(first.unwrap_or(end), t0).min(cap),
                seen: first.is_some(),
            });
        }
    }
    out
}

/// The `n` slowest L5 samples of a finished run, one line each, for diagnosis.
pub fn slowest_awareness(world: &World, rec: &Rec, n: usize) -> Vec<String> {
    let mut s = aware_samples(world, rec);
    s.sort_by_key(|x| core::cmp::Reverse(x.lag));
    s.iter()
        .take(n)
        .map(|x| {
            format!(
                "L5 {:?} of {} at {} ns: node {} after {} ns{}",
                x.kind,
                x.member,
                x.t0,
                x.node,
                x.lag,
                if x.seen { "" } else { " (never)" }
            )
        })
        .collect()
}

/// Sample counts of the current and the fair rule, for the report.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FairSamples {
    /// Small-message samples by the fair rule.
    pub small: usize,
    /// Small-message samples by the current rule.
    pub small_current: usize,
    /// Under-bulk samples by the fair rule.
    pub under_bulk: usize,
    /// Under-bulk samples by the current rule.
    pub under_bulk_current: usize,
    /// Stream fetches counted by the fair rule.
    pub stream: usize,
    /// Stream fetches with a measured stall fraction (counted by the current rule).
    pub stream_current: usize,
}

/// L1, L2, L4 and T4 by the fair rule from the same finished run (all other terms are absent in the result).
pub fn compute_fair_terms(_world: &World, rec: &Rec, _facts: &RunFacts) -> (Terms, FairSamples) {
    let end = rec.end;
    let (mut small, mut under_bulk) = (Vec::<i64>::new(), Vec::<i64>::new());
    let mut s = FairSamples::default();
    for it in rec.intents.values().filter(|it| it.small && !it.receivers.is_empty()) {
        let dl = it.deadline.unwrap_or(end);
        for &r in it.receivers.iter().filter(|&&r| r != it.node) {
            let done = it.delivered.get(&r).copied();
            let lat = diff(done.unwrap_or(end).min(dl).min(end), it.t);
            small.push(lat);
            let counted = done.is_some() || it.must_set.contains(&r);
            s.small_current += usize::from(counted);
            if it.under_bulk {
                under_bulk.push(lat);
                s.under_bulk_current += usize::from(counted);
            }
        }
    }
    let mut stalls = Vec::<f64>::new();
    for it in rec
        .intents
        .values()
        .filter(|it| it.kind == IntentKind::Fetch && it.must && it.meta.stream_rate.is_some_and(|r| r != 0))
    {
        let st = if it.delivered.contains_key(&it.node) {
            it.meta.stall_frac
        } else {
            None
        };
        s.stream_current += usize::from(it.meta.stall_frac.is_some());
        stalls.push(st.unwrap_or(1.0));
    }
    s.small = small.len();
    s.under_bulk = under_bulk.len();
    s.stream = stalls.len();
    let mut f = Terms::new();
    f.set("L1", p50(&small));
    f.set("L2", tail_mean(&small));
    f.set(
        "L4",
        if under_bulk.len() >= 5 {
            tail_mean(&under_bulk)
        } else {
            None
        },
    );
    f.set("T4", mean_f(&stalls));
    (f, s)
}

/// The terms with L1, L2, L4 and T4 replaced by the fair ones.
pub fn with_fair(terms: &Terms, fair: &Terms) -> Terms {
    let mut out = *terms;
    for k in ["L1", "L2", "L4", "T4"] {
        out.set(k, fair.get(k));
    }
    out
}
