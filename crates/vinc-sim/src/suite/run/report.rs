//! Text tables for a set of finished runs: gates per scenario and seed, the terms of each scenario next to the
//! reference numbers, the scores against the cached reference terms, and the scenarios that wait for a layer.
//!
//! Every table says what it covers. A scenario that was not run is listed as waiting with the layer it needs, a
//! gate that was not evaluated is printed as such, and the scores are marked partial: they use only the terms the
//! runs have and only the scenarios that ran, so they are not comparable with a full grading.
//!
//! Invariants: nothing here reads a clock or a random source; an absent value prints as `-`, never as zero.

use std::collections::BTreeMap;
use std::fmt::Write;

use super::reference_table::{COLUMNS, EXTRA, UNITS, comparability, display, row};
use super::{RunResult, Status};
use crate::Driver;
use crate::suite::grade::{GateStatus, ScenarioRuns, TERMS, Terms, pool, score, with_fair};
use crate::suite::world::{SeedSet, Variant};

/// A finished run with the variant it was made from.
#[derive(Clone, Debug)]
pub struct Entry {
    /// The matrix entry.
    pub variant: Variant,
    /// What the run reported.
    pub result: RunResult,
    /// Wall seconds the run took on the machine that made it (not part of any verdict).
    pub wall_s: f64,
}

fn set_name(s: SeedSet) -> &'static str {
    match s {
        SeedSet::Matrix => "matrix",
        SeedSet::Noise => "noise",
        SeedSet::Extra1 => "extra1",
        SeedSet::Extra2 => "extra2",
    }
}

fn driver_name(d: Driver) -> &'static str {
    match d {
        Driver::Vinc => "vinc",
        Driver::Reference => "reference",
    }
}

fn num(v: Option<f64>) -> String {
    v.map_or_else(
        || "-".to_owned(),
        |x| {
            if x.abs() >= 1000.0 {
                format!("{x:.0}")
            } else {
                format!("{x:.3}")
            }
        },
    )
}

/// One row per run: the gates that failed, the gates not evaluated, and how much was measured.
pub fn gate_table(entries: &[Entry]) -> String {
    let mut o = String::new();
    let _ = writeln!(
        o,
        "scenario var set    seed   driver    status    failed gates                    must in time   wall s"
    );
    for e in entries {
        let r = &e.result;
        let failed = r.gates.failed();
        let st = match &r.status {
            Status::Running => "running",
            Status::Partial(_) => "partial",
            Status::Waiting(_) => "WAITING",
        };
        let _ = writeln!(
            o,
            "{:<8} {:>3} {:<6} {:>6} {:<9} {:<9} {:<31} {:>5}/{:<5}    {:>6.1}",
            r.id,
            e.variant.variant,
            set_name(e.variant.set),
            r.seed,
            driver_name(r.driver),
            st,
            if !r.ran {
                "(not run)".to_owned()
            } else if failed.is_empty() {
                "none".to_owned()
            } else {
                failed.join(",")
            },
            r.samples.must_in_time,
            r.samples.must_owed,
            e.wall_s
        );
    }
    o
}

/// The failure details of every run with a failed gate: the messages and the first late deliveries.
pub fn failures(entries: &[Entry]) -> String {
    let mut o = String::new();
    for e in entries.iter().filter(|e| !e.result.gates.failed().is_empty()) {
        let r = &e.result;
        let _ = writeln!(
            o,
            "{} {} seed {} ({}):",
            r.id,
            set_name(e.variant.set),
            r.seed,
            driver_name(r.driver)
        );
        for (g, s) in &r.gates.gates {
            if let GateStatus::Fail(m) = s {
                let _ = writeln!(o, "  {g}: {}", m.join("; "));
            }
        }
        for l in &r.late {
            let _ = writeln!(o, "    late: {l}");
        }
    }
    o
}

/// The scenarios that were not run, with the layer each waits for, and the scenarios that ran in part with what they
/// left out.
pub fn status_list(entries: &[Entry]) -> String {
    let mut o = String::new();
    let mut seen: BTreeMap<(String, bool), (String, BTreeMap<String, u64>, usize)> = BTreeMap::new();
    for e in entries {
        let r = &e.result;
        let (why, waiting) = match &r.status {
            Status::Running => continue,
            Status::Partial(w) => (w.join("; "), false),
            Status::Waiting(w) => (w.join("; "), true),
        };
        let slot = seen.entry((r.id.clone(), waiting)).or_insert((why, BTreeMap::new(), 0));
        slot.2 += 1;
        for (k, v) in &r.excluded {
            *slot.1.entry(k.clone()).or_insert(0) += v;
        }
    }
    for ((id, waiting), (_, ex, n)) in &seen {
        let tag = if *waiting { "WAITING (not run)" } else { "PARTIAL" };
        let list: Vec<String> = ex.iter().map(|(k, v)| format!("{k}: {v}")).collect();
        let _ = writeln!(
            o,
            "{id:<4} {tag:<18} runs {n:>3}  intents left out: {}",
            list.join(" | ")
        );
    }
    o
}

/// The terms of one scenario pooled over `entries` (the runs that ran), next to the reference numbers.
pub fn terms_table(scenario: &str, entries: &[Entry]) -> String {
    let runs: Vec<&Entry> = entries
        .iter()
        .filter(|e| e.result.id == scenario && e.result.ran)
        .collect();
    let mut o = String::new();
    if runs.is_empty() {
        let _ = writeln!(o, "{scenario}: no run");
        return o;
    }
    let cur = pool(&runs.iter().map(|e| e.result.terms).collect::<Vec<_>>());
    let fair = pool(
        &runs
            .iter()
            .map(|e| with_fair(&e.result.terms, &e.result.fair))
            .collect::<Vec<_>>(),
    );
    let _ = writeln!(
        o,
        "{scenario}: terms pooled over {} runs (unit, ours current, ours fair, leader, reference, comparability)",
        runs.len()
    );
    let row = row(scenario);
    let mut names: Vec<&str> = COLUMNS.to_vec();
    names.extend(TERMS.iter().copied().filter(|t| !COLUMNS.contains(t)));
    for t in names {
        let ci = COLUMNS.iter().position(|c| *c == t);
        let unit = ci.map_or("", |i| UNITS[i]);
        let refs = ci.and_then(|i| row.and_then(|r| r[i])).or_else(|| {
            EXTRA
                .iter()
                .find(|(s, k, ..)| *s == scenario && *k == t)
                .map(|&(_, _, a, b)| (a, b))
        });
        let ours = cur.get(t).map(|v| display(t, v));
        let ours_fair = fair.get(t).map(|v| display(t, v));
        if ours.is_none() && refs.is_none() {
            continue;
        }
        let _ = writeln!(
            o,
            "  {t:<3} {unit:<9} {:>12} {:>12} {:>12} {:>12}  {}",
            num(ours),
            num(ours_fair),
            num(refs.map(|r| r.0)),
            num(refs.map(|r| r.1)),
            comparability(t).label()
        );
    }
    o
}

/// The reference runs of the cached terms file: current and fair terms per `(scenario, variant, seed slot)`.
#[derive(Clone, Debug, Default)]
pub struct RefTerms {
    cur: BTreeMap<(String, usize, usize), Terms>,
    fair: BTreeMap<(String, usize, usize), Terms>,
}

impl RefTerms {
    /// Parses the text of the cached reference terms (`cur|fair scenario variant slot TERM=value ...` per line).
    ///
    /// # Errors
    /// A message naming the malformed line.
    pub fn parse(text: &str) -> Result<Self, String> {
        let mut out = Self::default();
        for ln in text.lines().filter(|l| !l.trim().is_empty()) {
            let mut it = ln.split_whitespace();
            let (Some(kind), Some(sid), Some(v), Some(k)) = (it.next(), it.next(), it.next(), it.next()) else {
                return Err(format!("malformed line: {ln}"));
            };
            let key = (
                sid.to_owned(),
                v.parse().map_err(|_| format!("bad variant: {ln}"))?,
                k.parse().map_err(|_| format!("bad slot: {ln}"))?,
            );
            let mut t = Terms::new();
            for kv in it {
                let (name, x) = kv.split_once('=').ok_or_else(|| format!("bad term: {ln}"))?;
                t.set(name, Some(x.parse().map_err(|_| format!("bad number: {ln}"))?));
            }
            match kind {
                "cur" => out.cur.insert(key, t),
                "fair" => out.fair.insert(key, t),
                _ => return Err(format!("unknown kind: {ln}")),
            };
        }
        Ok(out)
    }

    fn for_entry(&self, e: &Entry, fair: bool) -> Option<Terms> {
        // The slots are in the order the noise floor documents: matrix seed, its extra, noise seed, its extra.
        let slot = match e.variant.set {
            SeedSet::Matrix => 0,
            SeedSet::Extra1 => 1,
            SeedSet::Noise => 2,
            SeedSet::Extra2 => 3,
        };
        let key = (e.variant.id.to_owned(), usize::from(e.variant.variant) - 1, slot);
        let cur = self.cur.get(&key)?;
        Some(if fair {
            with_fair(cur, self.fair.get(&key)?)
        } else {
            *cur
        })
    }
}

fn scores_for(entries: &[&Entry], refs: &RefTerms, fair: bool) -> Vec<(String, Option<f64>, usize)> {
    let mut ids: Vec<String> = Vec::new();
    for e in entries {
        if !ids.contains(&e.result.id) {
            ids.push(e.result.id.clone());
        }
    }
    let scen: Vec<ScenarioRuns> = ids
        .iter()
        .map(|id| {
            let es: Vec<&&Entry> = entries.iter().filter(|e| &e.result.id == id).collect();
            ScenarioRuns {
                id: id.clone(),
                cand: es
                    .iter()
                    .map(|e| {
                        if fair {
                            with_fair(&e.result.terms, &e.result.fair)
                        } else {
                            e.result.terms
                        }
                    })
                    .collect(),
                reference: es.iter().filter_map(|e| refs.for_entry(e, fair)).collect(),
                runs_expected: es.len(),
            }
        })
        .collect();
    let rep = score(&scen);
    rep.scenarios
        .iter()
        .map(|s| (s.id.clone(), s.score, es_count(entries, &s.id)))
        .collect()
}

fn es_count(entries: &[&Entry], id: &str) -> usize {
    entries.iter().filter(|e| e.result.id == id).count()
}

/// The current and fair scores of the runs that ran, per scenario and per seed set, against the cached reference.
/// PARTIAL: only the scenarios that ran, only the terms that exist, and none of the excluded workload.
pub fn score_table(entries: &[Entry], refs: &RefTerms) -> String {
    let ran: Vec<&Entry> = entries.iter().filter(|e| e.result.ran).collect();
    let mut o = String::new();
    let _ = writeln!(
        o,
        "scores against the cached reference terms - PARTIAL: scenarios that ran only, terms that exist only, excluded workload left out; not comparable with a full grading"
    );
    for fair in [false, true] {
        let _ = writeln!(o, "{} metric:", if fair { "fair" } else { "current" });
        let mut sets: Vec<(&str, Vec<&Entry>)> = [SeedSet::Matrix, SeedSet::Noise, SeedSet::Extra1, SeedSet::Extra2]
            .iter()
            .map(|s| {
                (
                    set_name(*s),
                    ran.iter().copied().filter(|e| e.variant.set == *s).collect(),
                )
            })
            .collect();
        sets.push(("all", ran.clone()));
        for (name, es) in sets.iter().filter(|(_, es)| !es.is_empty()) {
            let sc = scores_for(es, refs, fair);
            let vals: Vec<f64> = sc.iter().filter_map(|s| s.1).collect();
            let geo = (!vals.is_empty())
                .then(|| (vals.iter().map(|v| v.max(1e-12).ln()).sum::<f64>() / vals.len() as f64).exp());
            let per: Vec<String> = sc
                .iter()
                .map(|(id, s, n)| format!("{id}={} ({n} runs)", num(*s)))
                .collect();
            let _ = writeln!(o, "  {name:<7} geomean {:>8}  {}", num(geo), per.join(", "));
        }
    }
    o
}

/// All tables, in the order a reader wants them.
pub fn full(entries: &[Entry], refs: &RefTerms) -> String {
    let mut o = String::new();
    let _ = writeln!(o, "== gates per scenario and seed\n{}", gate_table(entries));
    let _ = writeln!(o, "== failures\n{}", failures(entries));
    let _ = writeln!(o, "== status\n{}", status_list(entries));
    let mut ids: Vec<&str> = Vec::new();
    for e in entries {
        if !ids.contains(&e.result.id.as_str()) {
            ids.push(&e.result.id);
        }
    }
    let _ = writeln!(o, "== terms");
    for drv in [Driver::Vinc, Driver::Reference] {
        let of: Vec<Entry> = entries.iter().filter(|e| e.result.driver == drv).cloned().collect();
        if of.is_empty() {
            continue;
        }
        let _ = writeln!(o, "driver {}", driver_name(drv));
        for id in &ids {
            let _ = write!(o, "{}", terms_table(id, &of));
        }
        let _ = writeln!(o, "{}", score_table(&of, refs));
    }
    o
}
