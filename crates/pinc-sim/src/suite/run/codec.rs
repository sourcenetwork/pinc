//! A text form of a [`RunResult`], so a run in one process can be read in another.
//!
//! A long series of runs is made one process per run, so one run cannot take the others down, and the parent reads
//! each child's result through this form. The form is lossless:
//! floats travel as their bit patterns, strings are escaped, and `decode(encode(r))` equals `r` field by field.
//!
//! Invariants: one record per line, tab-separated, strings escaped for backslash, tab and newline; an unknown line is
//! an error, never skipped.

use std::collections::BTreeMap;
use std::fmt::Write;

use super::{LayerSet, RunResult, Samples, Stats, Status};
use crate::Driver;
use crate::suite::grade::{FairSamples, GATES, GateReport, GateStatus, TERMS, Terms};
use crate::suite::rec::Violation;

fn esc(s: &str) -> String {
    s.replace('\\', "\\\\").replace('\t', "\\t").replace('\n', "\\n")
}

fn unesc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut it = s.chars();
    while let Some(c) = it.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match it.next() {
            Some('t') => out.push('\t'),
            Some('n') => out.push('\n'),
            Some(o) => out.push(o),
            None => {}
        }
    }
    out
}

fn terms_line(tag: &str, t: &Terms, out: &mut String) {
    let _ = write!(out, "{tag}");
    for (_, v) in t.iter() {
        match v {
            Some(x) => {
                let _ = write!(out, "\t{:x}", x.to_bits());
            }
            None => out.push_str("\t-"),
        }
    }
    out.push('\n');
}

fn map_lines(tag: &str, m: &BTreeMap<String, u64>, out: &mut String) {
    for (k, v) in m {
        let _ = writeln!(out, "{tag}\t{}\t{v}", esc(k));
    }
}

/// Encodes a result.
pub fn encode(r: &RunResult) -> String {
    let mut o = String::new();
    let l = r.layers;
    let bits: String = [l.broadcast, l.values, l.reconcile, l.membership, l.connectivity]
        .iter()
        .map(|b| if *b { '1' } else { '0' })
        .collect();
    let _ = writeln!(
        o,
        "id\t{}\t{}\t{:?}\t{bits}\t{}\t{}\t{}",
        esc(&r.id),
        r.seed,
        r.driver,
        r.ran,
        r.intents_total,
        r.trace_hash
    );
    match &r.status {
        Status::Running => o.push_str("status\trunning\n"),
        Status::Partial(w) => {
            let _ = writeln!(
                o,
                "status\tpartial\t{}",
                w.iter().map(|x| esc(x)).collect::<Vec<_>>().join("\t")
            );
        }
        Status::Waiting(w) => {
            let _ = writeln!(
                o,
                "status\twaiting\t{}",
                w.iter().map(|x| esc(x)).collect::<Vec<_>>().join("\t")
            );
        }
    }
    map_lines("excluded", &r.excluded, &mut o);
    map_lines("scheduled", &r.scheduled, &mut o);
    for (g, s) in &r.gates.gates {
        let (kind, msgs) = match s {
            GateStatus::Pass => ("pass", vec![]),
            GateStatus::Fail(m) => ("fail", m.clone()),
            GateStatus::NotApplicable => ("na", vec![]),
            GateStatus::Pending => ("pending", vec![]),
            GateStatus::NotEvaluated(m) => ("noteval", vec![m.clone()]),
        };
        let _ = writeln!(
            o,
            "gate\t{g}\t{kind}\t{}",
            msgs.iter().map(|x| esc(x)).collect::<Vec<_>>().join("\t")
        );
    }
    for c in &r.coverage {
        let _ = writeln!(o, "coverage\t{}", esc(c));
    }
    terms_line("terms", &r.terms, &mut o);
    terms_line("fair", &r.fair, &mut o);
    let f = r.fair_samples;
    let _ = writeln!(
        o,
        "fairs\t{}\t{}\t{}\t{}\t{}\t{}",
        f.small, f.small_current, f.under_bulk, f.under_bulk_current, f.stream, f.stream_current
    );
    let s = r.samples;
    let _ = writeln!(
        o,
        "samples\t{}\t{}\t{}\t{}\t{}\t{}",
        s.intents, s.must_intents, s.must_owed, s.must_in_time, s.small, s.must_echoes
    );
    for v in &r.violations {
        let _ = writeln!(o, "viol\t{}\t{}\t{}\t{}", v.gate, v.node, v.t, esc(&v.msg));
    }
    let t = &r.stats;
    let _ = writeln!(
        o,
        "stats\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
        t.wire_bytes, t.app_bytes, t.third_bytes, t.resumes, t.crashes, t.punched, t.mtu_drops, t.events
    );
    map_lines("adv", &t.adversary, &mut o);
    map_lines("drop", &t.drops, &mut o);
    map_lines("sw", &t.stack_waiting, &mut o);
    map_lines("cpu", &t.cpu, &mut o);
    for l in &r.late {
        let _ = writeln!(o, "late\t{}", esc(l));
    }
    o
}

fn num<T: std::str::FromStr>(s: Option<&&str>) -> Result<T, String> {
    s.and_then(|x| x.parse().ok())
        .ok_or_else(|| "a number is missing or malformed".to_owned())
}

fn terms_of(f: &[&str]) -> Result<Terms, String> {
    let mut t = Terms::new();
    for (name, v) in TERMS.iter().zip(f.iter().skip(1)) {
        if *v != "-" {
            let bits = u64::from_str_radix(v, 16).map_err(|e| e.to_string())?;
            t.set(name, Some(f64::from_bits(bits)));
        }
    }
    Ok(t)
}

/// Decodes the text made by [`encode`].
///
/// # Errors
/// A message naming the malformed line.
pub fn decode(text: &str) -> Result<RunResult, String> {
    let mut r = RunResult {
        id: String::new(),
        seed: 0,
        driver: Driver::Pinc,
        layers: LayerSet::NONE,
        status: Status::Running,
        ran: false,
        excluded: BTreeMap::new(),
        scheduled: BTreeMap::new(),
        intents_total: 0,
        gates: GateReport { gates: Vec::new() },
        coverage: Vec::new(),
        terms: Terms::new(),
        fair: Terms::new(),
        fair_samples: FairSamples::default(),
        samples: Samples::default(),
        trace_hash: String::new(),
        violations: Vec::new(),
        stats: Stats::default(),
        late: Vec::new(),
    };
    for line in text.lines().filter(|l| !l.is_empty()) {
        let f: Vec<&str> = line.split('\t').collect();
        let bad = || format!("malformed line: {line}");
        match f.first().copied().unwrap_or("") {
            "id" => {
                r.id = unesc(f.get(1).ok_or_else(bad)?);
                r.seed = num(f.get(2))?;
                r.driver = if f.get(3) == Some(&"Reference") {
                    Driver::Reference
                } else {
                    Driver::Pinc
                };
                let b: Vec<bool> = f.get(4).ok_or_else(bad)?.chars().map(|c| c == '1').collect();
                let g = |i: usize| b.get(i).copied().unwrap_or(false);
                r.layers = LayerSet {
                    broadcast: g(0),
                    values: g(1),
                    reconcile: g(2),
                    membership: g(3),
                    connectivity: g(4),
                };
                r.ran = f.get(5) == Some(&"true");
                r.intents_total = num(f.get(6))?;
                r.trace_hash = (*f.get(7).ok_or_else(bad)?).to_owned();
            }
            "status" => {
                let w: Vec<String> = f.iter().skip(2).map(|x| unesc(x)).collect();
                r.status = match f.get(1).copied() {
                    Some("running") => Status::Running,
                    Some("partial") => Status::Partial(w),
                    Some("waiting") => Status::Waiting(w),
                    _ => return Err(bad()),
                };
            }
            "excluded" | "scheduled" | "adv" | "drop" | "sw" | "cpu" => {
                let (k, v) = (unesc(f.get(1).ok_or_else(bad)?), num::<u64>(f.get(2))?);
                match f[0] {
                    "excluded" => r.excluded.insert(k, v),
                    "scheduled" => r.scheduled.insert(k, v),
                    "adv" => r.stats.adversary.insert(k, v),
                    "drop" => r.stats.drops.insert(k, v),
                    "cpu" => r.stats.cpu.insert(k, v),
                    _ => r.stats.stack_waiting.insert(k, v),
                };
            }
            "gate" => {
                let name = GATES.iter().find(|g| Some(**g) == f.get(1).copied()).ok_or_else(bad)?;
                let msgs: Vec<String> = f.iter().skip(3).map(|x| unesc(x)).collect();
                let st = match f.get(2).copied() {
                    Some("pass") => GateStatus::Pass,
                    Some("fail") => GateStatus::Fail(msgs),
                    Some("na") => GateStatus::NotApplicable,
                    Some("pending") => GateStatus::Pending,
                    Some("noteval") => GateStatus::NotEvaluated(msgs.into_iter().next().unwrap_or_default()),
                    _ => return Err(bad()),
                };
                r.gates.gates.push((name, st));
            }
            "coverage" => r.coverage.push(unesc(f.get(1).ok_or_else(bad)?)),
            "terms" => r.terms = terms_of(&f)?,
            "fair" => r.fair = terms_of(&f)?,
            "fairs" => {
                r.fair_samples = FairSamples {
                    small: num(f.get(1))?,
                    small_current: num(f.get(2))?,
                    under_bulk: num(f.get(3))?,
                    under_bulk_current: num(f.get(4))?,
                    stream: num(f.get(5))?,
                    stream_current: num(f.get(6))?,
                };
            }
            "samples" => {
                r.samples = Samples {
                    intents: num(f.get(1))?,
                    must_intents: num(f.get(2))?,
                    must_owed: num(f.get(3))?,
                    must_in_time: num(f.get(4))?,
                    small: num(f.get(5))?,
                    must_echoes: num(f.get(6))?,
                };
            }
            "viol" => r.violations.push(Violation {
                gate: (*f.get(1).ok_or_else(bad)?).to_owned(),
                node: num(f.get(2))?,
                t: num(f.get(3))?,
                msg: unesc(f.get(4).ok_or_else(bad)?),
            }),
            "stats" => {
                r.stats.wire_bytes = num(f.get(1))?;
                r.stats.app_bytes = num(f.get(2))?;
                r.stats.third_bytes = num(f.get(3))?;
                r.stats.resumes = num(f.get(4))?;
                r.stats.crashes = num(f.get(5))?;
                r.stats.punched = num(f.get(6))?;
                r.stats.mtu_drops = num(f.get(7))?;
                r.stats.events = num(f.get(8))?;
            }
            "late" => r.late.push(unesc(f.get(1).ok_or_else(bad)?)),
            _ => return Err(bad()),
        }
    }
    Ok(r)
}
