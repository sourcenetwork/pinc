//! Shared code of the scenario test targets: which seeds run, how a run is made (one child process per run, so a panic
//! or a stack overflow in one cannot take the others down and the determinism check has a clean environment), what a passing run must show, and the full-run switch.
//!
//! Default run: the matrix seed of the first variant of every scenario a target covers (one run per scenario). With
//! `VINC_SUITE_FULL=1` every target runs all 96 seeds of its scenarios; the `report` test of a target (ignored by
//! default; `cargo nextest run --run-ignored all` or `cargo test -- --ignored`) prints the full tables.
#![allow(
    dead_code,
    unreachable_pub,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::too_many_lines
)]

use std::collections::BTreeMap;
use std::process::Command;
use std::sync::Mutex;
use std::time::Instant;

use vinc_sim::Driver;
use vinc_sim::suite::grade::GateStatus;
use vinc_sim::suite::run::codec::{decode, encode};
use vinc_sim::suite::run::report::{Entry, RefTerms, failures, full as full_report, gate_table};
use vinc_sim::suite::run::{LayerSet, Status, run};
use vinc_sim::suite::world::{SeedSet, Variant, build, variants};

pub const REFERENCE_TERMS: &str = include_str!("../data/reference_terms.txt");
const CHILD_ENV: &str = "VINC_SUITE_CHILD";
const BEGIN: &str = "@@RESULT";
const END: &str = "@@END";

/// Whether the full 96-seed run is switched on.
pub fn full() -> bool {
    std::env::var("VINC_SUITE_FULL").is_ok_and(|v| v == "1")
}

/// The variants of `ids` that this run covers: all of them when [`full`], else the matrix seed of the first variant.
pub fn selected(ids: &[&str]) -> Vec<Variant> {
    variants()
        .into_iter()
        .filter(|v| ids.contains(&v.id) && (full() || (v.set == SeedSet::Matrix && v.variant == 1)))
        .collect()
}

fn position(v: &Variant) -> usize {
    variants()
        .iter()
        .position(|x| x.id == v.id && x.seed == v.seed && x.variant == v.variant)
        .unwrap()
}

fn driver_code(d: Driver) -> &'static str {
    match d {
        Driver::Vinc => "v",
        Driver::Reference => "r",
    }
}

/// The body of the `child_worker` test: runs the variant named by the environment and prints the result.
pub fn child_main() {
    let Ok(spec) = std::env::var(CHILD_ENV) else { return };
    let (pos, drv) = spec.split_once(':').unwrap();
    let v = variants().swap_remove(pos.parse().unwrap());
    let driver = if drv == "r" { Driver::Reference } else { Driver::Vinc };
    let world = build(&v).unwrap();
    let t0 = Instant::now();
    let res = run(&world, driver, LayerSet::NONE).unwrap();
    println!("{BEGIN}\nwall\t{}\n{}{END}", t0.elapsed().as_secs_f64(), encode(&res));
}

/// Runs one variant in a child process.
pub fn run_child(v: &Variant, driver: Driver, perturb: &str) -> Entry {
    let out = Command::new(std::env::current_exe().unwrap())
        .args(["child_worker", "--exact", "--nocapture", "--test-threads=1"])
        .env(CHILD_ENV, format!("{}:{}", position(v), driver_code(driver)))
        .env("VINC_SUITE_PERTURB", perturb)
        .output()
        .unwrap();
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "child run of {} seed {} failed: {}\n{}",
        v.id,
        v.seed,
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let body = text
        .split_once(BEGIN)
        .and_then(|(_, r)| r.split_once(END))
        .map(|(b, _)| b)
        .expect("child printed no result");
    let (wall, rest) = body.trim_start().split_once('\n').unwrap();
    let wall_s = wall.trim_start_matches("wall\t").parse().unwrap();
    Entry {
        variant: v.clone(),
        result: decode(rest).unwrap(),
        wall_s,
    }
}

/// Runs every `(variant, driver)` pair, a few children at a time, and returns the entries in input order.
pub fn run_all(jobs: &[(Variant, Driver)]) -> Vec<Entry> {
    let width = std::thread::available_parallelism().map_or(2, |n| (n.get() / 4).clamp(2, 8));
    let next = Mutex::new(0usize);
    let done: Mutex<BTreeMap<usize, Entry>> = Mutex::new(BTreeMap::new());
    std::thread::scope(|s| {
        for _ in 0..width {
            s.spawn(|| {
                loop {
                    let i = {
                        let mut n = next.lock().unwrap();
                        let i = *n;
                        *n += 1;
                        i
                    };
                    let Some((v, d)) = jobs.get(i) else { break };
                    let e = run_child(v, *d, "0");
                    done.lock().unwrap().insert(i, e);
                }
            });
        }
    });
    done.into_inner().unwrap().into_values().collect()
}

/// The Vinc-mode entries of `ids` for the selected seeds.
pub fn vinc_entries(ids: &[&str]) -> Vec<Entry> {
    let jobs: Vec<_> = selected(ids).into_iter().map(|v| (v, Driver::Vinc)).collect();
    run_all(&jobs)
}

/// What every Vinc-mode run must show: a waiting scenario is listed and not run; a run that ran passes every gate
/// that was evaluated, has samples, and keeps its not-evaluated gates visible.
pub fn assert_entries(entries: &[Entry]) {
    assert!(!entries.is_empty(), "no run was selected");
    eprintln!("{}", gate_table(entries));
    let mut bad = Vec::new();
    for e in entries {
        let r = &e.result;
        for (g, why) in r.gates.not_evaluated() {
            eprintln!("{} seed {}: {g} not evaluated: {why}", r.id, r.seed);
        }
        for c in &r.coverage {
            eprintln!("{} seed {}: {c}", r.id, r.seed);
        }
        if let Status::Waiting(w) = &r.status {
            eprintln!("{} seed {}: WAITING for {}", r.id, r.seed, w.join("; "));
            assert!(!r.ran, "{} seed {}: a waiting scenario was run", r.id, r.seed);
            assert!(
                r.gates
                    .gates
                    .iter()
                    .all(|(_, s)| matches!(s, GateStatus::NotEvaluated(_))),
                "{} seed {}: a waiting scenario shows a verdict",
                r.id,
                r.seed
            );
            continue;
        }
        assert!(
            r.ran && !r.trace_hash.is_empty(),
            "{} seed {}: did not run",
            r.id,
            r.seed
        );
        assert!(
            r.samples.must_owed > 0 && r.samples.small > 0,
            "{} seed {}: no samples (vacuous): {:?}",
            r.id,
            r.seed,
            r.samples
        );
        assert!(
            matches!(r.status, Status::Partial(_)),
            "{} seed {}: a run without its layers claims to be complete",
            r.id,
            r.seed
        );
        if !r.gates.failed().is_empty() {
            bad.push(format!("{} seed {}", r.id, r.seed));
        }
    }
    assert!(bad.is_empty(), "gates failed on {bad:?}:\n{}", failures(entries));
}

/// Reference-mode runs of the selected seeds: they must finish and run; their gates are printed, not asserted.
pub fn assert_reference_runs(ids: &[&str]) {
    let jobs: Vec<_> = selected(ids).into_iter().map(|v| (v, Driver::Reference)).collect();
    let entries = run_all(&jobs);
    eprintln!("{}", gate_table(&entries));
    for e in &entries {
        match &e.result.status {
            Status::Waiting(_) => assert!(!e.result.ran),
            _ => assert!(
                e.result.ran && !e.result.trace_hash.is_empty(),
                "{} seed {} did not finish",
                e.result.id,
                e.result.seed
            ),
        }
    }
}

/// Both drivers over the selected seeds, printed as the full report.
pub fn print_report(ids: &[&str]) {
    let mut jobs = Vec::new();
    for v in selected(ids) {
        jobs.push((v.clone(), Driver::Vinc));
        jobs.push((v, Driver::Reference));
    }
    let entries = run_all(&jobs);
    let refs = RefTerms::parse(REFERENCE_TERMS).unwrap();
    println!("{}", full_report(&entries, &refs));
}

#[allow(unused_macros)]
/// Declares the tests of a scenario target covering `$ids`.
macro_rules! scenario_target {
    ($ids:expr) => {
        #[test]
        fn child_worker() {
            $crate::scenario_support::child_main();
        }

        /// Every gate that was evaluated passes on the selected seeds (the matrix seed of the first variant, or all
        /// 96 seeds with `VINC_SUITE_FULL=1`), the samples are not vacuous, a waiting scenario is listed.
        #[test]
        fn vinc_mode_gates() {
            $crate::scenario_support::assert_entries(&$crate::scenario_support::vinc_entries(&$ids));
        }

        /// The reference driver mode finishes on the same seeds.
        #[test]
        fn reference_mode_finishes() {
            $crate::scenario_support::assert_reference_runs(&$ids);
        }

        /// Prints the gate, term and score tables of both drivers (ignored by default).
        #[test]
        #[ignore = "prints the report; run with --ignored, add VINC_SUITE_FULL=1 for all 96 seeds"]
        fn report() {
            $crate::scenario_support::print_report(&$ids);
        }
    };
}
