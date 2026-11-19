//! Shared code of the scenario test targets: which seeds run, how a run is made (one child process per run, so a panic
//! or a stack overflow in one cannot take the others down and the determinism check has a clean environment), what a passing run must show, and the full-run switch.
//!
//! Default run: one seed of the first variant of every scenario a target covers, its matrix seed unless
//! [`DEFAULT_SEED_SET`] names another group for the scenario (one run per scenario). With `PINC_SUITE_FULL=1` every
//! target runs all 96 seeds of its scenarios; the `report` test of a target (ignored by default;
//! `cargo nextest run --run-ignored all` or `cargo test -- --ignored`) prints the full tables.
//!
//! `PINC_SUITE_LOSS_SALT=k` (an integer, default 0) selects another realization of every LAN's packet loss: a row that
//! depends on which packets a link happens to lose is judged over several realizations, not one, for example
//! `PINC_SUITE_FULL=1 PINC_SUITE_LOSS_SALT=3 cargo nextest run --run-ignored all`. The switch is read by the
//! reference random source of `pinc-sim` (`RefRng`), and a value that is not an integer fails the run.
#![allow(
    dead_code,
    unreachable_pub,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::too_many_lines
)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::process::Command;
use std::sync::Mutex;
use std::time::Instant;

use pinc_sim::Driver;
use pinc_sim::suite::grade::GateStatus;
use pinc_sim::suite::run::codec::{decode, encode};
use pinc_sim::suite::run::report::{
    Entry, RefTerms, failures, full as full_report, gate_table, score_table, terms_table,
};
use pinc_sim::suite::run::{LayerSet, Status, run};
use pinc_sim::suite::world::model::{IntentKind, Must};
use pinc_sim::suite::world::{SeedSet, Variant, build, variants};

pub const REFERENCE_TERMS: &str = include_str!("../data/reference_terms.txt");
const CHILD_ENV: &str = "PINC_SUITE_CHILD";
const BEGIN: &str = "@@RESULT";
const END: &str = "@@END";

/// Whether the full 96-seed run is switched on.
pub fn full() -> bool {
    std::env::var("PINC_SUITE_FULL").is_ok_and(|v| v == "1")
}

/// The scenarios whose default seed is not the matrix seed of the first variant, with the group their default comes
/// from. The full run still runs every seed.
const DEFAULT_SEED_SET: &[(&str, SeedSet)] = &[
    // The matrix seed 86017 depends on the draw of the link loss: it fails in five of eight realizations on master and
    // in the reference model too (#516); it stays in the full run.
    ("S6", SeedSet::Extra1),
];

/// The group of seeds the default run takes for scenario `id`.
fn default_seed_set(id: &str) -> SeedSet {
    DEFAULT_SEED_SET
        .iter()
        .find_map(|&(s, set)| (s == id).then_some(set))
        .unwrap_or(SeedSet::Matrix)
}

/// The variants of `ids` that this run covers: all of them when [`full`], else one seed of the first variant (its
/// matrix seed, or the group [`DEFAULT_SEED_SET`] names for the scenario). `PINC_SUITE_LOSS_SALT` does not change the
/// selection, it changes the realization of the link loss the seeds run in.
pub fn selected(ids: &[&str]) -> Vec<Variant> {
    variants()
        .into_iter()
        .filter(|v| ids.contains(&v.id) && (full() || (v.set == default_seed_set(v.id) && v.variant == 1)))
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
        Driver::Pinc => "v",
        Driver::Reference => "r",
    }
}

/// The body of the `child_worker` test: runs the variant named by the environment and prints the result.
pub fn child_main() {
    let Ok(spec) = std::env::var(CHILD_ENV) else { return };
    let (pos, drv) = spec.split_once(':').unwrap();
    let v = variants().swap_remove(pos.parse().unwrap());
    let driver = if drv == "r" { Driver::Reference } else { Driver::Pinc };
    let world = build(&v).unwrap();
    let t0 = Instant::now();
    let res = run(&world, driver, LayerSet::NODE).unwrap();
    println!("{BEGIN}\nwall\t{}\n{}{END}", t0.elapsed().as_secs_f64(), encode(&res));
}

/// Runs one variant in a child process.
pub fn run_child(v: &Variant, driver: Driver, perturb: &str) -> Entry {
    let out = Command::new(std::env::current_exe().unwrap())
        .args(["child_worker", "--exact", "--nocapture", "--test-threads=1"])
        .env(CHILD_ENV, format!("{}:{}", position(v), driver_code(driver)))
        .env("PINC_SUITE_PERTURB", perturb)
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

/// The Pinc-mode entries of `ids` for the selected seeds.
pub fn pinc_entries(ids: &[&str]) -> Vec<Entry> {
    let jobs: Vec<_> = selected(ids).into_iter().map(|v| (v, Driver::Pinc)).collect();
    run_all(&jobs)
}

/// Whether the world of `v` has intents that owe must deliveries, and intents that give small-message latency samples.
fn expected_samples(v: &Variant) -> (bool, bool) {
    let world = build(v).unwrap();
    let (mut must, mut small) = (false, false);
    for it in &world.intents {
        let others: Vec<usize> = match it.kind {
            IntentKind::Publish => it.receivers.iter().copied().filter(|&r| r != it.node).collect(),
            IntentKind::Push | IntentKind::Docsync | IntentKind::Manage | IntentKind::Reconcile => {
                it.to.into_iter().filter(|&r| r != it.node).collect()
            }
            IntentKind::Echo => it.to.into_iter().collect(),
            IntentKind::Fetch => vec![it.node],
        };
        let is_small = !matches!(it.kind, IntentKind::Echo | IntentKind::Fetch);
        small |= is_small && !others.is_empty();
        must |= match &it.must {
            Must::Flag(f) => *f && !others.is_empty(),
            Must::Set(set) => set.iter().any(|&r| r != it.node),
        };
    }
    (must, small)
}

/// What every Pinc-mode run must show: a waiting scenario is listed and not run; a run that ran passes every gate
/// that was evaluated, has samples, and keeps its not-evaluated gates visible.
pub fn assert_entries(entries: &[Entry]) {
    assert!(!entries.is_empty(), "no run was selected");
    eprintln!("{}", gate_table(entries));
    write_tables(entries);
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
        // Samples are required where the world has the intents that produce them: a world with no small push has no
        // small-message latency to measure.
        let (must, small) = expected_samples(&e.variant);
        assert!(
            (r.samples.must_owed > 0 || !must) && (r.samples.small > 0 || !small),
            "{} seed {}: no samples (vacuous): {:?}",
            r.id,
            r.seed,
            r.samples
        );
        if !r.gates.failed().is_empty() {
            bad.push(format!("{} seed {}", r.id, r.seed));
        }
    }
    assert!(bad.is_empty(), "gates failed on {bad:?}:\n{}", failures(entries));
}

/// With `PINC_SUITE_OUT` naming a directory, the gate, failure, term and score tables of these runs are written there,
/// one file per test target, whatever the gates say: a passing run keeps its terms too. The terms are pooled per seed
/// set and over all sets.
fn write_tables(entries: &[Entry]) {
    let Ok(dir) = std::env::var("PINC_SUITE_OUT") else {
        return;
    };
    let ids: BTreeSet<&str> = entries.iter().map(|e| e.result.id.as_str()).collect();
    let mut o = gate_table(entries);
    o += &failures(entries);
    for id in &ids {
        for set in [SeedSet::Matrix, SeedSet::Extra1, SeedSet::Noise, SeedSet::Extra2] {
            let sub: Vec<Entry> = entries
                .iter()
                .filter(|e| e.result.id == *id && e.variant.set == set)
                .cloned()
                .collect();
            if !sub.is_empty() {
                let _ = writeln!(o, "--- {id} {set:?}");
                o += &terms_table(id, &sub);
            }
        }
        let _ = writeln!(o, "--- {id} all sets");
        o += &terms_table(id, entries);
    }
    o += "--- runs: wire and application bytes, CPU by part\n";
    for e in entries {
        let (r, t) = (&e.result, &e.result.stats);
        let _ = writeln!(
            o,
            "{} {:?} {} wire {} app {} third {} cpu {:?}",
            r.id, e.variant.set, r.seed, t.wire_bytes, t.app_bytes, t.third_bytes, t.cpu
        );
    }
    o += &score_table(entries, &RefTerms::parse(REFERENCE_TERMS).unwrap());
    let name = ids.into_iter().collect::<Vec<_>>().join("-");
    std::fs::write(format!("{dir}/{name}.txt"), o).unwrap_or_else(|e| panic!("writing the tables to {dir}: {e}"));
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
        jobs.push((v.clone(), Driver::Pinc));
        jobs.push((v, Driver::Reference));
    }
    let entries = run_all(&jobs);
    let refs = RefTerms::parse(REFERENCE_TERMS).unwrap();
    println!("{}", full_report(&entries, &refs));
}

#[allow(unused_macros)]
/// Declares the tests of a scenario target covering `$ids`. An optional second argument is the reason the gate test is
/// ignored for now: a seed that still fails a gate is named there, and the test runs with `--ignored`.
macro_rules! scenario_target {
    ($ids:expr $(, $why:literal)?) => {
        #[test]
        fn child_worker() {
            $crate::scenario_support::child_main();
        }

        /// Every gate that was evaluated passes on the selected seeds (one seed of the first variant of each scenario,
        /// or all 96 seeds with `PINC_SUITE_FULL=1`), the samples are not vacuous, a waiting scenario is listed.
        #[test]
        $(#[ignore = $why])?
        fn pinc_mode_gates() {
            $crate::scenario_support::assert_entries(&$crate::scenario_support::pinc_entries(&$ids));
        }

        /// The reference driver mode finishes on the same seeds.
        #[test]
        fn reference_mode_finishes() {
            $crate::scenario_support::assert_reference_runs(&$ids);
        }

        /// Prints the gate, term and score tables of both drivers (ignored by default).
        #[test]
        #[ignore = "prints the report; run with --ignored, add PINC_SUITE_FULL=1 for all 96 seeds"]
        fn report() {
            $crate::scenario_support::print_report(&$ids);
        }
    };
}
