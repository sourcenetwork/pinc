//! Memory across runs: the same world run again and again in one process keeps its resident size flat, because a
//! restarted node reuses the connection table of its previous incarnation and a finished run gives its tables back.
//! The scenario is S12 (many restarts); the numbers print with `--nocapture`.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_precision_loss
)]

use vinc_sim::Driver;
use vinc_sim::suite::run::{LayerSet, run};
use vinc_sim::suite::world::{build, variants};

/// The resident set of this process in bytes (Linux).
fn resident() -> u64 {
    let statm = std::fs::read_to_string("/proc/self/statm").unwrap();
    statm.split_whitespace().nth(1).unwrap().parse::<u64>().unwrap() * 4096
}

/// How much one more run may grow the process: far below the 16 MiB an incarnation used to leak.
const GROWTH_PER_RUN: u64 = 8 << 20;
/// How many times the world is run.
const RUNS: usize = 12;
/// The runs in which the warm-up may grow the process by more than that.
const WARM_UP_STEPS: usize = 2;
/// The most the warm-up adds in all: the two steps measured come to about 62 MiB.
const WARM_UP_TOTAL: u64 = 80 << 20;

#[test]
fn a_rerun_world_does_not_grow_the_process() {
    let v = variants().into_iter().find(|v| v.id == "S13").unwrap();
    let world = build(&v).unwrap();
    let mut seen = Vec::new();
    for _ in 0..RUNS {
        let r = run(&world, Driver::Vinc, LayerSet::NODE).unwrap();
        assert!(r.ran);
        seen.push(resident());
    }
    let mib = |b: u64| b as f64 / f64::from(1u32 << 20);
    println!(
        "resident after each run (MiB): {:?}",
        seen.iter().map(|b| mib(*b)).collect::<Vec<_>>()
    );
    // A node's connection memory is recycled between runs and becomes resident page by page as sessions first touch
    // it, so the process grows in a few steps while the busiest sessions reach pages no earlier run touched, and then
    // stays flat. Measured: one step of about 15 MiB and one of about 45 MiB, at the second run and at some later run
    // (the third to the tenth were seen; which one depends on the order the chunks were released in), then flat to a
    // few tens of KiB. A leak is different in kind: it adds to the process at every run. So a leak shows as growth in more runs
    // than the warm-up has steps, and as a total above what the tables can hold.
    let steps = seen
        .windows(2)
        .filter(|w| w[1].saturating_sub(w[0]) > GROWTH_PER_RUN)
        .count();
    assert!(
        steps <= WARM_UP_STEPS,
        "the process grew by more than 8 MiB in {steps} of {RUNS} runs"
    );
    let total = seen[RUNS - 1].saturating_sub(seen[0]);
    assert!(total <= WARM_UP_TOTAL, "grew {} MiB over {RUNS} runs", mib(total));
}
