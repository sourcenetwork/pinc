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

#[test]
fn a_rerun_world_does_not_grow_the_process() {
    let v = variants().into_iter().find(|v| v.id == "S13").unwrap();
    let world = build(&v).unwrap();
    let mut seen = Vec::new();
    for _ in 0..6 {
        let r = run(&world, Driver::Vinc, LayerSet::NODE).unwrap();
        assert!(r.ran);
        seen.push(resident());
    }
    let mib = |b: u64| b as f64 / f64::from(1u32 << 20);
    println!(
        "resident after each run (MiB): {:?}",
        seen.iter().map(|b| mib(*b)).collect::<Vec<_>>()
    );
    // The first three runs are a warm-up, not a leak. The connection memory of a node is one zeroed allocation per
    // table, so a page becomes resident only when a connection first touches it, and a recycled table hands its pool
    // chunks out in the order the previous run released them: the pages a node touches differ from run to run until
    // every chunk its busiest sessions can use has been touched once. Measured: the resident size rises by about
    // 20 MiB and 45 MiB over the second and third run and then stays flat to a few tens of KiB over the next five. A
    // leak keeps adding to it, which the fourth and sixth run show.
    let growth = seen[5].saturating_sub(seen[3]);
    assert!(growth <= 2 * GROWTH_PER_RUN, "grew {} MiB over two runs", mib(growth));
}
