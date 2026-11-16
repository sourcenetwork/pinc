//! G-DET: the same world gives the same trace hash twice in one process and in separate processes with a different
//! environment (and so a different hash-map seed). The scenario is the default seed of S5, or of every runnable
//! scenario with `VINC_SUITE_FULL=1`.
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

mod scenario_support;

use scenario_support::{run_child, selected};
use vinc_sim::Driver;
use vinc_sim::suite::grade::{GateStatus, gate_det};
use vinc_sim::suite::run::{LayerSet, Status, run};
use vinc_sim::suite::world::build;

#[test]
fn child_worker() {
    scenario_support::child_main();
}

#[test]
fn same_seed_same_trace_hash() {
    let ids: &[&str] = if scenario_support::full() {
        &["S1", "S2", "S3", "S5", "S6", "S12", "S13", "S15"]
    } else {
        &["S5"]
    };
    for v in selected(ids)
        .into_iter()
        .filter(|v| v.variant == 1 && v.set == vinc_sim::suite::world::SeedSet::Matrix)
    {
        let a = run_child(&v, Driver::Vinc, "0");
        let b = run_child(&v, Driver::Vinc, "1");
        assert!(a.result.ran && !a.result.trace_hash.is_empty());
        assert_eq!(
            gate_det(&a.result.trace_hash, &b.result.trace_hash),
            GateStatus::Pass,
            "{} seed {}",
            v.id,
            v.seed
        );
        assert_eq!(a.result.stats, b.result.stats);
    }
}

#[test]
fn same_seed_same_trace_hash_in_one_process() {
    let v = selected(&["S5"]).remove(0);
    let world = build(&v).unwrap();
    let a = run(&world, Driver::Vinc, LayerSet::NODE).unwrap();
    let b = run(&world, Driver::Vinc, LayerSet::NODE).unwrap();
    assert!(a.ran && !matches!(a.status, Status::Waiting(_)));
    assert_eq!(gate_det(&a.trace_hash, &b.trace_hash), GateStatus::Pass);
}

#[test]
fn different_seeds_differ() {
    let vs = selected(&["S5", "S6"]);
    let hashes: Vec<String> = vs
        .iter()
        .map(|v| run_child(v, Driver::Vinc, "0").result.trace_hash)
        .collect();
    assert_ne!(hashes[0], hashes[1]);
}
