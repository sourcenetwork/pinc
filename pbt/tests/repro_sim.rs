//! Reproducing tests of bugs the `sim_*` properties found in `pinc-sim`. Each fails on the unmodified code.

use pinc_sim::Driver;
use pinc_sim::suite::run::{LayerSet, codec, run};
use pinc_sim::suite::world::{Param, Params, generate};

fn one(id: &str, seed: u64, duration_s: i64, driver: Driver, layers: LayerSet) -> String {
    let mut params = Params::new();
    params.insert("duration_s".to_owned(), Param::Int(duration_s));
    let w = generate(id, &params, seed).unwrap();
    let r = run(&w, driver, layers).unwrap();
    format!("{}\n{}", r.trace_hash, codec::encode(&r))
}

fn differing(a: &str, b: &str) -> usize {
    a.lines().zip(b.lines()).filter(|(x, y)| x != y).count()
}

/// The same scenario run twice in a row in a fresh process gives two different results (another trace hash, other
/// terms, samples and counters): S5 at seed 2094483974239808261 for 29 s, the reference driver, the node's layers.
///
/// Expected (pinc-sim lib.rs): "The same seed and the same scenario calls give a byte-identical run and trace." A
/// run's inputs are its world, its driver and its layers (`suite::run::run`).
///
/// Actual: the second run differs from the first in 18 of 46 encoded lines, the trace hash first (the property's
/// case: `EPHYRA_REPLAY=3958981436805609987:5` of `a_run_depends_only_on_its_world_driver_and_layers`). A probe also
/// saw S5 at seed 1 (pinc driver, core UDP only) change after an S2 run in between, and runs after an S11 run stay
/// equal: the result follows the history of the process.
///
/// Suspected fault: the connection tables a finished run gives back are reused by the next run
/// (crates/pinc-sim/src/suite/node/mem.rs:76-104, `recycle` and `slots`: "a node gets its own table again ... else any
/// given back"), and some state of a table survives `Endpoint::into_slots` (crates/pinc-core/src/endpoint.rs:528-546,
/// "every session closed and every slot's memory returned, so another endpoint can run in the same memory") and the
/// reset in `slots` (only the shared loss estimate is reset). The first run takes fresh tables, the second recycled
/// ones. Not isolated further: whether the leak is in what pinc-core hands back (a slot's streams or tables) or in
/// what the simulator keeps beside it.
///
/// Who: the test and bench suite (any caller of `suite::run::run` that runs more than one world in a process): a
/// result, a gate verdict or a regression comparison depends on the order the runs are made in.
///
/// This test must be the only one of its binary: the first run has to be the first of the process.
#[test]
fn a_scenario_run_twice_in_a_row_gives_two_traces() {
    let h = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let x = || one("S5", 2_094_483_974_239_808_261, 29, Driver::Reference, LayerSet::NODE);
            let first = x();
            let second = x();
            eprintln!("lines differing between the two runs: {}", differing(&first, &second));
            assert!(second == first, "the second run of the same world differs from the first");
        })
        .unwrap();
    if let Err(e) = h.join() {
        std::panic::resume_unwind(e);
    }
}
