//! Diagnosis aid, ignored by default: runs one variant in process and prints the environment actions and session
//! events of chosen nodes. `VINC_DIAG_ID=S13 VINC_DIAG_SEED=81320 VINC_DIAG_NODES=17,1 cargo test --test scenario_diag -- --ignored --nocapture`
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss
)]

use vinc_sim::Driver;
use vinc_sim::suite::run::{LayerSet, run_watching};
use vinc_sim::suite::world::{build, variants};

#[test]
#[ignore = "diagnosis aid; needs VINC_DIAG_ID, VINC_DIAG_SEED and VINC_DIAG_NODES"]
fn diag() {
    let id = std::env::var("VINC_DIAG_ID").unwrap();
    let seed: u64 = std::env::var("VINC_DIAG_SEED").unwrap().parse().unwrap();
    let nodes: Vec<usize> = std::env::var("VINC_DIAG_NODES")
        .unwrap()
        .split(',')
        .filter_map(|x| x.parse().ok())
        .collect();
    let driver = if std::env::var("VINC_DIAG_REF").is_ok() {
        Driver::Reference
    } else {
        Driver::Vinc
    };
    if let (Ok(a), Ok(b)) = (std::env::var("VINC_DIAG_FROM_S"), std::env::var("VINC_DIAG_TO_S")) {
        let ns = |x: String| x.parse::<f64>().unwrap() * 1e9;
        vinc_sim::suite::node::set_trace_window(ns(a) as u64, ns(b) as u64);
    }
    let v = variants().into_iter().find(|v| v.id == id && v.seed == seed).unwrap();
    let w = build(&v).unwrap();
    for e in w.env.iter().filter(|e| nodes.contains(&e.node)) {
        println!("ENV t{} {:?} n{} {:?}", e.t, e.kind, e.node, e.arg);
    }
    println!("adversary {:?}", w.adversary);
    for c in &w.partitions {
        println!("CUT {c:?}");
    }
    for n in &nodes {
        println!("SITE n{n} {} clock {:?}", w.nodes[*n].site, w.nodes[*n].clock);
    }
    let (r, ev) = run_watching(&w, driver, LayerSet::NODE, &nodes).unwrap();
    for l in ev {
        println!("{l}");
    }
    println!("{:?}\n{:?}", r.gates.failed(), r.late);
    for (g, st) in &r.gates.gates {
        if let vinc_sim::suite::grade::GateStatus::Fail(msgs) = st {
            println!("GATE {g} {msgs:?}");
        }
    }
    println!("{:?}", r.stats);
    println!("{:?}", r.samples);
    for v in &r.violations {
        println!("VIOLATION {v:?}");
    }
}
