//! Diagnosis aid, ignored by default: runs one variant in process and prints the environment actions and session
//! events of chosen nodes. `SUITE_ID=S13 SUITE_SEED=81320 SUITE_NODES=17,1 cargo test --test scenario_diag -- --ignored --nocapture`
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

use vinc_sim::Driver;
use vinc_sim::suite::run::{LayerSet, run_watching};
use vinc_sim::suite::world::{build, variants};

#[test]
#[ignore = "diagnosis aid; needs SUITE_ID, SUITE_SEED and SUITE_NODES"]
fn diag() {
    let id = std::env::var("SUITE_ID").unwrap();
    let seed: u64 = std::env::var("SUITE_SEED").unwrap().parse().unwrap();
    let nodes: Vec<usize> = std::env::var("SUITE_NODES")
        .unwrap()
        .split(',')
        .filter_map(|x| x.parse().ok())
        .collect();
    let driver = if std::env::var("SUITE_REF").is_ok() {
        Driver::Reference
    } else {
        Driver::Vinc
    };
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
        println!("SITE n{n} {}", w.nodes[*n].site);
    }
    let (r, ev) = run_watching(&w, driver, LayerSet::NONE, &nodes).unwrap();
    for l in ev {
        println!("{l}");
    }
    println!("{:?}\n{:?}", r.gates.failed(), r.late);
    println!("{:?}", r.stats);
}
