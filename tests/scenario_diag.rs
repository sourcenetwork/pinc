//! Diagnosis aid, ignored by default: runs one variant in process and prints the environment actions and session
//! events of chosen nodes. `PINC_DIAG_ID=S13 PINC_DIAG_SEED=81320 PINC_DIAG_NODES=17,1 cargo test --test scenario_diag -- --ignored --nocapture`
//!
//! `PINC_DIAG_REF_POLL=1` does not run the reference model. The library runs either way; the switch only polls its
//! node the way the reference model's harness polls a node ([`Driver::Reference`]: not after a harness intent), which
//! is one of the two ways the scenario suite drives the library. The reference model's own run of a world is made
//! outside this repository, so nothing here compares the library with it.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss
)]

use pinc_sim::Driver;
use pinc_sim::suite::run::{LayerSet, run_watching};
use pinc_sim::suite::world::{build, variants};

#[test]
#[ignore = "diagnosis aid; needs PINC_DIAG_ID, PINC_DIAG_SEED and PINC_DIAG_NODES"]
fn diag() {
    let id = std::env::var("PINC_DIAG_ID").unwrap();
    let seed: u64 = std::env::var("PINC_DIAG_SEED").unwrap().parse().unwrap();
    // PINC_DIAG_DECISIONS=1 prints only the decision lines of every node, in the form the reference side prints, for
    // comparing the two runs of one world (nodes need not be named).
    let decisions = std::env::var("PINC_DIAG_DECISIONS").is_ok();
    pinc_sim::suite::node::set_decision_trace(decisions);
    let nodes: Vec<usize> = std::env::var("PINC_DIAG_NODES")
        .unwrap_or_default()
        .split(',')
        .filter_map(|x| x.parse().ok())
        .collect();
    let driver = if std::env::var("PINC_DIAG_REF_POLL").is_ok() {
        Driver::Reference
    } else {
        Driver::Pinc
    };
    if let (Ok(a), Ok(b)) = (std::env::var("PINC_DIAG_FROM_S"), std::env::var("PINC_DIAG_TO_S")) {
        let ns = |x: String| x.parse::<f64>().unwrap() * 1e9;
        pinc_sim::suite::node::set_trace_window(ns(a) as u64, ns(b) as u64);
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
    for l in ev
        .iter()
        .filter(|l| !decisions || l.starts_with("D ") || l.starts_with("C ") || l.starts_with("S "))
    {
        println!("{l}");
    }
    if decisions {
        return;
    }
    println!("{:?}\n{:?}", r.gates.failed(), r.late);
    for (g, st) in &r.gates.gates {
        if let pinc_sim::suite::grade::GateStatus::Fail(msgs) = st {
            println!("GATE {g} {msgs:?}");
        }
    }
    println!("{:?}", r.stats);
    println!("{:?}", r.samples);
    for v in &r.violations {
        println!("VIOLATION {v:?}");
    }
}
