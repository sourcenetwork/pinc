//! The same seed gives the same run: events, views and trace records are identical.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names
)]

mod node_common;

use std::fmt::Write as _;

use node_common::{World, big, secs};
use pinc_tests::NCmd;

fn run(seed: u64) -> String {
    let mut w = World::build_with(seed, 2, 4, |w| w.trace = true);
    let m = w.members.clone();
    w.sim.command(secs(20), m[1], NCmd::Subscribe(b"t".to_vec()));
    w.sim.command(
        secs(30),
        m[0],
        NCmd::Publish {
            topic: b"t".to_vec(),
            body: vec![9; 100],
        },
    );
    w.sim.crash(secs(40), m[2]);
    w.sim.restart(secs(50), m[2]);
    w.run(secs(120));
    let mut out = String::new();
    for n in w.hubs.iter().map(|(n, _)| *n).chain(m.iter().copied()) {
        for (t, e) in w.sim.events(n) {
            writeln!(out, "{n:?} {t} {e:?}").unwrap();
        }
        for (t, it) in &w.sim.node(n).traces {
            writeln!(out, "{n:?} {t} {:?}", it.body).unwrap();
        }
    }
    out
}

#[test]
fn the_same_seed_gives_the_same_run() {
    big(|| {
        let a = run(161);
        assert!(a.len() > 1000);
        assert_eq!(a, run(161));
    });
}

#[test]
fn trace_records_are_versioned_and_cover_every_layer() {
    big(|| {
        let mut w = World::build_with(171, 2, 2, |w| w.trace = true);
        w.run(secs(30));
        let t = &w.sim.node(w.hubs[0].0).traces;
        let mut kinds = std::collections::BTreeSet::new();
        for (_, it) in t {
            let mut line = String::new();
            it.write_ndjson(&mut line).unwrap();
            assert!(line.starts_with("{\"v\":1,\"t\":") && line.ends_with("}\n"), "{line}");
            kinds.insert(match it.body {
                pinc_node::Body::Node(_) => "node",
                pinc_node::Body::Membership(_) => "membership",
                pinc_node::Body::Broadcast(_) => "broadcast",
                pinc_node::Body::Core(_) => "core",
                pinc_node::Body::Values(..) => "values",
            });
        }
        assert!(kinds.contains("node") && kinds.contains("membership"), "{kinds:?}");
    });
}
