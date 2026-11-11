//! The node over real sessions: hubs and members find each other, and every view converges.
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

use node_common::{World, big, secs};

#[test]
fn every_view_lists_everyone() {
    big(|| {
        for seed in [1u64, 2, 3] {
            let mut w = World::build(seed, 2, 4);
            w.run(secs(60));
            let all: Vec<_> = w
                .hubs
                .iter()
                .map(|(n, _)| *n)
                .chain(w.members.iter().copied())
                .collect();
            for n in all {
                let want = w.others(n);
                let got = w.view(n);
                assert_eq!(got, want, "seed {seed}: the view of node {n:?}");
            }
        }
    });
}

#[test]
fn a_node_with_no_hub_is_alone_and_arms_no_timer() {
    big(|| {
        let mut w = World::new(1);
        let n = w.add_member(0x40, &[], 0);
        // The beacons of local discovery are the one thing a lone node would still send.
        w.sim.node_mut(n).node.set_local_discovery(false);
        w.run(secs(120));
        assert!(w.view(n).is_empty());
        assert_eq!(w.sim.node(n).poll_timeout(), None, "an idle node arms no timer");
        assert!(w.member_events(n).is_empty(), "an idle node reports no member event");
    });
}
