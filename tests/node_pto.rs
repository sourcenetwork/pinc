//! A healthy session never has two probe timeouts in a row. An early run once showed that on a session with no
//! fault in the world; this samples every session of every node each second, over many seeds and a fault-free
//! world, and fails on the first one.
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
use pinc_node::Ep;

#[test]
fn no_healthy_session_has_a_probe_timeout_outstanding() {
    big(|| {
        let (mut sessions_sampled, mut ones) = (0u64, 0u64);
        for seed in 300u64..324 {
            let mut w = World::build(seed, 2, 6);
            let nodes: Vec<_> = w
                .hubs
                .iter()
                .map(|(n, _)| *n)
                .chain(w.members.iter().copied())
                .collect();
            for t in 1..=150 {
                w.run(secs(t));
                for n in &nodes {
                    let ep = w.sim.node(*n).node.endpoint();
                    let mut i = 0;
                    while let Some(st) = ep.session_at(i) {
                        i += 1;
                        if st.established {
                            sessions_sampled += 1;
                            ones += u64::from(st.pto_count == 1);
                            assert!(
                                st.pto_count < 2,
                                "seed {seed} at {t} s: node {n:?} session {:?} to {:?} has {} probe timeouts in a row",
                                st.session,
                                st.node,
                                st.pto_count
                            );
                        }
                    }
                }
            }
        }
        eprintln!("{sessions_sampled} session samples, {ones} with one probe timeout outstanding");
        assert!(
            sessions_sampled > 10_000,
            "the sampling covered the sessions: {sessions_sampled}"
        );
    });
}
