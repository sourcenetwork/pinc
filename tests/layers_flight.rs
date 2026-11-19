//! A first flight that reaches the answering node twice inside one carrier read is answered at once: the answer does
//! not wait for the answering side's resend timer.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names
)]

mod layers_common;

use layers_common::{LWorld, big, secs};
use pinc_node::Enabled;
use pinc_node::trace::{Body, NodeTrace};
use pinc_sim::{MS, Time};
use pinc_tests::{LayerApps, NCmd, SplitMix64};

fn values_on(t: u8) -> LayerApps {
    LayerApps::new(
        t,
        Enabled {
            values: true,
            ..Enabled::NONE
        },
    )
}

/// When the first layer a peer dialed came up at node `n`, at or after `from`.
fn incoming_up(w: &LWorld, n: pinc_sim::NodeId, from: Time) -> Option<Time> {
    w.sim.node(n).traces.iter().find_map(|(t, it)| {
        (*t >= from && matches!(it.body, Body::Node(NodeTrace::LayerUp { incoming: 1, .. }))).then_some(*t)
    })
}

#[test]
fn a_flight_read_twice_in_one_carrier_read_is_answered_at_once() {
    big(|| {
        for seed in [301u64, 302, 303] {
            let mut w = LWorld::build_with(seed, 1, 4, 8_000_000, true, values_on);
            let m = w.members.clone();
            let mut value = vec![0; 2 << 20];
            SplitMix64::new(seed).fill(&mut value);
            let mut root = [0; 32];
            for p in &m[1..4] {
                root = w.provide(*p, value.clone());
                w.sim.node_mut(*p).carrier_hold = 10 * MS;
            }
            let providers: Vec<[u8; 32]> = m[1..4].iter().map(|n| w.id(*n)).collect();
            let at = secs(30);
            w.sim.command(
                at,
                m[0],
                NCmd::ValuesFetch {
                    root,
                    length: value.len() as u64,
                    ranges: vec![],
                    providers,
                },
            );
            w.run(secs(40));
            for p in &m[1..4] {
                let up = incoming_up(&w, *p, at).unwrap_or_else(|| panic!("seed {seed}: {p:?} took no session"));
                assert!(
                    up - at < 150 * MS,
                    "seed {seed}: the session came up {} ms after the dial",
                    (up - at) / MS
                );
            }
        }
    });
}
