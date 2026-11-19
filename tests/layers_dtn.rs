//! Delay-tolerant delivery over real sessions: a bundle crosses a chain of three nodes whose contacts come and go,
//! custody moves with the copies, and a bundle that finds no way expires everywhere.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

mod layers_common;

use layers_common::{LWorld, big, secs};
use pinc_node::{DtnPlan, Enabled, NodeEvent};
use pinc_sim::NodeId as SimId;
use pinc_tests::{LayerApps, NCmd, SplitMix64};

fn plan(lifetime_s: u64) -> DtnPlan {
    DtnPlan {
        lifetime_ms: lifetime_s * 1000,
        copies: 4,
        k: 4,
        m: 2,
        slice_log: 2,
    }
}

/// Three members in id order (so custody, which moves up the order, can move along the chain) and the world.
fn chain(seed: u64, windows: impl Fn([[u8; 32]; 3]) -> [Vec<([u8; 32], u64, u64)>; 3]) -> (LWorld, [SimId; 3]) {
    // Learn the ids first: the contact windows name peers.
    let probe = LWorld::build(seed, 2, 4, |tag| {
        LayerApps::new(
            tag,
            Enabled {
                dtn: true,
                ..Enabled::NONE
            },
        )
    });
    let mut order: Vec<usize> = (0..4).collect();
    order.sort_by_key(|i| probe.id(probe.members[*i]));
    let tags: Vec<u8> = order.iter().map(|i| probe.tags[*i]).collect();
    let ids = [0, 1, 2].map(|k| probe.id(probe.members[order[k]]));
    let spec = windows(ids);
    let w = LWorld::build(seed, 2, 4, |tag| {
        let mut apps = LayerApps::new(
            tag,
            Enabled {
                dtn: true,
                ..Enabled::NONE
            },
        );
        if let Some(k) = tags.iter().take(3).position(|t| *t == tag) {
            apps.dtn.windows = Some(spec[k].clone());
        } else {
            apps.dtn.windows = Some(vec![]);
        }
        apps
    });
    let nodes = [0, 1, 2].map(|k| w.members[order[k]]);
    (w, nodes)
}

fn events(w: &LWorld, n: SimId) -> Vec<NodeEvent> {
    w.node_events(n).into_iter().map(|(_, e)| e).collect()
}

fn payload(seed: u64) -> Vec<u8> {
    let mut v = vec![0; 3000];
    SplitMix64::new(seed).fill(&mut v);
    v
}

#[test]
fn a_bundle_crosses_a_chain_of_three_nodes_with_intermittent_contacts() {
    big(|| {
        for seed in [401u64, 402, 403] {
            let (mut w, [a, b, c]) = chain(seed, |ids| {
                [
                    vec![(ids[1], 20_000, 60_000)],
                    vec![(ids[0], 20_000, 60_000), (ids[2], 100_000, 160_000)],
                    vec![(ids[1], 100_000, 160_000)],
                ]
            });
            let keys = w.apps(c).dtn.keys();
            let body = payload(seed);
            w.sim.command(
                secs(30),
                a,
                NCmd::DtnSend {
                    to: Box::new(keys),
                    payload: body.clone(),
                    plan: plan(400),
                },
            );
            w.run(secs(90));
            // Custody moved to the middle node while the first contact lasted.
            let (ea, eb) = (events(&w, a), events(&w, b));
            assert!(
                eb.iter()
                    .any(|e| matches!(e, NodeEvent::DtnCustody { from, .. } if *from == w.id(a))),
                "seed {seed}: the middle node took custody"
            );
            assert!(
                ea.iter()
                    .any(|e| matches!(e, NodeEvent::DtnHandedOff { to, .. } if *to == w.id(b))),
                "seed {seed}: the first node was relieved"
            );
            assert!(
                events(&w, c)
                    .iter()
                    .all(|e| !matches!(e, NodeEvent::DtnReceived { .. })),
                "seed {seed}: nothing reached the end during the gap"
            );
            // The second contact carries it to the destination.
            w.run(secs(200));
            let got: Vec<_> = events(&w, c)
                .into_iter()
                .filter_map(|e| match e {
                    NodeEvent::DtnReceived { source, payload, .. } => Some((source, payload)),
                    _ => None,
                })
                .collect();
            assert_eq!(
                got,
                vec![(w.id(a), body)],
                "seed {seed}: delivered once, intact, with its source"
            );
            assert!(
                events(&w, b)
                    .iter()
                    .any(|e| matches!(e, NodeEvent::DtnDelivered { .. })),
                "seed {seed}: the destination acknowledged the middle node"
            );
        }
    });
}

#[test]
fn a_bundle_that_finds_no_way_expires_at_every_holder() {
    big(|| {
        for seed in [411u64, 412] {
            // The middle node never meets the destination.
            let (mut w, [a, b, c]) = chain(seed, |ids| {
                [vec![(ids[1], 20_000, 200_000)], vec![(ids[0], 20_000, 200_000)], vec![]]
            });
            let keys = w.apps(c).dtn.keys();
            w.sim.command(
                secs(30),
                a,
                NCmd::DtnSend {
                    to: Box::new(keys),
                    payload: payload(seed),
                    plan: plan(60),
                },
            );
            w.run(secs(70));
            assert_eq!(
                w.sim.node(b).node.dtn_held(),
                1,
                "seed {seed}: the middle node holds it"
            );
            w.run(secs(140));
            for n in [a, b] {
                assert!(
                    events(&w, n).iter().any(|e| matches!(e, NodeEvent::DtnExpired { .. })),
                    "seed {seed}: {n:?} reports the expiry"
                );
                assert_eq!(
                    w.sim.node(n).node.dtn_held(),
                    0,
                    "seed {seed}: nothing held after the expiry"
                );
                assert!(w.apps(n).dtn.bundles.is_empty(), "seed {seed}: the host store is empty");
            }
            assert!(
                events(&w, c)
                    .iter()
                    .all(|e| !matches!(e, NodeEvent::DtnReceived { .. }))
            );
        }
    });
}
