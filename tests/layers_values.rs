//! Values over real sessions: a fetch from four providers with a liar and a stalled one, a value larger than the
//! session windows, a resume after a restart, and the superseding of a peer's older session.
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
use vinc_node::trace::{Body, NodeTrace};
use vinc_node::{Enabled, NodeEvent};
use vinc_sim::{Loss, NodeId as SimId};
use vinc_tests::{LayerApps, Lie, NCmd, SplitMix64};

fn values_on(tag: u8) -> LayerApps {
    LayerApps::new(
        tag,
        Enabled {
            values: true,
            ..Enabled::NONE
        },
    )
}

fn data(seed: u64, len: usize) -> Vec<u8> {
    let mut v = vec![0; len];
    SplitMix64::new(seed).fill(&mut v);
    v
}

fn ids(w: &LWorld, nodes: &[SimId]) -> Vec<[u8; 32]> {
    nodes.iter().map(|n| w.id(*n)).collect()
}

fn completes(w: &LWorld, n: SimId) -> usize {
    w.node_events(n)
        .iter()
        .filter(|(_, e)| matches!(e, NodeEvent::ValueComplete { .. }))
        .count()
}

fn fails(w: &LWorld, n: SimId) -> usize {
    w.node_events(n)
        .iter()
        .filter(|(_, e)| matches!(e, NodeEvent::ValueFailed { .. }))
        .count()
}

#[test]
fn a_fetch_from_four_providers_survives_a_liar_and_a_stalled_provider() {
    big(|| {
        for seed in [201u64, 202, 203] {
            let mut w = LWorld::build_with(seed, 2, 6, 8_000_000, false, values_on);
            let m = w.members.clone();
            let value = data(seed, 768 << 10);
            let mut root = [0; 32];
            for p in &m[1..5] {
                root = w.apps(*p).values.provide(value.clone());
            }
            // The third provider flips a bit in what it reads; the fourth goes silent mid-transfer.
            w.apps(m[3]).values.lie(Some(Lie::EveryRead));
            let providers = ids(&w, &m[1..5]);
            w.sim.command(
                secs(30),
                m[0],
                NCmd::ValuesFetch {
                    root,
                    length: value.len() as u64,
                    ranges: vec![],
                    providers,
                },
            );
            let rest: Vec<SimId> = w
                .hubs
                .iter()
                .map(|(n, _)| *n)
                .chain(m.iter().copied().filter(|n| *n != m[4]))
                .collect();
            w.sim.partition(secs(30) + 300_000_000, &[&rest, &[m[4]]]);
            w.run(secs(120));
            assert_eq!(completes(&w, m[0]), 1, "seed {seed}: the fetch completes once");
            assert_eq!(fails(&w, m[0]), 0, "seed {seed}: the fetch did not fail");
            assert_eq!(
                w.apps(m[0]).values.fetched(&root, value.len() as u64),
                Some(value),
                "seed {seed}: the bytes in the store are the value"
            );
        }
    });
}

#[test]
fn a_value_larger_than_the_session_windows_arrives_whole() {
    big(|| {
        for seed in [211u64, 212, 213] {
            let mut w = LWorld::build(seed, 2, 4, values_on);
            let m = w.members.clone();
            // The stream window starts at 1.25 MiB.
            let value = data(seed, 6 << 20);
            let mut root = [0; 32];
            for p in &m[1..3] {
                root = w.apps(*p).values.provide(value.clone());
            }
            let providers = ids(&w, &m[1..3]);
            w.sim.command(
                secs(30),
                m[0],
                NCmd::ValuesFetch {
                    root,
                    length: value.len() as u64,
                    ranges: vec![],
                    providers,
                },
            );
            w.run(secs(120));
            assert_eq!(completes(&w, m[0]), 1, "seed {seed}");
            assert_eq!(
                w.apps(m[0]).values.fetched(&root, value.len() as u64),
                Some(value),
                "seed {seed}"
            );
            let readable: u64 = w
                .node_events(m[0])
                .iter()
                .filter_map(|(_, e)| match e {
                    NodeEvent::ValueReadable { len, .. } => Some(*len),
                    _ => None,
                })
                .sum();
            assert_eq!(readable, 6 << 20, "seed {seed}: every verified byte was announced once");
        }
    });
}

#[test]
fn a_fetch_resumes_from_the_verified_ranges_after_a_restart() {
    big(|| {
        for seed in [221u64, 222] {
            let mut w = LWorld::build_with(seed, 2, 3, 8_000_000, false, values_on);
            let m = w.members.clone();
            let value = data(seed, 3 << 20);
            let root = w.apps(m[1]).values.provide(value.clone());
            let providers = ids(&w, &m[1..2]);
            let request = NCmd::ValuesFetch {
                root,
                length: value.len() as u64,
                ranges: vec![],
                providers,
            };
            w.sim.command(secs(30), m[0], request.clone());
            w.sim.crash(secs(33), m[0]);
            w.sim.restart(secs(34), m[0]);
            w.run(secs(33) + 500_000_000);
            let before = w.apps(m[0]).values.covered(&root);
            assert!(
                before > 0 && before < value.len() as u64,
                "seed {seed}: the crash came mid-transfer ({before} of {})",
                value.len()
            );
            w.sim.command(secs(70), m[0], request);
            w.run(secs(160));
            assert_eq!(completes(&w, m[0]), 1, "seed {seed}");
            assert_eq!(
                w.apps(m[0]).values.fetched(&root, value.len() as u64),
                Some(value),
                "seed {seed}"
            );
        }
    });
}

#[test]
fn a_peer_that_dials_again_supersedes_its_older_incoming_session() {
    big(|| {
        let seed = 231u64;
        let mut w = LWorld::build_with(seed, 2, 3, 4_000_000, true, values_on);
        let m = w.members.clone();
        let value = data(seed, 4 << 20);
        let root = w.apps(m[1]).values.provide(value.clone());
        let providers = ids(&w, &m[1..2]);
        let request = NCmd::ValuesFetch {
            root,
            length: value.len() as u64,
            ranges: vec![],
            providers,
        };
        w.sim.command(secs(30), m[0], request.clone());
        // The requester restarts while the provider is still sending; its new session finds the old one open.
        w.sim.crash(secs(32), m[0]);
        w.sim.restart(secs(33), m[0]);
        w.sim.command(secs(40), m[0], request);
        w.run(secs(160));
        let superseded = w
            .sim
            .node(m[1])
            .traces
            .iter()
            .filter(|(_, t)| matches!(t.body, Body::Node(NodeTrace::ValuesSuperseded { .. })))
            .count();
        assert!(superseded >= 1, "the provider superseded the older session of its peer");
        assert_eq!(completes(&w, m[0]), 1);
        assert_eq!(w.apps(m[0]).values.fetched(&root, value.len() as u64), Some(value));
    });
}

/// How many groups the requester verified out of order against a range proof, from its traces.
fn ahead_groups(w: &LWorld, n: SimId) -> usize {
    w.sim
        .node(n)
        .traces
        .iter()
        .filter(|(_, t)| {
            matches!(
                &t.body,
                Body::Values(_, vinc_values::trace::Trace::Verified { ahead: true, .. })
            )
        })
        .count()
}

#[test]
fn groups_behind_a_lost_packet_verify_through_range_proofs_and_nothing_is_copied() {
    big(|| {
        for seed in [241u64, 242, 243] {
            let mut ahead = Vec::new();
            for loss in [Loss::None, Loss::Bernoulli(0.03)] {
                let mut w = LWorld::build_lossy(seed, 2, 3, 0, true, loss, values_on);
                let m = w.members.clone();
                let value = data(seed, 3 << 20);
                let root = w.apps(m[1]).values.provide(value.clone());
                let providers = ids(&w, &m[1..2]);
                w.sim.command(
                    secs(30),
                    m[0],
                    NCmd::ValuesFetch {
                        root,
                        length: value.len() as u64,
                        ranges: vec![],
                        providers,
                    },
                );
                w.run(secs(150));
                assert_eq!(completes(&w, m[0]), 1, "seed {seed} {loss:?}");
                assert_eq!(fails(&w, m[0]), 0, "seed {seed} {loss:?}");
                assert_eq!(
                    w.apps(m[0]).values.fetched(&root, value.len() as u64),
                    Some(value),
                    "seed {seed} {loss:?}"
                );
                ahead.push(ahead_groups(&w, m[0]));
            }
            assert!(
                ahead[1] > ahead[0],
                "seed {seed}: groups behind a lost packet were verified from their proofs: {ahead:?}"
            );
        }
    });
}
