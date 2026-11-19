//! Reconcile over real sessions: two nodes whose sets differ by a few items and by many learn the exact difference.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::too_many_lines
)]

mod layers_common;

use std::collections::BTreeSet;

use layers_common::{LWorld, big, secs};
use pinc_node::{Enabled, NodeEvent, ReconcileFailure};
use pinc_reconcile::Limits;
use pinc_tests::{LayerApps, NCmd, SplitMix64};

const SET: &[u8] = b"items";

fn items(rng: &mut SplitMix64, n: usize) -> BTreeSet<Vec<u8>> {
    let mut out = BTreeSet::new();
    while out.len() < n {
        let len = 8 + (rng.next_u64() % 40) as usize;
        let mut v = vec![0; len];
        rng.fill(&mut v);
        out.insert(v);
    }
    out
}

/// Two sets over `common` shared items, with `a` items only in the first and `b` only in the second.
fn run(seed: u64, common: usize, a: usize, b: usize, limits: Option<Limits>) {
    let mut rng = SplitMix64::new(seed);
    let all = items(&mut rng, common + a + b);
    let all: Vec<Vec<u8>> = all.into_iter().collect();
    // Shuffle deterministically so the extras are spread over the key space.
    let mut order: Vec<usize> = (0..all.len()).collect();
    for i in (1..order.len()).rev() {
        order.swap(i, (rng.next_u64() % (i as u64 + 1)) as usize);
    }
    let pick = |from: usize, n: usize| -> BTreeSet<Vec<u8>> {
        order[from..from + n].iter().map(|i| all[*i].clone()).collect()
    };
    let shared = pick(0, common);
    let only_a = pick(common, a);
    let only_b = pick(common + a, b);
    let mut w = LWorld::build(seed, 2, 3, |tag| {
        LayerApps::new(
            tag,
            Enabled {
                sets: true,
                ..Enabled::NONE
            },
        )
    });
    let m = w.members.clone();
    let mine: Vec<Vec<u8>> = shared.iter().chain(&only_a).cloned().collect();
    let theirs: Vec<Vec<u8>> = shared.iter().chain(&only_b).cloned().collect();
    for (n, set) in [(m[0], &mine), (m[1], &theirs)] {
        let sets = &mut w.apps(n).sets;
        sets.insert(SET, set);
        sets.limits = limits;
    }
    let peer = w.id(m[1]);
    w.sim.command(
        secs(30),
        m[0],
        NCmd::SetsStart {
            peer,
            set_ref: SET.to_vec(),
        },
    );
    w.run(secs(90));
    let done: Vec<_> = w
        .node_events(m[0])
        .into_iter()
        .filter_map(|(_, e)| match e {
            NodeEvent::ReconcileDone {
                missing_here,
                missing_there,
                peer: p,
                ..
            } => Some((missing_here, missing_there, p)),
            NodeEvent::ReconcileFailed { reason, .. } => panic!("seed {seed}: the round failed: {reason:?}"),
            _ => None,
        })
        .collect();
    assert_eq!(done.len(), 1, "seed {seed}: one round, one report");
    let (here, there, p) = &done[0];
    assert_eq!(*p, peer);
    let here: BTreeSet<Vec<u8>> = here.iter().cloned().collect();
    let there: BTreeSet<Vec<u8>> = there.iter().cloned().collect();
    assert_eq!(here, only_b, "seed {seed}: the items the peer has and we lack");
    assert_eq!(there, only_a, "seed {seed}: the items we have and the peer lacks");
}

#[test]
fn sets_that_differ_by_a_few_items_report_exactly_those() {
    big(|| {
        for seed in [301u64, 302, 303] {
            run(seed, 2000, 3, 5, None);
        }
    });
}

#[test]
fn sets_that_differ_by_many_items_report_the_exact_difference_over_many_messages() {
    big(|| {
        for seed in [311u64, 312, 313] {
            let limits = Limits {
                max_item: 64,
                max_message: 8 << 10,
                ..Limits::default()
            };
            run(seed, 1500, 900, 1100, Some(limits));
        }
    });
}

#[test]
fn a_round_over_a_set_the_peer_lacks_fails_without_retrying() {
    big(|| {
        let mut w = LWorld::build(321, 2, 3, |tag| {
            LayerApps::new(
                tag,
                Enabled {
                    sets: true,
                    ..Enabled::NONE
                },
            )
        });
        let m = w.members.clone();
        w.apps(m[0]).sets.insert(SET, &[b"a".to_vec()]);
        let peer = w.id(m[1]);
        w.sim.command(
            secs(30),
            m[0],
            NCmd::SetsStart {
                peer,
                set_ref: SET.to_vec(),
            },
        );
        w.run(secs(90));
        let failed = w
            .node_events(m[0])
            .into_iter()
            .filter(|(_, e)| {
                matches!(
                    e,
                    NodeEvent::ReconcileFailed {
                        reason: ReconcileFailure::UnknownSet,
                        ..
                    }
                )
            })
            .count();
        assert_eq!(failed, 1);
    });
}

#[test]
fn a_round_on_a_session_reported_before_its_handshake_ends_waits_for_stream_credit() {
    // The first round rides a sub-session of a values session, so no reconcile ticket is issued. The peer restarts;
    // the second round dials it again while its access answer is still cached: the session is reported at once,
    // holds no ticket and so no stream credit until the peer's limits arrive. The round waits for that credit
    // instead of spending its attempts.
    big(|| {
        for seed in [331u64, 332] {
            let mut w = LWorld::build(seed, 2, 3, |tag| {
                LayerApps::new(
                    tag,
                    Enabled {
                        sets: true,
                        values: true,
                        ..Enabled::NONE
                    },
                )
            });
            let m = w.members.clone();
            w.apps(m[0]).sets.insert(SET, &[b"a".to_vec(), b"b".to_vec()]);
            w.apps(m[1]).sets.insert(SET, &[b"b".to_vec(), b"c".to_vec()]);
            let value = vec![7u8; 64 << 10];
            let root = w.apps(m[1]).values.provide(value.clone());
            let peer = w.id(m[1]);
            w.sim.command(
                secs(30),
                m[0],
                NCmd::ValuesFetch {
                    root,
                    length: value.len() as u64,
                    ranges: vec![],
                    providers: vec![peer],
                },
            );
            for at in [32, 36] {
                w.sim.command(
                    secs(at),
                    m[0],
                    NCmd::SetsStart {
                        peer,
                        set_ref: SET.to_vec(),
                    },
                );
            }
            w.sim.crash(secs(33), m[1]);
            w.sim.restart(secs(34), m[1]);
            w.run(secs(120));
            let ev = w.node_events(m[0]);
            let failed: Vec<_> = ev
                .iter()
                .filter_map(|(_, e)| match e {
                    NodeEvent::ReconcileFailed { reason, .. } => Some(*reason),
                    _ => None,
                })
                .collect();
            assert!(failed.is_empty(), "seed {seed}: a round failed: {failed:?}");
            let done = ev
                .iter()
                .filter(|(_, e)| matches!(e, NodeEvent::ReconcileDone { .. }))
                .count();
            assert_eq!(done, 2, "seed {seed}: both rounds report");
        }
    });
}
