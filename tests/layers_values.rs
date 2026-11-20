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

use layers_common::{LWorld, big, completes, data, ids, secs, values_on};
use pinc_node::NodeEvent;
use pinc_node::trace::{Body, NodeTrace};
use pinc_sim::{LinkChange, Loss, MS, NodeId as SimId};
use pinc_tests::{Lie, NCmd};

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
                root = w.provide(*p, value.clone());
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
                    deadline: None,
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

/// The value traces of node `n` that match `f`.
fn value_traces(w: &LWorld, n: SimId, f: impl Fn(&pinc_values::trace::Trace) -> bool) -> usize {
    w.sim
        .node(n)
        .traces
        .iter()
        .filter(|(_, t)| matches!(&t.body, Body::Values(_, v) if f(v)))
        .count()
}

#[test]
fn a_second_fetch_from_a_provider_uses_the_session_the_first_one_dialed() {
    big(|| {
        for seed in [261u64, 262] {
            let mut w = LWorld::build_with(seed, 2, 3, 8_000_000, false, values_on);
            let m = w.members.clone();
            let (first, second) = (data(seed, 1 << 20), data(seed + 100, 1 << 20));
            let a = w.provide(m[1], first.clone());
            let b = w.provide(m[1], second.clone());
            for (at, root, len) in [(30, a, first.len()), (60, b, second.len())] {
                w.sim.command(
                    secs(at),
                    m[0],
                    NCmd::ValuesFetch {
                        root,
                        length: len as u64,
                        ranges: vec![],
                        providers: ids(&w, &m[1..2]),
                        deadline: None,
                    },
                );
            }
            w.run(secs(90));
            assert_eq!(completes(&w, m[0]), 2, "seed {seed}: both fetches complete");
            assert_eq!(
                w.apps(m[0]).values.fetched(&a, first.len() as u64),
                Some(first),
                "seed {seed}"
            );
            assert_eq!(
                w.apps(m[0]).values.fetched(&b, second.len() as u64),
                Some(second),
                "seed {seed}"
            );
        }
    });
}

#[test]
fn a_finished_fetch_gives_its_providers_back() {
    big(|| {
        let seed = 271u64;
        let mut w = LWorld::build_with(seed, 2, 5, 8_000_000, false, values_on);
        let m = w.members.clone();
        for (k, at) in [(1usize, 30u64), (2, 60), (3, 90)] {
            let value = data(seed + k as u64, 256 << 10);
            let root = w.provide(m[k], value.clone());
            w.sim.command(
                secs(at),
                m[0],
                NCmd::ValuesFetch {
                    root,
                    length: value.len() as u64,
                    ranges: vec![],
                    providers: ids(&w, &m[k..=k]),
                    deadline: None,
                },
            );
        }
        w.run(secs(30) + 50 * MS);
        assert!(
            w.sim.node(m[0]).node.values_stats().providers_in_use > 0,
            "a running fetch holds its provider"
        );
        w.run(secs(120));
        assert_eq!(completes(&w, m[0]), 3, "all three fetches complete");
        let stats = w.sim.node(m[0]).node.values_stats();
        assert_eq!(
            stats.providers_in_use, 0,
            "nothing uses a provider once its fetch finished"
        );
        assert_eq!(stats.providers_refused, 0);
        for (k, provider) in m.iter().enumerate().take(4).skip(1) {
            assert_eq!(
                w.sim.node(*provider).node.values_stats().providers_in_use,
                0,
                "provider {k} serves nothing once the fetch finished"
            );
        }
    });
}

/// A world in which node 0 fetched a 64 KiB value from node 1 and stored it, and holds no provider at the second the
/// first completion is seen; returns the world, the root, the length, the provider ids and that second.
fn stored_value(seed: u64) -> (LWorld, [u8; 32], u64, Vec<[u8; 32]>, u64) {
    let mut w = LWorld::build_with(seed, 2, 3, 8_000_000, false, values_on);
    let m = w.members.clone();
    let value = data(seed, 64 << 10);
    let root = w.provide(m[1], value.clone());
    let providers = ids(&w, &m[1..2]);
    w.sim.command(
        secs(30),
        m[0],
        NCmd::ValuesFetch {
            root,
            length: value.len() as u64,
            ranges: vec![],
            providers: providers.clone(),
            deadline: None,
        },
    );
    let mut at = 30;
    while completes(&w, m[0]) == 0 {
        assert!(at < 40, "the first fetch did not complete within ten seconds");
        at += 1;
        w.run(secs(at));
    }
    assert_eq!(completes(&w, m[0]), 1, "the first fetch completes and stores the value");
    assert_eq!(
        w.sim.node(m[0]).node.values_stats().providers_in_use,
        0,
        "nothing uses a provider once the fetch completed"
    );
    (w, root, value.len() as u64, providers, at)
}

/// Node 0 fetches from node 1 twice; during the second fetch most datagrams from node 0 to node 1 are lost, so node 1
/// retransmits what node 0 already read to the end. Returns, per seed, the providers in use on node 0 and on node 1
/// once the net is quiet.
fn late_frames(seeds: &[u64]) -> Vec<(u64, usize, usize)> {
    let mut held = Vec::new();
    for seed in seeds {
        let mut w = LWorld::build_with(*seed, 2, 3, 8_000_000, false, values_on);
        let m = w.members.clone();
        let (a, b) = (data(*seed, 64 << 10), data(*seed + 100, 256 << 10));
        let (ra, rb) = (w.provide(m[1], a.clone()), w.provide(m[1], b.clone()));
        for (at, root, len) in [(30, ra, a.len()), (60, rb, b.len())] {
            w.sim.command(
                secs(at),
                m[0],
                NCmd::ValuesFetch {
                    root,
                    length: len as u64,
                    ranges: vec![],
                    providers: ids(&w, &m[1..2]),
                    deadline: None,
                },
            );
        }
        // From just after the second request reached the provider, most datagrams on the path are lost for a second.
        let lossy = LinkChange::Loss(Loss::Bernoulli(0.9));
        w.sim.link_change(secs(60) + 6 * MS, m[0], m[1], lossy);
        w.sim.link_change(secs(61), m[0], m[1], LinkChange::Loss(Loss::None));
        w.run(secs(90));
        assert_eq!(completes(&w, m[0]), 2, "seed {seed}: both fetches complete");
        held.push((
            *seed,
            w.sim.node(m[0]).node.values_stats().providers_in_use,
            w.sim.node(m[1]).node.values_stats().providers_in_use,
        ));
    }
    held
}

#[test]
fn a_late_frame_for_a_stream_the_fetch_read_to_the_end_holds_no_provider() {
    // The acknowledgements of node 0 are lost, so node 1 retransmits the end of a response node 0 has read whole and
    // dropped: a frame for a stream the layer no longer holds. It registers no request.
    big(|| {
        let held = late_frames(&[281, 282, 283, 284, 285, 286]);
        assert!(
            held.iter()
                .all(|(_, fetcher, provider)| *fetcher == 0 && *provider == 0),
            "(seed, providers in use on the fetcher, on the provider): {held:?}"
        );
    });
}

#[test]
fn a_fetch_refused_at_start_holds_no_provider() {
    big(|| {
        let (mut w, root, length, providers, at) = stored_value(272);
        let m0 = w.members[0];
        let past_the_end = [pinc_values::span::Span { off: length, len: 1 }];
        let req = pinc_node::ValuesRequest {
            root,
            length,
            ranges: &past_the_end,
            providers: &providers,
            deadline: None,
        };
        let node = &mut w.sim.node_mut(m0).node;
        assert_eq!(
            node.values_fetch(secs(at) + MS, &req),
            Err(pinc_node::ValuesError::OutOfBounds)
        );
        assert_eq!(node.values_stats().providers_in_use, 0, "a refused fetch holds nothing");
        w.run(secs(at + 30));
        assert_eq!(w.sim.node(m0).node.values_stats().providers_in_use, 0);
    });
}

#[test]
fn a_fetch_done_at_start_holds_no_provider() {
    big(|| {
        let (mut w, root, length, providers, at) = stored_value(273);
        let m0 = w.members[0];
        let req = pinc_node::ValuesRequest {
            root,
            length,
            ranges: &[],
            providers: &providers,
            deadline: None,
        };
        let node = &mut w.sim.node_mut(m0).node;
        assert!(node.values_fetch(secs(at) + MS, &req).is_ok());
        assert_eq!(
            node.values_running(),
            0,
            "the value is stored, so the fetch was done at start"
        );
        assert_eq!(
            node.values_stats().providers_in_use,
            0,
            "a fetch done at start holds nothing"
        );
        w.run(secs(at + 30));
        assert_eq!(w.sim.node(m0).node.values_stats().providers_in_use, 0);
    });
}

#[test]
fn a_striped_fetch_asks_again_as_each_request_stream_ends() {
    // A stream whose end arrived with its last bytes must still free its place among the fetch's request streams, or
    // the fetch waits for the stall timer once the table is full.
    big(|| {
        for seed in [251u64, 252] {
            let mut w = LWorld::build_with(seed, 2, 4, 8_000_000, true, values_on);
            let m = w.members.clone();
            let value = data(seed, 12 << 20);
            let mut root = [0; 32];
            for p in &m[1..3] {
                root = w.provide(*p, value.clone());
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
                    deadline: None,
                },
            );
            w.run(secs(120));
            assert_eq!(completes(&w, m[0]), 1, "seed {seed}");
            assert_eq!(
                w.apps(m[0]).values.fetched(&root, value.len() as u64),
                Some(value),
                "seed {seed}"
            );
            let asked = value_traces(&w, m[0], |t| matches!(t, pinc_values::trace::Trace::Requested { .. }));
            let stalls = value_traces(&w, m[0], |t| matches!(t, pinc_values::trace::Trace::StallRedial { .. }));
            assert!(
                asked > 8,
                "seed {seed}: the providers were asked again ({asked} requests)"
            );
            assert_eq!(stalls, 0, "seed {seed}: the fetch never waited for its stall timer");
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
                root = w.provide(*p, value.clone());
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
                    deadline: None,
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
            let root = w.provide(m[1], value.clone());
            let providers = ids(&w, &m[1..2]);
            let request = NCmd::ValuesFetch {
                root,
                length: value.len() as u64,
                ranges: vec![],
                providers,
                deadline: None,
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
        let root = w.provide(m[1], value.clone());
        let providers = ids(&w, &m[1..2]);
        let request = NCmd::ValuesFetch {
            root,
            length: value.len() as u64,
            ranges: vec![],
            providers,
            deadline: None,
        };
        w.sim.command(secs(30), m[0], request.clone());
        // The requester restarts while the provider is still sending; its new session finds the old one open. It asks
        // again within two seconds of the restart: a session on a relay path that has heard nothing through four probe
        // timeouts, while the relay answers, is closed by its own side (about 4 s after the crash), and then there is
        // no older session left to supersede.
        w.sim.crash(secs(32), m[0]);
        w.sim.restart(secs(33), m[0]);
        w.sim.command(secs(34), m[0], request);
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
                Body::Values(_, pinc_values::trace::Trace::Verified { ahead: true, .. })
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
                let root = w.provide(m[1], value.clone());
                let providers = ids(&w, &m[1..2]);
                w.sim.command(
                    secs(30),
                    m[0],
                    NCmd::ValuesFetch {
                        root,
                        length: value.len() as u64,
                        ranges: vec![],
                        providers,
                        deadline: None,
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

#[test]
fn a_value_the_store_holds_is_served_only_while_its_root_is_provided() {
    big(|| {
        let seed = 261u64;
        let mut w = LWorld::build_with(seed, 2, 3, 8_000_000, false, values_on);
        let m = w.members.clone();
        let value = data(seed, 256 << 10);
        let root = w.provide(m[1], value.clone());
        // The second provider holds the same bytes but never registered the root.
        assert_eq!(w.apps(m[2]).values.provide(value.clone()), root);
        let fetch = |providers| NCmd::ValuesFetch {
            root,
            length: value.len() as u64,
            ranges: vec![],
            providers,
            deadline: None,
        };
        w.sim.command(secs(30), m[0], fetch(ids(&w, &m[2..3])));
        w.run(secs(100));
        assert_eq!(completes(&w, m[0]), 0, "an unprovided root was served");
        assert_eq!(
            w.apps(m[0]).values.covered(&root),
            0,
            "bytes of an unprovided root arrived"
        );
        // Registered, it is served; withdrawn, it is refused again.
        w.sim.command(secs(110), m[0], fetch(ids(&w, &m[1..2])));
        w.run(secs(180));
        assert_eq!(completes(&w, m[0]), 1);
        assert!(w.sim.node_mut(m[1]).node.values_unprovide(&root));
        assert!(!w.sim.node_mut(m[1]).node.values_unprovide(&root));
        let other = data(seed + 1, 256 << 10);
        let other_root = w.apps(m[1]).values.provide(other.clone());
        w.sim.command(
            secs(190),
            m[0],
            NCmd::ValuesFetch {
                root: other_root,
                length: other.len() as u64,
                ranges: vec![],
                providers: ids(&w, &m[1..2]),
                deadline: None,
            },
        );
        w.run(secs(260));
        assert_eq!(completes(&w, m[0]), 1, "a withdrawn or never provided root was served");
        assert_eq!(
            w.apps(m[0]).values.covered(&other_root),
            0,
            "bytes of a withdrawn root arrived"
        );
    });
}

#[test]
fn at_most_four_thousand_ninety_six_roots_are_provided() {
    big(|| {
        let mut w = LWorld::build(262, 1, 1, values_on);
        let n = w.members[0];
        let node = &mut w.sim.node_mut(n).node;
        let root = |i: u32| {
            let mut r = [0u8; 32];
            r[..4].copy_from_slice(&i.to_be_bytes());
            r
        };
        for i in 0..pinc_node::PROVIDED_MAX as u32 {
            assert!(node.values_provide(&root(i)), "root {i}");
        }
        assert!(!node.values_provide(&root(u32::MAX)), "the 4097th root is refused");
        assert!(node.values_provide(&root(7)), "a registered root stays registered");
        assert!(node.values_unprovide(&root(7)));
        assert!(node.values_provide(&root(u32::MAX)), "a freed place is reusable");
    });
}

#[test]
fn a_cancelled_fetch_reports_nothing_more_and_its_streams_are_gone() {
    big(|| {
        let seed = 271u64;
        let mut w = LWorld::build_with(seed, 2, 3, 4_000_000, true, values_on);
        let m = w.members.clone();
        let value = data(seed, 4 << 20);
        let root = w.provide(m[1], value.clone());
        w.sim.command(
            secs(30),
            m[0],
            NCmd::ValuesFetch {
                root,
                length: value.len() as u64,
                ranges: vec![],
                providers: ids(&w, &m[1..2]),
                deadline: None,
            },
        );
        // The first fetch of a node is number 1; cancel it while it is still receiving.
        w.sim.command(secs(32), m[0], NCmd::ValuesCancel(1));
        w.run(secs(120));
        let cancelled = w
            .sim
            .node(m[0])
            .traces
            .iter()
            .filter(|(_, t)| matches!(t.body, Body::Node(NodeTrace::ValuesCancel { fetch: 1 })))
            .count();
        assert_eq!(cancelled, 1, "the cancel took effect once");
        assert_eq!(
            completes(&w, m[0]) + fails(&w, m[0]),
            0,
            "a cancelled fetch reported an end"
        );
        assert!(
            w.apps(m[0]).values.covered(&root) < value.len() as u64,
            "a cancelled fetch kept receiving"
        );
        assert_eq!(w.sim.node(m[0]).node.values_running(), 0);
        assert_eq!(
            w.sim.node(m[0]).node.values_stats().providers_in_use,
            0,
            "a cancelled fetch gives its providers back"
        );
        assert!(
            !w.sim.node_mut(m[0]).node.values_cancel(secs(121), 1),
            "a finished cancel finds nothing"
        );
    });
}

#[test]
fn a_server_session_that_began_on_a_relay_moves_to_the_direct_path_that_validates() {
    // The consumer's first flight reaches the provider through the hub's relay, so the provider's session starts on a
    // relay path. A direct path validates within milliseconds; the provider must take it, or a bulk transfer rides the
    // relay's quota and stalls when it is used up.
    big(|| {
        use pinc_node::Ep;
        let mut w = LWorld::build_with(301, 2, 3, 400_000_000, false, values_on);
        let m = w.members.clone();
        let value = data(301, 16 << 20);
        let root = w.provide(m[1], value.clone());
        w.sim.command(
            secs(30),
            m[0],
            NCmd::ValuesFetch {
                root,
                length: value.len() as u64,
                ranges: vec![],
                providers: ids(&w, &m[1..2]),
                deadline: None,
            },
        );
        w.run(secs(30) + 400_000_000);
        let ep = w.sim.node(m[1]).node.endpoint();
        let busy: Vec<_> = (0..)
            .map_while(|n| ep.session_at(n))
            .filter(|s| s.transport.bytes_sent > 100_000)
            .collect();
        assert_eq!(busy.len(), 1, "the provider is serving the value");
        let route = busy[0].route.map(|(_, r)| r);
        assert!(
            route.is_some_and(|r| !pinc_core::is_relay_addr(&r)),
            "the provider's session is on a direct path 400 ms after the fetch began, not {route:?}"
        );
        w.run(secs(60));
        assert_eq!(completes(&w, m[0]), 1);
        assert_eq!(w.apps(m[0]).values.fetched(&root, value.len() as u64), Some(value));
    });
}

#[test]
fn a_dial_still_in_its_handshake_does_not_keep_the_node_awake() {
    // A node whose address changed arms the punch timer of every session it follows, the ones still in their
    // handshake included. A session that cannot be punched yet must not leave that timer due, or the host wakes the
    // node again and again for nothing while the peer cannot be reached.
    big(|| {
        let mut w = LWorld::build_with(7, 1, 3, 0, false, values_on);
        let (m, hub) = (w.members.clone(), w.hubs[0].0);
        let value = data(7, 64 << 10);
        let root = w.provide(m[1], value.clone());
        w.run(secs(10));
        w.sim.partition(secs(10), &[&[m[1]], &[m[0], m[2], hub]]);
        w.sim.command(
            secs(11),
            m[0],
            NCmd::ValuesFetch {
                root,
                length: value.len() as u64,
                ranges: vec![],
                providers: ids(&w, &m[1..2]),
                deadline: None,
            },
        );
        w.sim.command(secs(12), m[0], NCmd::AddressChanged);
        w.run(secs(14));
        let before = w.sim.node(m[0]).timeouts;
        w.run(secs(24));
        let woke = w.sim.node(m[0]).timeouts - before;
        assert!(
            woke < 1000,
            "the node woke {woke} times in ten seconds while waiting for a dial"
        );
    });
}

#[test]
fn a_burst_for_a_relay_carrier_is_held_and_sent_not_lost() {
    // The first flight of a fetch is dozens of packets in one step, more than the carrier's output buffer holds. The
    // ones that do not fit wait and leave as the host drains the buffer; none is lost, so no probe timeout fires
    // and the window is not cut while the transfer starts.
    big(|| {
        use pinc_node::Ep;
        let mut w = LWorld::build_with(301, 2, 3, 400_000_000, false, values_on);
        let m = w.members.clone();
        let value = data(301, 16 << 20);
        let root = w.provide(m[1], value.clone());
        w.sim.command(
            secs(30),
            m[0],
            NCmd::ValuesFetch {
                root,
                length: value.len() as u64,
                ranges: vec![],
                providers: ids(&w, &m[1..2]),
                deadline: None,
            },
        );
        w.run(secs(30) + 300_000_000);
        let ep = w.sim.node(m[1]).node.endpoint();
        let busy: Vec<_> = (0..)
            .map_while(|n| ep.session_at(n))
            .filter(|s| s.transport.bytes_sent > 100_000)
            .collect();
        assert_eq!(busy.len(), 1, "the provider is serving the value");
        let t = &busy[0].transport;
        assert_eq!((t.ptos, t.packets_lost), (0, 0), "nothing of the first burst was lost");
    });
}
