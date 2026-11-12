//! Hub duties over real sessions: the replay floor leaves with the first flight, a restarted hub gets its members
//! and its subscriptions back, and large broadcast bodies cross a hub stream under flow-control pressure.
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

use node_common::{OWD, World, big, secs};
use vinc_broadcast::Limits;
use vinc_membership::Trace as MTrace;
use vinc_membership::codec::ty;
use vinc_node::NodeTrace;
use vinc_node::trace::Body;
use vinc_sim::{LinkConfig, Sim, SimConfig};
use vinc_tests::{NCmd, with_pool_chunks};

const TOPIC: &[u8] = b"news";

fn body(len: usize, salt: u8) -> Vec<u8> {
    (0..len)
        .map(|i| (i as u8).wrapping_mul(31).wrapping_add(salt))
        .collect()
}

#[test]
fn a_hub_sends_its_replay_floor_before_the_members_hello_arrives() {
    big(|| {
        for seed in [401u64, 402, 403] {
            let mut w = World::build_with(seed, 2, 3, |w| w.trace = true);
            w.run(secs(30));
            for (hub, _) in w.hubs.clone() {
                let traces = &w.sim.node(hub).traces;
                let at = |out: bool, ty: u8, peer: &[u8; 32]| {
                    traces.iter().find_map(|(at, t)| match &t.body {
                        Body::Membership(MTrace::FrameOut { peer: p, ty: k }) if out && p == peer && *k == ty => {
                            Some(*at)
                        }
                        Body::Membership(MTrace::FrameIn { peer: p, ty: k }) if !out && p == peer && *k == ty => {
                            Some(*at)
                        }
                        _ => None,
                    })
                };
                for m in w.members.clone() {
                    let id = w.id(m);
                    let (floor, hello) = (at(true, ty::FLOOR, &id), at(false, ty::HELLO, &id));
                    let (floor, hello) = (
                        floor.expect("the hub sent a floor"),
                        hello.expect("the hub heard a HELLO"),
                    );
                    assert!(
                        floor < hello,
                        "seed {seed}: the floor left at {floor} ns, the HELLO arrived at {hello} ns"
                    );
                }
            }
        }
    });
}

#[test]
fn a_restarted_hub_gets_its_members_and_their_subscriptions_back() {
    big(|| {
        for seed in [411u64, 412, 413] {
            let mut w = World::build(seed, 2, 5);
            let m = w.members.clone();
            let (hub, _) = w.hubs[0];
            for s in &m[1..] {
                w.sim.command(secs(20), *s, NCmd::Subscribe(TOPIC.to_vec()));
            }
            w.sim.crash(secs(60), hub);
            w.sim.restart(secs(75), hub);
            for i in 0..12u8 {
                w.sim.command(
                    secs(50 + 10 * u64::from(i)),
                    m[0],
                    NCmd::Publish {
                        topic: TOPIC.to_vec(),
                        body: body(300, i),
                    },
                );
            }
            w.run(secs(300));
            // The restarted hub lists everyone again, and everyone lists it.
            for n in w.hubs.iter().map(|(n, _)| *n).chain(m.iter().copied()) {
                assert_eq!(
                    w.view(n),
                    w.others(n),
                    "seed {seed}: the view of {n:?} after the hub restart"
                );
            }
            // A message published after the hub came back reaches every subscriber, at most once.
            for s in &m[1..] {
                let got: Vec<Vec<u8>> = w.messages(*s).into_iter().map(|(_, _, _, b)| b).collect();
                for i in 0..12u8 {
                    if 50 + 10 * u64::from(i) >= 100 {
                        assert!(got.contains(&body(300, i)), "seed {seed}: {s:?} missed message {i}");
                    }
                }
                let mut seen = got.clone();
                seen.sort();
                seen.dedup();
                assert_eq!(seen.len(), got.len(), "seed {seed}: {s:?} got a message twice");
            }
        }
    });
}

#[test]
fn large_bodies_cross_a_slow_hub_stream_in_pieces_and_arrive_whole_once() {
    big(|| {
        for seed in [421u64, 422] {
            let max_body = 300_000;
            let limits = Limits {
                max_body,
                log_bytes: 12 * max_body,
                ..Limits::default()
            };
            let mut w = World::build_with(seed, 2, 3, |w| {
                w.limits = limits;
                // 1.5 Mbit/s: a 300 kB body takes 1.6 s, and six of them queue far beyond the stream's window.
                w.sim = Sim::with_config(
                    seed,
                    SimConfig {
                        default_link: Some(LinkConfig {
                            delay: OWD / 2,
                            bandwidth_bps: 1_500_000,
                            queue_bytes: 4 << 20,
                            ..LinkConfig::default()
                        }),
                        ..SimConfig::default()
                    },
                );
            });
            let m = w.members.clone();
            for s in &m[1..] {
                w.sim.command(secs(20), *s, NCmd::Subscribe(TOPIC.to_vec()));
            }
            for i in 0..6u8 {
                w.sim.command(
                    secs(40),
                    m[0],
                    NCmd::Publish {
                        topic: TOPIC.to_vec(),
                        body: body(max_body, i),
                    },
                );
            }
            w.run(secs(240));
            for s in &m[1..] {
                let got: Vec<Vec<u8>> = w.messages(*s).into_iter().map(|(_, _, _, b)| b).collect();
                assert_eq!(got.len(), 6, "seed {seed}: {s:?} got {} messages", got.len());
                for i in 0..6u8 {
                    assert!(
                        got.contains(&body(max_body, i)),
                        "seed {seed}: {s:?} got message {i} altered or not at all"
                    );
                }
            }
        }
    });
}

#[test]
fn hub_sessions_with_a_stream_each_way_live_in_a_small_pool() {
    // Every session gets 24 chunks: too few for the windows of both streams of a hub session at once, so
    // the second stream is admitted only as the credit allows. No session may stall: every member learns of every
    // other.
    big(|| {
        for seed in [411u64, 412] {
            let mut w = with_pool_chunks(24, || World::build_with(seed, 2, 3, |w| w.trace = true));
            w.run(secs(60));
            for m in w.members.clone() {
                for other in w.members.clone().into_iter().filter(|o| *o != m) {
                    let id = w.id(other);
                    assert!(w.view(m).contains(&id), "seed {seed}: {m:?} never learned of {other:?}");
                }
            }
        }
    });
}

#[test]
fn a_membership_frame_refused_by_a_full_backlog_closes_the_session_and_the_reconnect_repairs_it() {
    big(|| {
        let seed = 431u64;
        let max_body = 250_000;
        let limits = Limits {
            max_body,
            log_bytes: 12 * max_body,
            ..Limits::default()
        };
        let mut w = World::build_with(seed, 1, 2, |w| {
            w.limits = limits;
            w.trace = true;
        });
        let (hub, _) = w.hubs[0];
        let m = w.members.clone();
        // The member is cut off from the hub, so nothing it writes drains. It then fills the backlog of its hub
        // stream with big bodies (the ones the backlog has no room for wait in the publisher, unsent), then with the
        // subscriptions to topics with long names, until the next frame of any kind is refused.
        w.sim.partition(secs(41), &[&[hub, m[1]], &[m[0]]]);
        let publish = |w: &mut World, len: usize, n: usize| {
            for i in 0..n {
                w.sim.command(
                    secs(43),
                    m[0],
                    NCmd::Publish {
                        topic: TOPIC.to_vec(),
                        body: body(len, i as u8),
                    },
                );
            }
        };
        publish(&mut w, max_body, 12);
        // The room the last body that fitted left is under one body: 600 pairs of these frames are more than that.
        for _ in 0..600 {
            w.sim.command(secs(43), m[0], NCmd::Subscribe(vec![b'n'; 250]));
            w.sim.command(secs(43), m[0], NCmd::Unsubscribe(vec![b'n'; 250]));
        }
        w.sim.heal(secs(110));
        w.run(secs(330));
        let closed = w
            .sim
            .node(m[0])
            .traces
            .iter()
            .filter(|(_, t)| matches!(t.body, Body::Node(NodeTrace::BacklogClosed { .. })))
            .count();
        assert!(closed >= 1, "the refused membership frame did not close the session");
        // The reconnect repaired it: every node lists every other again.
        for n in [hub, m[0], m[1]] {
            assert_eq!(w.view(n), w.others(n), "the view of {n:?} after the repair");
        }
    });
}

#[test]
fn a_hub_names_the_route_a_datagram_to_a_member_takes() {
    use vinc_crypto::{IdentityAlg, NodeId};
    big(|| {
        let mut w = World::build(411, 1, 2);
        w.run(secs(30));
        let (hub, addr) = w.hubs[0];
        for m in w.members.clone() {
            let id = NodeId {
                alg: IdentityAlg::Ed25519,
                bytes: w.id(m),
            };
            let node = &w.sim.node(hub).node;
            // The datagram leaves from the address of the member's session and goes to the member's address, so a
            // member reached on one address family is not sent to from another.
            let (local, remote) = node
                .member_route(&id)
                .expect("the member has a validated direct session");
            assert_eq!(
                local, addr.udp,
                "the datagram leaves from the hub address the session uses"
            );
            assert_eq!(Some(remote), node.member_addr(&id));
        }
    });
}
