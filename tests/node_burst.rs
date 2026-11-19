//! A burst through a hub: the pushlog shape of `DefraDB` (2,000 bodies of 4 KiB at 10,000 a second) reaches every
//! subscriber behind a slow link, and the publisher hears the outcome of every publish.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss
)]

mod node_common;

use node_common::{OWD, World, big, secs};
use pinc_broadcast::Trace as BTrace;
use pinc_node::NodeEvent;
use pinc_node::trace::Body;
use pinc_node::trace::NodeTrace;
use pinc_sim::{LinkConfig, Loss, MS, Sim, SimConfig, Time};
use pinc_tests::{NCmd, NEv};

const TOPIC: &[u8] = b"pushlog";
const N: usize = 2000;
const SIZE: usize = 4096;
const SUBS: usize = 10;

fn body(i: usize) -> Vec<u8> {
    let mut b = vec![0u8; SIZE];
    b[..8].copy_from_slice(&(i as u64).to_le_bytes());
    b
}

/// One hub, one writer on the hub's LAN, and `SUBS` subscribers on paths of 10 Mbit/s (a 100 Mbit/s link shared ten
/// ways) with a 20 ms round trip.
fn world(seed: u64) -> World {
    world_with(seed, SUBS, Loss::None)
}

/// As [`world`], with `subs` subscribers whose paths lose datagrams as `loss` says.
fn world_with(seed: u64, subs: usize, loss: Loss) -> World {
    let mut w = World::build_with(seed, 1, 1 + subs, |w| {
        // The hub's log is what a subscriber on a slow path is served from: it must hold the burst (about 8.2 MiB).
        w.limits.log_bytes = 16 << 20;
        w.trace = true;
        w.sim = Sim::with_config(
            seed,
            SimConfig {
                default_link: Some(LinkConfig {
                    delay: OWD,
                    bandwidth_bps: 10_000_000,
                    loss,
                    ..LinkConfig::default()
                }),
                ..SimConfig::default()
            },
        );
    });
    let (hub, writer) = (w.sim.site(w.hubs[0].0), w.sim.site(w.members[0]));
    let lan = LinkConfig {
        delay: MS / 4,
        ..LinkConfig::default()
    };
    w.sim.set_link_pair(hub, writer, lan.clone(), lan);
    w
}

/// The same, with every subscriber on the hub's LAN too.
fn world_lan(seed: u64) -> World {
    let mut w = world(seed);
    let hub = w.sim.site(w.hubs[0].0);
    let lan = LinkConfig {
        delay: MS / 4,
        ..LinkConfig::default()
    };
    for m in w.members.clone() {
        let s = w.sim.site(m);
        w.sim.set_link_pair(hub, s, lan.clone(), lan.clone());
    }
    w
}

fn count(w: &World, n: pinc_sim::NodeId, until: Time, f: impl Fn(&NodeEvent) -> bool) -> usize {
    w.sim
        .events(n)
        .iter()
        .filter(|(t, e)| *t <= until && matches!(e, NEv::Node(ev) if f(ev)))
        .count()
}

/// Every publish of a burst is refused to its caller or ends acknowledged or given up, even with more of them in
/// flight than the publisher tracks: here the writer, not the hub, is behind the slow path.
#[test]
fn every_publish_of_a_burst_is_acked_or_given_up() {
    big(|| {
        let mut w = World::build_with(92, 1, 2, |w| {
            w.trace = true;
            w.sim = Sim::with_config(
                92,
                SimConfig {
                    default_link: Some(LinkConfig {
                        delay: OWD,
                        bandwidth_bps: 10_000_000,
                        ..LinkConfig::default()
                    }),
                    ..SimConfig::default()
                },
            );
        });
        let (writer, sub) = (w.members[0], w.members[1]);
        w.sim.command(secs(20), sub, NCmd::Subscribe(TOPIC.to_vec()));
        let start = secs(40);
        for i in 0..N {
            w.sim.command(
                start + (i as Time) * MS / 10,
                writer,
                NCmd::Publish {
                    topic: TOPIC.to_vec(),
                    body: body(i),
                },
            );
        }
        // Past the 90 s give-up of the last publish.
        let end = start + secs(100);
        w.run(end);
        let acked = count(&w, writer, end, |e| matches!(e, NodeEvent::PublishAcked { .. }));
        let gave_up = count(&w, writer, end, |e| matches!(e, NodeEvent::PublishGaveUp { .. }));
        // The publishes the node took; the others were refused to the caller.
        let accepted = w
            .sim
            .node(writer)
            .traces
            .iter()
            .filter(|(_, t)| matches!(t.body, Body::Broadcast(BTrace::Published { .. })))
            .count();
        eprintln!(
            "publisher: accepted {accepted} refused {} acked {acked} gave_up {gave_up} of {N}",
            N - accepted
        );
        assert!(accepted > 0, "the publisher took no publish");
        assert_eq!(
            acked + gave_up,
            accepted,
            "an accepted publish ended with no outcome the publisher heard"
        );
    });
}

/// The burst starts here, once every subscription is in.
const START: Time = 40 * pinc_sim::SEC;
/// The harness's drain: 15 s after the last publish.
const DRAINED: Time = START + 15 * pinc_sim::SEC + 200 * MS;

/// Subscribe every subscriber and schedule the burst at [`START`].
fn burst(w: &mut World, writer: pinc_sim::NodeId, subs: &[pinc_sim::NodeId]) {
    burst_of(w, writer, subs, N);
}

/// The same with `n` messages.
fn burst_of(w: &mut World, writer: pinc_sim::NodeId, subs: &[pinc_sim::NodeId], n: usize) {
    for s in subs {
        w.sim.command(secs(20), *s, NCmd::Subscribe(TOPIC.to_vec()));
    }
    for i in 0..n {
        w.sim.command(
            START + (i as Time) * MS / 10,
            writer,
            NCmd::Publish {
                topic: TOPIC.to_vec(),
                body: body(i),
            },
        );
    }
}

/// The publisher's acknowledged publishes per second, from the first publish to the last acknowledgement.
fn ack_rate(w: &World, writer: pinc_sim::NodeId) -> f64 {
    let last = w
        .sim
        .events(writer)
        .iter()
        .filter(|(_, e)| matches!(e, NEv::Node(NodeEvent::PublishAcked { .. })))
        .map(|(t, _)| *t)
        .max()
        .unwrap_or(START);
    let acked = count(w, writer, Time::MAX, |e| matches!(e, NodeEvent::PublishAcked { .. }));
    acked as f64 / ((last - START) as f64 / pinc_sim::SEC as f64)
}

/// A subscriber whose stream stops draining (the hub's packets to it are dropped for 10 s, its session stays up)
/// paces the topic for at most `PUSH_STALL`: the nine others still get the whole burst within the drain, and the
/// stalled one ends with the whole burst or is told its subscription was held (`Restored`).
#[test]
fn a_stalled_subscriber_does_not_hold_back_the_others() {
    big(|| {
        let mut w = world(93);
        let m = w.members.clone();
        let (writer, subs) = (m[0], &m[1..]);
        let (stalled, healthy) = (subs[0], &subs[1..]);
        burst(&mut w, writer, subs);
        let (hub, site) = (w.sim.site(w.hubs[0].0), w.sim.site(stalled));
        let path = LinkConfig {
            delay: OWD,
            bandwidth_bps: 10_000_000,
            ..LinkConfig::default()
        };
        w.run(START);
        w.sim.set_link(
            hub,
            site,
            LinkConfig {
                blocked: true,
                ..path.clone()
            },
        );
        w.run(START + secs(10));
        w.sim.set_link(hub, site, path);
        w.run(DRAINED);
        let acked = count(&w, writer, DRAINED, |e| matches!(e, NodeEvent::PublishAcked { .. }));
        let got: Vec<usize> = healthy
            .iter()
            .map(|s| count(&w, *s, DRAINED, |e| matches!(e, NodeEvent::Message { .. })))
            .collect();
        let end = START + secs(60);
        w.run(end);
        let stalled_got = count(&w, stalled, end, |e| matches!(e, NodeEvent::Message { .. }));
        let told = count(&w, stalled, end, |e| matches!(e, NodeEvent::Restored { .. }));
        eprintln!(
            "stalled: acked {acked} by the drain, healthy {got:?}, stalled got {stalled_got} told {told}, {:.0} acks/s",
            ack_rate(&w, writer)
        );
        assert_eq!(
            acked, N,
            "the publisher must hear every publish acknowledged by the drain"
        );
        for (j, g) in got.iter().enumerate() {
            assert_eq!(*g, N, "healthy subscriber {j} got {g} of {N} by the end of the drain");
        }
        assert!(
            stalled_got == N || told > 0,
            "the stalled subscriber got {stalled_got} of {N} and was not told"
        );
    });
}

#[test]
fn a_pushlog_burst_reaches_every_subscriber() {
    big(|| {
        let mut w = world(91);
        let m = w.members.clone();
        let (writer, subs) = (m[0], &m[1..]);
        burst(&mut w, writer, subs);
        let drained = DRAINED;
        w.run(drained);
        eprintln!("burst: {:.0} acks/s", ack_rate(&w, writer));
        let acked = count(&w, writer, drained, |e| matches!(e, NodeEvent::PublishAcked { .. }));
        let gave_up = count(&w, writer, drained, |e| matches!(e, NodeEvent::PublishGaveUp { .. }));
        let got: Vec<usize> = subs
            .iter()
            .map(|s| count(&w, *s, drained, |e| matches!(e, NodeEvent::Message { .. })))
            .collect();
        let repaired: usize = subs
            .iter()
            .map(|s| count(&w, *s, drained, |e| matches!(e, NodeEvent::GapRepaired { .. })))
            .sum();
        let lost = SUBS * N - got.iter().sum::<usize>();
        eprintln!(
            "burst: acked {acked} gave_up {gave_up} delivered {got:?} repaired {repaired} lost {lost} of {}",
            SUBS * N
        );
        assert_eq!(acked, N, "the publisher must hear every publish acknowledged");
        for (j, g) in got.iter().enumerate() {
            assert_eq!(*g, N, "subscriber {j} got {g} of {N} by the end of the drain");
        }
    });
}

/// A path that loses packets delivers a stream in jumps: everything behind a lost packet becomes readable at once
/// when the packet is sent again. A subscriber reads all of it as the frames it is, resets no stream, and misses
/// nothing.
#[test]
fn a_burst_over_a_path_that_loses_packets_reaches_every_subscriber_and_no_stream_is_reset() {
    const SOME: usize = 3;
    const COUNT: usize = 600;
    big(|| {
        let mut w = world_with(93, SOME, Loss::Bernoulli(0.02));
        let m = w.members.clone();
        let (writer, subs) = (m[0], &m[1..]);
        for s in subs {
            w.sim.command(secs(20), *s, NCmd::Subscribe(TOPIC.to_vec()));
        }
        let start = secs(40);
        for i in 0..COUNT {
            w.sim.command(
                start + (i as Time) * MS / 10,
                writer,
                NCmd::Publish {
                    topic: TOPIC.to_vec(),
                    body: body(i),
                },
            );
        }
        let drained = start + secs(30);
        w.run(drained);
        let got: Vec<usize> = subs
            .iter()
            .map(|s| count(&w, *s, drained, |e| matches!(e, NodeEvent::Message { .. })))
            .collect();
        let resets: usize = subs
            .iter()
            .map(|s| {
                w.sim
                    .node(*s)
                    .traces
                    .iter()
                    .filter(|(_, t)| matches!(t.body, Body::Node(NodeTrace::StreamReset { .. })))
                    .count()
            })
            .sum();
        eprintln!("lossy burst: delivered {got:?} stream resets {resets}");
        assert_eq!(resets, 0, "a subscriber reset a stream whose frames were whole");
        for (j, g) in got.iter().enumerate() {
            assert_eq!(*g, COUNT, "subscriber {j} got {g} of {COUNT}");
        }
    });
}

/// With every subscriber on the hub's LAN the streams keep up, so the hub refuses no store: every publish is
/// acknowledged on its first send, before any retry, and the publisher runs at the rate it publishes.
#[test]
fn a_burst_on_a_fast_lan_is_not_paced() {
    big(|| {
        let mut w = world_lan(94);
        let m = w.members.clone();
        let (writer, subs) = (m[0], &m[1..]);
        burst(&mut w, writer, subs);
        w.run(DRAINED);
        let acks: Vec<Time> = w
            .sim
            .events(writer)
            .iter()
            .filter(|(_, e)| matches!(e, NEv::Node(NodeEvent::PublishAcked { .. })))
            .map(|(t, _)| *t)
            .collect();
        let last = acks.iter().max().copied().unwrap_or(START);
        let got: Vec<usize> = subs
            .iter()
            .map(|s| count(&w, *s, DRAINED, |e| matches!(e, NodeEvent::Message { .. })))
            .collect();
        eprintln!(
            "lan: acked {} last ack at +{} ms, {:.0} acks/s, delivered {got:?}",
            acks.len(),
            (last - START) / MS,
            ack_rate(&w, writer)
        );
        assert_eq!(acks.len(), N, "the publisher must hear every publish acknowledged");
        assert!(
            last < START + pinc_broadcast::consts::PUB_RETRY,
            "a publish waited for a retry: the hub refused a store"
        );
        for (j, g) in got.iter().enumerate() {
            assert_eq!(*g, N, "subscriber {j} got {g} of {N} by the end of the drain");
        }
    });
}

/// A burst longer than the hub's log (6,000 bodies of 4 KiB, about 24 MiB, past the log's 2,048 entries and 16 MiB):
/// whatever the hub acknowledges, every subscriber gets. The hub stops storing, and so acknowledging, once the log
/// would evict what a subscriber is still owed; the publisher then retries, or is refused when it tracks as many
/// publishes as it can, but it never hears a message acknowledged that a subscriber then never gets.
#[test]
fn a_burst_longer_than_the_log_acknowledges_nothing_it_loses() {
    big(|| {
        const LONG: usize = 6000;
        let mut w = world(95);
        let m = w.members.clone();
        let (writer, subs) = (m[0], &m[1..]);
        burst_of(&mut w, writer, subs, LONG);
        // Past the 90 s give-up of the last publish, so every accepted publish has an outcome.
        let end = START + secs(100);
        w.run(end);
        let mids = |n: pinc_sim::NodeId, acked: bool| -> std::collections::BTreeSet<[u8; 8]> {
            w.sim
                .events(n)
                .iter()
                .filter_map(|(_, e)| match e {
                    NEv::Node(NodeEvent::PublishAcked { mid }) if acked => Some(*mid),
                    NEv::Node(NodeEvent::Message { mid, .. }) if !acked => Some(*mid),
                    _ => None,
                })
                .collect()
        };
        let acked = mids(writer, true);
        let missing: Vec<usize> = subs
            .iter()
            .map(|s| acked.difference(&mids(*s, false)).count())
            .collect();
        let gave_up = count(&w, writer, end, |e| matches!(e, NodeEvent::PublishGaveUp { .. }));
        eprintln!(
            "long: acked {} gave_up {gave_up} of {LONG}, acked but missing at each subscriber {missing:?}",
            acked.len()
        );
        assert!(!acked.is_empty(), "the publisher heard nothing acknowledged");
        for (j, n) in missing.iter().enumerate() {
            assert_eq!(
                *n, 0,
                "subscriber {j} never got {n} messages the publisher heard acknowledged"
            );
        }
    });
}
