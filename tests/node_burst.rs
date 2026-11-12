//! A burst through a hub: the pushlog shape of `DefraDB` (2,000 bodies of 4 KiB at 10,000 a second) reaches every
//! subscriber behind a slow link, and the publisher hears the outcome of every publish.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod node_common;

use node_common::{OWD, World, big, secs};
use vinc_broadcast::Trace as BTrace;
use vinc_node::NodeEvent;
use vinc_node::trace::Body;
use vinc_sim::{LinkConfig, MS, Sim, SimConfig, Time};
use vinc_tests::{NCmd, NEv};

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
    let mut w = World::build_with(seed, 1, 1 + SUBS, |w| {
        // The hub's log is what a subscriber on a slow path is served from: it must hold the burst (about 8.2 MiB).
        w.limits.log_bytes = 16 << 20;
        w.sim = Sim::with_config(
            seed,
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
    let (hub, writer) = (w.sim.site(w.hubs[0].0), w.sim.site(w.members[0]));
    let lan = LinkConfig {
        delay: MS / 4,
        ..LinkConfig::default()
    };
    w.sim.set_link_pair(hub, writer, lan.clone(), lan);
    w
}

fn count(w: &World, n: vinc_sim::NodeId, until: Time, f: impl Fn(&NodeEvent) -> bool) -> usize {
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

#[test]
fn a_pushlog_burst_reaches_every_subscriber() {
    big(|| {
        let mut w = world(91);
        let m = w.members.clone();
        let (writer, subs) = (m[0], &m[1..]);
        for s in subs {
            w.sim.command(secs(20), *s, NCmd::Subscribe(TOPIC.to_vec()));
        }
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
        // The harness's drain: 15 s after the last publish.
        let drained = start + secs(15) + MS * 200;
        w.run(drained);
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
