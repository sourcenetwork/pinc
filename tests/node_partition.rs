//! Partitions and heals over real sessions: views converge after a heal; a hub that confirmed a member down on a
//! dropped carrier restores its entry and its subscriptions when the carrier returns.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod node_common;

use node_common::{World, big, secs};
use vinc_node::NodeEvent;
use vinc_sim::{LinkChange, MS, NodeId as SimId};
use vinc_tests::{NCmd, NEv};

const TOPIC: &[u8] = b"news";

#[test]
fn views_converge_after_a_long_partition_heals() {
    big(|| {
        for seed in [91u64, 92, 93] {
            let mut w = World::build(seed, 3, 6);
            let hubs: Vec<SimId> = w.hubs.iter().map(|(n, _)| *n).collect();
            let m = w.members.clone();
            let side_a: Vec<SimId> = [hubs[0], hubs[1]].into_iter().chain(m[..3].iter().copied()).collect();
            let side_b: Vec<SimId> = [hubs[2]].into_iter().chain(m[3..].iter().copied()).collect();
            // Longer than the 80 s lease: each side declares the other down, as it must.
            w.sim.partition(secs(60), &[&side_a, &side_b]);
            w.sim.heal(secs(200));
            w.run(secs(220));
            // While apart, each side lost the other.
            // After the heal the views merge.
            w.run(secs(420));
            for n in hubs.iter().chain(m.iter()) {
                assert_eq!(w.view(*n), w.others(*n), "seed {seed}: the view of {n:?} after the heal");
            }
        }
    });
}

#[test]
fn a_returning_carrier_restores_the_subscriptions_its_hub_held() {
    big(|| {
        for seed in [101u64, 102, 103] {
            let mut w = World::build_with(seed, 3, 4, |w| w.trace = true);
            let (a, b, c) = (w.hubs[0].0, w.hubs[1].0, w.hubs[2].0);
            let (sub, publisher) = (w.members[0], w.members[1]);
            // The subscriber is nearest to hub A, so A is its primary.
            w.sim.link_change(0, sub, a, LinkChange::Delay(MS));
            w.sim.link_change(0, a, sub, LinkChange::Delay(MS));
            w.sim.command(secs(20), sub, NCmd::Subscribe(TOPIC.to_vec()));
            // A loses sight of the subscriber and of the other hubs for five seconds, with the subscriber's carriers
            // reset: A confirms it down on its dropped carrier and holds its subscriptions.
            w.sim.command(secs(41), sub, NCmd::DropCarriers);
            w.sim.outage(a, sub, secs(41), secs(47));
            w.sim.outage(a, b, secs(41), secs(47));
            w.sim.outage(a, c, secs(41), secs(47));
            w.sim.command(secs(70), publisher, NCmd::Publish { topic: TOPIC.to_vec(), body: b"after".to_vec() });
            w.run(secs(120));
            let restored = w.sim.events(sub).iter().any(|(_, e)| matches!(e, NEv::Node(NodeEvent::Restored { .. })));
            assert!(restored, "seed {seed}: the subscriber was never told its subscriptions are live again");
            let got: Vec<_> = w.messages(sub).into_iter().map(|(_, _, _, b)| b).collect();
            assert!(got.contains(&b"after".to_vec()), "seed {seed}: the restored subscriber missed the publish");
            let id = w.id(sub);
            assert_eq!(w.sim.node(a).node.broadcast().sub_state(TOPIC, &id), Some(true), "seed {seed}: hub A holds the subscription");
        }
    });
}
