//! A node that left its group keeps no membership deadline (pinc#551). Membership does nothing on a timer once it is
//! leaving, so a deadline it kept would stay due: every timer call would leave the node due again at once, which the
//! simulator counts as a timer violation, and a host that serves due timers before anything else (the facade's
//! `run_as`, under `Endpoint::close`) would spin forever.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod node_common;

use node_common::{World, big, secs};
use pinc_node::Timed;
use pinc_tests::NCmd;

#[test]
fn a_member_and_a_hub_that_left_arm_no_timer_already_due() {
    big(|| {
        let mut w = World::build(21, 2, 2);
        w.run(secs(20));
        assert_eq!(w.sim.metrics().timer_violations, 0, "no violation before anyone leaves");
        let (member, hub) = (w.members[0], w.hubs[1].0);
        w.sim.command(secs(20), member, NCmd::Leave);
        w.sim.command(secs(20), hub, NCmd::Leave);
        // Long enough for every membership timer the two nodes held to fall due: ticks, renewals, the slow tick.
        w.run(secs(40));
        assert_eq!(w.sim.metrics().timer_violations, 0, "a node that left kept a due timer");
        // The node holds back a deadline its timer calls do not move (pinc#569), so the simulator is handed it once at
        // most: the node's own count shows the rest.
        for n in [member, hub] {
            assert_eq!(
                w.sim.node(n).node.timer_stats().total(),
                0,
                "a node that left kept a due timer"
            );
        }
    });
}

/// A layer that keeps a deadline due across timer calls is counted by the node, which yields one tick after it: the
/// simulator sees no violation and the run ends (`run` returns: a live-lock at one instant would not).
#[test]
fn a_layer_that_leaves_its_deadline_due_is_counted_and_yields() {
    big(|| {
        let mut w = World::build(21, 2, 2);
        w.run(secs(20));
        let member = w.members[0];
        w.sim.node_mut(member).node.stick_timer(Some(secs(20)));
        w.run(secs(22));
        assert!(
            w.sim.node(member).node.timer_stats().stuck(Timed::Endpoint) > 0,
            "the node did not count the deadline it was left"
        );
        assert_eq!(
            w.sim.metrics().timer_violations,
            0,
            "the node answers a tick after a stuck call, so the simulator sees none"
        );
    });
}
