//! A node that left its group keeps no membership deadline (vinc#551). Membership does nothing on a timer once it is
//! leaving, so a deadline it kept would stay due: every timer call would leave the node due again at once, which the
//! simulator counts as a timer violation, and a host that serves due timers before anything else (the facade's
//! `run_as`, under `Endpoint::close`) would spin forever.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod node_common;

use node_common::{World, big, secs};
use vinc_tests::NCmd;

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
    });
}
