//! With every layer active and idle (a value fetched, a set reconciled, a bundle held) the node allocates nothing
//! in steady state.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod layers_common;

use layers_common::{all_layers, big, secs};
use vinc_node::NodeEvent;
use vinc_tests::{meter_endpoint_calls, take_metered_allocs};

vinc_tests::install_counting_allocator!();

#[test]
fn the_node_allocates_nothing_in_steady_state_with_every_layer_active() {
    big(|| {
        let mut w = all_layers(501, secs(120));
        let m = w.members.clone();
        let seen = w.node_events(m[0]);
        assert!(
            seen.iter().any(|(_, e)| matches!(e, NodeEvent::ValueComplete { .. })),
            "the fetch completed"
        );
        assert!(
            seen.iter().any(|(_, e)| matches!(e, NodeEvent::ReconcileDone { .. })),
            "the round finished"
        );
        assert_eq!(w.sim.node(m[0]).node.dtn_held(), 1, "the bundle is held");
        let _ = take_metered_allocs();
        meter_endpoint_calls(true);
        w.run(secs(420));
        meter_endpoint_calls(false);
        let n = take_metered_allocs();
        assert_eq!(n, 0, "the node allocated {n} times in steady state");
    });
}
