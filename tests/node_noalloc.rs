//! The node allocates nothing in steady state: datagrams in, the hub stream, membership timers and datagrams out,
//! over a quiet minute of a hub and its members.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod node_common;

use node_common::{World, big, secs};
use vinc_tests::{meter_endpoint_calls, take_metered_allocs};

vinc_tests::install_counting_allocator!();

#[test]
fn the_node_allocates_nothing_in_steady_state() {
    big(|| {
        let mut w = World::build(151, 2, 4);
        w.run(secs(90));
        let _ = take_metered_allocs();
        meter_endpoint_calls(true);
        w.run(secs(300));
        meter_endpoint_calls(false);
        let n = take_metered_allocs();
        assert_eq!(n, 0, "the node allocated {n} times in steady state");
    });
}
