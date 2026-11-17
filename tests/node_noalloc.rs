//! The node allocates nothing in steady state: datagrams in, the hub stream, membership timers and datagrams out,
//! over a quiet minute of a hub and its members.
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

use node_common::{World, big, secs};
use vinc_node::NodeEvent;
use vinc_tests::{NCmd, NEv, meter_endpoint_calls, take_metered_allocs};

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

/// The messages one subscriber is delivered and the allocations the nodes make over a window of `n` publishes, with
/// the same seed and schedule whether the nodes keep heads or not.
fn delivery_window(keep_heads: bool, n: u64) -> (u64, u64) {
    const TOPIC: &[u8] = b"alloc";
    big(move || {
        let mut w = World::build_with(152, 2, 2, |w| w.limits.keep_heads = keep_heads);
        let (publisher, subscriber) = (w.members[0], w.members[1]);
        w.sim.command(secs(20), subscriber, NCmd::Subscribe(TOPIC.to_vec()));
        let publish = |w: &mut World, at: u64, i: u64| {
            let cmd = NCmd::Publish {
                topic: TOPIC.to_vec(),
                body: vec![i as u8; 100],
            };
            w.sim.command(secs(at), publisher, cmd);
        };
        // Warm: the first messages size the queues and tables.
        for i in 0..8 {
            publish(&mut w, 40 + i, i);
        }
        w.run(secs(90));
        let seen = |w: &World| {
            w.sim
                .events(subscriber)
                .iter()
                .filter(|(_, e)| matches!(e, NEv::Node(NodeEvent::Message { .. } | NodeEvent::Envelope { .. })))
                .count() as u64
        };
        let warm = seen(&w);
        assert_eq!(warm, 8, "every warm-up message was delivered");
        for i in 0..n {
            publish(&mut w, 100 + i, i);
        }
        let _ = take_metered_allocs();
        meter_endpoint_calls(true);
        w.run(secs(110 + n));
        meter_endpoint_calls(false);
        (seen(&w) - warm, take_metered_allocs())
    })
}

/// Ed25519 nodes are enough: an envelope is one allocation whatever the identity algorithm is (only its size changes),
/// and a plain message is two (the topic and the payload). The nodes also allocate for other reasons (the publisher,
/// the queues), and those differ a little between the two runs, so the difference is not exactly one per message: it
/// is the 15 of 16 and 46 of 48 messages that the simulator's fixed schedule measures, deterministically.
#[test]
fn a_delivered_message_makes_about_one_allocation_fewer_as_an_envelope_than_as_a_plain_message() {
    let (short, long) = (16, 48);
    let (off_s, off_s_allocs) = delivery_window(false, short);
    let (off_l, off_l_allocs) = delivery_window(false, long);
    let (on_s, on_s_allocs) = delivery_window(true, short);
    let (on_l, on_l_allocs) = delivery_window(true, long);
    println!(
        "allocations over {short} and {long} messages: off {off_s_allocs} and {off_l_allocs}, \
         on {on_s_allocs} and {on_l_allocs}"
    );
    assert_eq!(
        (off_s, off_l, on_s, on_l),
        (short, long, short, long),
        "every message was delivered"
    );
    assert_eq!(
        (off_s_allocs - on_s_allocs, off_l_allocs - on_l_allocs),
        (15, 46),
        "allocations off and on: {off_s_allocs} and {on_s_allocs} over {short} messages, {off_l_allocs} and \
         {on_l_allocs} over {long}"
    );
}
