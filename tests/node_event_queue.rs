//! The node's event queue keeps an event the application cannot recover: the node stops taking events from the
//! endpoint while its queue is nearly full, so the endpoint's own rule applies, and what it must drop it drops
//! recoverable first.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::semicolon_if_nothing_returned
)]

mod node_common;

use node_common::{World, big, secs};
use pinc_core::{Answer, Command, Event, Query, Role, SessionStats};
use pinc_node::{HUB_ALPN, NodeEvent};
use pinc_tests::MS_NS;

/// Every live session of an endpoint, as its counters.
macro_rules! stats_list {
    ($ep:expr) => {{
        let mut v: Vec<SessionStats> = Vec::new();
        for i in 0..256 {
            match $ep.query(Query::SessionAt(i)) {
                Answer::Stats(s) => v.push(s),
                _ => break,
            }
        }
        v
    }};
}

fn is_hub_with(s: &SessionStats, peer: &[u8; 32]) -> bool {
    s.node.is_some_and(|n| n.bytes == *peer) && s.alpn.is_some_and(|a| a.as_bytes() == HUB_ALPN)
}

#[test]
fn the_node_queue_keeps_the_close_of_a_session_the_host_reads_late() {
    big(|| {
        let mut w = World::build(13, 1, 1);
        w.run(secs(20));
        let (hub, m) = (w.hubs[0].0, w.members[0]);
        let hid = w.id(hub);
        let sid = stats_list!(w.sim.node(m).node.endpoint())
            .into_iter()
            .find(|s| is_hub_with(s, &hid))
            .expect("the member holds a hub session")
            .session;
        let me = w.sim.node(m).me;
        let t = secs(20);
        let node = &mut w.sim.node_mut(m).node;
        // A host that reads no event for a while issues commands: each dial of itself queues one ConnectFailed.
        for _ in 0..8_300 {
            let _ = node.command(
                t,
                Command::Connect {
                    node: me,
                    alpn: b"t/app",
                    addrs: &[],
                    role: Role::Other,
                },
            );
        }
        // Then the hub session ends.
        let _ = node.command(t, Command::Close { session: sid, error: 0 });
        for k in 1..=100u64 {
            node.handle_timeout(t + k * 100 * MS_NS);
        }
        let core = node.endpoint().node_stats();
        let (mut lost, mut closed) = (0u32, 0u32);
        while let Some(e) = node.poll_event() {
            match e {
                NodeEvent::Lost { count } => lost += count,
                NodeEvent::Endpoint(Event::Closed { session, .. }) if session == sid => closed += 1,
                _ => {}
            }
        }
        assert_eq!((core.events_dropped, core.events_lost), (0, 0));
        assert_eq!(
            closed, 1,
            "the Closed of the session was dropped by the node's queue (Lost {lost})"
        );
    });
}
