//! A stream event of a hub session never reaches the application, and a hub stream the peer stopped is replaced, so
//! the member's later publishes arrive.
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
use vinc_core::{Answer, Command, Event, Query, SessionStats};
use vinc_node::{HUB_ALPN, NodeEvent};
use vinc_tests::{NCmd, NEv, SEC_NS};

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
fn a_stopped_hub_stream_does_not_reach_the_application() {
    big(|| {
        let mut w = World::build_with(11, 1, 1, |w| w.trace = true);
        w.run(secs(20));
        let (hub, m) = (w.hubs[0].0, w.members[0]);
        let mid = w.id(m);
        let sid = stats_list!(w.sim.node(hub).node.endpoint())
            .into_iter()
            .find(|s| is_hub_with(s, &mid))
            .expect("the hub holds a hub session with the member")
            .session;
        let t = secs(20);
        // The hub asks the member to stop sending on stream 0, the write stream the member opened when it dialed.
        let r = w.sim.node_mut(hub).node.command(
            t,
            Command::StopSending {
                session: sid,
                stream: 0,
                error: 7,
            },
        );
        assert!(r.is_ok(), "{r:?}");
        w.sim.command(t, hub, NCmd::Tick);
        w.run(secs(25));
        let stopped: Vec<_> = w
            .sim
            .events(m)
            .iter()
            .filter(|(at, e)| *at >= t && matches!(e, NEv::Node(NodeEvent::Endpoint(Event::StreamStopped { .. }))))
            .cloned()
            .collect();
        assert!(
            stopped.is_empty(),
            "a hub-protocol session raised a stream event for the application: {stopped:?}"
        );
    });
}

/// What the stopped write stream costs: the node keeps it as the member's hub write stream, so what the member

#[test]
fn after_the_stop_a_members_publish_still_arrives() {
    big(|| {
        let mut w = World::build_with(12, 1, 2, |w| w.trace = true);
        let (hub, m0, m1) = (w.hubs[0].0, w.members[0], w.members[1]);
        for m in [m0, m1] {
            w.sim.command(secs(1), m, NCmd::Subscribe(b"t".to_vec()));
        }
        w.run(secs(20));
        w.sim.command(
            secs(20),
            m0,
            NCmd::Publish {
                topic: b"t".to_vec(),
                body: b"before".to_vec(),
            },
        );
        w.run(secs(30));
        let mid = w.id(m0);
        let sid = stats_list!(w.sim.node(hub).node.endpoint())
            .into_iter()
            .find(|s| is_hub_with(s, &mid))
            .unwrap()
            .session;
        let t = secs(30);
        let _ = w.sim.node_mut(hub).node.command(
            t,
            Command::StopSending {
                session: sid,
                stream: 0,
                error: 7,
            },
        );
        w.sim.command(t, hub, NCmd::Tick);
        w.run(secs(35));
        w.sim.command(
            secs(35),
            m0,
            NCmd::Publish {
                topic: b"t".to_vec(),
                body: b"after".to_vec(),
            },
        );
        w.run(secs(120));
        let got: Vec<_> = w
            .messages(m1)
            .into_iter()
            .map(|(at, _, _, body)| (at / SEC_NS, body))
            .collect();
        assert!(
            got.iter().any(|(_, b)| b == b"after"),
            "the publish after the stop never arrived"
        );
    });
}

// ------------------------------------------------------------------------------------------------ claim 2
