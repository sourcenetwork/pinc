//! A hub's write stream to a member that the member stopped or reset is replaced by a fresh one on the hub's next duty
//! pass, so the hub's later frames (a message, a delta) still reach the member.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names
)]

mod node_common;

use node_common::{World, big, secs};
use vinc_core::{Answer, Command, Query, SessionStats};
use vinc_node::HUB_ALPN;
use vinc_tests::{NCmd, SEC_NS};

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

/// The member stops (`Some(true)`) or resets (`Some(false)`) the hub's write stream, the first stream the hub opened on
/// the session, or leaves it (`None`); then the other member publishes: the publish reaches the member.
fn publish_after(seed: u64, action: Option<bool>) {
    big(move || {
        let mut w = World::build_with(seed, 1, 2, |w| w.trace = true);
        let (m0, m1) = (w.members[0], w.members[1]);
        for m in [m0, m1] {
            w.sim.command(secs(1), m, NCmd::Subscribe(b"t".to_vec()));
        }
        w.run(secs(20));
        let hub_id = w.id(w.hubs[0].0);
        let sid = stats_list!(w.sim.node(m0).node.endpoint())
            .into_iter()
            .find(|s| s.node.is_some_and(|n| n.bytes == hub_id) && s.alpn.is_some_and(|a| a.as_bytes() == HUB_ALPN))
            .expect("the member holds a hub session")
            .session;
        let t = secs(20);
        // Stream 1 is the first stream the hub opened on the session: the one it writes its frames to the member on.
        if let Some(stop) = action {
            let cmd = if stop {
                Command::StopSending {
                    session: sid,
                    stream: 1,
                    error: 7,
                }
            } else {
                Command::Reset {
                    session: sid,
                    stream: 1,
                    error: 1,
                }
            };
            let r = w.sim.node_mut(m0).node.command(t, cmd);
            assert!(r.is_ok(), "{r:?}");
        }
        w.sim.command(t, m0, NCmd::Tick);
        w.run(secs(40));
        w.sim.command(
            secs(40),
            m1,
            NCmd::Publish {
                topic: b"t".to_vec(),
                body: b"after".to_vec(),
            },
        );
        w.run(secs(120));
        let got: Vec<_> = w
            .messages(m0)
            .into_iter()
            .map(|(at, _, _, body)| (at / SEC_NS, body))
            .collect();
        assert!(
            got.iter().any(|(_, b)| b == b"after"),
            "the hub's frame never reached the member (its action on the hub's write stream: {action:?})"
        );
    });
}

#[test]
fn after_a_member_stops_the_hubs_write_stream_the_hubs_later_frames_reach_it() {
    publish_after(21, Some(true));
}

#[test]
fn after_a_member_resets_the_hubs_write_stream_the_hubs_later_frames_reach_it() {
    publish_after(22, Some(false));
}

/// The setup itself: with the stream left alone, the publish arrives.
#[test]
fn with_the_hubs_write_stream_left_alone_the_hubs_later_frames_reach_the_member() {
    publish_after(23, None);
}
