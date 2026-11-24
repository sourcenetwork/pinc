//! A revoke ends a dial that is still probing its quiet parent: the dial is listed with the sessions of the peer, so
//! the revoke closes it, and when its probe window passes no handshake goes to the revoked peer.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::similar_names
)]

mod node_common;

use node_common::{World, big, secs};
use pinc_core::{Answer, Command, Event, Query, Role, SessionStats, Value};
use pinc_node::NodeEvent;
use pinc_tests::{NCmd, NEv};

fn sessions_of(w: &World, peer: &[u8; 32]) -> Vec<SessionStats> {
    let ep = w.sim.node(w.members[0]).node.endpoint();
    (0..)
        .map_while(|i| match ep.query(Query::SessionAt(i)) {
            Answer::Stats(s) => Some(s),
            _ => None,
        })
        .filter(|s| s.node.is_some_and(|n| n.bytes == *peer))
        .collect()
}

#[test]
fn a_revoke_during_a_probe_ends_the_dial_and_no_handshake_goes_to_the_peer() {
    big(|| {
        let mut w = World::build(31, 1, 1);
        let (hub, m) = (w.hubs[0].0, w.members[0]);
        let (hid, haddr) = (w.sim.node(hub).me, w.hubs[0].1.udp);
        w.run(secs(8));
        assert!(
            !sessions_of(&w, &hid.bytes).is_empty(),
            "the member holds no session with the hub"
        );
        // The hub falls silent: its session with the member is quiet for over 20 s at the dial.
        w.sim.outage(m, hub, secs(8), secs(300));
        w.run(secs(34));
        let t = secs(34);
        let Ok(Value::Session(dial)) = w.sim.node_mut(m).node.command(
            t,
            Command::Connect {
                node: hid,
                alpn: b"t/app",
                addrs: &[haddr],
                role: Role::Other,
            },
        ) else {
            panic!("the dial was refused")
        };
        let probing = sessions_of(&w, &hid.bytes).into_iter().find(|s| s.session == dial);
        assert!(
            probing.is_some_and(|s| !s.established),
            "the dial is not listed while it probes"
        );
        w.sim.command(t, m, NCmd::Revoke(hid.bytes));
        w.run(secs(45));
        assert!(
            sessions_of(&w, &hid.bytes).is_empty(),
            "a session with the revoked peer is left: {:?}",
            sessions_of(&w, &hid.bytes)
        );
        let failed = w.sim.events(m).iter().any(|(_, e)| {
            matches!(e, NEv::Node(NodeEvent::Endpoint(Event::ConnectFailed { session: Some(s), .. })) if *s == dial)
        });
        assert!(failed, "the dial was not reported failed");
    });
}
