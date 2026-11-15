//! The push-back of the accept room (vinc#436): an endpoint owes its host every server session a first flight made
//! until the host reads its `Incoming` or it ends, and starts none while the owed sessions fill the room the host set.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use vinc_core::{Command, Event, Role, Taken};
use vinc_tests::*;

fn dial(net: &mut CoreNet, from: usize, to: usize) {
    let (peer, addr, now) = (net.nodes[to].node, net.nodes[to].addr, net.now);
    net.nodes[from].connect(now, peer, ALPN_A, addr, Role::Other).unwrap();
}

fn connected(net: &CoreNet, n: usize) -> usize {
    net.nodes[n].count(|e| matches!(e, Event::Connected { .. }))
}

#[test]
fn a_first_flight_past_the_room_is_refused_before_any_work() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        net.nodes[b].ep.set_backlog_room(0);
        dial(&mut net, a, b);
        net.run_for(3 * SEC_NS);
        let ns = net.nodes[b].ep.node_stats();
        assert!(
            ns.backlog_refused >= 2,
            "the first flight and its resend are refused: {ns:?}"
        );
        assert_eq!(
            (ns.sessions, ns.half_open, ns.owed, ns.dropped_in),
            (0, 0, 0, 0),
            "nothing kept: {ns:?}"
        );
        // Room for one: the next resend makes the session.
        net.nodes[b].ep.set_backlog_room(1);
        let end = net.now + 20 * SEC_NS;
        assert!(net.run(end, |n| connected(n, a) == 1), "no session once there was room");
        assert_eq!(net.nodes[b].ep.node_stats().owed, 1);
    });
}

#[test]
fn a_session_the_host_has_not_taken_keeps_its_place_after_its_handshake() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b, c) = (net.add(1), net.add(2), net.add(3));
        net.nodes[b].ep.set_backlog_room(1);
        let (_, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        // The handshake is over and the Incoming raised, but the host has not taken it: its place is still held.
        assert_eq!(net.nodes[b].ep.node_stats().owed, 1);
        let refused = net.nodes[b].ep.node_stats().backlog_refused;
        dial(&mut net, c, b);
        net.run_for(3 * SEC_NS);
        let ns = net.nodes[b].ep.node_stats();
        assert!(ns.backlog_refused > refused, "c was not pushed back: {ns:?}");
        assert_eq!((connected(&net, c), ns.sessions), (0, 1));
        assert_eq!(net.nodes[b].ep.session_taken(sb), Taken::Reserved);
        assert_eq!(
            net.nodes[b].ep.session_taken(sb),
            Taken::Unreserved { owed: 0 },
            "taken once"
        );
        // Its place is free: c's next resend is admitted.
        let end = net.now + 20 * SEC_NS;
        assert!(net.run(end, |n| connected(n, c) == 1), "c never got the free place");
        assert_eq!(net.nodes[b].ep.node_stats().owed, 1);
    });
}

#[test]
fn a_session_that_ends_before_it_is_taken_gives_its_place_back_and_gets_none() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        net.nodes[b].ep.set_backlog_room(1);
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let now = net.now;
        net.nodes[a].cmd(now, Command::Close { session: sa, error: 0 }).unwrap();
        let end = net.now + 10 * SEC_NS;
        let closed =
            |n: &mut CoreNet| n.nodes[b].count(|e| matches!(e, Event::Closed { session, .. } if *session == sb)) == 1;
        assert!(net.run(end, closed), "b never saw the close");
        assert_eq!(
            net.nodes[b].ep.node_stats().owed,
            0,
            "the place went back when the session ended"
        );
        assert_eq!(net.nodes[b].ep.session_taken(sb), Taken::Gone);
        assert_eq!(net.nodes[b].ep.node_stats().owed, 0);
    });
}
