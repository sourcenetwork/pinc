//! The push-back of the accept room (pinc#436): an endpoint owes its host every server session a first flight made
//! until the host reads its `Incoming` or it ends, and starts none while the owed sessions fill the room the host set.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::net::SocketAddr;

use pinc_core::{Command, Event, Role, Taken};
use pinc_tests::*;

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

/// Sessions whose peer is not authenticated yet hold at most half of the room (rounded up), so first flights that
/// never finish, each of which keeps its place for 30 s, leave the rest to a peer that resumes with a ticket.
#[test]
fn first_flights_that_never_finish_leave_room_for_a_peer_that_resumes() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        // Node a gets a ticket of node b's: a session the host takes, then closed.
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let end = net.now + 5 * SEC_NS;
        let ticket = |n: &mut CoreNet| n.nodes[a].saw(|e| matches!(e, Event::TicketsReceived { .. }));
        assert!(net.run(end, ticket), "a got no ticket");
        assert_eq!(net.nodes[b].ep.session_taken(sb), Taken::Reserved);
        let now = net.now;
        net.nodes[a].cmd(now, Command::Close { session: sa, error: 0 }).unwrap();
        let end = net.now + 10 * SEC_NS;
        let closed = |n: &mut CoreNet| n.nodes[b].count(|e| matches!(e, Event::Closed { .. })) == 1;
        assert!(net.run(end, closed), "b never saw the close");
        // Room for four, and four dialers whose replies never arrive: their sessions stay unauthenticated at b.
        net.nodes[b].ep.set_backlog_room(4);
        let from_b = net.nodes[b].addr;
        let flood: Vec<usize> = (10..14).map(|tag| net.add(tag)).collect();
        let deaf: Vec<SocketAddr> = flood.iter().map(|f| net.nodes[*f].addr).collect();
        net.loss = Some(Box::new(move |from, to, _| from == from_b && deaf.contains(&to)));
        for f in &flood {
            dial(&mut net, *f, b);
        }
        net.run_for(SEC_NS);
        let ns = net.nodes[b].ep.node_stats();
        assert_eq!(
            (ns.half_open, ns.owed),
            (2, 2),
            "unauthenticated sessions took more than half of the room: {ns:?}"
        );
        // The peer with a ticket is admitted beside them, and is not one of the counted.
        let incoming = |n: &CoreNet| n.nodes[b].count(|e| matches!(e, Event::Incoming { .. }));
        let before = incoming(&net);
        dial(&mut net, a, b);
        let end = net.now + 5 * SEC_NS;
        assert!(
            net.run(end, |n| incoming(n) > before),
            "the peer that resumes was shut out: {:?}",
            net.nodes[b].ep.node_stats()
        );
        let ns = net.nodes[b].ep.node_stats();
        assert_eq!((ns.half_open, ns.backlog_refused), (2, 0), "{ns:?}");
    });
}
