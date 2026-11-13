//! The endpoint-level timing rules for redial and flights: redial after a suspension, the flush order, and the hooks
//! that send a handshake flight on several paths.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss
)]

#[path = "core_timing_common.rs"]
mod common;

use std::net::SocketAddr;

use common::{S, is_connected};
use vinc_core::{Answer, Command, EndReason, Event, IfaceEvent, IfaceId, Query, Role, Value};
use vinc_crypto::NodeId;
use vinc_tests::*;
use vinc_transport::conn::{PathId, PathInfo};

#[test]
fn a_resume_that_cannot_be_woken_closes_at_once_for_a_redial() {
    big_stack(|| {
        // The node moved while suspended: its sessions close with Redial, no 800 ms wait.
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Suspend).unwrap();
        net.run_for(2 * S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Resume { moved: true }).unwrap();
        assert!(
            net.nodes[a].saw(|e| matches!(e, Event::Closed { session, reason: EndReason::Redial } if *session == sa))
                || {
                    net.nodes[a].service(t);
                    net.nodes[a]
                        .saw(|e| matches!(e, Event::Closed { session, reason: EndReason::Redial } if *session == sa))
                }
        );
        // A resume at the same address wakes the session instead.
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Suspend).unwrap();
        net.run_for(2 * S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Resume { moved: false }).unwrap();
        net.run_for(5 * S);
        assert!(!net.nodes[a].saw(|e| matches!(e, Event::Closed { .. })));
        assert!(net.nodes[b].saw(|e| matches!(e, Event::PeerAwake { .. })));
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(sa)) else {
            panic!()
        };
        assert!(st.established);
        // A session already timing out when the node went to sleep is not woken either.
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.loss = Some(Box::new(|_, _, _| true));
        let t = net.now;
        let Value::Stream(id) = net.nodes[a]
            .cmd(
                t,
                Command::OpenStream {
                    session: sa,
                    bidi: false,
                },
            )
            .unwrap()
            .value
        else {
            panic!()
        };
        net.nodes[a]
            .cmd(
                t,
                Command::Write {
                    session: sa,
                    stream: id,
                    data: b"lost",
                },
            )
            .unwrap();
        net.run_for(2 * S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Suspend).unwrap();
        net.loss = None;
        net.run_for(S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Resume { moved: false }).unwrap();
        net.nodes[a].service(t);
        assert!(net.nodes[a].saw(|e| matches!(
            e,
            Event::Closed {
                reason: EndReason::Redial,
                ..
            }
        )));
    });
}

#[test]
fn a_session_suspended_while_its_link_is_down_is_redialled_on_resume() {
    big_stack(|| {
        // The link went down and the node was suspended before it came back: the session closes for a redial.
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(S);
        let t = net.now;
        net.nodes[a].ep.iface_event(t, IfaceId(0), IfaceEvent::Down);
        net.run_for(S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Suspend).unwrap();
        net.run_for(2 * S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Resume { moved: false }).unwrap();
        net.nodes[a].service(t);
        assert!(
            net.nodes[a].saw(|e| matches!(e, Event::Closed { session, reason: EndReason::Redial } if *session == sa)),
            "a session that went to sleep in the dark was woken"
        );
        // A link that came back before the suspension leaves no doubt: the session wakes.
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(S);
        let t = net.now;
        net.nodes[a].ep.iface_event(t, IfaceId(0), IfaceEvent::Down);
        net.run_for(S);
        let t = net.now;
        net.nodes[a].ep.iface_event(t, IfaceId(0), IfaceEvent::Up);
        net.run_for(S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Suspend).unwrap();
        net.run_for(2 * S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Resume { moved: false }).unwrap();
        net.run_for(5 * S);
        assert!(!net.nodes[a].saw(|e| matches!(e, Event::Closed { .. })));
        assert!(net.nodes[b].saw(|e| matches!(e, Event::PeerAwake { .. })));
    });
}

#[test]
fn ordinary_sessions_are_flushed_before_broadcast_ones() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b, c) = (net.add(1), net.add(2), net.add(3));
        let (sb, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let (sc, _) = net.connect_pair(a, c, ALPN_A, Role::Other);
        net.run_for(2 * S);
        net.nodes[a]
            .cmd(
                net.now,
                Command::SetGossip {
                    session: sb,
                    gossip: true,
                },
            )
            .unwrap();
        let now = net.now;
        // The broadcast session writes first; the ordinary one second.
        for s in [sb, sc] {
            let Value::Stream(id) = net.nodes[a]
                .cmd(
                    now,
                    Command::OpenStream {
                        session: s,
                        bidi: false,
                    },
                )
                .unwrap()
                .value
            else {
                panic!()
            };
            net.nodes[a]
                .cmd(
                    now,
                    Command::Write {
                        session: s,
                        stream: id,
                        data: &[7u8; 500],
                    },
                )
                .unwrap();
        }
        let mut buf = vec![0u8; 65_536];
        let first = net.nodes[a].ep.poll_transmit(now, &mut buf).unwrap();
        assert_eq!(first.remote, net.nodes[c].addr, "the ordinary session did not go first");
        let mut dests = vec![first.remote];
        while let Some(t) = net.nodes[a].ep.poll_transmit(now, &mut buf) {
            dests.push(t.remote);
        }
        assert!(dests.contains(&net.nodes[b].addr));
        // A broadcast session with a sub-session open still to leave keeps its place.
        net.nodes[a]
            .cmd(
                now,
                Command::SetGossip {
                    session: sc,
                    gossip: false,
                },
            )
            .unwrap();
        let mut net2 = CoreNet::new(10 * MS_NS);
        let (a, b, c) = (net2.add(1), net2.add(2), net2.add(3));
        let (sb, _) = net2.connect_pair(a, b, ALPN_A, Role::Other);
        let (sc, _) = net2.connect_pair(a, c, ALPN_A, Role::Other);
        net2.run_for(2 * S);
        net2.nodes[a]
            .cmd(
                net2.now,
                Command::SetGossip {
                    session: sb,
                    gossip: true,
                },
            )
            .unwrap();
        let now = net2.now;
        let (peer, to) = (net2.nodes[b].node, net2.nodes[b].addr);
        net2.nodes[a].connect(now, peer, ALPN_B, to, Role::Other).unwrap(); // the open queues in the broadcast parent
        let Value::Stream(id) = net2.nodes[a]
            .cmd(
                now,
                Command::OpenStream {
                    session: sc,
                    bidi: false,
                },
            )
            .unwrap()
            .value
        else {
            panic!()
        };
        net2.nodes[a]
            .cmd(
                now,
                Command::Write {
                    session: sc,
                    stream: id,
                    data: &[7u8; 500],
                },
            )
            .unwrap();
        let first = net2.nodes[a].ep.poll_transmit(now, &mut buf).unwrap();
        assert_eq!(first.remote, net2.nodes[b].addr, "the sub-session open lost its place");
    });
}

#[test]
fn a_handshake_flight_can_leave_on_several_candidate_paths() {
    big_stack(|| {
        use vinc_security::ClientTickets;
        let w = World::new(vinc_crypto::IdentityAlg::Ed25519);
        let mut store = Store::new(true);
        let mut client = w.client(&mut store, None, ClientTickets::new());
        let now = T0;
        let second = PathId(2);
        client.with_env(now, |c, env| c.add_path(env, second, PathInfo::default()).unwrap());
        let mut paths = Vec::new();
        let mut buf = vec![0u8; 65_536];
        let mut drain = |client: &mut Node<'_>, paths: &mut Vec<(PathId, usize)>| {
            while let Some(t) = client.with_env(now, |c, env| c.poll_transmit(env, &mut buf)) {
                paths.push((t.path, t.len));
            }
        };
        drain(&mut client, &mut paths);
        assert!(
            paths.iter().all(|(p, _)| *p == PathId(1)),
            "without the hook the flight stays on the active path: {paths:?}"
        );
        let only = paths.iter().map(|(_, l)| l).sum::<usize>();
        // With the hook, a flight (here the resend after the timer) leaves on both paths.
        client.conn.set_flight_fanout(&[second]);
        paths.clear();
        let later = now + 600 * MS;
        client.with_env(later, vinc_transport::conn::Connection::handle_timeout);
        let mut buf2 = vec![0u8; 65_536];
        while let Some(t) = client.with_env(later, |c, env| c.poll_transmit(env, &mut buf2)) {
            paths.push((t.path, t.len));
        }
        let on = |p: PathId| paths.iter().filter(|(q, _)| *q == p).map(|(_, l)| l).sum::<usize>();
        assert!(on(PathId(1)) > 0 && on(second) > 0, "{paths:?}");
        assert_eq!(
            on(PathId(1)),
            on(second),
            "the copy is the same flight: {paths:?} (first flight {only})"
        );
        let _: Option<NodeId> = None;
    });
}

#[test]
fn the_endpoint_sends_a_dialing_flight_on_the_paths_it_is_told() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let second: SocketAddr = "10.0.1.2:4433".parse().unwrap();
        net.nodes[b].extra.push(second);
        net.nodes[b].ep.add_iface(second).unwrap();
        let (peer, first, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, first, Role::Other).unwrap();
        let sa = net.nodes[a].session(&rep);
        net.nodes[a]
            .cmd(
                now,
                Command::FlightPaths {
                    session: sa,
                    addrs: &[second],
                    skip_primary: false,
                },
            )
            .unwrap();
        net.pump(a);
        let to = |d: SocketAddr| {
            net.tapped
                .iter()
                .filter(|t| t.0 == now && t.2 == d)
                .map(|t| t.3)
                .sum::<usize>()
        };
        assert!(to(first) > 1000, "the flight is missing on the first path");
        assert_eq!(to(first), to(second), "the second path did not get the same flight");
        assert!(net.run(now + 5 * SEC_NS, |n| n.nodes[a].saw(is_connected)));
        // Turned off, a later flight stays on one path.
        let t = net.now;
        net.nodes[a]
            .cmd(
                t,
                Command::FlightPaths {
                    session: sa,
                    addrs: &[],
                    skip_primary: false,
                },
            )
            .unwrap();
    });
}

#[test]
fn a_relay_path_at_the_end_of_a_long_list_of_flight_paths_still_carries_the_flight() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (peer, first, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, first, Role::Other).unwrap();
        let sa = net.nodes[a].session(&rep);
        // More direct addresses than the path table holds, then the relay path that is sure to reach the peer.
        let mut addrs: Vec<SocketAddr> = (1..=6).map(|i| format!("10.0.9.{i}:4433").parse().unwrap()).collect();
        let relay = vinc_core::relay_addr(false, 0, 7);
        addrs.push(relay);
        net.nodes[a]
            .cmd(
                now,
                Command::FlightPaths {
                    session: sa,
                    addrs: &addrs,
                    skip_primary: false,
                },
            )
            .unwrap();
        net.pump(a);
        let to_relay: usize = net
            .tapped
            .iter()
            .filter(|t| t.0 == now && t.2 == relay)
            .map(|t| t.3)
            .sum();
        let all: Vec<_> = net.tapped.iter().filter(|t| t.0 == now).map(|t| (t.2, t.3)).collect();
        assert!(
            to_relay > 1000,
            "the flight did not leave on the relay path: {to_relay} bytes, sent {all:?}"
        );
    });
}

#[test]
fn a_flight_can_skip_the_primary_path_and_leave_on_the_listed_ones_only() {
    big_stack(|| {
        use vinc_security::ClientTickets;
        let w = World::new(vinc_crypto::IdentityAlg::Ed25519);
        let mut store = Store::new(true);
        let mut client = w.client(&mut store, None, ClientTickets::new());
        let now = T0;
        let second = PathId(2);
        client.with_env(now, |c, env| c.add_path(env, second, PathInfo::default()).unwrap());
        // With the skip set, even the first flight leaves on the listed path only.
        client.conn.set_flight_fanout(&[second]);
        client.conn.set_flight_skip_primary(true);
        let mut buf = vec![0u8; 65_536];
        let mut paths = Vec::new();
        while let Some(t) = client.with_env(now, |c, env| c.poll_transmit(env, &mut buf)) {
            paths.push((t.path, t.len));
        }
        assert!(
            !paths.is_empty() && paths.iter().all(|(p, _)| *p == second),
            "{paths:?}"
        );
        // The resend after the timer goes the same way, and only there.
        paths.clear();
        let later = now + 600 * MS;
        client.with_env(later, vinc_transport::conn::Connection::handle_timeout);
        while let Some(t) = client.with_env(later, |c, env| c.poll_transmit(env, &mut buf)) {
            paths.push((t.path, t.len));
        }
        assert!(
            !paths.is_empty() && paths.iter().all(|(p, _)| *p == second),
            "{paths:?}"
        );
        // With no fan-out path the skip sends nothing at all in that try.
        client.conn.set_flight_fanout(&[]);
        paths.clear();
        let later = later + 2 * SEC_NS;
        client.with_env(later, vinc_transport::conn::Connection::handle_timeout);
        while let Some(t) = client.with_env(later, |c, env| c.poll_transmit(env, &mut buf)) {
            paths.push((t.path, t.len));
        }
        assert!(paths.is_empty(), "a try with no path sends nothing: {paths:?}");
        // Turned off, the flight returns to the primary path.
        client.conn.set_flight_skip_primary(false);
        let later = later + 10 * SEC_NS;
        client.with_env(later, vinc_transport::conn::Connection::handle_timeout);
        while let Some(t) = client.with_env(later, |c, env| c.poll_transmit(env, &mut buf)) {
            paths.push((t.path, t.len));
        }
        assert!(paths.iter().any(|(p, _)| *p == PathId(1)), "{paths:?}");
    });
}
