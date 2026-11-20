//! Sub-sessions: a second protocol to a connected peer opens with no round trip and early data, needs no age on its
//! parent, survives a lost open, is gated with its parent, and an unheard child dies with its parent.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation
)]

use std::cell::Cell;
use std::rc::Rc;

use pinc_core::{Answer, Command, EndReason, Event, Query, Role};
use pinc_tests::*;

#[test]
fn a_second_protocol_connects_at_once_and_its_data_arrives_one_way_later() {
    big_stack(|| {
        let delay = 10 * MS_NS;
        let mut net = CoreNet::new(delay);
        net.capture = true;
        let (a, b, c) = (net.add(1), net.add(2), net.add(3));
        let (parent_a, parent_b) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);

        let t0 = net.now;
        let marker = net.captured.len();
        let (child_a, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(rep.events.any(is_connected), "Connected is not immediate");
        assert_ne!(child_a, parent_a);
        write_new(&mut net, a, child_a, b"second-protocol");
        let incoming0 = net.nodes[b].count(|e| matches!(e, Event::Incoming { .. }));
        assert!(net.run(t0 + 5 * SEC_NS, |n| {
            n.nodes[b].read.values().any(|v| v == b"second-protocol")
        }));
        let readable = net.nodes[b]
            .time_of(|e| matches!(e, Event::StreamReadable { session, .. } if *session != parent_b))
            .unwrap();
        assert!(
            readable - t0 <= delay + MS_NS,
            "first byte after {} ns: more than one way",
            readable - t0
        );
        assert_eq!(
            net.nodes[b].count(|e| matches!(e, Event::Incoming { .. })),
            incoming0 + 1
        );
        let child_b = net.nodes[b]
            .events
            .iter()
            .rev()
            .find_map(|(_, e)| {
                if let Event::Incoming { session, alpn, .. } = e {
                    (alpn.as_bytes() == ALPN_B).then_some(*session)
                } else {
                    None
                }
            })
            .unwrap();
        assert_eq!(
            net.nodes[b]
                .read
                .iter()
                .find(|(k, _)| k.0 == child_b)
                .map(|(_, v)| v.as_slice()),
            Some(&b"second-protocol"[..])
        );
        // No handshake message left either way: every datagram since the dial is a short-header packet.
        assert!(
            net.captured[marker..].iter().all(|(_, _, d)| d[0] & 0x80 == 0),
            "a handshake datagram was sent for a sub-session"
        );
        // For contrast: a first dial to a stranger needs the handshake before its data can leave.
        let t1 = net.now;
        let (peer_c, to_c) = (net.nodes[c].node, net.nodes[c].addr);
        let rep = net.nodes[a].connect(t1, peer_c, ALPN_A, to_c, Role::Other).unwrap();
        let sc = net.nodes[a].session(&rep);
        assert!(net.run(t1 + 5 * SEC_NS, |n| n.nodes[a].count(is_connected) >= 3));
        let t2 = net.now;
        write_new(&mut net, a, sc, b"late");
        assert!(net.run(t2 + 5 * SEC_NS, |n| n.nodes[c].fin.len() == 1));
        assert!(
            net.now - t1 >= 3 * delay,
            "a handshake dial took only {} ns",
            net.now - t1
        );
        // The child has its own session state.
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(child_a)) else {
            panic!()
        };
        assert!(st.established && st.allowed && st.alpn.map(|x| x.as_bytes().to_vec()) == Some(ALPN_B.to_vec()));
    });
}

/// A parent heard from within twenty seconds carries a dial with no round trip; a silent one does not: the dial
/// probes it first (the ride and the lapse are covered by the probe tests above and below).
#[test]
fn a_parent_heard_within_twenty_seconds_carries_a_dial_and_a_silent_one_probes_first() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let marker = net.captured.len();
        let (_, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(
            !rep.events.any(is_connected),
            "the dial connected before its probe resolved"
        );
        net.run_for(SEC_NS);
        assert!(
            !handshake_since(&net, marker),
            "a handshake was sent while the dial's probe still ran"
        );
        // A parent heard from a moment ago carries the next dial.
        net.run_for(SEC_NS);
        let marker = net.captured.len();
        let (child, rep) = dial(&mut net, a, b, ALPN_A);
        assert!(rep.events.any(is_connected));
        write_new(&mut net, a, child, b"old-parent");
        assert!(net.run(net.now + 5 * SEC_NS, |n| {
            n.nodes[b].read.values().any(|v| v == b"old-parent")
        }));
        assert!(
            !handshake_since(&net, marker),
            "a handshake datagram was sent for a sub-session"
        );
    });
}

#[test]
fn a_carrier_ping_sent_does_not_count_as_hearing_the_parent_but_a_pong_does() {
    big_stack(|| {
        // A carrier ping the node sent is not the peer answering: the dial does not ride at once, it probes the
        // parent first. (The window is two of the session's probe timeouts now, so the lapse it guards against
        // comes fast; what the rule guards is the ride, and that waits for an answer.)
        let (mut net, a, b) = silent_parent();
        let parent = net.nodes[a].ep.sessions().next().unwrap();
        let t = net.now;
        net.nodes[a]
            .cmd(
                t,
                Command::Pulse {
                    session: parent,
                    sent: true,
                },
            )
            .unwrap();
        let (_, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(
            !rep.events.any(is_connected),
            "a ping that went out made the parent look heard"
        );
        // A pong that came back is the peer alive: the dial rides the parent at once, with no probe and no
        // handshake.
        let (mut net, a, b) = silent_parent();
        let parent = net.nodes[a].ep.sessions().next().unwrap();
        let t = net.now;
        net.nodes[a]
            .cmd(
                t,
                Command::Pulse {
                    session: parent,
                    sent: false,
                },
            )
            .unwrap();
        let marker = net.captured.len();
        let (child, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(
            rep.events.any(is_connected),
            "a heard parent did not carry the dial at once"
        );
        net.run_for(SEC_NS);
        assert!(
            !handshake_since(&net, marker),
            "a pong that came back did not make the parent heard"
        );
        assert!(net.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == child)));
    });
}

#[test]
fn two_children_of_one_protocol_stay_apart_and_a_lost_open_is_repeated() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        // The first two datagrams after the dials are lost: the open and the early data of the first child.
        let dropped = Rc::new(Cell::new(0u32));
        let d = dropped.clone();
        let from = net.nodes[a].addr;
        net.loss = Some(Box::new(move |f, _, _| {
            if f == from && d.get() < 2 {
                d.set(d.get() + 1);
                true
            } else {
                false
            }
        }));
        let (c1, _) = dial(&mut net, a, b, ALPN_B);
        let (c2, _) = dial(&mut net, a, b, ALPN_B);
        assert_ne!(c1, c2);
        write_new(&mut net, a, c1, b"one");
        write_new(&mut net, a, c2, b"two");
        assert!(net.run(net.now + 20 * SEC_NS, |n| {
            n.nodes[b].read.values().any(|v| v == b"one") && n.nodes[b].read.values().any(|v| v == b"two")
        }));
        assert!(dropped.get() >= 2);
        // Each open produced exactly one session at the peer, however often the frame was repeated.
        let incoming_b = net.nodes[b]
            .events
            .iter()
            .filter(|(_, e)| matches!(e, Event::Incoming { alpn, .. } if alpn.as_bytes() == ALPN_B))
            .count();
        assert_eq!(incoming_b, 2);
        let by_session: std::collections::HashMap<_, _> =
            net.nodes[b].read.iter().map(|(k, v)| (k.0, v.clone())).collect();
        assert_eq!(
            by_session.len(),
            2,
            "the two children are separate sessions: {by_session:?}"
        );
    });
}

#[test]
fn a_protocol_the_peer_does_not_serve_opens_nothing_there() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        net.nodes[b].ep.unregister_alpn(ALPN_B);
        net.connect_pair(a, b, ALPN_A, Role::Other);
        let (child, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(rep.events.any(is_connected));
        write_new(&mut net, a, child, b"unserved");
        net.run_for(3 * SEC_NS);
        assert_eq!(
            net.nodes[b].ep.sessions().count(),
            1,
            "the peer opened a session for a protocol it does not serve"
        );
        assert!(net.nodes[b].read.values().all(|v| v != b"unserved"));
    });
}

#[test]
fn an_unheard_child_closes_with_its_parent_and_a_heard_one_stays() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (parent_a, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        // A heard child first: it exchanges data with the peer.
        let (heard, _) = dial(&mut net, a, b, ALPN_A);
        write_new(&mut net, a, heard, b"hello");
        let now = net.now;
        let nb = net.nodes[b].ep.sessions().count();
        assert!(net.run(now + 5 * SEC_NS, |n| n.nodes[b].ep.sessions().count() == nb + 1
            && n.nodes[b].read.len() == 1));
        // The reply makes the child hear the peer: the peer writes back on the child's session.
        let child_b = net.nodes[b].ep.sessions().last().unwrap();
        write_new(&mut net, b, child_b, b"reply");
        assert!(net.run(net.now + 5 * SEC_NS, |n| {
            n.nodes[a].read.values().any(|v| v == b"reply")
        }));
        // Then everything the node sends is lost, and a second child is opened over the same parent: it is never heard.
        net.loss = Some(Box::new(|_, _, _| true));
        let from = net.nodes[a].addr;
        net.loss = Some(Box::new(move |f, _, _| f == from));
        let (unheard, _) = dial(&mut net, a, b, ALPN_B);
        write_new(&mut net, a, unheard, b"never");
        net.run_for(100 * MS_NS);
        net.loss = None;
        // The parent closes: the child that never heard its peer is orphaned; the one that did stays.
        let t = net.now;
        net.nodes[a]
            .cmd(
                t,
                Command::Close {
                    session: parent_a,
                    error: 0,
                },
            )
            .unwrap();
        net.run_for(SEC_NS);
        assert!(
            net.nodes[a]
                .saw(|e| matches!(e, Event::Closed { session, reason: EndReason::Orphaned } if *session == unheard)),
            "{:?}",
            net.nodes[a].events
        );
        assert!(!net.nodes[a].saw(|e| matches!(e, Event::Closed { session, .. } if *session == heard)));
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(heard)) else {
            panic!("the heard child is gone")
        };
        assert!(st.established);
    });
}

#[test]
fn a_child_waits_with_its_parent_for_the_access_check() {
    big_stack(|| {
        let mut net = CoreNet::new(15 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        net.nodes[b].acp = Acp::Manual;
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        assert!(net.run(now + 5 * SEC_NS, |n| !n.nodes[b].checks.is_empty()
            && n.nodes[a].saw(is_connected)));
        let (child, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(
            rep.events.any(is_connected),
            "the dialer's parent is allowed, so its child is"
        );
        write_new(&mut net, a, child, b"gated");
        net.run_for(SEC_NS);
        assert_eq!(net.nodes[b].ep.sessions().count(), 2);
        assert!(!net.nodes[b].saw(|e| matches!(e, Event::Incoming { .. } | Event::StreamReadable { .. })));
        let (check, _) = net.nodes[b].checks[0];
        let t = net.now;
        net.nodes[b].cmd(t, Command::AcpAnswer { check, allow: true }).unwrap();
        net.run_for(SEC_NS);
        let incoming: Vec<_> = net.nodes[b]
            .events
            .iter()
            .filter_map(|(_, e)| {
                if let Event::Incoming { alpn, .. } = e {
                    Some(alpn.as_bytes().to_vec())
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(
            incoming,
            [ALPN_A.to_vec(), ALPN_B.to_vec()],
            "the parent is announced first"
        );
        assert!(net.nodes[b].read.values().any(|v| v == b"gated"));
    });
}

#[test]
fn a_dial_within_twenty_seconds_of_hearing_a_peer_that_restarted_rides_the_dead_session() {
    big_stack(|| {
        let (mut net, a, b, heard) = restarted_peer();
        net.run_for((heard + 19 * SEC_NS).saturating_sub(net.now));
        let marker = net.captured.len();
        let (_, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(rep.events.any(is_connected));
        net.run_for(SEC_NS);
        assert!(
            !handshake_since(&net, marker),
            "a handshake started while the parent was recent"
        );
        assert!(
            !net.nodes[b].saw(|e| matches!(e, Event::Incoming { .. })),
            "the restarted peer heard the dial"
        );
    });
}

/// A dial to a peer that restarted and stayed silent past twenty seconds probes the dead session first; the peer
/// never answers, so the probe lapses into the dial's own handshake and the data flows on it.
#[test]
fn a_dial_after_twenty_seconds_without_hearing_a_peer_that_restarted_makes_a_handshake_and_connects() {
    big_stack(|| {
        let (mut net, a, b, heard) = restarted_peer();
        net.run_for((heard + 21 * SEC_NS).saturating_sub(net.now));
        assert_eq!(net.nodes[a].ep.sessions().count(), 1, "the dead session closed early");
        let marker = net.captured.len();
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        net.run_for(3 * SEC_NS);
        assert!(
            handshake_since(&net, marker),
            "no handshake started for a silent parent"
        );
        write_new(&mut net, a, child, b"restarted");
        assert!(net.run(net.now + 5 * SEC_NS, |n| {
            n.nodes[b].read.values().any(|v| v == b"restarted")
        }));
    });
}

// The two optimistic dials below started from `silent_parent` until the quiet-parent probe (#693): a dial to a quiet
// parent now probes it first. They start from a closed parent, so they still test the optimistic handshake itself;
// the probe's lapse into one is tested in `core_sub_probe`.
#[test]
fn an_optimistic_handshake_dial_opens_a_stream_and_writes_before_the_handshake_ends() {
    big_stack(|| {
        let (mut net, a, b) = closed_parent();
        let t0 = net.now;
        let (child, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(rep.events.any(is_connected));
        // No time has passed: the stream opens and takes its bytes now, they leave with the handshake's last flight.
        write_new(&mut net, a, child, b"early");
        assert!(net.run(t0 + 5 * SEC_NS, |n| n.nodes[b].read.values().any(|v| v == b"early")));
        assert!(
            net.now - t0 <= 3 * 10 * MS_NS + 5 * MS_NS,
            "the bytes took {} ns",
            net.now - t0
        );
    });
}

#[test]
fn an_optimistic_dial_that_is_never_answered_ends_with_its_early_stream_and_is_told_once() {
    big_stack(|| {
        let (mut net, a, b) = closed_parent();
        let addr_b = net.nodes[b].addr;
        net.loss = Some(Box::new(move |_, to, _| to == addr_b));
        let (child, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(rep.events.any(is_connected));
        write_new(&mut net, a, child, b"never");
        let end = net.now + 60 * SEC_NS;
        assert!(net.run(end, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Closed { session, .. } if *session == child))
        }));
        net.run_for(SEC_NS);
        assert_eq!(
            net.nodes[a].count(|e| matches!(e, Event::Closed { session, .. } if *session == child)),
            1
        );
        assert!(!net.nodes[b].read.values().any(|v| v == b"never"));
    });
}

/// Two nodes where `b` dialed `a` for `ALPN_A` and `a` still holds the access check for `b` open.
fn incoming_not_allowed() -> (CoreNet, usize, usize) {
    let mut net = CoreNet::new(15 * MS_NS);
    net.capture = true;
    let (a, b) = (net.add(1), net.add(2));
    net.nodes[a].acp = Acp::Manual;
    let (peer, to, now) = (net.nodes[a].node, net.nodes[a].addr, net.now);
    net.nodes[b].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
    assert!(net.run(now + 5 * SEC_NS, |n| !n.nodes[a].checks.is_empty()
        && n.nodes[b].saw(is_connected)));
    net.run_for(SEC_NS);
    (net, a, b)
}

#[test]
fn a_third_protocol_rides_the_root_session_and_does_not_wait_on_a_sub_session() {
    big_stack(|| {
        const ALPN_C: &[u8] = b"pinc/c";
        let mut net = CoreNet::new(10 * MS_NS);
        net.capture = true;
        let (a, b) = (net.add(1), net.add(2));
        assert!(net.nodes[a].ep.register_alpn(ALPN_C) && net.nodes[b].ep.register_alpn(ALPN_C));
        net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        let (second, _) = dial(&mut net, a, b, ALPN_B);
        write_new(&mut net, a, second, b"second");
        assert!(net.run(net.now + 5 * SEC_NS, |n| {
            n.nodes[b].read.values().any(|v| v == b"second")
        }));
        let marker = net.captured.len();
        let (third, rep) = dial(&mut net, a, b, ALPN_C);
        assert!(rep.events.any(is_connected));
        write_new(&mut net, a, third, b"third");
        assert!(
            net.run(net.now + 5 * SEC_NS, |n| n.nodes[b]
                .read
                .values()
                .any(|v| v == b"third")),
            "the third protocol never got its data through"
        );
        assert!(
            !handshake_since(&net, marker),
            "the third protocol made its own handshake"
        );
    });
}

#[test]
fn a_dial_waits_on_a_session_the_peer_opened_that_is_not_allowed_yet() {
    big_stack(|| {
        let (mut net, a, b) = incoming_not_allowed();
        let marker = net.captured.len();
        let (child, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(rep.events.any(is_connected), "the dial did not connect at once");
        write_new(&mut net, a, child, b"waited");
        net.run_for(SEC_NS);
        assert!(!handshake_since(&net, marker), "the dial made its own handshake");
        let incoming_b =
            |n: &CoreNet| n.nodes[b].saw(|e| matches!(e, Event::Incoming { alpn, .. } if alpn.as_bytes() == ALPN_B));
        assert!(!incoming_b(&net), "the open left before the parent was allowed");
        let (check, _) = net.nodes[a].checks[0];
        let t = net.now;
        net.nodes[a].cmd(t, Command::AcpAnswer { check, allow: true }).unwrap();
        assert!(net.run(net.now + 5 * SEC_NS, |n| {
            n.nodes[b].read.values().any(|v| v == b"waited")
        }));
        assert!(incoming_b(&net));
    });
}

#[test]
fn a_second_protocol_dialed_during_the_handshake_connects_at_once_and_opens_with_its_parent() {
    big_stack(|| {
        let delay = 10 * MS_NS;
        let mut net = CoreNet::new(delay);
        let (a, b) = (net.add(1), net.add(2));
        let t0 = net.now;
        let (parent_a, _) = dial(&mut net, a, b, ALPN_A);
        // The handshake has not run a single round trip: the second protocol still reports at once and takes writes.
        let (child_a, _) = dial(&mut net, a, b, ALPN_B);
        assert_ne!(child_a, parent_a);
        let connected: Vec<_> = net.nodes[a]
            .events
            .iter()
            .filter(|(_, e)| matches!(e, Event::Connected { session, .. } if *session == child_a))
            .map(|(t, _)| *t)
            .collect();
        assert!(connected.len() <= 1);
        net.pump_all();
        write_new(&mut net, a, child_a, b"early");
        let end = net.now + 5 * SEC_NS;
        assert!(net.run(end, |n| n.nodes[b].fin.len() == 1));
        // Connected came with the dial, not a handshake later.
        let at = net.nodes[a]
            .time_of(|e| matches!(e, Event::Connected { session, .. } if *session == child_a))
            .unwrap();
        assert!(at <= t0 + delay, "Connected after {} ns", at - t0);
        // Both sessions are open at the peer, for their own protocols.
        let alpns: Vec<_> = net.nodes[b]
            .events
            .iter()
            .filter_map(|(_, e)| {
                if let Event::Incoming { alpn, .. } = e {
                    Some(alpn.as_bytes().to_vec())
                } else {
                    None
                }
            })
            .collect();
        assert!(
            alpns.contains(&ALPN_A.to_vec()) && alpns.contains(&ALPN_B.to_vec()),
            "{alpns:?}"
        );
        assert_eq!(net.nodes[b].read.values().next().unwrap(), b"early");
    });
}

#[test]
fn a_dial_that_waited_for_a_parent_that_fails_is_closed_for_a_redial() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        // The peer drops everything it is sent: the handshake never completes.
        let addr_b = net.nodes[b].addr;
        net.loss = Some(Box::new(move |_, to, _| to == addr_b));
        let (_parent, _) = dial(&mut net, a, b, ALPN_A);
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        assert!(net.nodes[a].saw(is_connected));
        let end = net.now + 60 * SEC_NS;
        assert!(net.run(end, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Closed { session, .. } if *session == child))
        }));
        assert!(net.nodes[a].saw(|e| matches!(
            e,
            Event::Closed { session, reason: EndReason::Orphaned } if *session == child
        )));
    });
}

#[test]
fn a_second_protocol_opened_after_the_peer_moved_behind_its_nat_gets_its_answer() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let inside = net.nodes[a].addr;
        let outside: std::net::SocketAddr = ([10, 9, 0, 1], 5000).into();
        net.nat = Some((inside, outside));
        // The first session is made behind the NAT, as seen from the outside address.
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        let parent_a = net.nodes[a].session(&rep);
        let ok = net.run(now + 5 * SEC_NS, |n| {
            n.nodes[a].saw(is_connected) && n.nodes[b].saw(|e| matches!(e, Event::Incoming { .. }))
        });
        assert!(ok);
        net.run_for(2 * SEC_NS);
        // The mapping changes while the node idles: the old outside address stops working, a new one appears.
        let moved: std::net::SocketAddr = ([10, 9, 0, 1], 5001).into();
        net.nat = Some((inside, moved));
        // A second protocol: its open, its data and the answer must all get through.
        let (child_a, _) = dial(&mut net, a, b, ALPN_B);
        assert_ne!(child_a, parent_a);
        write_new(&mut net, a, child_a, b"ask");
        let end = net.now + SEC_NS;
        assert!(net.run(end, |n| n.nodes[b].fin.len() == 1), "the request never arrived");
        let sb = net.nodes[b]
            .events
            .iter()
            .rev()
            .find_map(|(_, e)| {
                if let Event::Incoming { session, alpn, .. } = e {
                    (alpn.as_bytes() == ALPN_B).then_some(*session)
                } else {
                    None
                }
            })
            .unwrap();
        write_new(&mut net, b, sb, b"answer");
        let end = net.now + 10 * SEC_NS;
        assert!(
            net.run(end, |n| n.nodes[a].fin.len() == 1),
            "the answer never came back"
        );
    });
}

#[test]
fn a_big_answer_reaches_a_peer_that_moved_even_when_the_first_path_check_is_lost() {
    use std::cell::Cell;
    use std::rc::Rc;

    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let inside = net.nodes[a].addr;
        let outside: std::net::SocketAddr = ([10, 9, 0, 1], 5000).into();
        net.nat = Some((inside, outside));
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        let parent_a = net.nodes[a].session(&rep);
        assert!(net.run(now + 5 * SEC_NS, |n| {
            n.nodes[a].saw(is_connected) && n.nodes[b].saw(|e| matches!(e, Event::Incoming { .. }))
        }));
        net.run_for(2 * SEC_NS);
        // The mapping changes. The two datagrams that follow get through (the request); the next three, which hold
        // the answer to the path check, are lost.
        let moved: std::net::SocketAddr = ([10, 9, 0, 1], 5001).into();
        net.nat = Some((inside, moved));
        let seen = Rc::new(Cell::new(0u32));
        let counter = Rc::clone(&seen);
        net.loss = Some(Box::new(move |from, _, _| {
            if from != inside {
                return false;
            }
            counter.set(counter.get() + 1);
            (3..=5).contains(&counter.get())
        }));
        write_new(&mut net, a, parent_a, b"ask");
        let end = net.now + 2 * SEC_NS;
        assert!(net.run(end, |n| n.nodes[b].fin.len() == 1), "the request never arrived");
        let sb = net.nodes[b]
            .events
            .iter()
            .find_map(|(_, e)| {
                if let Event::Incoming { session, .. } = e {
                    Some(*session)
                } else {
                    None
                }
            })
            .unwrap();
        write_new(&mut net, b, sb, &pattern(40_000, 3));
        let end = net.now + 3 * SEC_NS;
        assert!(
            net.run(end, |n| n.nodes[a].read.values().map(Vec::len).sum::<usize>() == 40_000),
            "the answer did not arrive within 3 s"
        );
    });
}

#[test]
fn a_child_that_waited_for_its_parent_runs_on_the_path_the_parent_settled_on() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        // The peer's first address drops everything; its second one works. The dial's flight goes to both and the
        // answer comes back on the second, where the parent session continues.
        let second: std::net::SocketAddr = "10.0.1.2:4433".parse().unwrap();
        net.nodes[b].extra.push(second);
        net.nodes[b].ep.add_iface(second).unwrap();
        let first = net.nodes[b].addr;
        net.loss = Some(Box::new(move |_, to, _| to == first));
        let (peer, now) = (net.nodes[b].node, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, first, Role::Other).unwrap();
        let parent = net.nodes[a].session(&rep);
        net.nodes[a]
            .cmd(
                now,
                Command::FlightPaths {
                    session: parent,
                    addrs: &[second],
                    skip_primary: false,
                },
            )
            .unwrap();
        // A second protocol dialed before any answer: it waits for the parent, on the path the parent dialed first.
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        assert_ne!(child, parent);
        assert!(net.run(now + 5 * SEC_NS, |n| {
            n.nodes[b].saw(|e| matches!(e, Event::Incoming { .. }))
        }));
        write_new(&mut net, a, child, b"after the wait");
        let end = net.now + 5 * SEC_NS;
        assert!(
            net.run(end, |n| n.nodes[b].fin.len() == 1),
            "the child's bytes never left on the path its parent uses"
        );
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(child)) else {
            panic!()
        };
        assert_eq!(st.route.map(|(_, r)| r), Some(second), "{st:?}");
    });
}

/// A parent between `a` and `b`, a sub-session open from `a` that `b` refuses once, and a short window where the answers
/// from `b` are lost so `a` repeats the open. Returns how many sessions with `ALPN_B` `b` reports.
fn refused_open_repeated(refuse: impl FnOnce(&mut CoreNet, usize) -> Box<dyn FnOnce(&mut CoreNet)>) -> usize {
    let mut net = CoreNet::new(10 * MS_NS);
    let (a, b) = (net.add(1), net.add(2));
    net.connect_pair(a, b, ALPN_A, Role::Other);
    net.run_for(SEC_NS);
    let lift = refuse(&mut net, b);
    let silent = Rc::new(Cell::new(true));
    let s = silent.clone();
    let from = net.nodes[b].addr;
    net.loss = Some(Box::new(move |f, _, _| s.get() && f == from));
    let (child, _) = dial(&mut net, a, b, ALPN_B);
    write_new(&mut net, a, child, b"after-refusal");
    // The open is repeated at 75 ms, 225 ms and 525 ms after the dial; the answers are held back past the first.
    net.run_for(150 * MS_NS);
    assert_eq!(
        net.nodes[b].count(|e| matches!(e, Event::Incoming { alpn, .. } if alpn.as_bytes() == ALPN_B)),
        0,
        "the open was served while it should be refused"
    );
    lift(&mut net);
    silent.set(false);
    net.run(net.now + 30 * SEC_NS, |n| {
        n.nodes[b].read.values().any(|v| v == b"after-refusal")
    });
    net.nodes[b].count(|e| matches!(e, Event::Incoming { alpn, .. } if alpn.as_bytes() == ALPN_B))
}

#[test]
fn a_sub_open_refused_for_a_full_table_opens_when_repeated_after_a_slot_frees() {
    big_stack(|| {
        let opened = refused_open_repeated(|net, b| {
            let filler = net.fill_table(b);
            Box::new(move |net| {
                let now = net.now;
                net.nodes[b]
                    .cmd(
                        now,
                        Command::Close {
                            session: filler[0],
                            error: 0,
                        },
                    )
                    .unwrap();
                assert!(
                    net.run(now + 10 * SEC_NS, |n| n.nodes[b].ep.node_stats().sessions
                        < filler.len() + 1),
                    "the closed session kept its slot"
                );
            })
        });
        assert_eq!(opened, 1, "the repeat of an open refused for a full table was ignored");
    });
}

#[test]
fn a_sub_open_refused_for_an_unregistered_protocol_opens_when_repeated_after_it_is_served() {
    big_stack(|| {
        let opened = refused_open_repeated(|net, b| {
            net.nodes[b].ep.unregister_alpn(ALPN_B);
            Box::new(move |net| assert!(net.nodes[b].ep.register_alpn(ALPN_B)))
        });
        assert_eq!(opened, 1);
    });
}

#[test]
fn a_child_that_waited_for_its_parent_is_answered_by_its_peer_and_not_by_its_keys() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (parent, _) = dial(&mut net, a, b, ALPN_A);
        // The handshake still runs: the second protocol is reported at once and gets its keys when the parent is up.
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        let answered = |n: &CoreNet| {
            let Answer::Stats(st) = n.nodes[a].ep.query(Query::Stats(child)) else {
                panic!()
            };
            st.answered
        };
        assert!(!answered(&net));
        let end = net.now + 5 * SEC_NS;
        assert!(net.run(end, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == parent))
        }));
        // The child has its keys and its open has only just left: the peer has not answered it.
        assert!(!answered(&net), "a sub-session counts as answered by getting its keys");
        assert!(!net.nodes[a].saw(|e| matches!(e, Event::Answered { .. })));
        // The peer opens the child and acknowledges what it carries: that is its answer.
        write_new(&mut net, a, child, b"early");
        let end = net.now + 5 * SEC_NS;
        assert!(net.run(end, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Answered { session, .. } if *session == child))
        }));
        assert!(answered(&net));
        net.run_for(SEC_NS);
        assert_eq!(
            net.nodes[a].count(|e| matches!(e, Event::Answered { .. })),
            1,
            "told once, and only for the session reported before its peer answered"
        );
    });
}
