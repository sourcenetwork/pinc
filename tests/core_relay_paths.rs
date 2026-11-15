//! Sessions on relay and direct paths at the endpoint: a session whose relay path stops answering while the relay's
//! carrier still does is closed, the re-join challenges of a thin node's sessions to one address are spaced, a
//! datagram heard on a relay path does not count as UDP heard for the short Initial, an end on a relay path that is
//! challenged on a direct path validates it in the round trip of that challenge, and a relay path added to a session
//! is kept alive from the moment it is added (a child of the session keeps its parent's send times).
#![allow(clippy::unwrap_used, clippy::panic, clippy::indexing_slicing)]

#[path = "core_timing_common.rs"]
mod common;

use std::net::SocketAddr;

use common::{dial, flights};
use vinc_core::{Command, Event, PathState, Role, SessionId, Value, relay_addr};
use vinc_tests::*;

const MS: u64 = MS_NS;
/// The size of a datagram that carries only a path challenge.
const CHALLENGE_LEN: usize = 32;

/// Node 0 and node 1, node 1 also reachable through relay slot 3; returns the net, the direct and the relay address.
fn pair(delay: u64) -> (CoreNet, SocketAddr, SocketAddr) {
    let mut net = CoreNet::new(delay);
    let (_, b) = (net.add(1), net.add(2));
    let via = relay_addr(false, 3, 7);
    net.nodes[b].extra.push(via);
    let direct = net.nodes[b].addr;
    (net, direct, via)
}

/// Open a session for `alpn` and give it a validated relay path as well as its direct one.
fn session(net: &mut CoreNet, alpn: &[u8], via: SocketAddr) -> SessionId {
    let (sa, _) = net.connect_pair(0, 1, alpn, Role::Other);
    let t = net.now;
    net.nodes[0].cmd(t, Command::Punch { session: sa, addr: via }).unwrap();
    net.run_for(SEC_NS);
    sa
}

/// Write `data` on a new unidirectional stream of `s` and finish it.
fn send(net: &mut CoreNet, s: SessionId, data: &[u8]) {
    let t = net.now;
    let Value::Stream(id) = net.nodes[0]
        .cmd(
            t,
            Command::OpenStream {
                session: s,
                bidi: false,
            },
        )
        .unwrap()
        .value
    else {
        panic!("no stream")
    };
    net.nodes[0]
        .cmd(
            t,
            Command::Write {
                session: s,
                stream: id,
                data,
            },
        )
        .unwrap();
    net.nodes[0].cmd(t, Command::Finish { session: s, stream: id }).unwrap();
    net.pump(0);
}

/// Lose everything on the direct path and through the relay.
fn outage(net: &mut CoreNet, direct: SocketAddr, via: SocketAddr) {
    net.loss = Some(Box::new(move |f, to, _| {
        f == via || to == via || f == direct || to == direct
    }));
}

#[test]
fn the_sessions_of_a_thin_node_space_their_rejoin_challenges_to_one_address() {
    big_stack(|| {
        // One-way 150 ms: every session is thin, and each would challenge the abandoned path once a second.
        let (mut net, direct, via) = pair(150 * MS);
        let s1 = session(&mut net, b"vinc/a", via);
        let s2 = session(&mut net, b"vinc/b", via);
        outage(&mut net, direct, via);
        send(&mut net, s1, &pattern(2_000, 1));
        send(&mut net, s2, &pattern(2_000, 2));
        net.run_for(20 * SEC_NS);
        // Once both sessions abandoned the direct path, the small datagrams to its address are re-join challenges.
        let failed = |s: SessionId| {
            net.nodes[0]
                .events
                .iter()
                .find(
                    |(_, e)| matches!(e, Event::PathChanged { session, state: PathState::Failed, .. } if *session == s),
                )
                .map(|(t, _)| *t)
                .unwrap()
        };
        let from = failed(s1).max(failed(s2));
        let times: Vec<u64> = net
            .tapped
            .iter()
            .filter(|t| t.0 > from && t.2 == direct && t.3 == CHALLENGE_LEN)
            .map(|t| t.0)
            .collect();
        assert!(times.len() >= 4, "both sessions re-join: {times:?}");
        let closest = times.windows(2).map(|w| w[1] - w[0]).min().unwrap_or(u64::MAX);
        assert!(
            closest + 10 * MS >= SEC_NS,
            "two datagrams to the one address {} ms apart: {times:?}",
            closest / MS
        );
    });
}

/// How long after an outage that began under a transfer the session of node 0 ended, if it did within 20 s; the
/// carrier of the relay is reported as answering at every step when `carrier_answers`.
fn time_to_close(carrier_answers: bool) -> Option<u64> {
    let (mut net, direct, via) = pair(10 * MS);
    let s = session(&mut net, b"vinc/a", via);
    outage(&mut net, direct, via);
    send(&mut net, s, &pattern(2_000, 1));
    let start = net.now;
    while net.now < start + 20 * SEC_NS {
        if carrier_answers {
            let t = net.now;
            net.nodes[0]
                .cmd(t, Command::CarrierHeard { session: s, at: t })
                .unwrap();
        }
        net.run_for(100 * MS);
        if net.nodes[0]
            .events
            .iter()
            .any(|(_, e)| matches!(e, Event::Closed { session, .. } if *session == s))
        {
            return Some(net.now - start);
        }
    }
    None
}

#[test]
fn a_session_whose_relay_path_stops_answering_behind_an_answering_carrier_is_closed() {
    big_stack(|| {
        let closed = time_to_close(true);
        let natural = time_to_close(false);
        assert!(
            closed.is_some_and(|c| natural.is_none_or(|n| c + SEC_NS < n)),
            "{closed:?} {natural:?}"
        );
    });
}

#[test]
fn a_datagram_heard_on_a_relay_path_does_not_allow_the_short_initial() {
    big_stack(|| {
        // Node 0 reaches node 1 through a relay path only: no validated direct UDP path was ever heard, so the dial of
        // a peer and every resend of it carry the full Initial.
        let mut net = CoreNet::new(10 * MS);
        net.capture = true;
        let (a, b, c) = (net.add(1), net.add(2), net.add(3));
        let via = relay_addr(false, 3, 7);
        net.nodes[b].extra.push(via);
        let (peer, now) = (net.nodes[b].node, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, via, Role::Other).unwrap();
        let sa = net.nodes[a].session(&rep);
        assert!(net.run(now + 10 * SEC_NS, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Connected { .. }))
        }));
        let t = net.now;
        net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
        net.run_for(SEC_NS);
        let to_c = net.nodes[c].addr;
        net.loss = Some(Box::new(move |_, to, _| to == to_c));
        let marker = net.captured.len();
        dial(&mut net, a, c, ALPN_A, Role::Other);
        net.run_for(16 * SEC_NS);
        assert_eq!(flights(&net, marker, a, c), [1, 1, 1, 1, 1, 1]);
    });
}

/// When session `s` of node `i` reported a validated path, at or after `from`.
fn validated_at(net: &CoreNet, i: usize, s: SessionId, from: u64) -> Option<u64> {
    net.nodes[i].events.iter().find_map(|(t, e)| {
        let hit = matches!(e, Event::PathChanged { session, state: PathState::Validated, .. } if *session == s);
        (hit && *t >= from).then_some(*t)
    })
}

#[test]
fn an_end_on_a_relay_path_validates_a_direct_path_in_the_round_trip_of_its_peers_challenge() {
    big_stack(|| {
        // Node a reaches node b through a relay only. Node b then challenges a's own address, and a is told b's
        // address right after that challenge arrived, as it is when the peer's candidate list comes through the
        // relay, a hop behind the challenge.
        let one_way = 25 * MS;
        let mut net = CoreNet::new(one_way);
        let (a, b) = (net.add(1), net.add(2));
        let via = relay_addr(false, 3, 7);
        net.nodes[b].extra.push(via);
        let (peer, now) = (net.nodes[b].node, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, via, Role::Other).unwrap();
        let sa = net.nodes[a].session(&rep);
        assert!(net.run(now + 10 * SEC_NS, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Connected { .. }))
                && n.nodes[b].saw(|e| matches!(e, Event::Incoming { .. }))
        }));
        let sb = net.nodes[b]
            .events
            .iter()
            .find_map(|(_, e)| match e {
                Event::Incoming { session, .. } => Some(*session),
                _ => None,
            })
            .unwrap();
        net.run_for(SEC_NS);
        let (to_a, to_b) = (net.nodes[a].addr, net.nodes[b].addr);
        let t0 = net.now;
        net.nodes[b]
            .cmd(
                t0,
                Command::Punch {
                    session: sb,
                    addr: to_a,
                },
            )
            .unwrap();
        net.run(t0 + one_way, |_| false);
        let t1 = net.now;
        assert_eq!(t1, t0 + one_way);
        // Node a's answer has left. A challenge sent on its own after it is more than an address that has sent
        // 32 bytes may be answered with (three times that), so the endpoint's address limit holds it back. These two
        // nodes already exchanged datagrams from the same addresses (the relay here is a second address of node b),
        // so their limit is open: the test takes that one datagram off the wire itself.
        let mut held = 0;
        net.loss = Some(Box::new(move |from, to, bytes| {
            let alone = from == to_a && to == to_b && bytes.len() == CHALLENGE_LEN && held == 0;
            held += u32::from(alone);
            alone
        }));
        net.nodes[a]
            .cmd(
                t1,
                Command::Punch {
                    session: sa,
                    addr: to_b,
                },
            )
            .unwrap();
        net.run_for(SEC_NS);
        // Node b has its answer after one round trip. Node a's challenge left with that answer, so its own answer
        // comes one way later: it did not wait for the second probe of its punch, 33.3 ms on.
        assert_eq!(validated_at(&net, b, sb, t0), Some(t0 + 2 * one_way));
        assert_eq!(
            validated_at(&net, a, sa, t0),
            Some(t0 + 3 * one_way),
            "the challenge of the end on the relay waited for its next probe"
        );
    });
}

/// An idle end on a relay only answers a challenge on a direct path: the reference model looks for no direct path on
/// a session that moved no application data for 20 s (its punch round is skipped), so the challenger validates the
/// path and the idle end, which sends none of its own, stays on its relay.
#[test]
fn an_idle_end_on_a_relay_path_answers_a_challenge_and_sends_none() {
    big_stack(|| {
        let one_way = 25 * MS;
        let mut net = CoreNet::new(one_way);
        let (a, b) = (net.add(1), net.add(2));
        let via = relay_addr(false, 3, 7);
        net.nodes[b].extra.push(via);
        let (peer, now) = (net.nodes[b].node, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, via, Role::Other).unwrap();
        let sa = net.nodes[a].session(&rep);
        assert!(net.run(now + 10 * SEC_NS, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Connected { .. }))
                && n.nodes[b].saw(|e| matches!(e, Event::Incoming { .. }))
        }));
        let sb = net.nodes[b]
            .events
            .iter()
            .find_map(|(_, e)| match e {
                Event::Incoming { session, .. } => Some(*session),
                _ => None,
            })
            .unwrap();
        // No application data for more than 20 s: the session is idle at both ends.
        net.run_for(21 * SEC_NS);
        let to_a = net.nodes[a].addr;
        let t0 = net.now;
        net.nodes[b]
            .cmd(
                t0,
                Command::Punch {
                    session: sb,
                    addr: to_a,
                },
            )
            .unwrap();
        net.run_for(SEC_NS);
        assert_eq!(
            validated_at(&net, b, sb, t0),
            Some(t0 + 2 * one_way),
            "the challenger did not validate the path in one round trip"
        );
        assert_eq!(
            validated_at(&net, a, sa, t0),
            None,
            "an idle end on a relay challenged the direct path itself"
        );
    });
}

/// A datagram from a relay address the session does not track yet says nothing about the direct path the session is
/// on. The endpoint names the new path a relay's, and the session stays where it is: the reference model chooses the
/// active path by itself only from a relay. Chosen again here, a direct path slower than a second lost to a relay
/// path that was added and never heard, whose round trip reads as zero.
#[test]
fn a_session_on_a_slow_direct_path_stays_on_it_when_a_datagram_comes_from_a_new_relay_address() {
    big_stack(|| {
        // One way 600 ms: the direct path's round trip is above the second a relay path is charged.
        let one_way = 600 * MS;
        let (mut net, direct, via) = pair(one_way);
        let via2 = relay_addr(false, 4, 7);
        net.nodes[1].extra.push(via2);
        let (s, _) = net.connect_pair(0, 1, b"vinc/a", Role::Other);
        // A relay path the session adds and never hears on: nothing passes through that relay.
        net.loss = Some(Box::new(move |f, to, _| f == via || to == via));
        let t = net.now;
        net.nodes[0].cmd(t, Command::Punch { session: s, addr: via }).unwrap();
        send(&mut net, s, &pattern(2_000, 1));
        net.run_for(5 * SEC_NS);
        // One datagram of node 1 is taken off the direct path and arrives later from the other relay address, behind
        // a newer one, as a datagram that took the relay does.
        let me = net.nodes[0].addr;
        let held = std::rc::Rc::new(std::cell::RefCell::new(None::<Vec<u8>>));
        let h = held.clone();
        net.loss = Some(Box::new(move |f, to, bytes| {
            if f == via || to == via {
                return true;
            }
            if f == direct && to == me && h.borrow().is_none() {
                *h.borrow_mut() = Some(bytes.to_vec());
                return true;
            }
            false
        }));
        send(&mut net, s, &pattern(2_000, 2));
        net.run_for(3 * SEC_NS);
        send(&mut net, s, &pattern(2_000, 3));
        net.run_for(3 * SEC_NS);
        let Some(bytes) = held.borrow_mut().take() else {
            panic!("node 1 sent nothing on the direct path")
        };
        net.inject(via2, me, bytes, 0);
        net.run_for(SEC_NS);
        // The session's next data leaves on the direct path, none of it towards the relay it never heard.
        let from = net.now;
        send(&mut net, s, &pattern(3_000, 4));
        net.run_for(2 * SEC_NS);
        let big = |to: SocketAddr| {
            net.tapped
                .iter()
                .filter(|d| d.0 >= from && d.2 == to && d.3 > 1_000)
                .count()
        };
        assert_eq!(
            big(via),
            0,
            "the session left its direct path for a relay path it never heard on"
        );
        assert!(big(direct) > 0, "no data left on the direct path");
    });
}

/// A valid relay path added to a session is pinged at once while data moved in the last 20 s, as the reference model's
/// keepalive pings every valid path never sent on: nothing else would leave on it.
#[test]
fn a_relay_path_added_to_a_session_is_pinged_at_once() {
    big_stack(|| {
        let (mut net, _, via) = pair(10 * MS);
        net.capture = true;
        let (sa, _) = net.connect_pair(0, 1, ALPN_A, Role::Other);
        let (t, marker) = (net.now, net.captured.len());
        net.nodes[0].cmd(t, Command::Punch { session: sa, addr: via }).unwrap();
        net.run_for(100 * MS);
        assert!(
            net.captured[marker..].iter().any(|(_, to, _)| *to == via),
            "a datagram left on the relay path"
        );
    });
}

/// A child takes its parent's paths with when the endpoint last sent on each, as the reference model's sub-session
/// keeps its parent's path times: a relay path the parent pinged a moment ago is not pinged again by the child.
#[test]
fn a_child_does_not_ping_a_relay_path_its_parent_just_pinged() {
    big_stack(|| {
        let (mut net, _, via) = pair(10 * MS);
        net.capture = true;
        session(&mut net, ALPN_A, via);
        let (peer, to, t) = (net.nodes[1].node, net.nodes[1].addr, net.now);
        let marker = net.captured.len();
        net.nodes[0].connect(t, peer, ALPN_B, to, Role::Other).unwrap();
        net.run_for(500 * MS);
        assert!(
            net.nodes[0].saw(|e| matches!(e, Event::Connected { alpn, .. } if alpn.as_bytes() == ALPN_B)),
            "the child connected"
        );
        let on_relay = net.captured[marker..].iter().filter(|(_, to, _)| *to == via).count();
        assert_eq!(on_relay, 0, "the relay path was pinged by the parent a second ago");
    });
}
