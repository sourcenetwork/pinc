//! The quiet-parent probe (`QUIET_PROBE`, #693): a dial to a peer whose session was not heard for twenty seconds asks
//! that session for a ping, rides it when the peer answers, and lapses into its own handshake when it does not; and
//! the plain dial paths the probe shares (a refused dial takes no slot, every routable address is tried).
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

use std::net::SocketAddr;

use pinc_core::{Answer, Command, CommandError, Endpoint, EndpointConfig, Event, Query, Role, SessionId, Value};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use pinc_security::{KeyHandle, LocalIdentity};
use pinc_tests::*;

#[test]
fn a_probe_that_lapses_makes_an_optimistic_handshake_that_writes_at_once() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let (child, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(!rep.events.any(is_connected), "the dial connected during its probe");
        // Nothing reaches the peer while the probe runs, so the probe lapses: the dial makes its own handshake,
        // and an optimistic dial may open a stream and write at once: the bytes leave with the handshake's last
        // flight.
        let marker = net.captured.len();
        let addr_b = net.nodes[b].addr;
        net.loss = Some(Box::new(move |_, to, _| to == addr_b));
        net.run_for(2 * SEC_NS + 5 * MS_NS);
        net.loss = None;
        assert!(
            handshake_since(&net, marker),
            "the probe did not lapse into a handshake"
        );
        let t0 = net.now;
        write_new(&mut net, a, child, b"early");
        assert!(net.run(t0 + 5 * SEC_NS, |n| n.nodes[b].read.values().any(|v| v == b"early")));
        // The blackout ate the handshake's first flight, so the bytes ride its first resend: one PTO backoff
        // (600 ms) plus a few round trips, not a wait for a separate connection event.
        assert!(net.now - t0 <= 2 * SEC_NS, "the bytes took {} ns", net.now - t0);
    });
}

#[test]
fn a_lapsed_probe_whose_handshake_is_never_answered_ends_with_its_early_stream() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let addr_b = net.nodes[b].addr;
        net.loss = Some(Box::new(move |_, to, _| to == addr_b));
        let (child, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(!rep.events.any(is_connected), "the dial connected during its probe");
        // The probe lapses (nothing reaches the peer): the dial makes its own handshake, and its early stream
        // ends with the dial when the peer never answers.
        net.run_for(3 * SEC_NS);
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

/// A dial to a peer whose session has gone quiet (not heard for [`PARENT_RX`], but the peer lives) probes the
/// session first: the dial asks the parent's session for a ping, and rides it when the peer answers, instead of
/// making a second root beside the old one.
#[test]
fn a_dial_to_a_quiet_peer_probes_its_session_rides_it_and_pings_it() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let parent = net.nodes[a].ep.sessions().next().unwrap();
        let heard_before = match net.nodes[a].ep.query(Query::Stats(parent)) {
            Answer::Stats(st) => st.heard,
            _ => panic!(),
        };
        let marker = net.captured.len();
        let t0 = net.now;
        let (child, rep) = dial(&mut net, a, b, ALPN_B);
        // The dial reports its id at once and connects when the probe resolves, with the same id.
        assert!(!rep.events.any(is_connected), "the probe does not connect at once");
        // The probe pings the parent's session: the peer's answer credits the parent's last hear.
        net.run_for(SEC_NS);
        let heard_after = match net.nodes[a].ep.query(Query::Stats(parent)) {
            Answer::Stats(st) => st.heard,
            _ => panic!(),
        };
        assert!(
            heard_after > heard_before,
            "the probe's ping was not answered: the parent was not heard from again"
        );
        assert!(
            !handshake_since(&net, marker),
            "a handshake started for a peer that answered its probe"
        );
        // The answer came back: the dial rides the parent's session as soon as it is heard from, not when the
        // window runs out.
        assert!(
            net.run(net.now + SEC_NS, |n| {
                n.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == child))
            }),
            "the probe never resolved into the ride"
        );
        assert_eq!(
            net.nodes[a].ep.sessions().count(),
            2,
            "the ride left a second root beside the parent"
        );
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(child)) else {
            panic!()
        };
        assert!(st.established && st.sub, "the probe did not resolve into a sub-session");
        write_new(&mut net, a, child, b"quiet");
        assert!(net.run(t0 + 10 * SEC_NS, |n| {
            n.nodes[b].read.values().any(|v| v == b"quiet")
        }));
    });
}

/// The probe of a parent that never answers (the peer restarted) lapses into the dial's own handshake, and the dead
/// parent is closed with it: one root is left, not two.
#[test]
fn an_unanswered_probe_lapses_to_a_handshake_and_leaves_one_root() {
    big_stack(|| {
        let (mut net, a, b, heard) = restarted_peer();
        net.run_for((heard + 21 * SEC_NS).saturating_sub(net.now));
        let marker = net.captured.len();
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        net.run_for(5 * SEC_NS);
        assert!(
            handshake_since(&net, marker),
            "the probe lapsed but no handshake started"
        );
        assert_eq!(
            net.nodes[a].ep.sessions().count(),
            1,
            "the lapse left the dead parent beside the new dial"
        );
        assert!(net.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == child)));
        write_new(&mut net, a, child, b"restarted");
        assert!(net.run(net.now + 5 * SEC_NS, |n| {
            n.nodes[b].read.values().any(|v| v == b"restarted")
        }));
    });
}

/// While a dial probes a quiet parent, the application holds an id with no session behind it yet: writes fail fast
/// with an explicit error instead of being buffered for a session that may never come, and the id is the one that
/// connects when the probe resolves.
#[test]
fn a_write_on_a_probing_dial_fails_fast_and_the_id_connects_after_the_probe() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let t0 = net.now;
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        let err = net.nodes[a].cmd(
            t0,
            Command::OpenStream {
                session: child,
                bidi: false,
            },
        );
        assert!(
            matches!(err, Err(CommandError::NoSession)),
            "a write path on a probing dial did not fail fast: {err:?}"
        );
        net.run_for(3 * SEC_NS);
        assert!(net.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == child)));
        write_new(&mut net, a, child, b"after");
        assert!(net.run(t0 + 10 * SEC_NS, |n| {
            n.nodes[b].read.values().any(|v| v == b"after")
        }));
    });
}

/// A second dial for another protocol while a probe runs does not latch onto the probing slot: it probes the same
/// quiet parent itself, and both probes ride the parent's session when its ping is answered.
#[test]
fn a_dial_for_another_protocol_during_a_probe_does_not_latch_onto_the_probe() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let (probe, _) = dial(&mut net, a, b, ALPN_B);
        let marker = net.captured.len();
        // The parent's own protocol, dialed again while the probe runs: not a waiting parent (the parent is
        // allowed and quiet), and the probing slot is not one either, so this dial probes the parent for itself.
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        let second = net.nodes[a].session(&rep);
        assert_ne!(second, probe, "the second dial took the probe's id");
        net.run_for(SEC_NS);
        assert!(
            !handshake_since(&net, marker),
            "a handshake was sent while both probes still ran"
        );
        // Both probes resolve into rides: two sub-sessions of the one root, each with its own protocol.
        assert!(net.run(net.now + SEC_NS, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == probe))
                && n.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == second))
        }));
        assert_eq!(net.nodes[a].ep.sessions().count(), 3, "the rides left extra roots");
        for (s, data) in [(probe, &b"still"[..]), (second, &b"second-dial"[..])] {
            write_new(&mut net, a, s, data);
            assert!(
                net.run(net.now + 5 * SEC_NS, |n| n.nodes[b].read.values().any(|v| v == data)),
                "the dial that rode did not carry data"
            );
        }
    });
}

/// A probe of a pulse session (its keepalive is the layer above's, carried by the hub's own relay) asks for its ping
/// through the carrier: the plan reports one due now, and when the carrier's answer is credited the dial rides the
/// session at once. A pulse session is never closed by a lapse: nothing in flight is the quiet state of a pulse
/// session, not proof its peer is gone.
#[test]
fn a_probe_of_a_pulse_session_pings_through_the_carrier_and_rides_it() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let parent = net.nodes[a].ep.sessions().next().unwrap();
        net.nodes[a]
            .cmd(
                net.now,
                Command::SetPulse {
                    session: parent,
                    on: true,
                },
            )
            .unwrap();
        net.run_for(SEC_NS);
        let stats = |net: &CoreNet, s: SessionId| match net.nodes[a].ep.query(Query::Stats(s)) {
            Answer::Stats(st) => st,
            _ => panic!("the session ended"),
        };
        assert!(!stats(&net, parent).pulse_due, "a ping was due before the probe asked");
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        net.run_for(SEC_NS);
        assert!(
            stats(&net, parent).pulse_due,
            "the probe never made the carrier's ping due: no probe packet can leave"
        );
        // The layer above carried the ping and the hub's answer came back: the parent is heard from, and the dial
        // rides it without waiting out the window.
        let now = net.now;
        net.nodes[a]
            .cmd(
                now,
                Command::Pulse {
                    session: parent,
                    sent: true,
                },
            )
            .unwrap();
        net.nodes[a]
            .cmd(
                now,
                Command::Pulse {
                    session: parent,
                    sent: false,
                },
            )
            .unwrap();
        assert!(
            net.run(now + SEC_NS, |n| n.nodes[a]
                .saw(|e| matches!(e, Event::Connected { session, .. } if *session == child))),
            "the dial never rode the pulse session its probe proved alive"
        );
        assert!(
            stats(&net, parent).established,
            "the probe closed the live pulse session it was asking"
        );
        assert_eq!(
            net.nodes[a].ep.sessions().count(),
            2,
            "the ride left the wrong sessions"
        );
    });
}

/// A probe whose parent's session dies during the window does not strand the dial: the lapse makes the dial's own
/// handshake to the addresses the caller gave, and the dial connects.
#[test]
fn a_probe_whose_parent_died_lapses_to_a_handshake_on_the_dial_s_own_addresses() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let parent = net.nodes[a].ep.sessions().next().unwrap();
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        net.run_for(MS_NS);
        // The parent's session ends mid-probe (the application closed it): the slot frees, and the lapse can no
        // longer read an address from it.
        net.nodes[a]
            .cmd(
                net.now,
                Command::Close {
                    session: parent,
                    error: 0,
                },
            )
            .unwrap();
        net.run_for(5 * SEC_NS);
        assert!(
            net.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == child)),
            "the dial ended refused when its parent died, instead of making its own handshake"
        );
        assert_eq!(net.nodes[a].ep.sessions().count(), 1, "the dial left a stray session");
        write_new(&mut net, a, child, b"lapsed");
        assert!(net.run(net.now + 5 * SEC_NS, |n| {
            n.nodes[b].read.values().any(|v| v == b"lapsed")
        }));
    });
}

/// A probe never closes a parent with a write in flight on it: an application write during the window leaves the
/// session to its own keepalive (its end closes as usual), and nothing the application sent is lost by the rule.
#[test]
fn a_probe_does_not_close_a_parent_with_a_write_in_flight() {
    big_stack(|| {
        let (mut net, a, b, heard) = restarted_peer();
        net.run_for((heard + 21 * SEC_NS).saturating_sub(net.now));
        let parent = net.nodes[a].ep.sessions().next().unwrap();
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        // The application writes on the quiet parent during the probe: the write leaves and is never acknowledged
        // (the peer is gone), so it is still in flight when the probe lapses.
        let Value::Stream(id) = net.nodes[a]
            .cmd(
                net.now,
                Command::OpenStream {
                    session: parent,
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
                net.now,
                Command::Write {
                    session: parent,
                    stream: id,
                    data: b"payload",
                },
            )
            .unwrap();
        net.run_for(4 * SEC_NS);
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(parent)) else {
            panic!("the probe closed the parent with the write unacknowledged");
        };
        assert!(
            st.established,
            "the probe closed the parent with the write unacknowledged"
        );
        let _ = child;
    });
}

/// A probe lapse never touches the session that came to occupy its parent's slot: the lapse reads the session it
/// probed by identity, so a slot reused by a dial to another peer keeps that session, and the dial still reaches the
/// peer it asked for.
#[test]
fn a_probe_lapse_leaves_the_session_that_reused_its_parents_slot_alone() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        net.capture = true;
        let (a, b, c) = (net.add(1), net.add(2), net.add(3));
        net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        let silent = net.nodes[b].addr;
        net.loss = Some(Box::new(move |f, _, _| f == silent));
        net.run_for(25 * SEC_NS);
        net.loss = None;
        let parent = net.nodes[a]
            .ep
            .sessions()
            .next()
            .expect("the session to b did not survive its silence");
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        net.run_for(MS_NS);
        // The parent's session ends mid-probe, and a dial to a third peer takes its slot.
        net.nodes[a]
            .cmd(
                net.now,
                Command::Close {
                    session: parent,
                    error: 0,
                },
            )
            .unwrap();
        let (cc, _) = dial(&mut net, a, c, ALPN_A);
        net.run_for(5 * SEC_NS);
        // The lapse found the third peer's session in its parent's slot and must have left it alone: the dial to b
        // reaches b, and the session to c is still up.
        assert!(
            net.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == child)),
            "the dial to b never connected after its lapse"
        );
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(cc)) else {
            panic!("the lapse closed the session to c that reused its parent's slot");
        };
        assert!(
            st.established,
            "the lapse closed the session to c that reused its parent's slot"
        );
        write_new(&mut net, a, cc, b"third");
        assert!(net.run(net.now + 5 * SEC_NS, |n| {
            n.nodes[c].read.values().any(|v| v == b"third")
        }));
    });
}

/// A dial made before the endpoint holds a prekey is refused and takes no slot: repeated past the table's size, every
/// one is still `NoPrekey`, never `Full`.
#[test]
fn a_dial_without_a_prekey_takes_no_slot() {
    big_stack(|| {
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7; 32]).unwrap();
        let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
        let mut ep: Box<CoreEp> = Box::new(Endpoint::new(
            0,
            Caps(Software, true),
            Drbg::new(&[3; 32]),
            identity,
            EndpointConfig::new(7),
            slots(),
        ));
        let here: SocketAddr = ([10, 0, 0, 7], 4433).into();
        let there: SocketAddr = ([10, 0, 0, 8], 4433).into();
        ep.add_iface(here).unwrap();
        let peer = TNode::new(8, there, 0).node;
        for _ in 0..=CK {
            let r = ep.command(
                0,
                Command::Connect {
                    node: peer,
                    alpn: ALPN_A,
                    addrs: &[there],
                    role: Role::Other,
                },
            );
            assert!(matches!(r, Err(CommandError::NoPrekey)), "{:?}", r.err());
        }
        assert_eq!(ep.node_stats().sessions, 0, "a refused dial kept a slot");
    });
}
/// A dial whose only routable address comes after four it cannot route still reaches the peer.
#[test]
fn a_dial_reaches_a_routable_address_listed_fifth() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let v6: SocketAddr = "[2001:db8::1]:4433".parse().unwrap();
        let addrs = [v6, v6, v6, v6, net.nodes[b].addr];
        let (peer, now) = (net.nodes[b].node, net.now);
        let rep = net.nodes[a]
            .cmd(
                now,
                Command::Connect {
                    node: peer,
                    alpn: ALPN_A,
                    addrs: &addrs,
                    role: Role::Other,
                },
            )
            .expect("the dial found no route");
        let s = net.nodes[a].session(&rep);
        assert!(net.run(net.now + 5 * SEC_NS, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == s))
        }));
    });
}
/// A replayed datagram of the peer's (an old packet an attacker on the path recorded) does not make a dead parent
/// look heard: the dial to a peer that restarted makes its own handshake and ends with one root.
#[test]
fn a_replayed_packet_does_not_make_a_dead_parent_carry_a_dial() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        net.capture = true;
        let (a, b) = (net.add(1), net.add(2));
        let (parent, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        let (addr_a, addr_b) = (net.nodes[a].addr, net.nodes[b].addr);
        let old: Vec<Vec<u8>> = net
            .captured
            .iter()
            .filter(|(f, t, d)| *f == addr_b && *t == addr_a && d[0] & 0x80 == 0)
            .map(|c| c.2.clone())
            .collect();
        assert!(!old.is_empty(), "no datagram of the peer was recorded");
        let now = net.now;
        net.nodes[b] = TNode::new(2, addr_b, now);
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(parent)) else {
            panic!()
        };
        net.run_for((st.heard + 21 * SEC_NS).saturating_sub(net.now));
        let marker = net.captured.len();
        let (peer, now) = (net.nodes[b].node, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_B, addr_b, Role::Other).unwrap();
        let child = net.nodes[a].session(&rep);
        for d in &old {
            net.inject(addr_b, addr_a, d.clone(), 0);
        }
        net.run_for(5 * SEC_NS);
        assert!(
            handshake_since(&net, marker),
            "a replay made the dead parent carry the dial"
        );
        assert!(net.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == child)));
        assert_eq!(
            net.nodes[a].ep.sessions().count(),
            1,
            "the dead parent stayed beside the dial"
        );
    });
}

/// Seven dials probe one quiet session and ride it on a 1 MiB stack: the resolution of the probes nests at most
/// twice, whatever their number. Measured unoptimised (`just unoptimised`, where the frames are largest): one probe
/// needs under 1 MiB, seven nested probes abort at 1 MiB and still fit 2 MiB, so 1 MiB is the stack that tells them
/// apart.
#[test]
fn seven_probes_of_one_session_ride_it_on_a_one_mebibyte_stack() {
    std::thread::Builder::new()
        .stack_size(1 << 20)
        .spawn(|| {
            let (mut net, a, b) = silent_parent();
            let children: Vec<SessionId> = (0..7)
                .map(|_| {
                    let (child, rep) = dial(&mut net, a, b, ALPN_B);
                    assert!(!rep.events.any(is_connected), "a dial did not probe");
                    child
                })
                .collect();
            let connected = |n: &mut CoreNet| {
                children
                    .iter()
                    .all(|c| n.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if session == c)))
            };
            assert!(
                net.run(net.now + 3 * SEC_NS, connected),
                "the probes did not all connect"
            );
            for c in &children {
                let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(*c)) else {
                    panic!("a ridden probe has no session");
                };
                assert!(st.sub, "a probe made a root instead of riding the session");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A probe of a pulse session whose probe lapses without the carrier's answer leaves the session up: a pulse
/// session's liveness is its carrier's, and a late answer is not proof of death.
#[test]
fn a_probe_of_a_pulse_session_that_lapses_leaves_the_session_up() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let parent = net.nodes[a].ep.sessions().next().unwrap();
        net.nodes[a]
            .cmd(
                net.now,
                Command::SetPulse {
                    session: parent,
                    on: true,
                },
            )
            .unwrap();
        net.run_for(SEC_NS);
        let marker = net.captured.len();
        let _ = dial(&mut net, a, b, ALPN_B);
        // The carrier carried the ping, and no answer ever comes back.
        let now = net.now;
        net.nodes[a]
            .cmd(
                now,
                Command::Pulse {
                    session: parent,
                    sent: true,
                },
            )
            .unwrap();
        assert!(
            net.run(now + 5 * SEC_NS, |n| handshake_since(n, marker)),
            "the probe never lapsed into a handshake"
        );
        net.run_for(5 * SEC_NS);
        assert!(
            !net.nodes[a].saw(|e| matches!(e, Event::Closed { session, .. } if *session == parent)),
            "the lapse closed the live pulse session"
        );
        let r = net.nodes[a].cmd(
            net.now,
            Command::OpenStream {
                session: parent,
                bidi: false,
            },
        );
        assert!(r.is_ok(), "the pulse session does not take a stream: {:?}", r.err());
    });
}

/// A dial probing its quiet parent answers `Stats` as a dial that has not started its handshake (the connectivity
/// client reads `None` as "the session is gone" and drops it), and keeps the `FlightPaths`, `FirstResend` and
/// `HoldFlight` it is sent: the lapse's handshake flies to the address of the flight.
#[test]
fn a_probing_dial_answers_stats_and_keeps_the_flight_for_its_lapse() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let addr_b = net.nodes[b].addr;
        net.loss = Some(Box::new(move |_, to, _| to == addr_b));
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(child)) else {
            panic!("a probing dial answers no stats");
        };
        assert!(
            !st.established && st.dialer,
            "a probing dial is a dial that has not connected"
        );
        let x: SocketAddr = ([192, 0, 2, 77], 4433).into();
        let now = net.now;
        let flight = [
            Command::FlightPaths {
                session: child,
                addrs: &[x],
                skip_primary: false,
            },
            Command::FirstResend {
                session: child,
                delay: 0,
            },
            Command::HoldFlight {
                session: child,
                hold: false,
            },
        ];
        for cmd in flight {
            let r = net.nodes[a].cmd(now, cmd);
            assert!(r.is_ok(), "a flight command on a probing dial failed: {:?}", r.err());
        }
        let addr_a = net.nodes[a].addr;
        let marker = net.captured.len();
        let to_x = |n: &mut CoreNet| {
            n.captured[marker..]
                .iter()
                .any(|(f, t, d)| *f == addr_a && *t == x && d[0] & 0x80 != 0)
        };
        assert!(
            net.run(now + 5 * SEC_NS, to_x),
            "the lapse never flew to the address of the flight"
        );
    });
}

/// Two probes of different protocols that lapse together make one handshake: the second waits on the first's, as a
/// dial does on a peer whose handshake runs.
#[test]
fn two_probes_of_different_protocols_that_lapse_together_make_one_handshake() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let addr_b = net.nodes[b].addr;
        net.loss = Some(Box::new(move |_, to, _| to == addr_b));
        let marker = net.captured.len();
        let (one, _) = dial(&mut net, a, b, ALPN_B);
        let (two, _) = dial(&mut net, a, b, ALPN_A);
        assert!(
            net.run(net.now + 5 * SEC_NS, |n| handshake_since(n, marker)),
            "the probes never lapsed into a handshake"
        );
        net.loss = None;
        let connected = |n: &mut CoreNet| {
            [one, two]
                .iter()
                .all(|c| n.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if session == c)))
        };
        assert!(
            net.run(net.now + 5 * SEC_NS, connected),
            "the dials did not both connect"
        );
        let roots = [one, two]
            .into_iter()
            .filter(|c| matches!(net.nodes[a].ep.query(Query::Stats(*c)), Answer::Stats(st) if !st.sub))
            .count();
        assert_eq!(roots, 1, "the two lapsed probes made {roots} handshakes");
    });
}
