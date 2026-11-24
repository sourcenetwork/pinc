//! The quiet-parent probe (`QUIET_PROBE`, #693) at its edges: what ends a probing dial, how fast a ride is, which
//! addresses a lapse dials, and the bounds of the probe window.
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

use std::collections::BTreeSet;
use std::net::SocketAddr;

use pinc_core::{Answer, Command, CommandError, ConnectFailure, Event, Query, Role};
use pinc_tests::*;

/// Every entry `SessionAt` lists on node `n`, as its counters.
fn listed(net: &CoreNet, n: usize) -> Vec<pinc_core::SessionStats> {
    (0..)
        .map_while(|i| match net.nodes[n].ep.query(Query::SessionAt(i)) {
            Answer::Stats(st) => Some(st),
            _ => None,
        })
        .collect()
}

/// A dial that probes is listed by `SessionAt` (so a revoke finds it), and closing it ends it: it is reported failed
/// and no handshake ever leaves for its peer, not even once the probe window would have passed.
#[test]
fn a_probing_dial_is_listed_and_closing_it_sends_no_handshake() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let marker = net.captured.len();
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        let entry = listed(&net, a).into_iter().find(|st| st.session == child);
        let entry = entry.expect("a probing dial is not listed by SessionAt");
        assert!(!entry.established && entry.path.is_none());
        assert_eq!(entry.node, Some(net.nodes[b].node));
        let now = net.now;
        net.nodes[a]
            .cmd(
                now,
                Command::Close {
                    session: child,
                    error: 0,
                },
            )
            .unwrap();
        assert!(
            !listed(&net, a).iter().any(|st| st.session == child),
            "the closed dial is still listed"
        );
        net.run_for(5 * SEC_NS);
        assert!(net.nodes[a].saw(|e| matches!(e, Event::ConnectFailed { session: Some(s), .. } if *s == child)));
        assert!(!net.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == child)));
        assert!(
            !handshake_since(&net, marker),
            "a handshake left for the peer of a closed dial"
        );
    });
}

/// The probe challenges the path of the quiet session instead of pinging it: a path challenge is answered at once,
/// where the acknowledgement of a ping waits for the peer's acknowledgement delay (up to 25 ms). Over a link with a
/// round trip of 1 ms the dial rides within a few round trips, far under that delay.
#[test]
fn a_probe_rides_within_the_round_trip_not_the_peers_acknowledgement_delay() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent_at(MS_NS / 2);
        let t0 = net.now;
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        assert!(net.run(t0 + SEC_NS, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == child))
        }));
        let at = net.nodes[a]
            .time_of(|e| matches!(e, Event::Connected { session, .. } if *session == child))
            .unwrap();
        assert!(
            at - t0 < 5 * MS_NS,
            "the ride took {} ns over a 1 ms round trip",
            at - t0
        );
    });
}

/// The addresses the handshake datagrams `from` sent since `marker` went to.
fn handshake_targets(net: &CoreNet, marker: usize, from: SocketAddr) -> BTreeSet<SocketAddr> {
    net.captured[marker..]
        .iter()
        .filter(|(f, _, d)| *f == from && d[0] & 0x80 != 0)
        .map(|(_, t, _)| *t)
        .collect()
}

/// Dial `to` from node `a` with `addrs`, name the same addresses for the flight, run five seconds with nothing
/// reaching `to` (so a probe lapses): where the handshake went.
fn dialed_set(net: &mut CoreNet, a: usize, to: usize, addrs: &[SocketAddr]) -> BTreeSet<SocketAddr> {
    let (peer, now, addr_to) = (net.nodes[to].node, net.now, net.nodes[to].addr);
    net.loss = Some(Box::new(move |_, t, _| t == addr_to));
    let marker = net.captured.len();
    let rep = net.nodes[a]
        .cmd(
            now,
            Command::Connect {
                node: peer,
                alpn: ALPN_B,
                addrs,
                role: Role::Other,
            },
        )
        .unwrap();
    let session = net.nodes[a].session(&rep);
    net.nodes[a]
        .cmd(
            now,
            Command::FlightPaths {
                session,
                addrs,
                skip_primary: false,
            },
        )
        .unwrap();
    net.run_for(5 * SEC_NS);
    handshake_targets(net, marker, net.nodes[a].addr)
}

/// With more addresses than a connection has paths, and addresses the node cannot route among them, a lapsed probe
/// dials the set a fresh dial of the same addresses dials: the routable ones in the caller's order, at most as many
/// as the paths.
#[test]
fn a_lapse_dials_the_addresses_a_fresh_dial_dials() {
    big_stack(|| {
        let x = |n: u8| -> SocketAddr { ([192, 0, 2, n], 4433).into() };
        let v6 = |n: u16| -> SocketAddr { format!("[2001:db8::{n}]:4433").parse().unwrap() };
        let (mut fresh_net, fa, fb) = closed_parent();
        let addrs = [x(1), v6(1), v6(2), v6(3), fresh_net.nodes[fb].addr, x(2), x(3), x(4)];
        let fresh = dialed_set(&mut fresh_net, fa, fb, &addrs);
        let (mut lapse_net, la, lb) = silent_parent();
        let addrs = [x(1), v6(1), v6(2), v6(3), lapse_net.nodes[lb].addr, x(2), x(3), x(4)];
        let lapse = dialed_set(&mut lapse_net, la, lb, &addrs);
        let want: BTreeSet<SocketAddr> = [x(1), lapse_net.nodes[lb].addr, x(2), x(3)].into();
        assert_eq!(fresh, want, "the fresh dial went to another set");
        assert_eq!(lapse, want, "the lapse went to another set than the fresh dial");
    });
}

/// As [`silent_parent`], the dialer's quiet-parent wait set to `window`.
fn silent_parent_waiting(window: u64) -> (CoreNet, usize, usize) {
    let mut net = CoreNet::new(10 * MS_NS);
    net.capture = true;
    let (a, b) = (net.add_with_probe_window(1, window), net.add(2));
    net.connect_pair(a, b, ALPN_A, Role::Other);
    net.run_for(SEC_NS);
    let silent = net.nodes[b].addr;
    net.loss = Some(Box::new(move |f, _, _| f == silent));
    net.run_for(25 * SEC_NS);
    (net, a, b)
}

/// How long after the dial the first handshake datagram leaves, with the dialer's wait set to `window`.
fn lapse_after(window: u64) -> u64 {
    let (mut net, a, b) = silent_parent_waiting(window);
    let (t0, marker) = (net.now, net.captured.len());
    dial(&mut net, a, b, ALPN_B);
    assert!(
        net.run(t0 + 30 * SEC_NS, |n| handshake_since(n, marker)),
        "the probe never lapsed"
    );
    net.now - t0
}

/// A configured wait stands in for the two probe timeouts: the probe lapses after it, not before.
#[test]
fn a_configured_probe_window_sets_the_wait() {
    big_stack(|| {
        let waited = lapse_after(3 * SEC_NS);
        assert!(
            waited >= 3 * SEC_NS,
            "the probe lapsed after {waited} ns, before its window"
        );
        assert!(
            waited < 3 * SEC_NS + 500 * MS_NS,
            "the probe lapsed after {waited} ns, long after its window"
        );
    });
}

/// A wait of 20 s or more is cut under the quiet threshold, which the model of the probe assumes: a dial never waits
/// longer on a session that was heard again.
#[test]
fn a_probe_window_over_the_quiet_threshold_is_cut_under_it() {
    big_stack(|| {
        let waited = lapse_after(60 * SEC_NS);
        assert!(waited < 20 * SEC_NS, "the probe waited {waited} ns");
    });
}

/// The ends of a dial's probe the application can see: it connected, or it was reported failed.
fn outcomes(net: &CoreNet, n: usize, dial: pinc_core::SessionId) -> (usize, usize) {
    (
        net.nodes[n].count(|e| matches!(e, Event::Connected { session, .. } if *session == dial)),
        net.nodes[n].count(|e| matches!(e, Event::ConnectFailed { session: Some(s), .. } if *s == dial)),
    )
}

/// A shutdown while a dial probes ends the dial (reported failed once) and no handshake goes out for it.
#[test]
fn a_shutdown_during_a_probe_ends_the_dial_without_a_handshake() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let marker = net.captured.len();
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        let now = net.now;
        net.nodes[a].cmd(now, Command::Shutdown).unwrap();
        net.run_for(5 * SEC_NS);
        assert_eq!(outcomes(&net, a, child), (0, 1));
        assert!(!listed(&net, a).iter().any(|st| st.session == child));
        assert!(!handshake_since(&net, marker), "a handshake left after the shutdown");
    });
}

/// A suspend and a resume while a dial probes leave the probe to resolve on its own: the dial ends exactly once,
/// connected or failed, and nothing is left probing.
#[test]
fn a_suspend_and_resume_during_a_probe_leave_one_outcome() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        let now = net.now;
        net.nodes[a].cmd(now, Command::Suspend).unwrap();
        net.run_for(3 * SEC_NS);
        let now = net.now;
        net.nodes[a].cmd(now, Command::Resume { moved: false }).unwrap();
        net.run_for(10 * SEC_NS);
        let (connected, failed) = outcomes(&net, a, child);
        assert_eq!(
            connected + failed,
            1,
            "the dial ended {connected} times connected and {failed} failed"
        );
        assert!(
            !listed(&net, a).iter().any(|st| st.session == child && !st.established),
            "a dial is still probing"
        );
    });
}

/// A lapse that cannot make its handshake (the node has no interface left to reach the peer from) ends the dial
/// as failed, once, and leaves no slot probing.
#[test]
fn a_lapse_that_cannot_dial_fails_the_dial_once() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let addr_b = net.nodes[b].addr;
        net.loss = Some(Box::new(move |_, to, _| to == addr_b));
        let marker = net.captured.len();
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        net.nodes[a].ep.remove_iface(pinc_core::IfaceId(0));
        net.run_for(5 * SEC_NS);
        assert_eq!(outcomes(&net, a, child), (0, 1));
        assert!(net.nodes[a].saw(|e| matches!(
            e,
            Event::ConnectFailed { session: Some(s), reason: ConnectFailure::Refused, .. } if *s == child
        )));
        assert!(!listed(&net, a).iter().any(|st| st.session == child));
        assert!(!handshake_since(&net, marker), "a handshake left with no interface");
    });
}

/// Eight dials probe one quiet session; the ninth is past the waiter bound and makes its own handshake at once. The
/// eight still ride the session when the peer answers.
#[test]
fn the_ninth_dial_past_the_waiter_bound_makes_its_own_handshake() {
    big_stack(|| {
        // Ten sessions at once (the parent, eight probes and the ninth dial) need more slots than the shared table.
        let (mut net, a, b) = silent_parent_k::<12>(10 * MS_NS);
        let marker = net.captured.len();
        let eight: Vec<_> = (0..8).map(|_| dial(&mut net, a, b, ALPN_B).0).collect();
        // One way takes 10 ms, so no answer is back yet: nothing but the eight probes has left.
        net.run_for(MS_NS);
        assert!(!handshake_since(&net, marker), "a probing dial sent a handshake");
        let (ninth, _) = dial(&mut net, a, b, ALPN_B);
        net.run_for(MS_NS);
        assert!(
            handshake_since(&net, marker),
            "the ninth dial sent no handshake of its own"
        );
        assert!(net.run(net.now + 5 * SEC_NS, |n| {
            eight
                .iter()
                .chain([&ninth])
                .all(|d| n.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if session == d)))
        }));
        for d in &eight {
            let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(*d)) else {
                panic!()
            };
            assert!(st.sub, "a dial within the bound did not ride");
        }
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(ninth)) else {
            panic!()
        };
        assert!(!st.sub, "the ninth dial rode instead of making its own handshake");
    });
}

/// Fill the host's event queue without reading it: dialing this node itself fails at once with an event each time,
/// until the endpoint holds commands back.
fn stall_events(ep: &mut CoreEp, now: u64) {
    let me = ep.identity().node_id();
    for _ in 0..10_000 {
        let cmd = Command::Connect {
            node: me,
            alpn: ALPN_A,
            addrs: &[],
            role: Role::Other,
        };
        match ep.command(now, cmd) {
            Err(CommandError::Refused) => {}
            Err(CommandError::EventsPending) => return,
            other => panic!("unexpected {other:?}"),
        }
    }
    panic!("the queue never stalled");
}

/// The peer's answer to a probe reaches a dialer whose event queue is full and unread: once the host reads, the dial
/// connects once as a sub-session of the quiet session, with no handshake and no second root.
#[test]
fn a_ride_while_the_event_queue_is_stalled_connects_once_after_the_host_reads() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let addr_a = net.nodes[a].addr;
        // The peer's answers are held back on the wire; the test hands them over by hand.
        net.loss = Some(Box::new(move |_, to, _| to == addr_a));
        let marker = net.captured.len();
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        net.run_for(30 * MS_NS);
        assert_eq!(
            outcomes(&net, a, child),
            (0, 0),
            "the probe resolved before its answer arrived"
        );
        let answers: Vec<_> = net.captured[marker..]
            .iter()
            .filter(|(_, to, _)| *to == addr_a)
            .cloned()
            .collect();
        assert!(!answers.is_empty(), "the peer sent no answer to the probe");
        net.loss = None;
        let t = net.now;
        stall_events(&mut net.nodes[a].ep, t);
        for (from, to, mut data) in answers {
            net.nodes[a].ep.handle_datagram(t, to, from, &mut data);
        }
        // The host reads everything now; the dial must connect exactly once by itself, with nothing more arriving.
        net.run_for(5 * SEC_NS);
        assert_eq!(
            outcomes(&net, a, child),
            (1, 0),
            "the stalled ride did not connect the dial once"
        );
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(child)) else {
            panic!()
        };
        assert!(st.sub, "the dial did not ride the quiet session");
        assert_eq!(net.nodes[a].ep.sessions().count(), 2, "a second root exists");
        assert_eq!(net.nodes[a].ep.node_stats().events_lost, 0);
        let handshakes = net.captured[marker..]
            .iter()
            .filter(|(_, _, d)| d[0] & 0x80 != 0)
            .count();
        assert_eq!(handshakes, 0, "a handshake left though the peer answered");
    });
}
