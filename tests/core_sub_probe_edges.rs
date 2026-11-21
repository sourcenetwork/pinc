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

use pinc_core::{Answer, Command, Event, Query, Role};
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
        assert!(!listed(&net, a).iter().any(|st| st.session == child), "the closed dial is still listed");
        net.run_for(5 * SEC_NS);
        assert!(net.nodes[a].saw(|e| matches!(e, Event::ConnectFailed { session: Some(s), .. } if *s == child)));
        assert!(!net.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == child)));
        assert!(!handshake_since(&net, marker), "a handshake left for the peer of a closed dial");
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
        assert!(at - t0 < 5 * MS_NS, "the ride took {} ns over a 1 ms round trip", at - t0);
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
