//! Sessions on relay and direct paths at the endpoint: a session whose relay path stops answering while the relay's
//! carrier still does is closed, and the re-join challenges of a thin node's sessions to one address are spaced.
#![allow(clippy::unwrap_used, clippy::panic, clippy::indexing_slicing)]

use std::net::SocketAddr;

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
