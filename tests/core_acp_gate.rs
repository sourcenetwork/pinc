//! The access gate after a deny or a lapsed answer: every path that releases events to the application asks one
//! predicate (the session is allowed, its peer's answer stands and is an allow), and a deny clears the allow and
//! drops what was held at once.
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

use vinc_core::{Answer, Command, CommandError, ConnectFailure, EndReason, Event, Query, Role, SessionId, Value};
use vinc_tests::*;

const FAST: u64 = 5 * MS_NS; // a round trip of 10 ms is below the 20 ms READY threshold

/// Application data of session `s`: what the gate holds back until the session may release events.
fn is_data(e: &Event, s: SessionId) -> bool {
    e.session() == Some(s)
        && matches!(
            e,
            Event::StreamOpened { .. }
                | Event::StreamReadable { .. }
                | Event::StreamWritable { .. }
                | Event::OpenReady { .. }
                | Event::StreamReset { .. }
                | Event::StreamStopped { .. }
                | Event::DatagramReceived { .. }
        )
}

fn is_connected(e: &Event) -> bool {
    matches!(e, Event::Connected { .. })
}
fn is_incoming(e: &Event) -> bool {
    matches!(e, Event::Incoming { .. })
}

/// Opens a unidirectional stream on `n`'s session `s` and writes `data` to it.
fn write_once(net: &mut CoreNet, n: usize, s: SessionId, data: &[u8]) {
    let t = net.now;
    let Value::Stream(id) = net.nodes[n]
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
        panic!()
    };
    net.nodes[n]
        .cmd(
            t,
            Command::Write {
                session: s,
                stream: id,
                data,
            },
        )
        .unwrap();
}

/// Fill the host's event queue without reading it: dialing this node itself fails at once with an event each time,
/// until the endpoint holds the dials back.
fn stall_events(ep: &mut CoreEp, now: u64) {
    let me = ep.identity().node_id();
    for _ in 0..10_000 {
        match ep.command(
            now,
            Command::Connect {
                node: me,
                alpn: ALPN_A,
                addrs: &[],
                role: Role::Other,
            },
        ) {
            Err(CommandError::Refused) => {}
            Err(CommandError::EventsPending) => return,
            other => panic!("unexpected {other:?}"),
        }
    }
    panic!("the queue never stalled");
}

/// The datagrams `from` sent while `net` ran for `span` with everything `from` sends dropped on the wire.
fn withheld(net: &mut CoreNet, from: SocketAddr, span: u64) -> Vec<Vec<u8>> {
    let first = net.captured.len();
    net.capture = true;
    net.loss = Some(Box::new(move |f, _, _| f == from));
    net.run_for(span);
    net.loss = None;
    net.capture = false;
    net.captured[first..]
        .iter()
        .filter(|(f, _, _)| *f == from)
        .map(|(_, _, d)| d.clone())
        .collect()
}

/// A dialer `a` with a manual access check, connected to `b`, and the second check `a` raises 5 s before its allow
/// lapses (not answered yet).
fn dialer_at_its_recheck(net: &mut CoreNet) -> (usize, usize, SessionId, SessionId) {
    let (a, b) = (net.add(1), net.add(2));
    net.nodes[a].acp = Acp::Manual;
    let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
    let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
    let sa = net.nodes[a].session(&rep);
    assert!(net.run(now + 5 * SEC_NS, |n| !n.nodes[a].checks.is_empty()));
    let (check, _) = net.nodes[a].checks[0];
    let t = net.now;
    net.nodes[a].cmd(t, Command::AcpAnswer { check, allow: true }).unwrap();
    assert!(net.run(t + 5 * SEC_NS, |n| n.nodes[a].saw(is_connected)
        && n.nodes[b].saw(is_incoming)));
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
    let t = net.now;
    assert!(net.run(t + 40 * SEC_NS, |n| n.nodes[a].checks.len() == 2), "no re-ask");
    (a, b, sa, sb)
}

#[test]
fn a_dial_denied_on_its_recheck_delivers_nothing_after_the_deny() {
    big_stack(|| {
        let mut net = CoreNet::new(FAST);
        let (a, b, _sa, sb) = dialer_at_its_recheck(&mut net);
        let (a_addr, b_addr) = (net.nodes[a].addr, net.nodes[b].addr);
        // The peer writes; its datagrams reach the dialer only after the deny, as when the host reads a batch of
        // datagrams before it sends.
        write_once(&mut net, b, sb, b"after");
        let held = withheld(&mut net, b_addr, 300 * MS_NS);
        assert_ne!(held.len(), 0, "nothing was withheld");
        let mark = net.nodes[a].events.len();
        let (check, _) = net.nodes[a].checks[1];
        let t = net.now;
        net.nodes[a].cmd(t, Command::AcpAnswer { check, allow: false }).unwrap();
        for mut d in held {
            net.nodes[a].ep.handle_datagram(t, a_addr, b_addr, &mut d);
        }
        net.nodes[a].service(t);
        let after: Vec<Event> = net.nodes[a].events[mark..].iter().map(|(_, e)| *e).collect();
        assert!(
            !after
                .iter()
                .any(|e| matches!(e, Event::StreamOpened { .. } | Event::StreamReadable { .. })),
            "data reached the application after the deny: {after:?}"
        );
        // The session was reported Connected: it ends with Closed, never with ConnectFailed.
        net.run_for(2 * SEC_NS);
        let after: Vec<Event> = net.nodes[a].events[mark..].iter().map(|(_, e)| *e).collect();
        assert!(
            !after.iter().any(|e| matches!(e, Event::ConnectFailed { .. })),
            "ConnectFailed for a session already reported Connected: {after:?}"
        );
        assert!(
            after.iter().any(|e| matches!(
                e,
                Event::Closed {
                    reason: EndReason::Denied,
                    ..
                }
            )),
            "no Closed with the denied reason: {after:?}"
        );
    });
}

/// The answer of node `b`'s peer lapsed (the host did not run for a minute), the peer wrote and `b` holds its data
/// and asks again, nobody answers; then `b`'s host lets its queue fill and a second datagram parks the session.
fn lapsed_and_parked(net: &mut CoreNet) -> (usize, SessionId, u64) {
    let (a, b) = (net.add(1), net.add(2));
    let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
    net.nodes[b].acp = Acp::Manual;
    net.now += 60 * SEC_NS;
    write_once(net, a, sa, b"late");
    net.run_for(SEC_NS);
    let (check, _) = net.nodes[b].checks[0];
    let Answer::Stats(st) = net.nodes[b].ep.query(Query::Stats(sb)) else {
        panic!()
    };
    assert!(st.held >= 1, "nothing was held: {st:?}");
    let (a_addr, b_addr) = (net.nodes[a].addr, net.nodes[b].addr);
    write_once(net, a, sa, b"more");
    let more = withheld(net, a_addr, 300 * MS_NS);
    assert_ne!(more.len(), 0, "nothing was withheld");
    let t = net.now;
    stall_events(&mut net.nodes[b].ep, t);
    for mut d in more {
        net.nodes[b].ep.handle_datagram(t, b_addr, a_addr, &mut d);
    }
    (b, sb, check)
}

fn drain(net: &mut CoreNet, n: usize) -> Vec<Event> {
    let mut got = Vec::new();
    while let Some(e) = net.nodes[n].ep.poll_event() {
        got.push(e);
    }
    got
}

#[test]
fn a_parked_session_releases_nothing_held_on_a_lapsed_answer_before_a_fresh_allow() {
    big_stack(|| {
        let mut net = CoreNet::new(FAST);
        let (b, sb, _check) = lapsed_and_parked(&mut net);
        let got = drain(&mut net, b);
        assert!(
            !got.iter().any(|e| is_data(e, sb)),
            "application events left on a lapsed answer before any fresh allow: {got:?}"
        );
    });
}

#[test]
fn a_parked_denied_session_resumed_releases_nothing() {
    big_stack(|| {
        let mut net = CoreNet::new(FAST);
        let (b, sb, check) = lapsed_and_parked(&mut net);
        let t = net.now;
        net.nodes[b]
            .ep
            .command(t, Command::AcpAnswer { check, allow: false })
            .unwrap();
        let got = drain(&mut net, b);
        assert!(
            !got.iter().any(|e| is_data(e, sb)),
            "a denied session released held events: {got:?}"
        );
    });
}

#[test]
fn ready_after_the_answer_lapsed_releases_nothing_before_a_fresh_allow() {
    big_stack(|| {
        let mut net = CoreNet::new(FAST);
        let (a, b) = (net.add(1), net.add(2));
        net.nodes[a].acp = Acp::Manual;
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        // A first session: b answers at once, a only after 20 s, so a's answer outlives b's.
        let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        let first = net.nodes[a].session(&rep);
        assert!(net.run(now + 5 * SEC_NS, |n| !n.nodes[a].checks.is_empty()));
        net.run_for(20 * SEC_NS);
        let (check, _) = net.nodes[a].checks[0];
        let t = net.now;
        net.nodes[a].cmd(t, Command::AcpAnswer { check, allow: true }).unwrap();
        net.run_for(SEC_NS);
        net.nodes[a]
            .cmd(
                net.now,
                Command::Close {
                    session: first,
                    error: 0,
                },
            )
            .unwrap();
        // b's answer lapsed, a's has 18 s left: the next dial is reported at once and waits for READY, which b sends
        // when its host answers.
        net.run_for(12 * SEC_NS);
        net.nodes[b].acp = Acp::Manual;
        let before = net.nodes[a].count(is_connected);
        let t = net.now;
        let rep = net.nodes[a].connect(t, peer, ALPN_B, to, Role::Other).unwrap();
        let sa = net.nodes[a].session(&rep);
        net.run_for(SEC_NS);
        assert_eq!(
            net.nodes[a].count(is_connected),
            before + 1,
            "the dial was not reported at once"
        );
        assert!(!net.nodes[b].checks.is_empty(), "b raised no check");
        // More than the send buffer takes: the write is cut short and a writable notice follows the acknowledgements.
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
                    data: &vec![7u8; 1 << 20],
                },
            )
            .unwrap();
        net.run_for(SEC_NS);
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(sa)) else {
            panic!()
        };
        assert!(st.held >= 1, "nothing was held waiting for READY: {st:?}");
        // a's answer lapses; b's host answers only now.
        let first_check = net.nodes[a].checks.len();
        net.run_for(20 * SEC_NS);
        assert!(net.nodes[a].checks.len() > first_check, "a did not ask again");
        let mark = net.nodes[a].events.len();
        let (check, _) = net.nodes[b].checks[0];
        let t = net.now;
        net.nodes[b].cmd(t, Command::AcpAnswer { check, allow: true }).unwrap();
        net.run_for(SEC_NS);
        let after: Vec<Event> = net.nodes[a].events[mark..].iter().map(|(_, e)| *e).collect();
        assert!(
            !after.iter().any(|e| is_data(e, sa)),
            "READY released held events on a lapsed answer: {after:?}"
        );
        // A fresh allow lifts the hold.
        let (check, _) = *net.nodes[a].checks.last().unwrap();
        let t = net.now;
        net.nodes[a].cmd(t, Command::AcpAnswer { check, allow: true }).unwrap();
        net.run_for(SEC_NS);
        assert!(
            net.nodes[a].events[mark..].iter().any(|(_, e)| is_data(e, sa)),
            "the fresh allow released nothing"
        );
    });
}

#[test]
fn a_sub_session_of_a_parent_denied_since_is_not_allowed_with_it() {
    big_stack(|| {
        let mut net = CoreNet::new(FAST);
        let (a, b, _sa, _sb) = dialer_at_its_recheck(&mut net);
        let (peer, to) = (net.nodes[b].node, net.nodes[b].addr);
        let (check, _) = net.nodes[a].checks[1];
        let t = net.now;
        net.nodes[a].cmd(t, Command::AcpAnswer { check, allow: false }).unwrap();
        // The parent's close waits for its queue to drain: a dial for another protocol in between opens a
        // sub-session over it.
        let mark = net.nodes[a].events.len();
        net.nodes[a].connect(t, peer, ALPN_B, to, Role::Other).unwrap();
        net.run_for(SEC_NS);
        let after: Vec<Event> = net.nodes[a].events[mark..].iter().map(|(_, e)| *e).collect();
        assert!(
            !after
                .iter()
                .any(|e| matches!(e, Event::Connected { alpn, .. } if alpn.as_bytes() == ALPN_B)),
            "a sub-session was reported open over a denied parent: {after:?}"
        );
        assert!(
            after.iter().any(|e| matches!(
                e,
                Event::ConnectFailed { alpn, reason: ConnectFailure::Denied, .. } if alpn.as_bytes() == ALPN_B
            )),
            "the dial was not refused as denied: {after:?}"
        );
    });
}
