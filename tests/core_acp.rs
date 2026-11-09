//! The access check: gating, a deny that closes with code 3, the 30 s cache and its 5 s re-ask, the optimistic report
//! and the READY hold.
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

use vinc_core::{Answer, Command, CommandError, ConnectFailure, EndReason, Event, Query, Role, Value};
use vinc_tests::*;
use vinc_transport::conn::{CloseReason, code};

const SLOW: u64 = 15 * MS_NS; // one way; a round trip of 30 ms is above the 20 ms READY threshold
const FAST: u64 = 5 * MS_NS; // a round trip of 10 ms is below it

fn is_connected(e: &Event) -> bool {
    matches!(e, Event::Connected { .. })
}
fn is_incoming(e: &Event) -> bool {
    matches!(e, Event::Incoming { .. })
}
fn is_check(e: &Event) -> bool {
    matches!(e, Event::AcpCheck { .. })
}

#[test]
fn no_application_event_leaves_a_session_before_it_is_allowed() {
    big_stack(|| {
        let mut net = CoreNet::new(SLOW);
        let (a, b) = (net.add(1), net.add(2));
        net.nodes[b].acp = Acp::Manual;
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        let sa = net.nodes[a].session(&rep);
        // The client is allowed by its own node and may write at once; the server's answer is still out.
        assert!(net.run(now + 5 * SEC_NS, |n| n.nodes[a].saw(is_connected)
            && !n.nodes[b].checks.is_empty()));
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
                    data: b"early",
                },
            )
            .unwrap();
        net.run_for(SEC_NS);
        assert!(!net.nodes[b].saw(is_incoming), "Incoming before the allow");
        assert!(!net.nodes[b].saw(|e| matches!(e, Event::StreamOpened { .. } | Event::StreamReadable { .. })));
        let sb = net.nodes[b].ep.sessions().next().unwrap();
        let Answer::Stats(st) = net.nodes[b].ep.query(Query::Stats(sb)) else {
            panic!()
        };
        assert!(!st.allowed && st.held >= 1, "{st:?}");
        // Allowing releases them in order: Incoming first.
        let (check, _) = net.nodes[b].checks[0];
        let t = net.now;
        net.nodes[b].cmd(t, Command::AcpAnswer { check, allow: true }).unwrap();
        net.run_for(SEC_NS);
        let order: Vec<_> = net.nodes[b]
            .events
            .iter()
            .filter_map(|(_, e)| match e {
                Event::Incoming { .. } => Some("incoming"),
                Event::StreamOpened { .. } => Some("opened"),
                Event::StreamReadable { .. } => Some("readable"),
                _ => None,
            })
            .collect();
        assert_eq!(order.first(), Some(&"incoming"), "{order:?}");
        assert!(order.contains(&"opened") && order.contains(&"readable"), "{order:?}");
        assert_eq!(
            net.nodes[b].read.values().next().map(Vec::as_slice),
            Some(&b"early"[..])
        );
        assert_eq!(
            net.nodes[b]
                .ep
                .command(net.now, Command::AcpAnswer { check, allow: true })
                .err(),
            Some(CommandError::NoCheck)
        );
    });
}

#[test]
fn a_deny_closes_with_code_three_on_either_side() {
    big_stack(|| {
        // The server denies: it closes the session with code 3 before the application ever saw it.
        let mut net = CoreNet::new(SLOW);
        let (a, b) = (net.add(1), net.add(2));
        net.nodes[b].acp = Acp::Deny;
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        assert!(net.run(now + 5 * SEC_NS, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Closed { .. } | Event::ConnectFailed { .. }))
        }));
        assert!(!net.nodes[b].saw(is_incoming));
        assert!(
            !net.nodes[b].saw(|e| matches!(e, Event::Closed { .. })),
            "a session the application never saw ends silently"
        );
        assert!(net.nodes[a].saw(|e| matches!(
            e,
            Event::Closed { reason: EndReason::Transport(CloseReason::Peer { error }), .. } if *error == code::FLOW_CONTROL
        )));
        assert_eq!(code::FLOW_CONTROL, 3);

        // The client denies: ConnectFailed, and the server, which allowed, sees the close with code 3.
        let mut net = CoreNet::new(SLOW);
        let (a, b) = (net.add(1), net.add(2));
        net.nodes[a].acp = Acp::Deny;
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        assert!(net.run(now + 5 * SEC_NS, |n| {
            n.nodes[b].saw(|e| matches!(e, Event::Closed { .. }))
        }));
        assert!(net.nodes[a].saw(|e| matches!(
            e,
            Event::ConnectFailed {
                reason: ConnectFailure::Denied,
                ..
            }
        )));
        assert!(!net.nodes[a].saw(is_connected));
        assert!(net.nodes[b].saw(|e| matches!(
            e,
            Event::Closed { reason: EndReason::Transport(CloseReason::Peer { error }), .. } if *error == 3
        )));
    });
}

#[test]
fn the_answer_is_cached_for_thirty_seconds_and_asked_again_five_seconds_before() {
    big_stack(|| {
        let mut net = CoreNet::new(SLOW);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        assert_eq!(net.nodes[b].count(is_check), 1);
        // The session lives on; 5 s before its cached allow runs out it asks once more.
        net.run_for(24 * SEC_NS);
        assert_eq!(net.nodes[b].count(is_check), 1, "asked too early");
        net.run_for(3 * SEC_NS);
        assert_eq!(net.nodes[b].count(is_check), 2, "no re-ask");
        assert!(net.nodes[b].saw(is_incoming));
        assert!(
            !net.nodes[b].saw(|e| matches!(e, Event::Closed { .. })),
            "a re-ask does not disturb the session"
        );
        // After the cache lapsed and with the session gone, a new dial asks again.
        let t = net.now;
        net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
        net.run_for(40 * SEC_NS);
        let before = net.nodes[b].count(is_check);
        net.connect_pair(a, b, ALPN_A, Role::Other);
        assert!(net.nodes[b].count(is_check) > before);
    });
}

#[test]
fn a_cached_allow_with_more_than_five_seconds_left_reports_connected_at_dial() {
    big_stack(|| {
        let mut net = CoreNet::new(SLOW);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
        net.run_for(10 * SEC_NS);
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        assert!(rep.events.any(is_connected), "no Connected at dial");
        let sent_before = net.nodes[a].sent.len();
        assert_eq!(sent_before, net.nodes[a].sent.len());
        // Late in the cache's life it no longer does.
        let sa2 = net.nodes[a].session(&rep);
        net.nodes[a]
            .cmd(now, Command::Close { session: sa2, error: 0 })
            .unwrap();
        net.run_for(16 * SEC_NS);
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        assert!(!rep.events.any(is_connected), "optimistic with too little left");
        assert!(net.run(now + 5 * SEC_NS, |n| n.nodes[a].count(is_connected) == 3));
    });
}

#[test]
fn ready_hold_makes_a_fast_client_wait_for_the_servers_answer() {
    big_stack(|| {
        for (delay, held) in [(FAST, true), (SLOW, false)] {
            let mut net = CoreNet::new(delay);
            let (a, b) = (net.add(1), net.add(2));
            net.nodes[b].acp = Acp::Manual;
            let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
            net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
            assert!(net.run(now + 5 * SEC_NS, |n| !n.nodes[b].checks.is_empty()));
            net.run_for(200 * MS_NS);
            let answered_at = net.now;
            let a_before = net.nodes[a].time_of(is_connected);
            assert_eq!(
                a_before.is_none(),
                held,
                "delay {delay}: the client's Connected before the server's answer: {a_before:?}"
            );
            let (check, _) = net.nodes[b].checks[0];
            net.nodes[b]
                .cmd(answered_at, Command::AcpAnswer { check, allow: true })
                .unwrap();
            assert!(net.run(answered_at + 5 * SEC_NS, |n| n.nodes[a].saw(is_connected)));
            if held {
                let t = net.nodes[a].time_of(is_connected).unwrap();
                assert!(t >= answered_at + delay, "Connected at {t} before READY could arrive");
            }
        }
    });
}

#[test]
fn a_flood_before_the_answer_fills_the_hold_and_stalls_the_session_without_losing_a_datagram() {
    big_stack(|| {
        let mut net = CoreNet::new(SLOW);
        let (a, b) = (net.add(1), net.add(2));
        net.nodes[b].acp = Acp::Manual;
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        let sa = net.nodes[a].session(&rep);
        assert!(net.run(now + 5 * SEC_NS, |n| n.nodes[a].saw(is_connected)
            && !n.nodes[b].checks.is_empty()));
        // One stream the peer opens first, then datagrams far past the 64 the hold keeps.
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
                    data: b"hi",
                },
            )
            .unwrap();
        net.run_for(50 * MS_NS);
        for i in 0..300u32 {
            let t = net.now;
            let _ = net.nodes[a].cmd(
                t,
                Command::SendDatagram {
                    session: sa,
                    data: &i.to_be_bytes(),
                },
            );
            net.run_for(MS_NS);
        }
        net.run_for(500 * MS_NS);
        let ns = net.nodes[b].ep.node_stats();
        assert!(ns.stalled_in > 0, "the flood was never held back: {ns:?}");
        assert_eq!(
            net.nodes[b].count(|e| matches!(e, Event::DatagramReceived { .. })),
            0,
            "nothing leaves before the answer"
        );
        let (check, _) = net.nodes[b].checks[0];
        let answered = net.now;
        net.nodes[b]
            .cmd(answered, Command::AcpAnswer { check, allow: true })
            .unwrap();
        net.run_for(SEC_NS);
        let got: Vec<&Event> = net.nodes[b].events.iter().map(|(_, e)| e).collect();
        let opened = got.iter().position(|e| matches!(e, Event::StreamOpened { .. }));
        let datagrams = got
            .iter()
            .filter(|e| matches!(e, Event::DatagramReceived { .. }))
            .count();
        assert!(opened.is_some(), "the stream the peer opened was dropped");
        let first_dg = got.iter().position(|e| matches!(e, Event::DatagramReceived { .. }));
        assert!(opened < first_dg, "order kept");
        // Every datagram the hold took reached the host: 64 places less the stream, less one recoverable read.
        assert!(
            datagrams >= vinc_core::HELD_EVENTS - 2,
            "{datagrams} datagrams of the {} held",
            vinc_core::HELD_EVENTS
        );
    });
}

/// Fill the host's event queue without reading it: dialing this node itself fails at once with an event each time,
/// until the endpoint holds the dials back. Returns how many dials were refused with an event.
fn stall_events(ep: &mut CoreEp, now: u64) -> usize {
    let me = ep.identity().node_id();
    let mut made = 0;
    loop {
        match ep.command(
            now,
            Command::Connect {
                node: me,
                alpn: ALPN_A,
                addrs: &[],
                role: Role::Other,
            },
        ) {
            Err(CommandError::Refused) => made += 1,
            Err(CommandError::EventsPending) => return made,
            other => panic!("unexpected {other:?}"),
        }
        assert!(made < 10_000, "the queue never stalled");
    }
}

#[test]
fn a_host_that_leaves_events_unread_holds_back_dials_and_timers_and_loses_nothing() {
    big_stack(|| {
        let mut net = CoreNet::new(SLOW);
        let (a, b) = (net.add(1), net.add(2));
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        assert!(net.run(now + 5 * SEC_NS, |n| n.nodes[a].saw(is_connected)
            && n.nodes[b].saw(is_incoming)));
        let t = net.now;
        let ep = &mut net.nodes[b].ep;
        assert!(ep.poll_timeout().is_some());
        let made = stall_events(ep, t);
        assert!(made > 1000, "only {made} events fit");
        assert_eq!(ep.poll_timeout(), None, "no timer is due while the queue is near full");
        ep.handle_timeout(t + 600 * SEC_NS);
        assert_eq!(ep.node_stats().sessions, 1, "a timer ran while the queue was near full");
        // Reading events lets the dials and the timers go on, and every event arrives.
        let mut failed = 0;
        while let Some(e) = ep.poll_event() {
            failed += usize::from(matches!(e, Event::ConnectFailed { .. }));
        }
        assert_eq!(failed, made);
        assert_eq!(ep.node_stats().events_lost, 0);
        assert!(ep.poll_timeout().is_some());
        let me = ep.identity().node_id();
        assert!(matches!(
            ep.command(
                t,
                Command::Connect {
                    node: me,
                    alpn: ALPN_A,
                    addrs: &[],
                    role: Role::Other
                }
            ),
            Err(CommandError::Refused)
        ));
    });
}

#[test]
fn held_events_released_into_a_near_full_queue_wait_and_arrive_in_order_after_the_host_reads() {
    big_stack(|| {
        let mut net = CoreNet::new(SLOW);
        let (a, b) = (net.add(1), net.add(2));
        net.nodes[b].acp = Acp::Manual;
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        let sa = net.nodes[a].session(&rep);
        assert!(net.run(now + 5 * SEC_NS, |n| n.nodes[a].saw(is_connected)
            && !n.nodes[b].checks.is_empty()));
        for i in 0..40u32 {
            let t = net.now;
            let _ = net.nodes[a].cmd(
                t,
                Command::SendDatagram {
                    session: sa,
                    data: &i.to_be_bytes(),
                },
            );
            net.run_for(MS_NS);
        }
        net.run_for(500 * MS_NS);
        let (check, _) = net.nodes[b].checks[0];
        let t = net.now;
        let ep = &mut net.nodes[b].ep;
        stall_events(ep, t);
        let rep = ep.command(t, Command::AcpAnswer { check, allow: true }).unwrap();
        assert_eq!(ep.node_stats().events_lost, 0);
        let mut got: Vec<Event> = rep.events.iter().copied().collect();
        while let Some(e) = ep.poll_event() {
            got.push(e);
        }
        let pos = |f: fn(&Event) -> bool| got.iter().position(f);
        let incoming = pos(is_incoming).expect("Incoming");
        let first_dg = pos(|e| matches!(e, Event::DatagramReceived { .. })).expect("datagram");
        assert!(incoming < first_dg, "Incoming before the datagrams");
        assert_eq!(
            got.iter()
                .filter(|e| matches!(e, Event::DatagramReceived { .. }))
                .count(),
            40,
            "every held datagram notification arrived"
        );
        assert_eq!(ep.node_stats().events_lost, 0);
    });
}
