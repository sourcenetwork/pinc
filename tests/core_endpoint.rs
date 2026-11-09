//! The endpoint end to end: dial, streams, resumption across a restart, registry, shutdown and queries.
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

use vinc_core::{
    Answer, Command, CommandError, ConnectFailure, EndReason, Event, Query, Role, SessionId, StateError, Value,
    state_len,
};
use vinc_tests::*;
use vinc_transport::conn::{CloseReason, code};

fn open_and_send(net: &mut CoreNet, n: usize, s: SessionId, data: &[u8]) -> u64 {
    let now = net.now;
    let Value::Stream(id) = net.nodes[n]
        .cmd(now, Command::OpenStream { session: s, bidi: true })
        .unwrap()
        .value
    else {
        panic!("no stream")
    };
    net.nodes[n]
        .cmd(
            now,
            Command::Write {
                session: s,
                stream: id,
                data,
            },
        )
        .unwrap();
    net.nodes[n]
        .cmd(now, Command::Finish { session: s, stream: id })
        .unwrap();
    id
}

#[test]
fn two_endpoints_connect_and_move_a_stream() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        open_and_send(&mut net, a, sa, b"hello");
        let end = net.now + 5 * SEC_NS;
        assert!(net.run(end, |n| !n.nodes[b].fin.is_empty()));
        assert_eq!(
            net.nodes[b].read.iter().next().map(|(k, v)| (k.0, v.clone())),
            Some((sb, b"hello".to_vec()))
        );
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(sa)) else {
            panic!()
        };
        assert!(st.established && st.allowed && st.dialer);
        assert_eq!(st.node, Some(net.nodes[b].node));
        assert_eq!(st.route.map(|r| r.1), Some(net.nodes[b].addr));
        let Answer::Stats(sb_stats) = net.nodes[b].ep.query(Query::Stats(sb)) else {
            panic!()
        };
        assert!(!sb_stats.dialer && sb_stats.transport.datagrams_received > 0);
        let Answer::Peer(p) = net.nodes[a].ep.query(Query::PeerAt(0)) else {
            panic!("no peer")
        };
        assert_eq!(p.node, net.nodes[b].node);
        assert!(p.krtt >= 20 * MS_NS && p.krtt < 60 * MS_NS, "krtt {}", p.krtt);
        let Answer::Node(ns) = net.nodes[a].ep.query(Query::Node) else {
            panic!()
        };
        assert_eq!(ns.sessions, 1);
        assert!(ns.lrtt >= 20 * MS_NS);
    });
}

#[test]
fn a_bulk_transfer_is_batched_and_arrives_whole() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let data = pattern(150_000, 7);
        let now = net.now;
        let Value::Stream(id) = net.nodes[a]
            .cmd(
                now,
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
        let mut off = 0;
        let end = now + 20 * SEC_NS;
        assert!(net.run(end, |n| {
            let t = n.now;
            while off < data.len() {
                let Ok(rep) = n.nodes[a].cmd(
                    t,
                    Command::Write {
                        session: sa,
                        stream: id,
                        data: &data[off..],
                    },
                ) else {
                    break;
                };
                let Value::Written(w) = rep.value else { break };
                if w == 0 {
                    break;
                }
                off += w;
            }
            if off == data.len() {
                let _ = n.nodes[a].cmd(
                    t,
                    Command::Finish {
                        session: sa,
                        stream: id,
                    },
                );
            }
            n.nodes[b].fin.len() == 1
        }));
        assert_eq!(net.nodes[b].read.values().next().unwrap(), &data);
        assert!(net.batches > 0, "no datagram batch was built");
    });
}

#[test]
fn a_restart_keeps_tickets_and_round_trips_and_the_first_dial_resumes_with_early_data() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        assert!(!net.nodes[a].ep.tickets().is_empty(), "no ticket received");
        let now = net.now;
        let mut buf = vec![0u8; state_len(8)];
        let n = net.nodes[a].ep.export_state(now, &mut buf).unwrap();
        let state = buf[..n].to_vec();
        assert_eq!(
            net.nodes[a].ep.export_state(now, &mut [0u8; 8]),
            Err(StateError::BufferTooSmall)
        );

        // The node restarts: a fresh endpoint with the same identity and nothing in memory.
        net.nodes[a]
            .ep
            .command(now, Command::Close { session: sa, error: 0 })
            .unwrap();
        net.run_for(SEC_NS);
        let addr = net.nodes[a].addr;
        net.nodes[a] = TNode::new(1, addr, net.now);
        assert!(net.nodes[a].ep.tickets().is_empty());
        let bad = [&state[..state.len() - 1], &[9u8][..]];
        assert_eq!(
            net.nodes[a].ep.restore_state(net.now, bad[0]),
            Err(StateError::Malformed)
        );
        assert_eq!(
            net.nodes[a].ep.restore_state(net.now, bad[1]),
            Err(StateError::Malformed)
        );
        assert!(net.nodes[a].ep.tickets().is_empty() && net.nodes[a].ep.rtt().peers().count() == 0);
        let r = net.nodes[a].ep.restore_state(net.now, &state).unwrap();
        assert!(r.tickets >= 1 && r.peers == 1 && r.prekeys == 1, "{r:?}");
        let peer = net.nodes[b].node;
        assert!(net.nodes[a].ep.rtt().krtt(&peer).is_some_and(|r| r >= 20 * MS_NS));

        // The first dial resumes, and data written before the answer arrives is read at the peer one way later.
        let t0 = net.now;
        let (to, now) = (net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        let s2 = net.nodes[a].session(&rep);
        open_and_send(&mut net, a, s2, b"early");
        let fin0 = net.nodes[b].fin.len();
        assert!(net.run(t0 + 5 * SEC_NS, |n| n.nodes[b].fin.len() > fin0));
        let at = net.nodes[b]
            .time_of(|e| matches!(e, Event::StreamReadable { .. }))
            .unwrap();
        assert!(at >= t0 && at - t0 <= 12 * MS_NS, "early data took {} ns", at - t0);
        assert!(net.run(t0 + 5 * SEC_NS, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Connected { resumed: true, .. }))
        }));
    });
}

#[test]
fn an_unregistered_protocol_is_refused_and_the_dial_fails() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        net.nodes[b].ep.unregister_alpn(ALPN_B);
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        net.nodes[a].connect(now, peer, ALPN_B, to, Role::Other).unwrap();
        let end = now + 60 * SEC_NS;
        assert!(net.run(end, |n| n.nodes[a].saw(|e| matches!(e, Event::ConnectFailed { .. }))));
        assert!(!net.nodes[b].saw(|e| matches!(e, Event::Incoming { .. })));
        assert!(!net.nodes[a].saw(|e| matches!(e, Event::Connected { .. })));
        // The registry is bounded and ignores empty names.
        assert!(!net.nodes[b].ep.register_alpn(b""));
        for i in 0..4u8 {
            let _ = net.nodes[b].ep.register_alpn(&[b'x', i]);
        }
        assert!(!net.nodes[b].ep.register_alpn(b"overflow"));
    });
}

#[test]
fn shutdown_closes_every_session_with_the_leave_code() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let now = net.now;
        net.nodes[a].cmd(now, Command::Shutdown).unwrap();
        assert!(net.run(now + 5 * SEC_NS, |n| {
            n.nodes[b].saw(|e| matches!(e, Event::Closed { .. }))
        }));
        assert!(net.nodes[b].saw(|e| matches!(
            e,
            Event::Closed { session, reason: EndReason::Transport(CloseReason::Peer { error }) }
                if *session == sb && *error == code::LEAVE
        )));
        assert!(net.nodes[a].saw(|e| matches!(e, Event::Closed { session, .. } if *session == sa)));
        net.run_for(SEC_NS);
        for n in [a, b] {
            let Answer::Node(ns) = net.nodes[n].ep.query(Query::Node) else {
                panic!()
            };
            assert_eq!(ns.sessions, 0);
        }
        // A stale session name is refused.
        assert_eq!(
            net.nodes[a]
                .cmd(net.now, Command::Close { session: sa, error: 0 })
                .err(),
            Some(CommandError::NoSession)
        );
    });
}

#[test]
fn a_node_does_not_dial_itself_and_a_dial_needs_a_route() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let a = net.add(1);
        let (me, addr, now) = (net.nodes[a].node, net.nodes[a].addr, net.now);
        let r = net.nodes[a].connect(now, me, ALPN_A, addr, Role::Other);
        assert_eq!(r.err(), Some(CommandError::Refused));
        net.nodes[a].service(now);
        assert!(net.nodes[a].saw(|e| matches!(
            e,
            Event::ConnectFailed {
                reason: ConnectFailure::Refused,
                ..
            }
        )));
        let other = vinc_crypto::NodeId {
            alg: vinc_crypto::IdentityAlg::Ed25519,
            bytes: [9; 32],
        };
        let v6: std::net::SocketAddr = "[::1]:1".parse().unwrap();
        assert_eq!(
            net.nodes[a].connect(now, other, ALPN_A, v6, Role::Other).err(),
            Some(CommandError::NoRoute)
        );
        assert_eq!(
            net.nodes[a].connect(now, other, b"", addr, Role::Other).err(),
            Some(CommandError::BadAlpn)
        );
    });
}
