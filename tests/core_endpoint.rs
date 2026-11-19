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

use pinc_core::{
    Answer, Command, CommandError, ConnectFailure, EndReason, Event, IfaceEvent, IfaceId, Query, Role, SessionId,
    StateError, Value, state_len,
};
use pinc_tests::*;
use pinc_transport::conn::{CloseReason, code};

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

/// The largest datagram each of two nodes sends while 2 MiB cross a path of `delay` one way, when both interfaces
/// carry datagrams of up to `mtu` bytes: `(dialer, acceptor)`.
fn largest_datagrams(mtu: u16, delay: u64) -> (usize, usize) {
    let mut net = CoreNet::new(delay);
    let now = net.now;
    for tag in [1u8, 2] {
        let addr: std::net::SocketAddr = ([10, 0, 0, tag], 4433).into();
        net.nodes
            .push(TNode::with_mtu(tag, addr, now, pinc_crypto::IdentityAlg::Ed25519, mtu));
    }
    let (a, b) = (0, 1);
    let (sa, _sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
    // Time for the datagram size probes of both ends.
    net.run_for(3 * SEC_NS);
    let data = pattern(2 << 20, 9);
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
    let end = now + 60 * SEC_NS;
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
    let largest = |i: usize| net.nodes[i].sent.iter().map(|s| s.2).max().unwrap_or(0);
    (largest(a), largest(b))
}

#[test]
fn a_wide_interface_on_a_fast_path_carries_jumbo_datagrams_from_both_ends() {
    big_stack(|| {
        // A round trip of half a millisecond and interfaces of 9000 bytes: both ends probe and use the large size,
        // the acceptor too, whose path the endpoint learned by receiving on it.
        let (dialer, acceptor) = largest_datagrams(9000, MS_NS / 4);
        assert!(dialer > 8000, "the dialer's largest datagram was {dialer}");
        assert!(acceptor > 8000, "the acceptor's largest datagram was {acceptor}");
        // The default interface never carries one.
        let (dialer, acceptor) = largest_datagrams(1500, MS_NS / 4);
        assert!(
            dialer <= 1452 && acceptor <= 1452,
            "{dialer} and {acceptor} on a 1500 byte interface"
        );
        // Nor does a path that is not a low-latency one.
        let (dialer, acceptor) = largest_datagrams(9000, 5 * MS_NS);
        assert!(
            dialer <= 1452 && acceptor <= 1452,
            "{dialer} and {acceptor} at a 10 ms round trip"
        );
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
        for i in 0..pinc_core::MAX_ALPNS as u8 {
            let _ = net.nodes[b].ep.register_alpn(&[b'x', i]);
        }
        assert!(!net.nodes[b].ep.register_alpn(b"overflow"));
    });
}

#[test]
fn a_node_serves_the_hub_protocol_and_four_application_protocols() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let b = net.add(2);
        net.nodes[b].ep.unregister_alpn(ALPN_B);
        let names: [&[u8]; 5] = [b"pinc/hub", b"/app/a", b"/app/b", b"/app/c", b"/app/d"];
        assert!(names.iter().all(|n| net.nodes[b].ep.register_alpn(n)));
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
        let other = pinc_crypto::NodeId {
            alg: pinc_crypto::IdentityAlg::Ed25519,
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

#[test]
fn a_session_goes_on_when_its_node_changes_address() {
    big_stack(|| {
        for gap_ms in [0u64, 200, 1_150, 2_000] {
            let mut net = CoreNet::new(5 * MS_NS);
            let (a, b) = (net.add(1), net.add(2));
            let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
            net.run_for(2 * SEC_NS);
            // The node moves: its link goes down, its address changes at once, and after the gap the link returns on
            // the new address. The old address reaches nobody.
            let new: std::net::SocketAddr = ([10, 0, 9, 1], 4433).into();
            let old = net.nodes[a].addr;
            net.nodes[a].addr = new;
            net.loss = Some(Box::new(move |from, _, _| from == old));
            let now = net.now;
            net.nodes[a].ep.iface_event(now, IfaceId(0), IfaceEvent::Down);
            net.run_for(gap_ms * MS_NS);
            let now = net.now;
            net.nodes[a]
                .ep
                .iface_event(now, IfaceId(0), IfaceEvent::AddrChange(new));
            net.nodes[a].ep.iface_event(now, IfaceId(0), IfaceEvent::Up);
            // Data in both directions after the change arrives within a few round trips.
            open_and_send(&mut net, a, sa, b"after");
            let t0 = net.now;
            let ok = net.run(t0 + 6 * SEC_NS, |n| !n.nodes[b].fin.is_empty());
            assert!(ok, "gap {gap_ms} ms: nothing from the moved node");
            open_and_send(&mut net, b, sb, b"back");
            let t0 = net.now;
            let ok = net.run(t0 + 6 * SEC_NS, |n| !n.nodes[a].fin.is_empty());
            assert!(ok, "gap {gap_ms} ms: nothing to the moved node");
        }
    });
}

/// The addresses the active path of session `sa` of node `a` runs between: local, then remote.
fn route_of(net: &mut CoreNet, a: usize, sa: SessionId) -> Option<(std::net::SocketAddr, std::net::SocketAddr)> {
    let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(sa)) else {
        panic!()
    };
    st.route
}

#[test]
fn a_standby_path_that_leaves_from_the_old_address_moves_with_the_address() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let b2: std::net::SocketAddr = ([10, 0, 0, 22], 4433).into();
        net.nodes[b].extra.push(b2);
        let (sa, _sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let now = net.now;
        net.nodes[a].cmd(now, Command::Punch { session: sa, addr: b2 }).unwrap();
        net.run_for(2 * SEC_NS);
        let b1 = net.nodes[b].addr;
        let route = route_of(&mut net, a, sa);
        assert_eq!(
            route,
            Some((net.nodes[a].addr, b1)),
            "the active path runs to the peer's first address"
        );
        // The node moves. Each path of the session that left from the old address now leaves from the new one, with
        // its state: the active path stays the active one and the standby path keeps probing its own address.
        let new: std::net::SocketAddr = ([10, 0, 9, 1], 4433).into();
        let old = net.nodes[a].addr;
        net.nodes[a].addr = new;
        let (from_old, to_b2) = (
            std::rc::Rc::new(std::cell::Cell::new(0u32)),
            std::rc::Rc::new(std::cell::Cell::new(0u32)),
        );
        let (old_count, b2_count) = (from_old.clone(), to_b2.clone());
        net.loss = Some(Box::new(move |from, to, _| {
            if from == old {
                old_count.set(old_count.get() + 1);
            }
            if from == new && to == b2 {
                b2_count.set(b2_count.get() + 1);
            }
            from == old
        }));
        let now = net.now;
        net.nodes[a].ep.iface_event(now, IfaceId(0), IfaceEvent::Down);
        net.nodes[a]
            .ep
            .iface_event(now, IfaceId(0), IfaceEvent::AddrChange(new));
        net.nodes[a].ep.iface_event(now, IfaceId(0), IfaceEvent::Up);
        assert_eq!(
            route_of(&mut net, a, sa),
            Some((new, b1)),
            "the active path stays the active one and leaves from the new address"
        );
        open_and_send(&mut net, a, sa, b"after");
        net.run_for(8 * SEC_NS);
        assert_eq!(
            from_old.get(),
            0,
            "no datagram leaves from the old address after the change"
        );
        assert!(to_b2.get() >= 1, "the standby path leaves from the new address too");
    });
}

#[test]
fn after_an_address_change_the_session_leaves_from_the_new_address_at_once() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(2 * SEC_NS);
        let new: std::net::SocketAddr = ([10, 0, 9, 1], 4433).into();
        let old = net.nodes[a].addr;
        net.nodes[a].addr = new;
        // Every datagram that still leaves from the old address is counted, and lost.
        let from_old = std::rc::Rc::new(std::cell::Cell::new(0u32));
        let counter = from_old.clone();
        net.loss = Some(Box::new(move |from, _, _| {
            if from == old {
                counter.set(counter.get() + 1);
            }
            from == old
        }));
        let now = net.now;
        net.nodes[a].ep.iface_event(now, IfaceId(0), IfaceEvent::Down);
        net.nodes[a]
            .ep
            .iface_event(now, IfaceId(0), IfaceEvent::AddrChange(new));
        net.nodes[a].ep.iface_event(now, IfaceId(0), IfaceEvent::Up);
        open_and_send(&mut net, a, sa, b"after");
        let t0 = net.now;
        assert!(
            net.run(t0 + 6 * SEC_NS, |n| !n.nodes[b].fin.is_empty()),
            "nothing from the moved node"
        );
        assert_eq!(
            from_old.get(),
            0,
            "no datagram leaves from the old address after the change"
        );
    });
}

#[test]
fn an_ended_endpoint_gives_its_table_back_with_every_session_closed() {
    use pinc_core::{Endpoint, EndpointConfig};
    use pinc_crypto::Drbg;
    use pinc_security::{KeyHandle, LocalIdentity};

    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        net.connect_pair(a, b, ALPN_A, Role::Other);
        net.connect_pair(a, b, ALPN_B, Role::Other);
        assert!(net.nodes[a].ep.sessions().count() >= 2);
        let node = net.nodes.swap_remove(a);
        let TNode { ep, prov, kp, .. } = node;
        let table = (*ep).into_slots().expect("every slot has its memory back");
        // The same memory runs another endpoint, with no session in it.
        let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
        let ep2: CoreEp = Endpoint::new(
            net.now,
            prov,
            Drbg::new(&[9; 32]),
            identity,
            EndpointConfig::new(1),
            table,
        );
        assert_eq!(ep2.sessions().count(), 0);
        let again = ep2.into_slots();
        assert!(again.is_some());
    });
}

/// An endpoint that owns its table holds the memory of the most sessions it has had at once, not of every slot.
#[test]
fn an_owned_endpoint_makes_the_memory_of_a_slot_when_the_slot_is_first_taken() {
    use pinc_core::{Endpoint, EndpointConfig};
    use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
    use pinc_security::{Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftPrekeys};
    use pinc_transport::stream::NoSource;

    let identity = |tag: u8| {
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[tag; 32]).unwrap();
        LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap()
    };
    let mut ep: Box<Endpoint<'static, 'static, Software, NoSource, CN, CC, CF, CNP, CK, CD, CPK, CTK, CCT>> =
        Endpoint::new_owned(
            SEC_NS,
            Software,
            Drbg::new(&[3; 32]),
            identity(1),
            EndpointConfig::new(7),
            CHUNKS_PER_CONN,
        );
    let mut drbg = Drbg::new(&[4; 32]);
    let mut env = Env {
        provider: &Software,
        now: SEC_NS,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    ep.set_prekey(prekeys.acquire(&mut env).unwrap());
    assert!(ep.register_alpn(ALPN_A));
    ep.add_iface("10.0.0.1:4000".parse().unwrap()).unwrap();
    assert_eq!(
        ep.backed_slots(),
        0,
        "an endpoint that had no session holds no session memory"
    );

    let dial = |ep: &mut Endpoint<'static, 'static, Software, NoSource, CN, CC, CF, CNP, CK, CD, CPK, CTK, CCT>,
                now: u64,
                tag: u8| {
        let to = [format!("10.0.0.{tag}:4000").parse().unwrap()];
        let rep = ep
            .command(
                now,
                Command::Connect {
                    node: identity(tag).node_id(),
                    alpn: ALPN_A,
                    addrs: &to,
                    role: Role::Other,
                },
            )
            .unwrap();
        let Value::Session(s) = rep.value else {
            panic!("not a session")
        };
        s
    };
    let a = dial(&mut ep, SEC_NS, 2);
    assert_eq!(ep.backed_slots(), 1);
    let _b = dial(&mut ep, SEC_NS, 3);
    assert_eq!(ep.backed_slots(), 2);

    // A session ends: its slot keeps the memory, and the next session runs in it.
    ep.command(SEC_NS, Command::Close { session: a, error: 0 }).unwrap();
    let mut now = SEC_NS;
    let mut out = [0u8; 1500];
    for _ in 0..10_000 {
        while ep.poll_transmit(now, &mut out).is_some() {}
        while ep.poll_event().is_some() {}
        if ep.node_stats().sessions == 1 {
            break;
        }
        now = ep.poll_timeout().unwrap().max(now);
        ep.handle_timeout(now);
    }
    assert_eq!(ep.node_stats().sessions, 1, "the closed session left the table");
    assert_eq!(ep.backed_slots(), 2);
    let _c = dial(&mut ep, now, 4);
    assert_eq!(ep.backed_slots(), 2, "the freed slot's memory serves the next session");
    let _d = dial(&mut ep, now, 5);
    assert_eq!(ep.backed_slots(), 3);

    // The table grows to its bound and no further.
    for tag in 6..=10 {
        dial(&mut ep, now, tag);
    }
    assert_eq!((ep.node_stats().sessions, ep.backed_slots()), (CK, CK));
    let to = ["10.0.0.11:4000".parse().unwrap()];
    let full = ep.command(
        now,
        Command::Connect {
            node: identity(11).node_id(),
            alpn: ALPN_A,
            addrs: &to,
            role: Role::Other,
        },
    );
    assert!(full.is_err(), "a ninth session has no slot: {full:?}");
    assert_eq!(ep.backed_slots(), CK);
}

#[test]
fn a_dial_refused_for_a_full_table_keeps_the_ticket_for_the_next_dial() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        let tickets = net.nodes[a].ep.tickets().len();
        assert!(tickets >= 1, "no ticket received");
        let now = net.now;
        net.nodes[a].cmd(now, Command::Close { session: sa, error: 0 }).unwrap();
        net.run_for(SEC_NS);
        let filler = net.fill_table(a);
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let full = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other);
        assert_eq!(full.err(), Some(CommandError::Full));
        assert_eq!(
            net.nodes[a].ep.tickets().len(),
            tickets,
            "the refused dial spent the ticket"
        );

        net.nodes[a]
            .cmd(
                now,
                Command::Close {
                    session: filler[0],
                    error: 0,
                },
            )
            .unwrap();
        assert!(net.run(now + 10 * SEC_NS, |n| n.nodes[a].ep.node_stats().sessions
            < filler.len()));
        let now = net.now;
        // The ACP answer is cached, so the dial reports Connected at once, before the resumption is known; the ticket
        // taken by the dial is what shows it resumed.
        net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        assert_eq!(
            net.nodes[a].ep.tickets().len(),
            tickets - 1,
            "the dial did not use the ticket"
        );
        assert!(net.run(now + 5 * SEC_NS, |n| n.nodes[a].ep.tickets().len() == tickets));
    });
}
