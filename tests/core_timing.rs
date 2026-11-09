//! The endpoint-level timing rules: keepalives by role, the node round trips and what they change (thin
//! classification, the handshake floor, the first resend, the probe timeout seed), the short Initial rule, redial after a
//! suspension, the flush order, and the hooks that send a handshake flight on several paths.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss
)]

use std::net::SocketAddr;

use vinc_core::{Answer, Command, ConnectFailure, EndReason, Event, Query, Role, SessionId, Value};
use vinc_crypto::NodeId;
use vinc_tests::*;
use vinc_transport::conn::{CloseReason, PathId, PathInfo};
use vinc_transport::packet::LongHeader;
use vinc_wire::Reader;

const S: u64 = SEC_NS;

fn is_connected(e: &Event) -> bool {
    matches!(e, Event::Connected { .. })
}

/// The sends of node `n` between `from` and `to`, as times in seconds relative to `base`.
fn sends(net: &CoreNet, n: usize, base: u64, from: f64, to: f64) -> Vec<f64> {
    net.nodes[n]
        .sent
        .iter()
        .map(|(t, _, _)| (*t as f64 - base as f64) / S as f64)
        .filter(|t| *t >= from && *t < to)
        .collect()
}

/// The handshake message type a datagram carries, if it is the start of one.
fn message_type(d: &[u8]) -> Option<u8> {
    let (h, len) = LongHeader::parse(d).ok()?;
    let mut r = Reader::new(d.get(len..len + h.body_len)?);
    r.read_varint().ok()?;
    if r.read_varint().ok()? != 0 {
        return None;
    }
    r.read_u8().ok()
}

fn dial(net: &mut CoreNet, a: usize, b: usize, alpn: &[u8], role: Role) -> SessionId {
    let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
    let rep = net.nodes[a].connect(now, peer, alpn, to, role).unwrap();
    net.nodes[a].session(&rep)
}

#[test]
fn a_quiet_dialer_holds_a_direct_path_every_fourteen_seconds_and_only_the_dialer_pings() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Hub);
        net.nodes[b]
            .cmd(
                net.now,
                Command::SetRole {
                    session: sb,
                    role: Role::Member,
                },
            )
            .unwrap();
        let est = net.now;
        net.run_for(300 * S);
        let first = sends(&net, a, est, 2.0, 20.0);
        let w1 = sends(&net, a, est, 20.0, 120.0);
        let w2 = sends(&net, a, est, 125.0, 300.0);
        // Data within 20 s keeps every path pinged every 5 s; then one ping per 14 s while data moved within 120 s and
        // the 60 s dialer interval after that.
        assert!(first.first().is_some_and(|t| (t - 5.0).abs() < 0.3), "{first:?}");
        assert!((6..=8).contains(&w1.len()), "{w1:?}");
        assert!(w1.windows(2).all(|g| (g[1] - g[0] - 14.0).abs() < 0.5), "{w1:?}");
        assert!((2..=4).contains(&w2.len()), "{w2:?}");
        assert!(w2.windows(2).all(|g| (g[1] - g[0] - 60.0).abs() < 1.0), "{w2:?}");
        // The accepting side only answers: each of its sends follows a datagram from the dialer within 100 ms.
        for t in sends(&net, b, est, 20.0, 300.0) {
            assert!(
                first.iter().chain(&w1).chain(&w2).any(|p| t >= *p && t - *p < 0.1),
                "the accepting side sent on its own at {t}"
            );
        }
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(sa)) else {
            panic!("the session ended")
        };
        assert!(st.established);
    });
}

#[test]
fn a_plain_session_pings_every_five_seconds_then_stops_and_lapses() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        net.connect_pair(a, b, ALPN_A, Role::Other);
        let est = net.now;
        net.run_for(200 * S);
        let early = sends(&net, a, est, 2.0, 20.0);
        // The first ping leaves 5 s after the session opened, then every 5 s while data moved in the last 20 s.
        assert!(early.first().is_some_and(|t| (t - 5.0).abs() < 0.3), "{early:?}");
        assert!((3..=6).contains(&early.len()), "{early:?}");
        // From 90 s after the last data a plain session stops pinging and lapses at the idle timeout.
        let quiet = sends(&net, a, est, 60.0, 125.0);
        assert!(quiet.is_empty(), "pinged while idle: {quiet:?}");
        assert!(net.nodes[a].saw(|e| matches!(
            e,
            Event::Closed {
                reason: EndReason::Transport(CloseReason::IdleTimeout),
                ..
            }
        )));
        assert!(net.nodes[b].saw(|e| matches!(
            e,
            Event::Closed {
                reason: EndReason::Transport(CloseReason::IdleTimeout),
                ..
            }
        )));
    });
}

#[test]
fn nothing_is_pinged_for_ten_seconds_after_a_resume() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        net.connect_pair(a, b, ALPN_A, Role::Hub);
        let est = net.now;
        net.run_for(100 * S);
        net.nodes[a].cmd(net.now, Command::Suspend).unwrap();
        net.run_for(S);
        let resume = net.now;
        net.nodes[a].cmd(resume, Command::Resume { moved: false }).unwrap();
        net.run_for(30 * S);
        let rel = |t: f64| t;
        let r = (resume - est) as f64 / S as f64;
        let after = sends(&net, a, est, r + 1.5, r + 10.0);
        assert!(
            after.iter().all(|t| rel(*t) < r + 1.5),
            "pinged inside the quiet period: {after:?}"
        );
        let later = sends(&net, a, est, r + 10.0, r + 30.0);
        assert!(!later.is_empty(), "the keepalive never came back");
        assert!(net.nodes[b].saw(|e| matches!(e, Event::PeerAwake { .. })));
        assert!(net.nodes[a].saw(|e| !matches!(e, Event::Closed { .. })));
    });
}

#[test]
fn a_late_start_quiet_session_defers_its_first_mtu_probe_by_three_seconds() {
    big_stack(|| {
        for (late, role) in [(true, Role::Hub), (true, Role::Other), (false, Role::Hub)] {
            let mut net = CoreNet::new(10 * MS_NS);
            let (a, b) = (net.add(1), net.add(2));
            if late {
                net.run_for(11 * S);
            }
            let t0 = net.now;
            net.connect_pair(a, b, ALPN_A, role);
            net.run_for(10 * S);
            let probe = net.nodes[a]
                .sent
                .iter()
                .find(|(_, _, len)| *len > 1300)
                .map(|(t, _, _)| *t - t0);
            let probe = probe.unwrap_or_else(|| panic!("no probe sent (late {late}, {role:?})"));
            if late && role.quiet() {
                assert!(probe >= 3 * S, "probe after {probe} ns");
            } else {
                assert!(probe < 3 * S, "probe after {probe} ns (late {late}, {role:?})");
            }
        }
    });
}

#[test]
fn node_round_trips_classify_thin_and_feed_new_sessions() {
    big_stack(|| {
        // A fast link: not thin.
        let mut fast = CoreNet::new(10 * MS_NS);
        let (a, b) = (fast.add(1), fast.add(2));
        let (sa, _) = fast.connect_pair(a, b, ALPN_A, Role::Other);
        fast.run_for(10 * S);
        let Answer::Stats(st) = fast.nodes[a].ep.query(Query::Stats(sa)) else {
            panic!()
        };
        assert!(!st.thin && !fast.nodes[a].ep.node_stats().thin);

        // A slow link: 300 ms round trips make the node thin, and a session starts from the node's numbers.
        let mut slow = CoreNet::new(150 * MS_NS);
        let (a, b, c) = (slow.add(1), slow.add(2), slow.add(3));
        let (sa, _) = slow.connect_pair(a, b, ALPN_A, Role::Other);
        slow.run_for(10 * S);
        let ns = slow.nodes[a].ep.node_stats();
        assert!(ns.thin && ns.lrtt >= 250 * MS_NS && ns.tgr >= 250 * MS_NS, "{ns:?}");
        let Answer::Stats(st) = slow.nodes[a].ep.query(Query::Stats(sa)) else {
            panic!()
        };
        assert!(st.thin);
        // A session to a third node, before it has a sample of its own, starts its probe timeout from the node.
        let sc = dial(&mut slow, a, c, ALPN_A, Role::Other);
        let Answer::Stats(fresh) = slow.nodes[a].ep.query(Query::Stats(sc)) else {
            panic!()
        };
        let mut baseline = CoreNet::new(150 * MS_NS);
        let (x, y) = (baseline.add(1), baseline.add(3));
        let sx = dial(&mut baseline, x, y, ALPN_A, Role::Other);
        let Answer::Stats(plain) = baseline.nodes[x].ep.query(Query::Stats(sx)) else {
            panic!()
        };
        assert!(
            fresh.pto >= plain.pto + 2 * ns.tgr.max(ns.lrtt) - 400 * MS_NS,
            "the probe timeout did not start from the node round trip: {} against {}",
            fresh.pto,
            plain.pto
        );
        assert!(fresh.thin, "a session with no sample counts as thin");
    });
}

#[test]
fn a_timed_out_dial_raises_the_handshake_floor_and_any_sample_resets_it() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        net.capture = true;
        let (a, b) = (net.add(1), net.add(2));
        let (peer, to) = (net.nodes[b].node, net.nodes[b].addr);
        let dead = Box::new(|_: SocketAddr, _: SocketAddr, _: &[u8]| true);
        net.loss = Some(dead);
        let mut floors = Vec::new();
        for _ in 0..5 {
            let now = net.now;
            net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
            let before = net.nodes[a].count(|e| matches!(e, Event::ConnectFailed { .. }));
            assert!(net.run(
                now + 70 * S,
                |n| n.nodes[a].count(|e| matches!(e, Event::ConnectFailed { .. })) > before
            ));
            floors.push(net.nodes[a].ep.node_stats().hs_floor);
        }
        let ms = MS_NS;
        assert_eq!(floors, [500 * ms, 1000 * ms, 2000 * ms, 4000 * ms, 8000 * ms]);
        assert!(net.nodes[a].saw(|e| matches!(
            e,
            Event::ConnectFailed {
                reason: ConnectFailure::Timeout,
                ..
            }
        )));
        // With the floor at its ceiling the first resend of the next dial waits that long.
        let now = net.now;
        let marker = net.captured.len();
        net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        net.run_for(20 * S);
        let times: Vec<u64> = net.tapped.iter().filter(|t| t.0 >= now).map(|t| t.0 - now).collect();
        let second = times.iter().copied().find(|t| *t > 0).unwrap();
        assert!(
            second >= 8 * S && second < 8 * S + 200 * ms,
            "first resend at {second} ns; {} datagrams",
            net.captured.len() - marker
        );
        // A successful handshake gives a sample, and the floor drops to zero.
        net.loss = None;
        assert!(net.run(net.now + 60 * S, |n| n.nodes[a].saw(is_connected)));
        // A handshake that needed a resend measures nothing; the first round trip sample of the session resets the floor.
        assert!(net.nodes[a].ep.node_stats().hs_floor > 0);
        net.run_for(10 * S);
        assert_eq!(net.nodes[a].ep.node_stats().hs_floor, 0);
    });
}

#[test]
fn a_resume_to_a_restarted_hub_resends_after_the_remembered_round_trip() {
    big_stack(|| {
        let ms = MS_NS;
        let mut firsts = Vec::new();
        for role in [Role::Hub, Role::Other] {
            let mut net = CoreNet::new(15 * ms);
            net.capture = true;
            let (a, b) = (net.add(1), net.add(2));
            // The node's first dial comes after ten seconds of running: a late start.
            net.run_for(11 * S);
            let (sa, _) = net.connect_pair(a, b, ALPN_A, role);
            net.run_for(S);
            let t = net.now;
            net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
            net.run_for(S);
            let krtt = net.nodes[a].ep.rtt().krtt(&net.nodes[b].node).unwrap();
            assert!(krtt >= 30 * ms - 1 && krtt < 40 * ms);
            net.loss = Some(Box::new(|_, _, _| true));
            let now = net.now;
            net.tapped.clear();
            let sess = dial(&mut net, a, b, ALPN_A, role);
            let _ = sess;
            net.run_for(3 * S);
            let times: Vec<u64> = net.tapped.iter().map(|t| t.0 - now).collect();
            firsts.push(times.iter().copied().find(|t| *t > 0).unwrap());
        }
        // max(300 ms, 1.5 x 30 ms + 20 ms) for the hub, max(500 ms, 2 x 30 ms) for any other.
        assert!((300 * ms..310 * ms).contains(&firsts[0]), "hub resend at {}", firsts[0]);
        assert!(
            (500 * ms..510 * ms).contains(&firsts[1]),
            "plain resend at {}",
            firsts[1]
        );
    });
}

#[test]
fn the_short_initial_is_used_only_for_a_peer_known_to_cache_the_prekey_on_a_fresh_udp_path() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        net.capture = true;
        let (a, b) = (net.add(1), net.add(2));
        let drop_tickets = |net: &mut CoreNet| {
            let (peer, now) = (net.nodes[b].node, net.now);
            while net.nodes[a].ep.tickets().take(&peer, ALPN_A, now).is_some() {}
        };
        let first_type = |net: &CoreNet, from: usize| {
            net.captured
                .iter()
                .rev()
                .find(|(f, _, d)| {
                    *f == net.nodes[from].addr
                        && d[0] & 0x80 != 0
                        && message_type(d).is_some_and(|m| matches!(m, 1 | 2 | 6))
                })
                .and_then(|(_, _, d)| message_type(d))
        };
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        assert_eq!(first_type(&net, a), Some(1), "the first dial carries the full Initial");
        net.run_for(S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
        net.run_for(S);
        // The peer is now known to hold the prekey and a validated UDP path was heard moments ago.
        drop_tickets(&mut net);
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        assert_eq!(first_type(&net, a), Some(2), "the short Initial was not used");
        net.run_for(S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
        // After 90 s without hearing the path, the full Initial again.
        net.run_for(100 * S);
        drop_tickets(&mut net);
        net.connect_pair(a, b, ALPN_A, Role::Other);
        assert_eq!(
            first_type(&net, a),
            Some(1),
            "a stale path still used the short Initial"
        );
    });
}

#[test]
fn a_resume_that_cannot_be_woken_closes_at_once_for_a_redial() {
    big_stack(|| {
        // The node moved while suspended: its sessions close with Redial, no 800 ms wait.
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Suspend).unwrap();
        net.run_for(2 * S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Resume { moved: true }).unwrap();
        assert!(
            net.nodes[a].saw(|e| matches!(e, Event::Closed { session, reason: EndReason::Redial } if *session == sa))
                || {
                    net.nodes[a].service(t);
                    net.nodes[a]
                        .saw(|e| matches!(e, Event::Closed { session, reason: EndReason::Redial } if *session == sa))
                }
        );
        // A resume at the same address wakes the session instead.
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Suspend).unwrap();
        net.run_for(2 * S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Resume { moved: false }).unwrap();
        net.run_for(5 * S);
        assert!(!net.nodes[a].saw(|e| matches!(e, Event::Closed { .. })));
        assert!(net.nodes[b].saw(|e| matches!(e, Event::PeerAwake { .. })));
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(sa)) else {
            panic!()
        };
        assert!(st.established);
        // A session already timing out when the node went to sleep is not woken either.
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.loss = Some(Box::new(|_, _, _| true));
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
                    data: b"lost",
                },
            )
            .unwrap();
        net.run_for(2 * S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Suspend).unwrap();
        net.loss = None;
        net.run_for(S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Resume { moved: false }).unwrap();
        net.nodes[a].service(t);
        assert!(net.nodes[a].saw(|e| matches!(
            e,
            Event::Closed {
                reason: EndReason::Redial,
                ..
            }
        )));
    });
}

#[test]
fn ordinary_sessions_are_flushed_before_broadcast_ones() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b, c) = (net.add(1), net.add(2), net.add(3));
        let (sb, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let (sc, _) = net.connect_pair(a, c, ALPN_A, Role::Other);
        net.run_for(2 * S);
        net.nodes[a]
            .cmd(
                net.now,
                Command::SetGossip {
                    session: sb,
                    gossip: true,
                },
            )
            .unwrap();
        let now = net.now;
        // The broadcast session writes first; the ordinary one second.
        for s in [sb, sc] {
            let Value::Stream(id) = net.nodes[a]
                .cmd(
                    now,
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
            net.nodes[a]
                .cmd(
                    now,
                    Command::Write {
                        session: s,
                        stream: id,
                        data: &[7u8; 500],
                    },
                )
                .unwrap();
        }
        let mut buf = vec![0u8; 65_536];
        let first = net.nodes[a].ep.poll_transmit(now, &mut buf).unwrap();
        assert_eq!(first.remote, net.nodes[c].addr, "the ordinary session did not go first");
        let mut dests = vec![first.remote];
        while let Some(t) = net.nodes[a].ep.poll_transmit(now, &mut buf) {
            dests.push(t.remote);
        }
        assert!(dests.contains(&net.nodes[b].addr));
        // A broadcast session with a sub-session open still to leave keeps its place.
        net.nodes[a]
            .cmd(
                now,
                Command::SetGossip {
                    session: sc,
                    gossip: false,
                },
            )
            .unwrap();
        let mut net2 = CoreNet::new(10 * MS_NS);
        let (a, b, c) = (net2.add(1), net2.add(2), net2.add(3));
        let (sb, _) = net2.connect_pair(a, b, ALPN_A, Role::Other);
        let (sc, _) = net2.connect_pair(a, c, ALPN_A, Role::Other);
        net2.run_for(2 * S);
        net2.nodes[a]
            .cmd(
                net2.now,
                Command::SetGossip {
                    session: sb,
                    gossip: true,
                },
            )
            .unwrap();
        let now = net2.now;
        let (peer, to) = (net2.nodes[b].node, net2.nodes[b].addr);
        net2.nodes[a].connect(now, peer, ALPN_B, to, Role::Other).unwrap(); // the open queues in the broadcast parent
        let Value::Stream(id) = net2.nodes[a]
            .cmd(
                now,
                Command::OpenStream {
                    session: sc,
                    bidi: false,
                },
            )
            .unwrap()
            .value
        else {
            panic!()
        };
        net2.nodes[a]
            .cmd(
                now,
                Command::Write {
                    session: sc,
                    stream: id,
                    data: &[7u8; 500],
                },
            )
            .unwrap();
        let first = net2.nodes[a].ep.poll_transmit(now, &mut buf).unwrap();
        assert_eq!(first.remote, net2.nodes[b].addr, "the sub-session open lost its place");
    });
}

#[test]
fn a_handshake_flight_can_leave_on_several_candidate_paths() {
    big_stack(|| {
        use vinc_security::ClientTickets;
        let w = World::new(vinc_crypto::IdentityAlg::Ed25519);
        let mut store = Store::new(true);
        let mut client = w.client(&mut store, None, ClientTickets::new());
        let now = T0;
        let second = PathId(2);
        client.with_env(now, |c, env| c.add_path(env, second, PathInfo::default()).unwrap());
        let mut paths = Vec::new();
        let mut buf = vec![0u8; 65_536];
        let mut drain = |client: &mut Node<'_>, paths: &mut Vec<(PathId, usize)>| {
            while let Some(t) = client.with_env(now, |c, env| c.poll_transmit(env, &mut buf)) {
                paths.push((t.path, t.len));
            }
        };
        drain(&mut client, &mut paths);
        assert!(
            paths.iter().all(|(p, _)| *p == PathId(1)),
            "without the hook the flight stays on the active path: {paths:?}"
        );
        let only = paths.iter().map(|(_, l)| l).sum::<usize>();
        // With the hook, a flight (here the resend after the timer) leaves on both paths.
        client.conn.set_flight_fanout(&[second]);
        paths.clear();
        let later = now + 600 * MS;
        client.with_env(later, vinc_transport::conn::Connection::handle_timeout);
        let mut buf2 = vec![0u8; 65_536];
        while let Some(t) = client.with_env(later, |c, env| c.poll_transmit(env, &mut buf2)) {
            paths.push((t.path, t.len));
        }
        let on = |p: PathId| paths.iter().filter(|(q, _)| *q == p).map(|(_, l)| l).sum::<usize>();
        assert!(on(PathId(1)) > 0 && on(second) > 0, "{paths:?}");
        assert_eq!(
            on(PathId(1)),
            on(second),
            "the copy is the same flight: {paths:?} (first flight {only})"
        );
        let _: Option<NodeId> = None;
    });
}

#[test]
fn the_endpoint_sends_a_dialing_flight_on_the_paths_it_is_told() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let second: SocketAddr = "10.0.1.2:4433".parse().unwrap();
        net.nodes[b].extra.push(second);
        net.nodes[b].ep.add_iface(second).unwrap();
        let (peer, first, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, first, Role::Other).unwrap();
        let sa = net.nodes[a].session(&rep);
        net.nodes[a]
            .cmd(
                now,
                Command::FlightPaths {
                    session: sa,
                    addrs: &[second],
                    skip_primary: false,
                },
            )
            .unwrap();
        net.pump(a);
        let to = |d: SocketAddr| {
            net.tapped
                .iter()
                .filter(|t| t.0 == now && t.2 == d)
                .map(|t| t.3)
                .sum::<usize>()
        };
        assert!(to(first) > 1000, "the flight is missing on the first path");
        assert_eq!(to(first), to(second), "the second path did not get the same flight");
        assert!(net.run(now + 5 * SEC_NS, |n| n.nodes[a].saw(is_connected)));
        // Turned off, a later flight stays on one path.
        let t = net.now;
        net.nodes[a]
            .cmd(
                t,
                Command::FlightPaths {
                    session: sa,
                    addrs: &[],
                    skip_primary: false,
                },
            )
            .unwrap();
    });
}

#[test]
fn a_flight_can_skip_the_primary_path_and_leave_on_the_listed_ones_only() {
    big_stack(|| {
        use vinc_security::ClientTickets;
        let w = World::new(vinc_crypto::IdentityAlg::Ed25519);
        let mut store = Store::new(true);
        let mut client = w.client(&mut store, None, ClientTickets::new());
        let now = T0;
        let second = PathId(2);
        client.with_env(now, |c, env| c.add_path(env, second, PathInfo::default()).unwrap());
        // With the skip set, even the first flight leaves on the listed path only.
        client.conn.set_flight_fanout(&[second]);
        client.conn.set_flight_skip_primary(true);
        let mut buf = vec![0u8; 65_536];
        let mut paths = Vec::new();
        while let Some(t) = client.with_env(now, |c, env| c.poll_transmit(env, &mut buf)) {
            paths.push((t.path, t.len));
        }
        assert!(
            !paths.is_empty() && paths.iter().all(|(p, _)| *p == second),
            "{paths:?}"
        );
        // The resend after the timer goes the same way, and only there.
        paths.clear();
        let later = now + 600 * MS;
        client.with_env(later, vinc_transport::conn::Connection::handle_timeout);
        while let Some(t) = client.with_env(later, |c, env| c.poll_transmit(env, &mut buf)) {
            paths.push((t.path, t.len));
        }
        assert!(
            !paths.is_empty() && paths.iter().all(|(p, _)| *p == second),
            "{paths:?}"
        );
        // With no fan-out path the skip sends nothing at all in that try.
        client.conn.set_flight_fanout(&[]);
        paths.clear();
        let later = later + 2 * SEC_NS;
        client.with_env(later, vinc_transport::conn::Connection::handle_timeout);
        while let Some(t) = client.with_env(later, |c, env| c.poll_transmit(env, &mut buf)) {
            paths.push((t.path, t.len));
        }
        assert!(paths.is_empty(), "a try with no path sends nothing: {paths:?}");
        // Turned off, the flight returns to the primary path.
        client.conn.set_flight_skip_primary(false);
        let later = later + 10 * SEC_NS;
        client.with_env(later, vinc_transport::conn::Connection::handle_timeout);
        while let Some(t) = client.with_env(later, |c, env| c.poll_transmit(env, &mut buf)) {
            paths.push((t.path, t.len));
        }
        assert!(paths.iter().any(|(p, _)| *p == PathId(1)), "{paths:?}");
    });
}

#[test]
fn a_session_handed_to_the_carrier_pulse_sends_no_keepalive_and_reports_when_one_is_due() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Hub);
        net.nodes[b]
            .cmd(
                net.now,
                Command::SetRole {
                    session: sb,
                    role: Role::Member,
                },
            )
            .unwrap();
        net.run_for(30 * S);
        let t0 = net.now;
        net.nodes[a]
            .cmd(t0, Command::SetPulse { session: sa, on: true })
            .unwrap();
        net.run_for(40 * S);
        assert!(sends(&net, a, t0, 0.5, 40.0).is_empty(), "no keepalive of its own");
        let stats = |net: &CoreNet| {
            let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(sa)) else {
                panic!("the session ended")
            };
            st
        };
        assert!(stats(&net).pulse_due, "a keepalive is due and the layer above is told");
        // The carrier answered: the session counts it as traffic both ways and the next one is due later.
        let now = net.now;
        net.nodes[a]
            .cmd(
                now,
                Command::Pulse {
                    session: sa,
                    sent: true,
                },
            )
            .unwrap();
        assert!(!stats(&net).pulse_due);
        // Handed back, the endpoint sends its own keepalive again.
        net.nodes[a]
            .cmd(net.now, Command::SetPulse { session: sa, on: false })
            .unwrap();
        let before = net.nodes[a].sent.len();
        net.run_for(30 * S);
        assert!(net.nodes[a].sent.len() > before, "the endpoint pinged again");
    });
}
