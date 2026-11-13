//! The endpoint-level timing rules: keepalives by role, the node round trips and what they change (thin
//! classification, the handshake floor, the first resend, the probe timeout seed), the short Initial rule, the carrier
//! pulse, and the acknowledgement cadence.
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

#[path = "core_timing_common.rs"]
mod common;

use std::net::SocketAddr;

use common::{S, dial, flights, is_connected, message_type, sends};
use vinc_core::{Answer, Command, ConnectFailure, EndReason, Event, IfaceEvent, IfaceId, Query, Role, Value};
use vinc_tests::*;
use vinc_transport::conn::CloseReason;

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

/// A quiet hub session at 130 s idle: `writer` (0 the dialer, 1 the acceptor) sends one 1 KiB frame. Returns the sends
/// of the dialer and of the acceptor after it, as seconds after the write.
fn quiet_session_after_a_frame(writer: usize) -> (Vec<f64>, Vec<f64>) {
    big_stack(move || {
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
        net.run_for(130 * S);
        let at = net.now;
        let (n, session) = if writer == 0 { (a, sa) } else { (b, sb) };
        let Value::Stream(stream) = net.nodes[n]
            .cmd(at, Command::OpenStream { session, bidi: true })
            .unwrap()
            .value
        else {
            panic!("no stream")
        };
        net.nodes[n]
            .cmd(
                at,
                Command::Write {
                    session,
                    stream,
                    data: &[7u8; 1024],
                },
            )
            .unwrap();
        net.run_for(170 * S);
        (sends(&net, a, at, 0.5, 170.0), sends(&net, b, at, 0.5, 170.0))
    })
}

#[test]
fn data_from_the_acceptor_does_not_arm_the_keepalive_of_a_quiet_session() {
    let (dialer, acceptor) = quiet_session_after_a_frame(1);
    // The dialer keeps its 60 s schedule after data it only received.
    assert!((2..=4).contains(&dialer.len()), "{dialer:?}");
    assert!(
        dialer.windows(2).all(|g| (g[1] - g[0] - 60.0).abs() < 1.0),
        "{dialer:?}"
    );
    // The acceptor's own write does not make it ping: each of its sends answers a datagram of the dialer.
    for t in acceptor {
        assert!(
            dialer.iter().any(|p| t >= *p && t - *p < 0.1) || t < 0.6,
            "the accepting side sent on its own at {t}"
        );
    }
}

#[test]
fn a_dialers_own_frame_arms_the_five_second_keepalive_of_a_quiet_session() {
    let (dialer, _) = quiet_session_after_a_frame(0);
    let early: Vec<f64> = dialer.iter().copied().filter(|t| *t < 20.0).collect();
    assert!(early.len() >= 3, "{dialer:?}");
    assert!(early.windows(2).all(|g| (g[1] - g[0] - 5.0).abs() < 0.5), "{dialer:?}");
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
fn a_ping_command_sends_one_acknowledgement_eliciting_packet_at_once_and_an_idle_session_sends_nothing() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Hub);
        net.run_for(3 * S);
        let sent = |net: &CoreNet| match net.nodes[a].ep.query(Query::Stats(sa)) {
            Answer::Stats(s) => s.transport.packets_sent,
            _ => panic!("no session"),
        };
        let idle = sent(&net);
        // The sessions' own 5 s keepalives fall 2 s on, a dialer that acknowledges every 4th packet one of them at
        // 35 ms after the other end's: the window stays clear of them.
        net.run_for(S);
        assert_eq!(sent(&net), idle, "an idle session sends nothing");
        let now = net.now;
        net.nodes[a].cmd(now, Command::Ping { session: sa }).unwrap();
        net.run_for(S / 10);
        assert_eq!(sent(&net), idle + 1, "the ping left in one packet");
        net.run_for(S * 8 / 10);
        assert_eq!(sent(&net), idle + 1, "and only one");
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
fn a_resend_is_the_short_initial_while_udp_was_heard_lately_whatever_the_first_flight_was() {
    big_stack(|| {
        // Node a had a session with b and closed it `idle` ns ago, then dials b (known to cache its prekey) or c (never
        // dialed) while everything sent to the target is lost. Resends go out at 0.5, 1.5, 3.5, 7.5 and 15.5 s. The idle
        // time is longer than the 30 s access answer of b, so the dial is not reported early and not ended early.
        let resends = |again: bool, idle: u64| {
            let mut net = CoreNet::new(10 * MS_NS);
            net.capture = true;
            let (a, b, c) = (net.add(1), net.add(2), net.add(3));
            let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
            let t = net.now;
            net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
            net.run_for(idle);
            let (peer, now) = (net.nodes[b].node, net.now);
            while net.nodes[a].ep.tickets().take(&peer, ALPN_A, now).is_some() {}
            let target = if again { b } else { c };
            let to = net.nodes[target].addr;
            net.loss = Some(Box::new(move |_, dst, _| dst == to));
            let marker = net.captured.len();
            dial(&mut net, a, target, ALPN_A, Role::Other);
            net.run_for(16 * S);
            flights(&net, marker, a, target)
        };
        // A full first flight (c was never dialed) with UDP heard lately: the resends are short, the third and the sixth
        // send carry the full prekey.
        assert_eq!(resends(false, 31 * S), [1, 2, 1, 2, 2, 1]);
        // A short first flight (b caches the prekey): the same schedule.
        assert_eq!(resends(true, 31 * S), [2, 2, 1, 2, 2, 1]);
        // After 90 s without hearing a UDP path every send is a full Initial.
        assert_eq!(resends(false, 100 * S), [1, 1, 1, 1, 1, 1]);
    });
}

/// Node a had a session with b and closed it; b restarted and lost the prekeys it cached, so it rejects the short
/// Initial of a's next dial, and nothing it sends after its first reject reaches a. Returns the net with the dial
/// started, the nodes and the number of datagrams captured before it.
fn rejected_dial() -> (CoreNet, usize, usize, usize) {
    let mut net = CoreNet::new(10 * MS_NS);
    net.capture = true;
    let (a, b) = (net.add(1), net.add(2));
    let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
    let t = net.now;
    net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
    // Longer than the 30 s access answer of b, so the dial is not reported early and not ended early.
    net.run_for(31 * S);
    let (peer, now) = (net.nodes[b].node, net.now);
    while net.nodes[a].ep.tickets().take(&peer, ALPN_A, now).is_some() {}
    let b_addr = net.nodes[b].addr;
    net.nodes[b] = TNode::new(2, b_addr, now);
    let passed = std::rc::Rc::new(std::cell::Cell::new(false));
    net.loss = Some(Box::new(move |from, _, d| {
        if from != b_addr || message_type(d) != Some(3) {
            return from == b_addr;
        }
        passed.replace(true)
    }));
    let marker = net.captured.len();
    dial(&mut net, a, b, ALPN_A, Role::Other);
    (net, a, b, marker)
}

#[test]
fn a_prekey_reject_sends_the_full_initial_once_and_the_resends_stay_short() {
    big_stack(|| {
        let (mut net, a, b, marker) = rejected_dial();
        // The reject answers the short Initial; the full one follows at once, not at the next timer.
        net.run_for(100 * MS_NS);
        assert_eq!(flights(&net, marker, a, b), [2, 1]);
        // The resends at 0.5, 1.5, 3.5, 7.5 and 15.5 s stay short except the third and the sixth send.
        net.run_for(16 * S);
        assert_eq!(flights(&net, marker, a, b), [2, 1, 2, 1, 2, 2, 1]);
    });
}

#[test]
fn a_prekey_reject_makes_the_next_dial_start_with_the_full_initial() {
    big_stack(|| {
        let (mut net, a, b, _) = rejected_dial();
        // The dial times out; a UDP path was heard moments ago, but the reject dropped what the node knew of the
        // peer's prekey cache, so the next first flight is the full Initial.
        net.run_for(36 * S);
        assert!(net.nodes[a].saw(|e| matches!(e, Event::ConnectFailed { .. })));
        net.loss = None;
        let marker = net.captured.len();
        dial(&mut net, a, b, ALPN_A, Role::Other);
        net.run_for(S);
        assert_eq!(
            flights(&net, marker, a, b)[0],
            1,
            "the dropped entry still gave a short Initial"
        );
    });
}

#[test]
fn the_initial_after_an_unanswered_hello_is_short_for_a_peer_known_to_cache_the_prekey() {
    big_stack(|| {
        // Node a had a session with b, which gave it a ticket and caches its prekey, and closed it a while ago. The idle
        // time is longer than the 30 s access answer of b, so the dial is not reported early and not ended early.
        let mut net = CoreNet::new(10 * MS_NS);
        net.capture = true;
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        // The ticket arrives a moment after the session is open.
        net.run_for(S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
        net.run_for(31 * S);
        // The Hello is sent at 0 and 0.5 s; the third send, at 1.5 s, is the Initial that takes its place.
        let b_addr = net.nodes[b].addr;
        net.loss = Some(Box::new(move |_, to, _| to == b_addr));
        let marker = net.captured.len();
        dial(&mut net, a, b, ALPN_A, Role::Other);
        net.run_for(1600 * MS_NS);
        assert_eq!(flights(&net, marker, a, b), [6, 6, 2]);
    });
}

#[test]
fn a_link_return_resends_a_dial_still_in_its_handshake_at_once() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        // The first flight is lost; the link goes down 100 ms after the dial and returns 100 ms later.
        net.loss = Some(Box::new(|_, _, _| true));
        let t0 = net.now;
        dial(&mut net, a, b, ALPN_A, Role::Other);
        net.run_for(100 * MS_NS);
        let now = net.now;
        net.nodes[a].ep.iface_event(now, IfaceId(0), IfaceEvent::Down);
        net.run_for(100 * MS_NS);
        net.loss = None;
        let now = net.now;
        net.nodes[a].ep.iface_event(now, IfaceId(0), IfaceEvent::Up);
        net.run_for(5 * MS_NS);
        let resent = sends(&net, a, t0, 0.15, 0.5);
        assert!(
            resent.first().is_some_and(|t| *t < 0.21),
            "the flight waited for its resend timer: {resent:?}"
        );
        assert!(net.run(t0 + S, |n| n.nodes[a].saw(is_connected)));
        assert!(net.now - t0 < 300 * MS_NS, "connected at {} ms", (net.now - t0) / MS_NS);
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
        // An answer that arrived is also a datagram heard on the active path; a ping that left is not.
        let before = stats(&net).heard;
        net.nodes[a]
            .cmd(
                now,
                Command::Pulse {
                    session: sa,
                    sent: false,
                },
            )
            .unwrap();
        assert!(
            before < now && stats(&net).heard == now,
            "heard {before} then {}",
            stats(&net).heard
        );
        // Handed back, the endpoint sends its own keepalive again.
        net.nodes[a]
            .cmd(net.now, Command::SetPulse { session: sa, on: false })
            .unwrap();
        let before = net.nodes[a].sent.len();
        net.run_for(30 * S);
        assert!(net.nodes[a].sent.len() > before, "the endpoint pinged again");
    });
}

#[test]
fn a_dialed_hub_session_acknowledges_every_fourth_packet() {
    big_stack(|| {
        // The acknowledgements the dialer sends for eight small packets (not bulk) that arrive 1 ms apart.
        let acks = |role: Role| {
            let mut net = CoreNet::new(5 * MS_NS);
            let (a, b) = (net.add(1), net.add(2));
            let (_, sb) = net.connect_pair(a, b, ALPN_A, role);
            net.run_for(3 * S);
            let t = net.now;
            let Value::Stream(id) = net.nodes[b]
                .cmd(
                    t,
                    Command::OpenStream {
                        session: sb,
                        bidi: false,
                    },
                )
                .unwrap()
                .value
            else {
                panic!("no stream")
            };
            let before = net.nodes[a].sent.len();
            for k in 0..8u8 {
                let t = net.now;
                net.nodes[b]
                    .cmd(
                        t,
                        Command::Write {
                            session: sb,
                            stream: id,
                            data: &[k; 100],
                        },
                    )
                    .unwrap();
                net.pump(b);
                net.run_for(MS_NS);
            }
            net.run_for(6 * MS_NS);
            net.nodes[a].sent.len() - before
        };
        assert_eq!((acks(Role::Hub), acks(Role::Other)), (2, 4));
    });
}

#[test]
fn an_endpoint_sends_the_first_handshake_flight_whole_by_default() {
    assert!(vinc_core::EndpointConfig::new(1).conn.flight_split);
}
