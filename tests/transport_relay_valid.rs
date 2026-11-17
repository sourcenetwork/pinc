//! A relay path is valid for as long as the session tracks it, so a session that establishes on another path keeps
//! the relay path it leaves validated: a dial sent through one relay and answered through another keeps the first
//! relay's path as a validated standby (pinged, chosen again when the active path fails), while a direct path it
//! leaves is validated again only by a challenge.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use vinc_core::{Answer, Command, Event, Query, Role, Value, relay_addr};
use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{PathId, PathInfo};
use vinc_transport::recovery::PathKind;

/// The path the Reply comes back on.
const OTHER: PathId = PathId(9);

fn relay() -> PathInfo {
    PathInfo {
        kind: PathKind::Relay,
        ..PathInfo::default()
    }
}

/// Run `net` until the responder has sent its Reply, which the dialer never gets over the link, and return the
/// datagrams of it. The dialer's own first flight goes out on its path 1.
fn reply_datagrams(net: &mut Net<'_, '_>) -> Vec<Vec<u8>> {
    net.link.route(PathId(1)).ba.p.loss_ppm = 1_000_000;
    let sent: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
    let sink = Rc::clone(&sent);
    net.on_tx = Some(Box::new(move |is_a, d, _| {
        if !is_a {
            sink.borrow_mut().push(d.to_vec());
        }
    }));
    let until = net.now + 100 * MS;
    net.run(until, |_| false);
    net.on_tx = None;
    let got = sent.borrow().clone();
    assert!(!got.is_empty(), "the responder sent no Reply");
    assert!(!net.a.conn.is_connected());
    got
}

/// Hand `datagrams` to the dialing side as arriving on `path`, in order.
fn deliver_on(net: &mut Net<'_, '_>, path: PathId, datagrams: &[Vec<u8>]) {
    let now = net.now;
    for d in datagrams {
        let mut d = d.clone();
        let _ = net.a.with_env(now, |c, env| c.handle_datagram(env, path, &mut d));
    }
    net.a.service(now);
}

/// A dial on path 1 of kind `dial`, with the path `OTHER` added when `other` names its info (else the dial does not
/// hold it and learns it from the Reply), whose Reply has come back on `OTHER`; runs `then` on the established
/// session.
fn answered_elsewhere(dial: PathInfo, other: Option<PathInfo>, then: impl FnOnce(&mut Net<'_, '_>) + Send + 'static) {
    big_stack(move || {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.dial_info = dial;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, None, vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(81, Params::new(10 * MS)), &mut w.stores);
        let now = net.now;
        if let Some(info) = other {
            net.a.with_env(now, |c, env| c.add_path(env, OTHER, info)).unwrap();
        }
        let reply = reply_datagrams(&mut net);
        deliver_on(&mut net, OTHER, &reply);
        assert!(net.a.conn.is_connected(), "the Reply on the other path was not taken");
        assert_eq!(net.a.conn.active_path(), Some(OTHER));
        then(&mut net);
    });
}

#[test]
fn the_relay_path_a_session_leaves_stays_validated_and_is_chosen_again_when_the_active_path_is_lost() {
    answered_elsewhere(relay(), Some(relay()), |net| {
        assert!(
            net.a.conn.path_validated(PathId(1)),
            "the relay path the session left is no longer validated"
        );
        net.a.conn.path_lost(OTHER).unwrap();
        assert_eq!(
            net.a.conn.active_path(),
            Some(PathId(1)),
            "the session did not fall over to the relay path it left"
        );
    });
}

#[test]
fn the_direct_path_a_session_leaves_is_no_longer_validated() {
    answered_elsewhere(PathInfo::default(), Some(relay()), |net| {
        assert!(net.a.conn.path_validated(OTHER));
        assert!(
            !net.a.conn.path_validated(PathId(1)),
            "the direct path the session left is still validated"
        );
    });
}

/// One timer pass of the dialing side, 1 ms after the last event.
fn timer_step(net: &mut Net<'_, '_>) {
    let t = net.now + MS;
    net.a.with_env(t, vinc_transport::conn::Connection::handle_timeout);
    net.a.service(t);
}

#[test]
fn a_session_answered_through_another_relay_stays_on_it_after_a_timer_step() {
    answered_elsewhere(relay(), Some(relay()), |net| {
        timer_step(net);
        assert_eq!(
            net.a.conn.active_path(),
            Some(OTHER),
            "the timer took the session back to the relay path that did not answer"
        );
        assert!(net.a.conn.path_validated(PathId(1)));
    });
}

#[test]
fn a_reply_on_a_relay_path_the_dial_does_not_hold_stays_on_it_once_named_a_relay() {
    answered_elsewhere(relay(), None, |net| {
        net.a.conn.set_path_info(OTHER, relay());
        timer_step(net);
        assert_eq!(
            net.a.conn.active_path(),
            Some(OTHER),
            "naming the path a relay took the session back to the relay path that did not answer"
        );
    });
}

/// Add a direct route 3/4 beside the two relay paths, and a route for the Reply's path so that the responder
/// completes; return once the session is on the direct path.
fn with_direct_path(net: &mut Net<'_, '_>) {
    let p = Params::new(10 * MS);
    net.link.add_route(OTHER, PathId(19), p, p);
    net.link.add_route(PathId(3), PathId(4), p, p);
    let now = net.now;
    net.a
        .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
        .unwrap();
    net.b
        .with_env(now, |c, env| c.add_path(env, PathId(4), PathInfo::default()))
        .unwrap();
    let until = net.now + 10 * SEC;
    assert!(
        net.run(until, |n| n.a.conn.active_path() == Some(PathId(3))),
        "the session did not move to the direct path"
    );
}

#[test]
fn a_direct_path_that_validates_while_a_relay_path_is_held_takes_the_session() {
    answered_elsewhere(relay(), Some(relay()), |net| {
        with_direct_path(net);
        assert!(net.a.conn.path_validated(PathId(1)));
        assert!(net.a.conn.path_validated(OTHER));
    });
}

#[test]
fn the_fall_back_from_a_failed_direct_path_takes_the_measured_relay_path() {
    answered_elsewhere(relay(), Some(relay()), |net| {
        with_direct_path(net);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(10), relay()))
            .unwrap();
        assert!(
            net.a.conn.path_rtt(OTHER).is_some(),
            "the relay path the session left has no round trip"
        );
        net.link.route(PathId(3)).up = false;
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &pattern(2_000, 3)).unwrap();
        let until = net.now + 30 * SEC;
        assert!(
            net.run(until, |n| n.a.conn.stats().ptos >= 3),
            "the direct path never failed three probe timeouts"
        );
        assert_eq!(
            net.a.conn.active_path(),
            Some(OTHER),
            "the fall-back took a relay path that was never measured"
        );
    });
}

#[test]
fn a_session_that_loses_its_path_with_no_probe_timeout_falls_back_to_the_measured_relay_path() {
    answered_elsewhere(relay(), Some(relay()), |net| {
        with_direct_path(net);
        // The later slot holds a relay path nothing was measured on, the earlier one the path the session left.
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(10), relay()))
            .unwrap();
        assert!(
            net.a.conn.path_rtt(OTHER).is_some(),
            "the relay path the session left has no round trip"
        );
        assert!(net.a.conn.path_rtt(PathId(10)).is_none());
        // The direct path hears nothing for longer than its idle limit, with no probe timeout on it.
        let t = net.now + 16 * SEC;
        net.a.with_env(t, vinc_transport::conn::Connection::handle_timeout);
        net.a.service(t);
        assert!(
            !net.a.conn.path_validated(PathId(3)),
            "the quiet direct path is still validated"
        );
        assert_eq!(
            net.a.conn.active_path(),
            Some(OTHER),
            "the fall-back took a relay path that was never measured"
        );
        net.a.with_env(t + MS, vinc_transport::conn::Connection::handle_timeout);
        assert_eq!(
            net.a.conn.active_path(),
            Some(OTHER),
            "the next timer step moved the session off the measured relay path"
        );
        assert!(net.a.conn.is_connected());
    });
}

#[test]
fn an_unmeasured_relay_path_failing_three_probe_timeouts_gives_way_to_a_measured_one() {
    answered_elsewhere(relay(), Some(relay()), |net| {
        net.a.conn.set_active(PathId(1)).unwrap();
        assert!(
            net.a.conn.path_rtt(OTHER).is_some(),
            "the relay path the session left has no round trip"
        );
        assert!(net.a.conn.path_rtt(PathId(1)).is_none());
        net.link.route(PathId(1)).ab.p.loss_ppm = 1_000_000;
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &pattern(2_000, 2)).unwrap();
        let until = net.now + 30 * SEC;
        assert!(
            net.run(until, |n| {
                let ptos = n.a.conn.stats().ptos;
                if ptos < 3 {
                    assert_eq!(
                        n.a.conn.active_path(),
                        Some(PathId(1)),
                        "the session left the path early"
                    );
                    return false;
                }
                assert_eq!(
                    n.a.conn.active_path(),
                    Some(OTHER),
                    "the session stayed on the failing path"
                );
                true
            }),
            "the path never failed three probe timeouts"
        );
        assert!(net.a.conn.is_connected(), "the session closed");
    });
}

/// Write `data` on a new unidirectional stream of `s` at node 0 and finish it.
fn send(net: &mut CoreNet, s: vinc_core::SessionId, data: &[u8]) {
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

#[test]
fn a_dial_sent_through_one_relay_and_answered_through_another_stays_on_it_and_pings_the_first_as_a_standby() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS);
        let (a, b) = (net.add(1), net.add(2));
        let (via_a, via_b) = (relay_addr(false, 3, 7), relay_addr(false, 4, 7));
        net.nodes[b].extra.extend([via_a, via_b]);
        let a_addr = net.nodes[a].addr;
        // The first relay's answer never reaches the dial; the Reply is captured instead.
        let drop_answers = Rc::new(Cell::new(true));
        let gate = Rc::clone(&drop_answers);
        net.capture = true;
        net.loss = Some(Box::new(move |_, to, _| gate.get() && to == a_addr));
        let (peer, now) = (net.nodes[b].node, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, via_a, Role::Other).unwrap();
        let s = net.nodes[a].session(&rep);
        net.run(now + SEC_NS, |n| n.captured.iter().any(|(_, to, _)| *to == a_addr));
        let reply: Vec<Vec<u8>> = net
            .captured
            .iter()
            .filter(|(_, to, d)| *to == a_addr && d[0] & 0x80 != 0)
            .map(|(_, _, d)| d.clone())
            .collect();
        assert!(
            !reply.is_empty(),
            "the responder sent no Reply: delivered {}, sent {:?}, events {:?} / {:?}",
            net.delivered,
            net.tapped,
            net.nodes[a].events,
            net.nodes[b].events
        );
        // The same Reply comes back through the second relay.
        drop_answers.set(false);
        for d in reply {
            net.inject(via_b, a_addr, d, 5 * MS);
        }
        let t = net.now;
        let up = net.run(t + 2 * SEC_NS, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Connected { .. }))
        });
        assert!(up, "the dial answered through the second relay did not connect");
        let connected = net.now;
        send(&mut net, s, &pattern(2_000, 1));
        net.run_for(12 * SEC_NS);
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(s)) else {
            panic!("no stats")
        };
        assert_eq!(
            st.route.map(|(_, r)| r),
            Some(via_b),
            "the session went back to the relay that did not answer"
        );
        let to_first: Vec<usize> = net
            .tapped
            .iter()
            .filter(|t| t.0 > connected && t.2 == via_a)
            .map(|t| t.3)
            .collect();
        eprintln!("datagrams to the first relay after connecting: {to_first:?}");
        assert!(
            !to_first.is_empty(),
            "nothing was sent to the first relay after the session left it"
        );
        assert!(
            to_first.iter().all(|n| *n < 100),
            "more than a ping went to the first relay: {to_first:?}"
        );
    });
}

#[test]
fn a_dial_whose_copy_through_the_first_relay_is_lost_completes_on_the_second() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (via_a, via_b) = (relay_addr(false, 3, 7), relay_addr(false, 4, 7));
        net.nodes[b].extra.extend([via_a, via_b]);
        net.loss = Some(Box::new(move |_, to, _| to == via_a));
        let (peer, now) = (net.nodes[b].node, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, via_a, Role::Other).unwrap();
        let s = net.nodes[a].session(&rep);
        net.nodes[a]
            .cmd(
                now,
                Command::FlightPaths {
                    session: s,
                    addrs: &[via_b],
                    skip_primary: false,
                },
            )
            .unwrap();
        net.pump(a);
        let up = net.run(now + 5 * SEC_NS, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Connected { .. }))
        });
        assert!(up, "the dial did not connect through the second relay");
        let connected = net.now;
        let data = pattern(2_000, 1);
        send(&mut net, s, &data);
        net.run_for(12 * SEC_NS);
        assert_eq!(
            net.nodes[b].read.values().next(),
            Some(&data),
            "the responder did not read the stream"
        );
        let to_first: Vec<usize> = net
            .tapped
            .iter()
            .filter(|t| t.0 > connected && t.2 == via_a)
            .map(|t| t.3)
            .collect();
        eprintln!("datagrams to the first relay after connecting, copy lost: {to_first:?}");
        assert!(
            to_first.iter().all(|n| *n < 100),
            "more than a ping went to the first relay: {to_first:?}"
        );
    });
}
