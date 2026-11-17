//! A relay path is valid for as long as the session tracks it, so a session that establishes on another path keeps
//! the relay path it leaves validated: a dial sent through one relay and answered through another keeps the first
//! relay's path as a validated standby (pinged, chosen again when the active path fails), while a direct path it
//! leaves is validated again only by a challenge.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use vinc_core::{Command, Event, Role, Value, relay_addr};
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

/// A dial on path 1 of kind `dial`, with the path `OTHER` of kind `other` added, whose Reply has come back on
/// `OTHER`; runs `then` on the established session.
fn answered_elsewhere(dial: PathInfo, other: PathInfo, then: impl FnOnce(&mut Net<'_, '_>) + Send + 'static) {
    big_stack(move || {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.dial_info = dial;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, None, vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(81, Params::new(10 * MS)), &mut w.stores);
        let now = net.now;
        net.a.with_env(now, |c, env| c.add_path(env, OTHER, other)).unwrap();
        let reply = reply_datagrams(&mut net);
        deliver_on(&mut net, OTHER, &reply);
        assert!(net.a.conn.is_connected(), "the Reply on the other path was not taken");
        assert_eq!(net.a.conn.active_path(), Some(OTHER));
        then(&mut net);
    });
}

#[test]
fn the_relay_path_a_session_leaves_stays_validated_and_is_chosen_again_when_the_active_path_is_lost() {
    answered_elsewhere(relay(), relay(), |net| {
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
    answered_elsewhere(PathInfo::default(), relay(), |net| {
        assert!(net.a.conn.path_validated(OTHER));
        assert!(
            !net.a.conn.path_validated(PathId(1)),
            "the direct path the session left is still validated"
        );
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
fn a_dial_sent_through_one_relay_and_answered_through_another_pings_the_first_as_a_standby() {
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
        assert!(
            net.tapped.iter().any(|t| t.0 > connected && t.2 == via_a),
            "nothing was sent to the first relay after the session left it"
        );
    });
}
