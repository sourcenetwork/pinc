//! A session that establishes on another path than the one it dialed un-validates the path it left only when that
//! path is direct. A relay path is born validated and nothing ever re-validates one, so un-validating it there
//! loses the path for good: it is never kept alive, never chosen again and is the first an eviction gives up.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::cell::RefCell;
use std::rc::Rc;

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::{PathId, PathInfo};
use pinc_transport::recovery::PathKind;

/// The path the Reply comes back on, which the dialing side does not hold.
const OTHER: PathId = PathId(9);

/// What the endpoint knows of a path through a relay.
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

/// Whether the dialing side has sent anything on `path` from `since` on.
fn sent_on(net: &Net<'_, '_>, path: PathId, since: u64) -> bool {
    net.a.tx_log.iter().any(|(t, _, p)| *t >= since && *p == path)
}

/// A dial through relay A answered through relay B: the session moves to B, relay A stays a validated standby, and
/// the session falls over to it when B is lost.
#[test]
fn a_dial_through_relay_a_answered_through_relay_b_keeps_a_validated_and_falls_over_to_it() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(91, Params::new(10 * MS)));
        // The dial leaves through relay A: a relay path is born validated.
        net.a.conn.set_path_info(PathId(1), relay());
        assert!(net.a.conn.path_validated(PathId(1)), "relay A is not validated");
        let reply = reply_datagrams(&mut net);
        // The answer comes back through relay B, on a path the dial does not hold.
        deliver_on(&mut net, OTHER, &reply);
        assert!(net.a.conn.is_connected(), "the Reply was not taken");
        assert_eq!(net.a.conn.active_path(), Some(OTHER));

        // The relay path the session left is still validated.
        assert!(
            net.a.conn.path_validated(PathId(1)),
            "the relay path the session left is not validated any more"
        );

        // A standby relay is kept alive: its PING leaves on it.
        let at = net.now;
        net.a.conn.ping_path(PathId(1)).unwrap();
        net.a.service(at);
        let _ = net.flush();
        assert!(
            sent_on(&net, PathId(1), at),
            "nothing left on the relay path the session left"
        );

        // The session falls over to relay A when relay B is lost.
        net.a.conn.path_lost(OTHER).unwrap();
        assert_eq!(
            net.a.conn.active_path(),
            Some(PathId(1)),
            "the session did not fall over to the validated relay path"
        );
    });
}

/// Both relay paths validated, B's round trip sampled lower than A's: the choice of the active path keeps the
/// session on the cheaper relay and hands it to A when B is lost. Nothing here re-validates relay A beyond the
/// round trip sampling itself, which is a challenge the peer answers; a standby relay is kept alive by
/// acknowledgements of PINGs, which validate nothing.
#[test]
fn two_validated_relays_stay_on_the_cheaper_one_and_fall_over_to_the_other_on_loss() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(92, Params::new(10 * MS)));
        net.a.conn.set_path_info(PathId(1), relay());
        let reply = reply_datagrams(&mut net);
        deliver_on(&mut net, OTHER, &reply);
        assert!(net.a.conn.is_connected() && net.a.conn.active_path() == Some(OTHER));

        // Relay B answers from its own path from here on.
        net.link.add_route(OTHER, OTHER, Params::new(MS), Params::new(MS));
        net.link.route(PathId(1)).ba.p.loss_ppm = 0;

        // Relay A's round trip, from a challenge the peer answers over the dial route.
        net.a.with_env(net.now, |c, env| c.probe(env, PathId(1))).unwrap();
        assert!(
            net.run(net.now + 2 * SEC, |n| n.a.conn.path_rtt(PathId(1)).is_some()),
            "relay A got no round trip sample"
        );

        // Relay B's round trip, from a challenge over its own fast route.
        net.a.with_env(net.now, |c, env| c.probe(env, OTHER)).unwrap();
        assert!(
            net.run(net.now + 2 * SEC, |n| n.a.conn.path_rtt(OTHER).is_some()),
            "relay B got no round trip sample"
        );
        let (rtt_a, rtt_b) = (
            net.a.conn.path_rtt(PathId(1)).unwrap(),
            net.a.conn.path_rtt(OTHER).unwrap(),
        );
        assert!(rtt_a > rtt_b, "relay B must read cheaper: A {rtt_a} B {rtt_b}");

        // Relay B is a relay's path too; the endpoint knows it from the host.
        net.a.conn.set_path_info(OTHER, relay());
        assert_eq!(
            net.a.conn.active_path(),
            Some(OTHER),
            "the session left the cheaper relay"
        );

        // A timer tick leaves the session on the cheaper relay.
        let now = net.now + 50 * MS;
        net.a.with_env(now, pinc_transport::conn::Connection::handle_timeout);
        net.now = now;
        net.flush();
        assert_eq!(
            net.a.conn.active_path(),
            Some(OTHER),
            "the session flipped back to the dearer relay"
        );

        // The session falls over to relay A when relay B is lost.
        net.a.conn.path_lost(OTHER).unwrap();
        assert_eq!(
            net.a.conn.active_path(),
            Some(PathId(1)),
            "the session did not fall over to the validated relay path"
        );
    });
}
