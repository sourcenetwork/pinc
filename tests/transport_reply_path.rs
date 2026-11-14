//! A dialing side takes the handshake Reply that arrives on a path it does not hold (another relay than the first
//! flight went through, or a path its table gave up), as a responder takes a packet on a path it does not know: the
//! Reply is processed, and the path joins the table, within its bound, only once the Reply has authenticated. A
//! packet on such a path that does not authenticate adds no path and moves nothing.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::cell::RefCell;
use std::rc::Rc;

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{PathId, PathInfo};

/// The path the Reply comes back on, which the dialing side does not hold.
const OTHER: PathId = PathId(9);

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

/// A Reply that arrives on a path the dial does not hold establishes the session, the path is held afterwards and
/// the Finish leaves on it.
fn reply_on_unheld_path(mut w: World, ticket: bool) {
    let mut tickets = if ticket {
        first_session(&mut w)
    } else {
        vinc_security::ClientTickets::new()
    };
    let ticket = ticket.then(|| tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap());
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let a = w.client(&mut sa, ticket, vinc_security::ClientTickets::new());
    let b = w.server(&mut sb);
    let mut net = Net::new(a, b, Link::new(71, Params::new(10 * MS)), &mut w.stores);
    let reply = reply_datagrams(&mut net);
    assert!(!net.a.conn.has_path(OTHER));
    let at = net.now;
    deliver_on(&mut net, OTHER, &reply);
    assert!(
        net.a.conn.is_connected(),
        "the Reply on a path the dial does not hold was not taken"
    );
    assert!(net.a.conn.has_path(OTHER), "the path of the Reply is not held");
    assert_eq!(net.a.conn.active_path(), Some(OTHER));
    assert!(net.a.conn.path_validated(OTHER));
    assert!(net.a.conn.rtt_estimate().has_sample());
    net.a.service(at);
    let _ = net.flush();
    assert!(sent_on(&net, OTHER, at), "nothing left on the path of the Reply");
    assert!(
        !sent_on(&net, PathId(1), at),
        "a packet left on the path the Reply did not use"
    );
}

#[test]
fn a_reply_on_a_path_the_dial_does_not_hold_establishes_and_the_finish_follows_it() {
    big_stack(|| reply_on_unheld_path(World::new(IdentityAlg::Ed25519), false));
}

#[test]
fn a_resume_reply_on_a_path_the_dial_does_not_hold_resumes_and_adds_it() {
    big_stack(|| reply_on_unheld_path(World::new(IdentityAlg::Ed25519), true));
}

#[test]
fn a_reply_in_several_datagrams_on_a_path_the_dial_does_not_hold_establishes() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Hybrid);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, None, vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(72, Params::new(10 * MS)), &mut w.stores);
        let reply = reply_datagrams(&mut net);
        assert!(reply.len() > 1, "the Reply fits one datagram: {}", reply.len());
        deliver_on(&mut net, OTHER, &reply);
        assert!(
            net.a.conn.is_connected(),
            "the Reply in {} datagrams was not taken",
            reply.len()
        );
        assert_eq!(net.a.conn.active_path(), Some(OTHER));
    });
}

#[test]
fn a_forged_reply_on_a_path_the_dial_does_not_hold_adds_no_path_and_moves_nothing() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let bad = Forgery::ZeroSignature {
            alg: w.rp.id.alg(),
            public_key: w.rp.id.public_key().to_vec(),
        };
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(73, Params::new(10 * MS)));
        let initial = sent_initial(&mut net);
        let now = net.now;
        let reply = forge_reply(&net.a.prov, &initial, &bad);
        let d = forge_message(net.a.conn.local_cids().next().unwrap(), &reply);
        deliver_on(&mut net, OTHER, &[d]);
        assert_eq!(
            net.a.conn.stats().handshake_dropped,
            1,
            "the forged Reply on the new path was not checked and counted"
        );
        assert!(!net.a.conn.has_path(OTHER), "a forged Reply added its path");
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        assert!(
            !net.a.conn.rtt_estimate().has_sample(),
            "a forged Reply gave a round trip sample"
        );
        assert!(!net.a.conn.is_connected() && net.a.closed().is_none());
        assert!(net.connect(now + 5 * SEC), "{:?}", net.rx_drops);
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        assert!(!net.a.conn.has_path(OTHER));
    });
}

#[test]
fn a_reply_on_a_new_path_at_a_full_table_takes_the_place_of_an_unvalidated_standby() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, None, vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(74, Params::new(10 * MS)), &mut w.stores);
        let now = net.now;
        // The table holds four paths: the dial's own and three the dial added, none validated yet.
        for p in [3, 4, 5] {
            net.a
                .with_env(now, |c, env| c.add_path(env, PathId(p), PathInfo::default()))
                .unwrap();
        }
        assert!(
            net.a
                .with_env(now, |c, env| c.add_path(env, PathId(6), PathInfo::default()))
                .is_ok()
        );
        let held = [1, 3, 4, 5, 6]
            .into_iter()
            .filter(|p| net.a.conn.has_path(PathId(*p)))
            .count();
        assert_eq!(held, 4, "the table holds its bound");
        let reply = reply_datagrams(&mut net);
        deliver_on(&mut net, OTHER, &reply);
        assert!(net.a.conn.is_connected(), "the Reply at a full table was not taken");
        assert!(net.a.conn.has_path(OTHER));
        assert_eq!(net.a.conn.active_path(), Some(OTHER));
        let held = [1, 3, 4, 5, 6, 9]
            .into_iter()
            .filter(|p| net.a.conn.has_path(PathId(*p)))
            .count();
        assert_eq!(held, 4, "the table grew past its bound");
    });
}

#[test]
fn a_reply_on_a_path_the_dial_gave_up_establishes_and_the_path_is_held_again() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, None, vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(75, Params::new(10 * MS)), &mut w.stores);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, OTHER, PathInfo::default()))
            .unwrap();
        net.a.conn.remove_path(OTHER).unwrap();
        let reply = reply_datagrams(&mut net);
        deliver_on(&mut net, OTHER, &reply);
        assert!(
            net.a.conn.is_connected(),
            "the Reply on a path the table gave up was not taken"
        );
        assert!(net.a.conn.has_path(OTHER));
        assert_eq!(net.a.conn.active_path(), Some(OTHER));
    });
}
