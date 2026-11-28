//! A dialing side takes the handshake Reply that arrives on a path it does not hold (another relay than the first
//! flight went through, or a path its table gave up), as a responder takes a packet on a path it does not know: the
//! Reply is processed, and the path joins the table, within its bound, only once the Reply has authenticated. A
//! packet on such a path that does not authenticate adds no path and moves nothing.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::cell::RefCell;
use std::rc::Rc;

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::{CloseReason, PathId, PathInfo};
use pinc_transport::packet::{Header, packets};

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
        let _ = net
            .a
            .with_lent(now, |c, env, l| c.handle_datagram(env, l, path, &mut d));
    }
    net.a.service(now);
}

/// The view of the dialing side's slot of `path`.
fn slot_of(net: &Net<'_, '_>, path: PathId) -> pinc_transport::conn::SlotView {
    net.a
        .conn
        .trace_paths()
        .slots
        .into_iter()
        .flatten()
        .find(|s| s.id == path.0)
        .unwrap()
}

/// No path id appears twice in the session's table.
fn no_duplicate_paths(net: &Net<'_, '_>) {
    let ids: Vec<u64> = net.a.conn.path_list().map(|(id, _, _)| id.0).collect();
    let mut once = ids.clone();
    once.sort_unstable();
    once.dedup();
    assert_eq!(once.len(), ids.len(), "a path is held twice: {ids:?}");
}

/// Whether the datagram holds a 1-RTT packet to the dialing side.
fn has_short(c: &Conn<'_>, d: &[u8]) -> bool {
    let mut d = d.to_vec();
    packets(&mut d, 4)
        .any(|p| matches!(p, Ok(p) if matches!(p.header, Header::Short { dcid } if c.local_cids().any(|l| l == dcid))))
}

/// A resume dial, the responder's datagrams (the Reply, then a 1-RTT packet) joined into one, handed to the dialing
/// side on `OTHER` after its table was given the paths `held`.
fn coalesced_resume(held: &[u64], seed: u64) -> Vec<(PathId, bool)> {
    let mut w = World::new(IdentityAlg::Ed25519);
    let mut tickets = first_session(&mut w);
    let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let a = w.client(&mut sa, Some(ticket), pinc_security::ClientTickets::new());
    let b = w.server(&mut sb);
    let mut net = Net::new(a, b, Link::new(seed, Params::new(10 * MS)), &mut w.stores);
    let now = net.now;
    for p in held {
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(*p), PathInfo::default()))
            .unwrap();
    }
    let mut reply = reply_datagrams(&mut net);
    assert!(
        reply.len() >= 2 && has_short(&net.a.conn, &reply[1]),
        "no 1-RTT datagram follows the Reply"
    );
    let tail = reply.remove(1);
    reply[0].extend_from_slice(&tail);
    deliver_on(&mut net, OTHER, &reply);
    assert!(net.a.conn.is_connected());
    no_duplicate_paths(&net);
    assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
    net.a.conn.path_list().map(|(id, _, v)| (id, v)).collect()
}

/// Whether the dialing side has sent anything on `path` from `since` on.
fn sent_on(net: &Net<'_, '_>, path: PathId, since: u64) -> bool {
    net.a.tx_log.iter().any(|(t, _, p)| *t >= since && *p == path)
}

/// A Reply that arrives on a path the dial does not hold establishes the session and the path is held afterwards,
/// unvalidated with a challenge queued: the session stays on the path it was on, and the Finish goes there and is
/// copied to the new path.
fn reply_on_unheld_path(mut w: World, ticket: bool) {
    let mut tickets = if ticket {
        first_session(&mut w)
    } else {
        pinc_security::ClientTickets::new()
    };
    let resumed = ticket;
    let ticket = ticket.then(|| tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap());
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let a = w.client(&mut sa, ticket, pinc_security::ClientTickets::new());
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
    assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
    // Anyone can send a copy of the Reply from any source: a path the dial did not hold proves nothing, its budget
    // counts the datagram and a challenge goes out on it.
    assert!(!net.a.conn.path_validated(OTHER));
    let slot = slot_of(&net, OTHER);
    assert!(
        slot.challenge.is_some() && slot.send_challenge,
        "no challenge queued on the path"
    );
    // The datagram that completed the Reply counts on the path it arrived on (the first of a resume Reply, the last of
    // a full one), and so does every datagram after it.
    let from = if resumed { 0 } else { reply.len() - 1 };
    assert_eq!(
        slot.amp_received,
        reply[from..].iter().map(|d| d.len() as u64).sum::<u64>(),
        "the datagram that completed the Reply does not count"
    );
    assert!(net.a.conn.rtt_estimate().has_sample());
    net.a.service(at);
    let _ = net.flush();
    assert!(sent_on(&net, OTHER, at), "nothing left on the path of the Reply");
    assert!(
        sent_on(&net, PathId(1), at),
        "the Finish did not leave on the path the session stayed on"
    );
    no_duplicate_paths(&net);
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
        let a = w.client(&mut sa, None, pinc_security::ClientTickets::new());
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
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        no_duplicate_paths(&net);
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
        no_duplicate_paths(&net);
    });
}

#[test]
fn a_reply_on_a_new_path_at_a_full_table_takes_the_place_of_an_unvalidated_standby() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, None, pinc_security::ClientTickets::new());
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
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        let held = [1, 3, 4, 5, 6, 9]
            .into_iter()
            .filter(|p| net.a.conn.has_path(PathId(*p)))
            .count();
        assert_eq!(held, 4, "the table grew past its bound");
        no_duplicate_paths(&net);
    });
}

#[test]
fn a_reply_on_a_path_the_dial_gave_up_establishes_and_the_path_is_held_again() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, None, pinc_security::ClientTickets::new());
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
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        no_duplicate_paths(&net);
    });
}

#[test]
fn a_resume_reply_with_a_1rtt_packet_behind_it_on_a_new_path_holds_the_path_once() {
    big_stack(|| {
        let paths = coalesced_resume(&[], 76);
        assert_eq!(paths.iter().filter(|(id, _)| *id == OTHER).count(), 1);
        assert!(
            paths.iter().any(|(id, _)| *id == PathId(1)),
            "the path the session left is gone"
        );
    });
}

#[test]
fn at_a_full_table_a_reply_with_a_1rtt_packet_behind_it_gives_up_one_path_only() {
    big_stack(|| {
        // Paths 1 (dialed, active), 3, 4, 5, none validated but the dialed one. The new path takes the first
        // unvalidated path that is not the active one: path 3. Path 1, which the session leaves, stays.
        let paths = coalesced_resume(&[3, 4, 5], 77);
        let ids: Vec<u64> = paths.iter().map(|(id, _)| id.0).collect();
        assert_eq!(ids.len(), 4, "{ids:?}");
        for keep in [1, 4, 5, 9] {
            assert!(ids.contains(&keep), "path {keep} was given up: {ids:?}");
        }
    });
}

#[test]
fn a_1rtt_packet_alone_on_a_held_path_adds_no_path() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(78, Params::new(10 * MS)));
        assert!(net.connect(net.now + 5 * SEC));
        let before: Vec<_> = net.a.conn.path_list().map(|(id, _, _)| id).collect();
        let t = net.now + 50 * MS;
        net.run(t, |_| false);
        let after: Vec<_> = net.a.conn.path_list().map(|(id, _, _)| id).collect();
        assert_eq!(before, after);
        no_duplicate_paths(&net);
    });
}

#[test]
fn a_reply_on_a_path_the_flight_went_to_validates_it() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, None, pinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(79, Params::new(10 * MS)), &mut w.stores);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        let reply = reply_datagrams(&mut net);
        deliver_on(&mut net, PathId(3), &reply);
        assert!(net.a.conn.is_connected());
        assert_eq!(net.a.conn.active_path(), Some(PathId(3)));
        assert!(
            net.a.conn.path_validated(PathId(3)),
            "a path the dial held was not validated"
        );
    });
}

#[test]
fn in_a_validated_session_a_held_path_is_limited_by_its_own_budget() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(80, Params::new(10 * MS)));
        assert!(net.connect(net.now + 5 * SEC));
        // What the server sends next never reaches the dialing side over the link; the dialing side takes a copy of it
        // from a new address, as a peer that moved.
        net.link.route(PathId(1)).ba.p.loss_ppm = 1_000_000;
        let sent: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
        let sink = Rc::clone(&sent);
        net.on_tx = Some(Box::new(move |is_a, d, _| {
            if !is_a {
                sink.borrow_mut().push(d.to_vec());
            }
        }));
        let id = net.b.conn.open_bi().unwrap();
        net.b.conn.write(id, b"hello").unwrap();
        let until = net.now + 100 * MS;
        net.run(until, |_| false);
        net.on_tx = None;
        let got = sent.borrow().clone();
        assert!(!got.is_empty(), "the server sent nothing");
        deliver_on(&mut net, OTHER, &got[..1]);
        assert!(net.a.conn.has_path(OTHER), "the copy did not teach the path");
        let slot = slot_of(&net, OTHER);
        assert_eq!(slot.amp_received, got[0].len() as u64);
        assert!(!net.a.conn.path_validated(OTHER));
        assert_eq!(
            slot.amp_room,
            usize::MAX,
            "a path the ledger does not hold is not limited"
        );
        net.a.conn.set_path_held(OTHER, true);
        let slot = slot_of(&net, OTHER);
        let allowed = 3 * slot.amp_received;
        assert_eq!(slot.amp_room as u64, allowed - slot.amp_sent - 48);
        net.a.conn.set_path_held(OTHER, false);
        assert_eq!(slot_of(&net, OTHER).amp_room, usize::MAX);
    });
}

/// The view of the responder's slot of `path`.
fn b_slot(net: &Net<'_, '_>, path: PathId) -> pinc_transport::conn::SlotView {
    net.b
        .conn
        .trace_paths()
        .slots
        .into_iter()
        .flatten()
        .find(|s| s.id == path.0)
        .unwrap()
}

/// A resumption Hello proves nothing about its source (anyone who saw it can send a copy from any address), and
/// neither does any packet under the 0-RTT keys, which a copy of the Hello also opens. The Reply goes to one path;
/// the dialer's first 1-RTT packet needs the Reply's fresh key share, so it proves the dialer received the Reply:
/// it validates that path, with no challenge sent.
#[test]
fn a_resumed_responders_path_is_validated_by_the_first_1rtt_packet_and_not_by_early_data() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, Some(ticket), pinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(81, Params::new(10 * MS)), &mut w.stores);
        // Early data goes with the Hello; the Reply never reaches the dialer.
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"ping").unwrap();
        net.link.route(PathId(1)).ba.p.loss_ppm = 1_000_000;
        let until = net.now + 100 * MS;
        net.run(until, |_| false);
        assert!(
            net.b.conn.is_connected(),
            "the resumed responder was not established at the Hello"
        );
        assert_eq!(
            net.b.read.get(&id).map(Vec::as_slice),
            Some(&b"ping"[..]),
            "the early data did not reach the responder"
        );
        let path = net.b.conn.active_path().unwrap();
        assert!(
            !net.b.conn.path_validated(path),
            "the Hello or a 0-RTT packet validated its source"
        );
        assert!(
            b_slot(&net, path).sent.iter().all(Option::is_none),
            "a challenge went out on the path"
        );
        // The Reply (or its resend) now reaches the dialer; its first 1-RTT packet validates the path.
        net.link.route(PathId(1)).ba.p.loss_ppm = 0;
        let until = net.now + 5 * SEC;
        assert!(
            net.run(until, |n| n.b.conn.path_validated(path)),
            "the dialer's first 1-RTT packet did not validate the path"
        );
        assert!(
            b_slot(&net, path).sent.iter().all(Option::is_none),
            "a challenge was needed to validate the path"
        );
    });
}

/// A copy of a resumption Hello from a source that never receives the Reply: the responder is established at it, but
/// no packet under the 1-RTT keys ever comes, so the source stays unvalidated, gets at most three times what it sent
/// and no challenge, and the session ends by the idle timeout (75 s): the responder has no confirm deadline, so it
/// holds its slot until then.
#[test]
fn a_copied_hello_from_a_forged_source_never_validates_and_gets_at_most_three_times() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, Some(ticket), pinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        // The forged source is a route the dialer does not use (it names it 8, the responder 7): what the responder
        // sends there never arrives, and what the dialer itself sends on its own route never reaches the responder.
        let forged = PathId(7);
        let mut link = Link::new(82, Params::new(10 * MS));
        link.add_route(PathId(8), forged, Params::new(10 * MS), Params::new(10 * MS));
        link.route(PathId(8)).ba.p.loss_ppm = 1_000_000;
        link.route(PathId(1)).ab.p.loss_ppm = 1_000_000;
        let mut net = Net::new(a, b, link, &mut w.stores);
        let sent: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
        let sink = Rc::clone(&sent);
        net.on_tx = Some(Box::new(move |is_a, d, _| {
            if is_a {
                sink.borrow_mut().push(d.to_vec());
            }
        }));
        let until = net.now + 50 * MS;
        net.run(until, |_| false);
        net.on_tx = None;
        let copy = sent.borrow().clone();
        assert!(!copy.is_empty(), "the dialer sent no Hello");
        let now = net.now;
        // The endpoint holds the forged address in its ledger, as it does a source it did not dial.
        net.b
            .with_env(now, |c, env| c.add_path(env, forged, PathInfo::default()))
            .unwrap();
        net.b.conn.set_path_held(forged, true);
        let mut heard = 0;
        for d in &copy {
            heard += d.len() as u64;
            net.link.send_a(now, PathId(8), d);
        }
        net.run(net.now + SEC, |n| n.b.conn.is_connected());
        assert!(
            net.b.conn.is_connected(),
            "the copied Hello did not establish the responder"
        );
        assert_eq!(net.b.conn.active_path(), Some(forged));
        net.run(net.now + 76 * SEC, |n| n.b.closed().is_some());
        assert_eq!(
            net.b.closed(),
            Some(CloseReason::IdleTimeout),
            "the session did not end by the idle timeout"
        );
        assert!(!net.b.conn.path_validated(forged));
        assert!(
            b_slot(&net, forged).sent.iter().all(Option::is_none),
            "a challenge went to the forged source"
        );
        let to_forged: u64 = net
            .b
            .tx_log
            .iter()
            .filter(|(_, _, p)| *p == forged)
            .map(|(_, n, _)| *n as u64)
            .sum();
        assert!(
            to_forged <= 3 * heard,
            "{to_forged} bytes went to a source that sent {heard}"
        );
    });
}
