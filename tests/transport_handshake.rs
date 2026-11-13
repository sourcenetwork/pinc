//! The handshake timers and recovery on a real connection: the dialing side's schedule (first resend, doubling, the
//! cap, the thin cap, the node round trip), the responder's schedule, the connect timeout, the Finish resent on the
//! probe timeout, the handshake round trip as the first round-trip sample, a link return, a lost resume Reply, a Hello
//! that falls back to a full handshake and is still answered late, and the buffers returned to the pool.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names
)]

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{CloseReason, PathId};

/// The dialing side's resend counts at `(offset, expected count)` checkpoints, on a link that delivers nothing.
fn dial_schedule(w: &mut World, checks: &[(u64, u64)]) -> Vec<(u64, u64)> {
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut link = Link::new(53, Params::new(10 * MS));
    link.route(PathId(1)).up = false;
    let mut net = setup(w, &mut sa, &mut sb, link);
    let t0 = net.now;
    checks
        .iter()
        .map(|&(at, _)| {
            net.run(t0 + at, |_| false);
            (at, net.a.conn.stats().handshake_retransmits)
        })
        .collect()
}

fn expect(checks: &[(u64, u64)], got: &[(u64, u64)]) {
    for (c, g) in checks.iter().zip(got) {
        assert_eq!(c, g, "at {} ms", c.0 / MS);
    }
}

#[test]
fn a_dialing_side_resends_at_500_ms_doubling_to_16_s_and_gives_up_at_30_s() {
    big_stack(|| {
        // Resends at 0.5, 1.5, 3.5, 7.5, 15.5 s (the delays 0.5, 1, 2, 4, 8, then 16 s would be 31.5 s).
        let checks = [
            (490 * MS, 0),
            (510 * MS, 1),
            (1490 * MS, 1),
            (1510 * MS, 2),
            (3490 * MS, 2),
            (3510 * MS, 3),
            (7490 * MS, 3),
            (7510 * MS, 4),
            (15490 * MS, 4),
            (15510 * MS, 5),
            (29_900 * MS, 5),
        ];
        let mut w = World::new(IdentityAlg::Ed25519);
        expect(&checks, &dial_schedule(&mut w, &checks));
        // The connect timeout: 30 s.
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(53, Params::new(10 * MS));
        link.route(PathId(1)).up = false;
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        let t0 = net.now;
        net.run(t0 + 29_990 * MS, |_| false);
        assert!(net.a.closed().is_none());
        net.run(t0 + 30_100 * MS, |_| false);
        assert_eq!(net.a.closed(), Some(CloseReason::HandshakeTimeout));
        assert!(!net.a.conn.is_connected());
    });
}

#[test]
fn a_thin_node_caps_the_back_off_and_waits_60_s() {
    big_stack(|| {
        // The cap is max(8 s, 2 x the node's largest round trip): 8 s here, so the resends are 0.5, 1.5, 3.5, 7.5,
        // 15.5, 23.5, 31.5 s.
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.thin = true;
        let checks = [
            (15_490 * MS, 4),
            (15_510 * MS, 5),
            (23_490 * MS, 5),
            (23_510 * MS, 6),
            (31_510 * MS, 7),
        ];
        expect(&checks, &dial_schedule(&mut w, &checks));
        // A node that has seen a 5 s round trip waits up to 10 s: ... 7.5, 15.5, 25.5 s.
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.thin = true;
        w.cfg.node_peak_rtt = Some(5 * SEC);
        let checks = [(15_510 * MS, 5), (25_490 * MS, 5), (25_510 * MS, 6)];
        expect(&checks, &dial_schedule(&mut w, &checks));
        // Thin nodes keep an unestablished handshake for 60 s.
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.thin = true;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(53, Params::new(10 * MS));
        link.route(PathId(1)).up = false;
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        let t0 = net.now;
        net.run(t0 + 59_900 * MS, |_| false);
        assert!(net.a.closed().is_none());
        net.run(t0 + 60_100 * MS, |_| false);
        assert_eq!(net.a.closed(), Some(CloseReason::HandshakeTimeout));
    });
}

#[test]
fn the_first_resend_follows_the_remembered_or_node_round_trip() {
    big_stack(|| {
        // max(500 ms, 2 x RTT): a remembered 1 s gives 2 s, doubling 4 s, 8 s: resends at 2, 6, 14 s.
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.remembered_rtt = Some(SEC);
        let checks = [
            (1990 * MS, 0),
            (2010 * MS, 1),
            (5990 * MS, 1),
            (6010 * MS, 2),
            (13_990 * MS, 2),
            (14_010 * MS, 3),
        ];
        expect(&checks, &dial_schedule(&mut w, &checks));
        // Without a remembered one the node's average stands in (and 400 ms is below the thin threshold).
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.node_rtt = Some(240 * MS);
        let checks = [(490 * MS, 0), (510 * MS, 1)];
        expect(&checks, &dial_schedule(&mut w, &checks));
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.node_rtt = Some(240 * MS);
        w.cfg.remembered_rtt = Some(10 * MS);
        let checks = [(490 * MS, 0), (510 * MS, 1)];
        expect(&checks, &dial_schedule(&mut w, &checks));
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.node_rtt = Some(240 * MS);
        w.cfg.node_peak_rtt = Some(240 * MS);
        w.cfg.remembered_rtt = Some(400 * MS);
        let checks = [(790 * MS, 0), (810 * MS, 1)];
        expect(&checks, &dial_schedule(&mut w, &checks));
    });
}

#[test]
fn a_responder_resends_its_flight_at_999_ms_then_every_4_s() {
    big_stack(|| {
        // The Finish never comes: nothing the responder sends reaches the dialing side.
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(52, Params::new(10 * MS));
        link.route(PathId(1)).ba.p.loss_ppm = 1_000_000;
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        let t0 = net.now;
        // The flight first leaves 10 ms in, when the Initial arrived: resends at 1.009, 3.007, 7.003, 11.003, 15.003 s.
        let checks = [
            (1000 * MS, 0),
            (1020 * MS, 1),
            (3000 * MS, 1),
            (3020 * MS, 2),
            (6990 * MS, 2),
            (7020 * MS, 3),
            (10_990 * MS, 3),
            (11_020 * MS, 4),
            (15_020 * MS, 5),
        ];
        for (at, want) in checks {
            net.run(t0 + at, |_| false);
            assert_eq!(net.b.conn.stats().handshake_retransmits, want, "at {} ms", at / MS);
        }
        // A responder that is never established gives up after 30 s as well.
        net.run(t0 + 30_100 * MS, |_| false);
        assert_eq!(net.b.closed(), Some(CloseReason::HandshakeTimeout));
    });
}

#[test]
fn the_finish_is_resent_after_999_ms_and_the_handshake_round_trip_seeds_the_estimate() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(51, Params::new(10 * MS)));
        net.drop_finish = true;
        let t0 = net.now;
        assert!(net.run(t0 + SEC, |n| n.a.conn.is_connected()));
        // The first flight was answered without a resend: its round trip (20 ms) is the first estimate.
        let srtt = net.a.conn.stats().srtt;
        assert!((20 * MS..25 * MS).contains(&srtt), "srtt {srtt}");
        assert!(!net.b.conn.is_connected(), "the Finish was lost");
        assert!(net.connect(t0 + 2 * SEC));
        // The Finish went out again after 999 ms, whatever the round trip it measured.
        let took = net.now - t0;
        assert!(
            (999 * MS..1100 * MS).contains(&took),
            "connected after {} ms",
            took / MS
        );
        assert_eq!(net.a.conn.stats().handshake_retransmits, 1);
        // Once the first 1-RTT packet is heard the timer is done.
        net.run(t0 + 5 * SEC, |_| false);
        assert_eq!(net.a.conn.stats().handshake_retransmits, 1);
    });
}

#[test]
fn a_link_return_resends_a_pending_handshake_at_once() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(50, Params::new(10 * MS));
        link.route(PathId(1)).up = false;
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        let t0 = net.now;
        net.a.with_env(t0 + SEC, |c, env| c.set_link_down(env, true));
        net.run(t0 + 5 * SEC, |_| false);
        assert_eq!(
            net.a.conn.stats().handshake_retransmits,
            3,
            "0.5, 1.5, 3.5 s; the next is due at 7.5 s"
        );
        let sent = net.a.tx_log.len();
        let now = net.now;
        net.a.with_env(now, |c, env| c.set_link_down(env, false));
        net.run(now + MS, |_| false);
        assert_eq!(net.a.conn.stats().handshake_retransmits, 4);
        assert!(net.a.tx_log.len() > sent && net.a.tx_log.last().unwrap().0 <= now + MS);
    });
}

/// A full session that leaves the client with a resumption ticket.
fn first_session(w: &mut World) -> vinc_security::ClientTickets<8> {
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(w, &mut sa, &mut sb, Link::new(4, Params::new(10 * MS)));
    assert!(net.connect(net.now + 10 * SEC));
    assert!(
        net.run(net.now + 5 * SEC, |n| !n.a.tickets.is_empty()),
        "no tickets arrived"
    );
    std::mem::take(&mut net.a.tickets)
}

#[test]
fn a_lost_resume_reply_is_sent_again_when_the_hello_is() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut link = Link::new(49, Params::new(10 * MS));
        link.route(PathId(1)).ba.drop_next(1);
        let mut net = Net::new(a, b, link, &mut w.stores);
        let t0 = net.now;
        assert!(
            net.connect(t0 + 5 * SEC),
            "the client was left waiting for a reply that never came"
        );
        assert!(net.a.conn.session().unwrap().resumed && net.b.conn.session().unwrap().resumed);
        // The Hello was sent a second time at 500 ms and answered again.
        assert_eq!(net.a.conn.stats().handshake_retransmits, 1);
        assert!(net.now - t0 >= 500 * MS && net.now - t0 < 700 * MS);
    });
}

#[test]
fn an_unanswered_hello_falls_back_after_three_tries_and_a_late_reply_still_resumes() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        // Replies take 2 s: the Hello is sent at 0, 0.5 s, and the third send at 1.5 s is a full Initial.
        let mut link = Link::new(48, Params::new(10 * MS));
        link.route(PathId(1)).ba.p.delay_ns = 2 * SEC;
        let mut net = Net::new(a, b, link, &mut w.stores);
        let t0 = net.now;
        net.run(t0 + 1700 * MS, |_| false);
        assert_eq!(net.a.conn.stats().handshake_retransmits, 2);
        assert!(!net.a.conn.is_connected());
        // The first reply arrives at about 2.01 s and completes the resumption.
        assert!(net.run(t0 + 2100 * MS, |n| n.a.conn.is_connected()));
        let est = net.a.conn.session().unwrap();
        assert!(est.resumed, "the late reply resumed the session");
        assert!(net.run(t0 + 5 * SEC, |n| n.b.conn.is_connected() && n.a.conn.is_connected()));
        assert!(net.a.closed().is_none() && net.b.closed().is_none());
    });
}

#[test]
fn the_handshake_buffers_go_back_to_the_pool() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(47, Params::new(10 * MS)));
        assert_eq!(
            net.a.conn.pool().used_chunks(),
            1,
            "one chunk holds both directions of the handshake"
        );
        assert_eq!(net.b.conn.pool().used_chunks(), 1);
        assert!(net.connect(net.now + 5 * SEC));
        // The server's chunk goes at establishment, the client's when the first 1-RTT packet arrives.
        net.run(net.now + 200 * MS, |_| false);
        assert_eq!(net.a.conn.pool().used_chunks(), 0);
        assert_eq!(net.b.conn.pool().used_chunks(), 0);
        // And the connection works without them.
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"hello").unwrap();
        net.a.conn.finish(id).unwrap();
        assert!(net.run(net.now + SEC, |n| n.b.fin.contains(&id)));
    });
}

#[test]
fn a_resumed_responder_returns_its_buffers_at_the_first_1_rtt_packet() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(46, Params::new(10 * MS)), &mut w.stores);
        assert!(net.connect(net.now + 5 * SEC));
        net.run(net.now + 300 * MS, |_| false);
        assert_eq!(net.b.conn.pool().used_chunks(), 0);
        assert_eq!(net.a.conn.pool().used_chunks(), 0);
    });
}

#[test]
fn the_dialing_side_gives_the_responder_a_ticket_to_resume_towards_it() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(45, Params::new(10 * MS)));
        assert!(net.connect(net.now + 5 * SEC));
        let mut issued: vinc_security::ServerTickets<4> = vinc_security::ServerTickets::new();
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.issue_tickets(env, &mut issued, 1, 3600))
            .unwrap();
        assert_eq!(issued.len(), 1);
        assert!(
            net.run(net.now + 2 * SEC, |n| !n.b.tickets.is_empty()),
            "the responder keeps it"
        );
        // It is the ticket of the dialing side's node, valid for the session's protocol.
        let taken = net.b.tickets.take(&dialer_id(&net), ALPN, net.now);
        assert!(taken.is_some());
        // Before the session is open there is nothing to issue for.
        let (mut sa2, mut sb2) = (Store::new(true), Store::new(false));
        let mut w2 = World::new(IdentityAlg::Ed25519);
        let mut fresh = setup(&mut w2, &mut sa2, &mut sb2, Link::new(44, Params::new(10 * MS)));
        let now = fresh.now;
        let r = fresh
            .a
            .with_env(now, |c, env| c.issue_tickets(env, &mut issued, 1, 3600));
        assert_eq!(r, Err(vinc_security::Failure::UnexpectedMessage));
    });
}

fn dialer_id(net: &Net<'_, '_>) -> vinc_crypto::NodeId {
    net.b.conn.session().unwrap().peer
}

#[test]
fn a_thin_node_resends_its_finish_only_after_twice_the_round_trip() {
    big_stack(|| {
        // Replies take 300 ms (a thin link). The Finish is lost; a thin node waits max(backoff, 2 x 600 ms).
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.thin = true;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(43, Params::new(10 * MS));
        link.route(PathId(1)).ba.p.delay_ns = 590 * MS;
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        net.drop_finish = true;
        let t0 = net.now;
        assert!(net.run(t0 + 5 * SEC, |n| n.a.conn.is_connected()));
        // The first resend is lost too, so the second shows the wait that follows it.
        net.link.route(PathId(1)).ab.drop_next(1);
        assert!(net.connect(t0 + 20 * SEC));
        let resends: Vec<u64> = net
            .a
            .tx_log
            .iter()
            .map(|t| t.0)
            .filter(|t| *t > t0 + 700 * MS)
            .collect();
        assert!(resends.len() >= 2, "{resends:?}");
        let next = resends
            .iter()
            .find(|t| **t > resends[0] + 500 * MS)
            .expect("a second resend");
        let gap = next - resends[0];
        // The wait after the first resend is at least twice the round trip, 1.2 s, not the 2 x PTO it would be.
        assert!(gap >= 1200 * MS, "waited {} ms", gap / MS);
        assert_eq!(net.a.conn.stats().handshake_retransmits, 3);
    });
}

#[test]
fn a_lost_finish_is_resent_999_ms_later_whatever_the_measured_round_trip() {
    big_stack(|| {
        // Replies take 590 ms, so the handshake round trip is about 600 ms and the probe timeout several seconds. One
        // flight went out before the Finish, so the waits are 999 ms, then 999 ms << 1, then the 2 s cap.
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(44, Params::new(10 * MS));
        link.route(PathId(1)).ba.p.delay_ns = 590 * MS;
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        net.drop_finish = true;
        let t0 = net.now;
        assert!(net.run(t0 + 5 * SEC, |n| n.a.conn.is_connected()));
        let sent = net.now;
        net.link.route(PathId(1)).ab.drop_next(3);
        let before = net.a.conn.stats().handshake_retransmits;
        // The re-sends the dialing side has made by each instant after the Finish: none before 999 ms, one at 1 s, a
        // second 1998 ms later, a third 2 s after that.
        let mut count = |at: u64| {
            net.run(sent + at, |_| false);
            net.a.conn.stats().handshake_retransmits - before
        };
        assert_eq!(count(990 * MS), 0, "resent before 999 ms");
        assert_eq!(count(1010 * MS), 1, "not resent at 999 ms");
        assert_eq!(count(2990 * MS), 1, "second resent before 999 + 1998 ms");
        assert_eq!(count(3010 * MS), 2, "second not resent at 999 + 1998 ms");
        assert_eq!(count(4990 * MS), 2, "third resent before 2 s later");
        assert_eq!(count(5010 * MS), 3, "third not resent 2 s later");
    });
}
