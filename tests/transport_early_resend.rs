//! A resumed dial whose first datagram is lost sends its early data again with the one resend of its Hello: the
//! request reaches the responder one way after the resend, as it does when only the Reply was lost, and not a round
//! trip after the handshake, when loss detection would find it. The early data goes again once: the send after the
//! resend is a full handshake, which has none, and a responder that already holds the data delivers it once.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::PathId;

pinc_tests::install_counting_allocator!();

/// The link's delay each way.
const ONE_WAY: u64 = 25 * MS;
/// The first resend of a dialing side that knows no round trip.
const FIRST_RESEND: u64 = 500 * MS;

/// What a request written before a resumed dial does when the `k`th datagram of one direction is dropped (`from_client`
/// says which; `k` 0 drops none): when the request was whole at the responder, when its answer was whole at the
/// client (both from the start of the dial), and the bytes the responder read on the stream.
fn early_request(from_client: bool, k: u64) -> (u64, u64, Vec<u8>) {
    let mut w = World::new(IdentityAlg::Ed25519);
    let mut tickets = first_session(&mut w);
    let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let a = w.client(&mut sa, Some(ticket), pinc_security::ClientTickets::new());
    let b = w.server(&mut sb);
    let mut link = Link::new(71, Params::new(ONE_WAY));
    if k > 0 {
        let route = link.route(PathId(1));
        if from_client {
            route.ab.drop_index(k);
        } else {
            route.ba.drop_index(k);
        }
    }
    let mut net = Net::new(a, b, link, &mut w.stores);
    let id = net.a.conn.open_bi().unwrap();
    net.a.conn.write(id, b"ping").unwrap();
    net.a.conn.finish(id).unwrap();
    let t0 = net.now;
    let mut at_responder = None;
    let answered = net.run(t0 + 10 * SEC, |n| {
        if at_responder.is_none() && n.b.fin.contains(&id) {
            n.b.conn.write(id, b"pong").unwrap();
            n.b.conn.finish(id).unwrap();
            at_responder = Some(n.now - t0);
        }
        n.a.fin.contains(&id)
    });
    assert!(answered, "no answer: {:?}", net.rx_drops);
    let at_client = net.now - t0;
    // Everything still on its way arrives: a second copy of the request must not be read again.
    net.run(net.now + SEC, |_| false);
    assert_eq!(net.a.read[&id], b"pong");
    assert_eq!((net.a.closed(), net.b.closed()), (None, None));
    (at_responder.unwrap(), at_client, net.b.read[&id].clone())
}

#[test]
fn a_lost_first_datagram_costs_the_resend_and_one_round_trip() {
    big_stack(|| {
        let (at_responder, at_client, read) = early_request(true, 1);
        assert_eq!(
            (at_responder, at_client),
            (FIRST_RESEND + ONE_WAY, FIRST_RESEND + 2 * ONE_WAY),
            "the request did not leave again with the Hello"
        );
        assert_eq!(read, b"ping");
    });
}

#[test]
fn a_request_the_responder_already_holds_is_delivered_once_when_it_arrives_again() {
    big_stack(|| {
        // Only the Reply is lost: the responder has the request after one way, and the resent Hello brings it again.
        let (at_responder, at_client, read) = early_request(false, 1);
        assert_eq!((at_responder, at_client), (ONE_WAY, FIRST_RESEND + 2 * ONE_WAY));
        assert_eq!(read, b"ping");
        // Nothing lost: nothing is sent again.
        let (at_responder, at_client, read) = early_request(true, 0);
        assert_eq!((at_responder, at_client), (ONE_WAY, 2 * ONE_WAY));
        assert_eq!(read, b"ping");
    });
}

#[test]
fn the_early_data_of_a_dial_nobody_answers_goes_again_once() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, Some(ticket), pinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut link = Link::new(72, Params::new(ONE_WAY));
        link.route(PathId(1)).ab.drop_next(u32::MAX);
        let mut net = Net::new(a, b, link, &mut w.stores);
        let id = net.a.conn.open_bi().unwrap();
        let request = pattern(600, 3);
        net.a.conn.write(id, &request).unwrap();
        net.a.conn.finish(id).unwrap();
        let t0 = net.now;
        net.run(t0 + 6 * SEC, |_| false);
        // The Hello with the request, the same again at the first resend, then the full handshake without early data:
        // every later datagram is shorter than the request alone would make it, or is the full first flight.
        let sent: Vec<(u64, usize)> = net.a.tx_log.iter().map(|(t, len, _)| (*t - t0, *len)).collect();
        let with_request = sent[0].1;
        assert!(with_request > request.len(), "{sent:?}");
        assert_eq!(sent[1], (FIRST_RESEND, with_request), "{sent:?}");
        let again = sent.iter().filter(|(_, len)| *len == with_request).count();
        assert_eq!(again, 2, "the request left {again} times: {sent:?}");
        assert!(sent.len() > 2 && sent[2].0 > FIRST_RESEND, "{sent:?}");
    });
}
