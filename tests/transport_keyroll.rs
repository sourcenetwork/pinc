//! The key roll of a real connection: a lost answer is answered again, and a late copy of a request of a settled
//! roll changes nothing. Each test drives two connections datagram by datagram (loss, delay and repetition are steps
//! of the test) and reads what the key layer did through the `trace` feature of `vinc-transport`.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names,
    unreachable_pub
)]

use vinc_crypto::IdentityAlg;
use vinc_security::Rekey;
use vinc_tests::*;
use vinc_transport::conn::{KeyEvent, Slot};

/// A settled connection whose keys roll after `after` packets, and its stream ids (A to B, B to A).
fn connected<'a>(w: &'a mut World, sa: &'a mut Store, sb: &'a mut Store, after: u64) -> (Pair<'a>, u64, u64) {
    w.cfg.key_update_after = after;
    let mut net = setup(w, sa, sb, Link::new(1, Params::new(MS)));
    assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
    let mut pair = Pair::from_net(net);
    let (ia, ib) = (pair.a.conn.open_bi().unwrap(), pair.b.conn.open_bi().unwrap());
    pair.settle();
    pair.events.clear();
    (pair, ia, ib)
}

/// Write on a stream of node `a` until it sealed a request, building (not delivering) its packets; returns the
/// indices of the datagrams built and the request.
fn until_request(pair: &mut Pair<'_>, a: bool, stream: u64) -> (Vec<usize>, Rekey) {
    let data = pattern(1100, 5);
    let mut built = Vec::new();
    for _ in 0..40 {
        let _ = pair.node(a).conn.write(stream, &data);
        built.extend(pair.pump(a));
        if let Some(req) = sent_rekey(pair, a, false) {
            return (built, req);
        }
    }
    panic!("no request after 40 writes")
}

/// The first REKEY message of the given kind that node `a` sent.
fn sent_rekey(pair: &Pair<'_>, a: bool, answer: bool) -> Option<Rekey> {
    pair.events.iter().find_map(|l| match &l.ev {
        KeyEvent::Sent { rekey: Some(r), .. } if l.a == a && r.answer == answer => Some(*r),
        _ => None,
    })
}

/// The first REKEY message of the given kind that node `a` sealed after event `from`, with its datagram.
fn sent_rekey_after(pair: &Pair<'_>, from: usize, a: bool, answer: bool) -> Option<(Rekey, usize)> {
    pair.events[from..].iter().find_map(|l| match &l.ev {
        KeyEvent::Sent { rekey: Some(r), .. } if l.a == a && r.answer == answer => Some((*r, l.dgram.unwrap())),
        _ => None,
    })
}

fn updates(pair: &Pair<'_>) -> (u64, u64) {
    (pair.a.conn.stats().key_updates, pair.b.conn.stats().key_updates)
}

#[test]
fn a_repeated_request_is_answered_again_while_the_keys_are_staged() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let (mut pair, ia, _) = connected(&mut w, &mut sa, &mut sb, 8);
        let (built, req) = until_request(&mut pair, true, ia);
        // The request reaches B, which stages the new keys and answers; the answer is lost.
        pair.deliver_all(&built);
        let first = pair.pump(false);
        let answer = sent_rekey(&pair, false, true).expect("B answers");
        assert_eq!(answer.echo, vinc_security::keyroll::request_id(&req.share));
        assert!(
            pair.b.conn.trace_keys().unwrap().next.is_some(),
            "B staged the new keys"
        );
        let _ = first;
        // A sends the request again after a probe timeout. B receives the repeat in a new packet: no time has
        // passed at B, so only the repeat can make it answer again.
        let before = pair.events.len();
        let mut again = Vec::new();
        for _ in 0..8 {
            pair.now = pair
                .a
                .conn
                .rekey_deadline()
                .expect("the request is pending")
                .max(pair.now);
            pair.fire_timers(true);
            again.extend(pair.pump(true));
            if sent_rekey_after(&pair, before, true, false).is_some() {
                break;
            }
        }
        let repeat = sent_rekey_after(&pair, before, true, false).expect("A sends the request again");
        assert_eq!(repeat.0, req);
        assert!(again.contains(&repeat.1));
        pair.deliver(repeat.1);
        let before = pair.events.len();
        pair.pump(false);
        let resent = sent_rekey_after(&pair, before, false, true).map(|r| r.0);
        assert_eq!(resent, Some(answer), "the same answer goes out again");
        // The answer arrives and the roll completes on both sides.
        pair.settle();
        assert_eq!(updates(&pair), (1, 1));
    });
}

#[test]
fn a_late_copy_of_the_request_that_lost_a_collision_is_ignored() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let (mut pair, ia, ib) = connected(&mut w, &mut sa, &mut sb, 8);
        // Both sides ask at once: A (the dialer) and B (the acceptor) each build their request.
        let (from_a, _) = until_request(&mut pair, true, ia);
        let (from_b, loser) = until_request(&mut pair, false, ib);
        let late = pair
            .events
            .iter()
            .find_map(|l| match &l.ev {
                KeyEvent::Sent { rekey: Some(r), .. } if !l.a && !r.answer => l.dgram,
                _ => None,
            })
            .unwrap();
        assert!(from_b.contains(&late));
        // B receives A's request: it drops its own and answers. B's request packet stays on the network.
        pair.deliver_all(&from_a);
        let answered = pair.pump(false);
        let b_new: Vec<usize> = answered.into_iter().filter(|i| !from_b.contains(i)).collect();
        assert!(sent_rekey(&pair, false, true).is_some(), "B answered");
        // The answer completes A's roll; both sides move to the new keys.
        pair.deliver_all(&b_new);
        for _ in 0..8 {
            let mut sent = pair.pump(true);
            sent.extend(pair.pump(false).into_iter().filter(|i| *i != late));
            pair.deliver_all(&sent);
        }
        assert_eq!(updates(&pair), (1, 1), "the first roll completed");
        assert!(
            pair.a.conn.trace_keys().unwrap().prev.is_some(),
            "A still holds the old key"
        );
        // The late copy of B's request arrives at A within the hold: it is ignored.
        let before = pair.events.len();
        pair.deliver(late);
        let seen = pair.events[before..]
            .iter()
            .find_map(|l| match &l.ev {
                KeyEvent::Received {
                    rekey: Some(r), slot, ..
                } if l.a => Some((*r, *slot)),
                _ => None,
            })
            .expect("A processed the packet");
        assert_eq!(seen, (loser, Some(Slot::Previous)));
        let view = pair.a.conn.trace_keys().unwrap();
        assert!(view.next.is_none() && view.staged_send.is_none(), "A staged nothing");
        assert!(view.out.is_none(), "A queued no answer");
        // A further roll is still possible.
        let data = pattern(1100, 6);
        for _ in 0..60 {
            if updates(&pair) == (2, 2) {
                break;
            }
            for (a, id) in [(true, ia), (false, ib)] {
                let _ = pair.node(a).conn.write(id, &data);
            }
            pair.settle();
        }
        assert_eq!(updates(&pair), (2, 2), "the next roll completes");
    });
}
