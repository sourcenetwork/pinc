//! A dialing side reassembles its Reply from fragments a third party can race with forged ones (damaged copies, other
//! offsets and lengths, another message length): the two candidates of the reassembly keep the genuine message
//! reachable, a message that completes and does not authenticate goes back to what the candidate held, and a refused
//! fragment is counted.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::cell::RefCell;
use std::rc::Rc;

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::{CloseReason, PathId};
use pinc_transport::packet::LongHeader;
use pinc_wire::{Reader, Writer};

/// The Reply of a Hybrid responder in its datagrams, which never reach the dialing side over the link.
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
    let got: Vec<Vec<u8>> = sent
        .borrow()
        .iter()
        .filter(|d| LongHeader::parse(d).is_ok())
        .cloned()
        .collect();
    assert!(!got.is_empty(), "the responder sent no Reply");
    got
}

/// Hand the dialing side each datagram in turn, serving its key operations between them (the host does, between two
/// datagrams it reads).
fn deliver(net: &mut Net<'_, '_>, datagrams: &[Vec<u8>]) {
    let now = net.now;
    for d in datagrams {
        let mut d = d.clone();
        let _ = net
            .a
            .with_lent(now, |c, env, l| c.handle_datagram(env, l, PathId(1), &mut d));
        net.a.service(now);
    }
}

/// Hand the dialing side the datagrams with no key answer between them (the host answers the Decapsulate request later),
/// then serve its key operations until none is pending.
fn deliver_late(net: &mut Net<'_, '_>, datagrams: &[Vec<u8>]) {
    let now = net.now;
    for d in datagrams {
        let mut d = d.clone();
        let _ = net
            .a
            .with_lent(now, |c, env, l| c.handle_datagram(env, l, PathId(1), &mut d));
    }
    for _ in 0..8 {
        net.a.service(now);
        if net.a.conn.pending_key_request().is_none() {
            break;
        }
    }
}

/// The fragment's message length, offset and bytes.
fn parts(d: &[u8]) -> (usize, usize, Vec<u8>, LongHeader) {
    let (h, at) = LongHeader::parse(d).unwrap();
    let mut r = Reader::new(&d[at..at + h.body_len]);
    let (total, off) = (r.read_varint().unwrap() as usize, r.read_varint().unwrap() as usize);
    (total, off, r.read_bytes(r.remaining()).unwrap().to_vec(), h)
}

/// A datagram of the same ids carrying `data` at `off` of a message of `total` bytes.
fn piece(h: &LongHeader, total: usize, off: usize, data: &[u8]) -> Vec<u8> {
    let mut body = vec![0u8; data.len() + 16];
    let mut w = Writer::new(&mut body);
    w.put_varint(total as u64).unwrap();
    w.put_varint(off as u64).unwrap();
    w.put_slice(data).unwrap();
    let n = w.written().len();
    let h = LongHeader { body_len: n, ..*h };
    let mut d = vec![0u8; h.header_len() + n];
    let mut w = Writer::new(&mut d);
    h.write(&mut w, 0).unwrap();
    w.put_slice(&body[..n]).unwrap();
    d
}

/// The Reply message of an Ed25519 responder cut into the two genuine datagrams of the model of the reassembly (a
/// message in two datagrams, each sent once per flight), and what a third party needs to forge more of them.
struct Cut {
    g: [Vec<u8>; 2],
    h: LongHeader,
    total: usize,
    msg: Vec<u8>,
}

impl Cut {
    fn of(net: &mut Net<'_, '_>) -> Self {
        let reply = reply_datagrams(net);
        let msg = first_message(reply.iter().map(Vec::as_slice)).unwrap();
        let (total, _, _, h) = parts(&reply[0]);
        assert_eq!(total, msg.len());
        let k = total / 2;
        Self {
            g: [piece(&h, total, 0, &msg[..k]), piece(&h, total, k, &msg[k..])],
            h,
            total,
            msg,
        }
    }

    /// Genuine datagram `i` with one byte flipped.
    fn damaged(&self, i: usize) -> Vec<u8> {
        let (total, off, mut data, _) = parts(&self.g[i]);
        let k = data.len() / 2;
        data[k] ^= 1;
        piece(&self.h, total, off, &data)
    }

    /// `len` bytes of the message at `off` flipped, as a message of `total` bytes.
    fn forged(&self, total: usize, off: usize, len: usize) -> Vec<u8> {
        let data: Vec<u8> = self.msg[off..off + len].iter().map(|b| b ^ 0x5a).collect();
        piece(&self.h, total, off, &data)
    }
}

fn fresh<'a>(w: &'a mut World, sa: &'a mut Store, sb: &'a mut Store, seed: u64) -> Net<'a, 'a> {
    setup(w, sa, sb, Link::new(seed, Params::new(10 * MS)))
}

/// Every genuine datagram raced by a damaged copy of itself, before or after it: the Reply is taken by the end of the
/// second flight.
#[test]
fn every_datagram_of_a_reply_raced_by_a_damaged_copy_is_still_taken_by_the_second_flight() {
    big_stack(|| {
        for mask in 0..4usize {
            let mut w = World::new(IdentityAlg::Ed25519);
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut net = fresh(&mut w, &mut sa, &mut sb, 81);
            let c = Cut::of(&mut net);
            let mut flight = Vec::new();
            for i in 0..2 {
                if mask >> i & 1 == 1 {
                    flight.extend([c.damaged(i), c.g[i].clone()]);
                } else {
                    flight.extend([c.g[i].clone(), c.damaged(i)]);
                }
            }
            deliver(&mut net, &flight);
            deliver(&mut net, &c.g);
            assert!(
                net.a.conn.is_connected(),
                "order {mask}: the Reply was not taken by the second flight"
            );
        }
    });
}

/// One forged fragment of any offset and length in a flight, and one of another message length: the Reply is taken by
/// the end of the second flight, and one in every flight is taken by the end of the third.
#[test]
fn a_forged_fragment_of_any_offset_length_and_message_length_does_not_block_the_reply() {
    big_stack(|| {
        for (k, (total_shift, off, len)) in [(0usize, 1usize, 2usize), (1, 0, 3), (0, 0, 2), (0, 3, 1)]
            .into_iter()
            .enumerate()
        {
            let mut w = World::new(IdentityAlg::Ed25519);
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut net = fresh(&mut w, &mut sa, &mut sb, 82);
            let c = Cut::of(&mut net);
            let forged = c.forged(c.total - total_shift, off, len);
            for _ in 0..2 {
                deliver(&mut net, &[c.g[0].clone(), forged.clone(), c.g[1].clone()]);
            }
            assert!(
                net.a.conn.is_connected(),
                "forgery {k}: the Reply was not taken by the second flight"
            );
        }
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = fresh(&mut w, &mut sa, &mut sb, 85);
        let c = Cut::of(&mut net);
        // One forged fragment in every flight, each before the genuine datagrams it contradicts.
        for forged in [
            c.forged(c.total, 1, 2),
            c.forged(c.total - 1, 0, 3),
            c.forged(c.total, c.total / 2 + 1, 2),
        ] {
            deliver(&mut net, &[forged, c.g[0].clone(), c.g[1].clone()]);
        }
        assert!(net.a.conn.is_connected(), "the Reply was not taken by the third flight");
    });
}

/// A responder that holds the start of a first message refuses a fragment of another message length and one that
/// disagrees in bytes at a held offset, and counts each (`handshake_conflicts`: 0, 1, then 2).
#[test]
fn a_fragment_of_another_message_length_is_refused_and_counted_by_the_responder() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = fresh(&mut w, &mut sa, &mut sb, 83);
        let sent: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
        let sink = Rc::clone(&sent);
        net.on_tx = Some(Box::new(move |is_a, d, _| {
            if is_a {
                sink.borrow_mut().push(d.to_vec());
            }
        }));
        net.flush();
        net.on_tx = None;
        let first = sent
            .borrow()
            .iter()
            .find(|d| LongHeader::parse(d).is_ok())
            .cloned()
            .unwrap();
        let msg = first_message(sent.borrow().iter().map(Vec::as_slice)).unwrap();
        let (total, _, _, h) = parts(&first);
        let k = total / 2;
        let now = net.now;
        let feed = |net: &mut Net<'_, '_>, mut d: Vec<u8>| {
            let stores = &mut *net.stores;
            let _ = net.b.with_lent(now, |c, env, l| {
                c.handle_datagram_with(env, l, stores, PathId(2), &mut d)
            });
        };
        feed(&mut net, piece(&h, total, 0, &msg[..k]));
        assert_eq!(net.b.conn.stats().handshake_conflicts, 0);
        feed(&mut net, piece(&h, total - 1, k, &msg[k..total - 1]));
        assert_eq!(net.b.conn.stats().handshake_conflicts, 1);
        // A fragment of the same length that disagrees in bytes with the held start is refused and counted too.
        let mut bent = msg[..k].to_vec();
        bent[k / 2] ^= 1;
        feed(&mut net, piece(&h, total, 0, &bent));
        assert_eq!(net.b.conn.stats().handshake_conflicts, 2);
        // The refused fragments changed nothing: the rest of the real message completes it.
        feed(&mut net, piece(&h, total, k, &msg[k..]));
        assert_eq!(net.b.conn.stats().handshake_conflicts, 2);
        assert!(net.b.conn.has_path(PathId(2)), "the real message was not taken");
    });
}

/// The genuine first part, a damaged last part, then the genuine last part, all before the verdict on the first
/// completion is answered: the genuine last part is held, not applied beside the damaged one, and completes the
/// message once the verdict fails. Witness shape `ReasmPair_keep`.
#[test]
fn a_damaged_last_part_ahead_of_the_genuine_one_does_not_hide_it_while_the_verdict_waits() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = fresh(&mut w, &mut sa, &mut sb, 86);
        let c = Cut::of(&mut net);
        deliver_late(&mut net, &[c.g[0].clone(), c.damaged(1), c.g[1].clone()]);
        assert!(net.a.conn.is_connected(), "the Reply was not taken by one flight");
    });
}

/// A candidate a fragment completed goes back to its runs at once, while the verdict on it waits, so the genuine
/// fragment of the next flight completes it. Witness shape `ReasmPair_async`.
#[test]
fn a_completed_candidate_goes_back_at_once_while_its_verdict_waits() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = fresh(&mut w, &mut sa, &mut sb, 87);
        let c = Cut::of(&mut net);
        deliver_late(&mut net, &[c.g[0].clone(), c.damaged(1)]);
        deliver(&mut net, &[c.g[1].clone()]);
        assert!(
            net.a.conn.is_connected(),
            "the Reply was not taken by the second flight"
        );
    });
}

/// A fragment that completes both candidates: the one the machine holds fails its verdict, and the other, kept as
/// ready, is fed at once, so the same flight connects and nothing is counted as a conflict.
#[test]
fn the_other_candidate_completed_by_the_same_fragment_is_fed_after_a_failed_verdict() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = fresh(&mut w, &mut sa, &mut sb, 88);
        let c = Cut::of(&mut net);
        let conflicts = net.a.conn.stats().handshake_conflicts;
        deliver_late(&mut net, &[c.damaged(0), c.g[0].clone(), c.g[1].clone()]);
        assert!(net.a.conn.is_connected(), "the Reply was not taken by one flight");
        assert_eq!(net.a.conn.stats().handshake_conflicts, conflicts);
    });
}

/// Fragments held beyond the chunk are dropped and counted, each once; the next flight carries them again.
#[test]
fn fragments_held_beyond_a_chunk_are_dropped_and_counted() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = fresh(&mut w, &mut sa, &mut sb, 89);
        let c = Cut::of(&mut net);
        let mut flight = vec![c.g[0].clone(), c.damaged(1)];
        // Enough copies to fill a 16384-byte chunk, whatever the size of a part (a held part costs its body and 22 bytes).
        let copies = 2 * 16384 / c.damaged(0).len() + 2;
        flight.extend((0..copies).map(|_| c.damaged(0)));
        flight.push(c.g[1].clone());
        // Every fragment after the one that completed the message is held, in order, at its body and 22 bytes, until a
        // chunk of 16384 bytes has no room for the next one; each refused one is counted once.
        let (mut used, mut refused) = (0usize, 0u64);
        for d in &flight[2..] {
            let need = 22 + parts(d).3.body_len;
            if used + need <= 16384 {
                used += need;
            } else {
                refused += 1;
            }
        }
        assert!(refused > 0);
        deliver_late(&mut net, &flight);
        assert_eq!(net.a.conn.stats().handshake_held_full, refused);
        deliver(&mut net, &c.g);
        assert!(net.a.conn.is_connected(), "the Reply was not taken by the next flight");
    });
}

/// A held fragment is let go with the verdict: after a good one the pool holds what it held without a held fragment.
#[test]
fn the_hold_is_back_in_the_pool_after_the_verdict() {
    big_stack(|| {
        let used = |held: bool| {
            let mut w = World::new(IdentityAlg::Ed25519);
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut net = fresh(&mut w, &mut sa, &mut sb, 90);
            let c = Cut::of(&mut net);
            let mut flight = c.g.to_vec();
            if held {
                flight.push(c.g[1].clone());
            }
            deliver_late(&mut net, &flight);
            assert!(net.a.conn.is_connected());
            net.a.conn.pool().used_chunks()
        };
        assert_eq!(used(true), used(false));
    });
}

/// Hand the dialing side one datagram as arriving on `path`, then let its host compute (not deliver) the key answer.
fn deliver_on(net: &mut Net<'_, '_>, path: u64, d: &[u8]) {
    let now = net.now;
    let mut d = d.to_vec();
    let _ = net
        .a
        .with_lent(now, |c, env, l| c.handle_datagram(env, l, PathId(path), &mut d));
    net.a.service(now);
}

/// A genuine first part, then a damaged last part that completes the message on path 7 (its verdict waits for the key
/// host), then the genuine last part held from path 8 and a damaged first part held from path 7 (the path the verdict
/// waits on). The failed verdict replays the genuine last part, which completes the message on path 8 and moves the
/// reply's path there; the part from path 7 is still held, so its path must still be named by `path_ids` (it was
/// recorded only because it was not a slot's, even while it was the reply's path).
fn held_from_the_reply_path(net: &mut Net<'_, '_>, c: &Cut) {
    net.a.auto_keys = false;
    deliver_on(net, 1, &c.g[0]);
    deliver_on(net, 7, &c.damaged(1));
    assert!(
        net.a.deferred.is_some(),
        "the damaged message did not wait for the key host"
    );
    deliver_on(net, 8, &c.g[1]);
    deliver_on(net, 7, &c.damaged(0));
}

/// The Reply was taken: the dialing side's host answers the request that signs its Finish, a key operation of its
/// own and not a verdict on the Reply, so it does not end the session's handshake by itself.
fn sign_finish(net: &mut Net<'_, '_>) {
    let now = net.now;
    net.a.service(now);
    assert!(
        matches!(
            net.a.conn.pending_key_request(),
            Some(pinc_security::KeyRequest::Sign { .. })
        ),
        "the dialing side does not wait to sign its Finish"
    );
    assert!(net.a.deliver_deferred(now).is_ok());
    net.a.service(now);
}

/// A fragment held from the path the verdict waits on keeps that path named after the replay moved the reply's path:
/// `path_ids` holds it until the fragment is taken. Pins the record of a held fragment's path in `hold_ids` when the
/// path is also `reply_from` (`hold_part`).
#[test]
fn a_fragment_held_from_the_reply_path_keeps_its_path_named_after_the_reply_path_moves() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = fresh(&mut w, &mut sa, &mut sb, 91);
        let c = Cut::of(&mut net);
        held_from_the_reply_path(&mut net, &c);
        let now = net.now;
        assert!(
            net.a.deliver_deferred(now).is_err(),
            "the damaged message authenticated"
        );
        net.a.service(now);
        assert!(
            net.a.deferred.is_some(),
            "the replayed genuine last part did not wait for the key host"
        );
        let ids = net.a.conn.path_ids();
        assert!(ids.contains(&Some(PathId(8))), "the reply's path is not named: {ids:?}");
        assert!(
            ids.contains(&Some(PathId(7))),
            "the path of the held fragment is not named: {ids:?}"
        );
        assert!(net.a.deliver_deferred(now).is_ok());
        sign_finish(&mut net);
        assert!(net.a.conn.is_connected(), "the genuine Reply was not taken");
    });
}

/// After a verdict that takes the Reply, no path of a held fragment is named any more: the pair table is not kept
/// full by a fragment that was let go. Pins the clear of `hold_ids` on a verdict that is not a failed authentication
/// (`after_verdict`).
#[test]
fn the_path_of_a_held_fragment_is_let_go_when_the_reply_is_taken() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = fresh(&mut w, &mut sa, &mut sb, 92);
        let c = Cut::of(&mut net);
        held_from_the_reply_path(&mut net, &c);
        let now = net.now;
        assert!(net.a.deliver_deferred(now).is_err());
        net.a.service(now);
        assert!(net.a.deliver_deferred(now).is_ok());
        let ids = net.a.conn.path_ids();
        assert!(
            !ids.contains(&Some(PathId(7))),
            "the path of a fragment that was let go is still named: {ids:?}"
        );
        sign_finish(&mut net);
        assert!(net.a.conn.is_connected());
    });
}

/// A failed verdict that applies every held fragment leaves no path of a held fragment named. Pins the clear of
/// `hold_ids` when the replay empties the hold (`after_verdict`).
#[test]
fn the_path_of_a_held_fragment_is_let_go_when_the_replay_empties_the_hold() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = fresh(&mut w, &mut sa, &mut sb, 93);
        let c = Cut::of(&mut net);
        net.a.auto_keys = false;
        deliver_on(&mut net, 1, &c.g[0]);
        deliver_on(&mut net, 7, &c.damaged(1));
        deliver_on(&mut net, 9, &c.damaged(0));
        assert!(
            net.a.conn.path_ids().contains(&Some(PathId(9))),
            "the held fragment's path is not named"
        );
        let now = net.now;
        assert!(net.a.deliver_deferred(now).is_err());
        assert!(
            net.a.deferred.is_none(),
            "a fragment that completes nothing asked the key host again"
        );
        let ids = net.a.conn.path_ids();
        assert!(
            !ids.contains(&Some(PathId(9))),
            "the path of a fragment that was applied is still named: {ids:?}"
        );
    });
}

/// A verdict that ends the session (the key host failed) frees the chunk the held fragments took: the pool holds what
/// it holds when no fragment was held. Pins `drop_held` on a verdict that is not a failed authentication
/// (`after_verdict`).
#[test]
fn a_verdict_that_ends_the_session_frees_the_held_fragments() {
    big_stack(|| {
        let used = |held: bool| {
            let mut w = World::new(IdentityAlg::Ed25519);
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut net = fresh(&mut w, &mut sa, &mut sb, 94);
            let c = Cut::of(&mut net);
            net.a.auto_keys = false;
            net.a.fail_keys = true;
            deliver_on(&mut net, 1, &c.g[0]);
            deliver_on(&mut net, 1, &c.g[1]);
            assert!(net.a.deferred.is_some());
            if held {
                deliver_on(&mut net, 1, &c.g[1]);
            }
            let now = net.now;
            assert!(
                net.a.deliver_deferred(now).is_err(),
                "the failed key answer did not fail the handshake"
            );
            net.a.conn.pool().used_chunks()
        };
        assert_eq!(used(true), used(false));
    });
}

/// A session that ended while the verdict on a Reply waited (its connect limit passed) takes no handshake packet any
/// more, and neither does the replay of what it held: a late failed verdict applies no held fragment, so the genuine
/// last part held meanwhile does not complete the Reply and ask the key host to open it. Pins the check of the replay
/// against the session's phase, the one `on_handshake` makes (`after_verdict`).
#[test]
fn a_late_failed_verdict_on_a_session_that_ended_applies_no_held_fragment() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = fresh(&mut w, &mut sa, &mut sb, 95);
        let c = Cut::of(&mut net);
        net.a.auto_keys = false;
        deliver_on(&mut net, 1, &c.g[0]);
        deliver_on(&mut net, 1, &c.damaged(1));
        assert!(
            net.a.deferred.is_some(),
            "the damaged message did not wait for the key host"
        );
        deliver_on(&mut net, 1, &c.g[1]);
        let until = net.now + 40_000 * MS;
        net.run(until, |_| false);
        assert_eq!(net.a.closed(), Some(CloseReason::HandshakeTimeout));
        let now = net.now;
        assert!(
            net.a.deliver_deferred(now).is_err(),
            "the damaged message authenticated"
        );
        net.a.service(now);
        assert!(
            net.a.deferred.is_none() && net.a.conn.pending_key_request().is_none(),
            "a session that ended applied a held fragment and asked the key host to open the Reply it completed"
        );
    });
}
