//! The key roll state machine and the schedule: the REKEY encoding, the exchange, the collision rule, the triggers
//! and the post-compromise property.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    unreachable_pub
)]

use pinc_crypto::{Aead, Drbg, Provider, Secret, Software};
use pinc_security::keyroll::{MAX_KEY_AGE_NS, MAX_REKEY_LEN, due, request_id};
use pinc_security::{Env, Failure, Limits, PacketKey, Rekey, Roll, roll_secret};

fn env<'a>(p: &'a Software, drbg: &'a mut Drbg) -> Env<'a, Software> {
    Env {
        provider: p,
        now: 0,
        drbg,
    }
}

/// One roll between two machines; returns each side's Diffie-Hellman value and the answer's switch number.
fn exchange(dialer: &mut Roll, acceptor: &mut Roll, switch_pn: u64) -> (Secret<32>, Secret<32>, Rekey) {
    let p = Software;
    let (mut da, mut db) = (Drbg::new(&[1; 32]), Drbg::new(&[2; 32]));
    let request = dialer.start(&mut env(&p, &mut da)).unwrap();
    let answered = acceptor.on_request(&mut env(&p, &mut db), &request, switch_pn).unwrap();
    let theirs = answered.dh.unwrap();
    let done = dialer.on_answer(&env(&p, &mut da), &answered.answer).unwrap();
    assert_eq!(done.peer_switch_pn, switch_pn);
    (done.dh, theirs, answered.answer)
}

#[test]
fn rekey_bodies_encode_and_decode_exactly() {
    let req = Rekey {
        answer: false,
        share: [7; 32],
        echo: [0; 8],
        switch_pn: 0,
    };
    let ans = Rekey {
        answer: true,
        share: [9; 32],
        echo: [3; 8],
        switch_pn: 1 << 40,
    };
    let mut buf = [0u8; MAX_REKEY_LEN];
    let n = req.encode(&mut buf).unwrap();
    assert_eq!((n, buf[0]), (33, 0));
    assert_eq!(Rekey::decode(&buf[..n]).unwrap(), req);
    let n = ans.encode(&mut buf).unwrap();
    assert_eq!((n, buf[0]), (1 + 32 + 8 + 6, 1), "2^40 takes six varint bytes");
    assert_eq!(Rekey::decode(&buf[..n]).unwrap(), ans);
    assert!(MAX_REKEY_LEN >= n);
    // Strict: trailing bytes, short bodies, unknown kinds, and a number over 2^63 are refused.
    let n = ans.encode(&mut buf).unwrap();
    assert!(Rekey::decode(&buf[..n - 1]).is_err());
    assert!(Rekey::decode(&buf[..=n]).is_err());
    assert!(Rekey::decode(&[]).is_err());
    let mut kind = buf;
    kind[0] = 2;
    assert!(Rekey::decode(&kind[..n]).is_err());
    let mut tiny = [0u8; 20];
    assert!(ans.encode(&mut tiny).is_err());
    let big = Rekey {
        switch_pn: u64::MAX,
        ..ans
    };
    assert!(big.encode(&mut buf).is_err());
}

#[test]
fn both_sides_compute_the_same_value_and_roll_in_step() {
    let p = Software;
    for aead in [Aead::ChaCha20Poly1305, Aead::Aes128Gcm] {
        let (mut a, mut b) = (Roll::new(true), Roll::new(false));
        let (dh_a, dh_b, answer) = exchange(&mut a, &mut b, 500);
        assert_eq!(dh_a.expose(), dh_b.expose());
        assert!(answer.answer && answer.switch_pn == 500);
        assert!(a.is_idle() && b.is_idle());
        assert_eq!((a.rolls(), b.rolls()), (1, 1));
        // Each direction's key rolls with the shared value and the peers agree.
        let (s_ab, s_ba) = (Secret::new([1; 32]), Secret::new([2; 32]));
        let mut tx = PacketKey::from_secret(&p, aead, &s_ab)
            .unwrap()
            .rolled(&p, &dh_a)
            .unwrap();
        let mut rx = PacketKey::from_secret(&p, aead, &s_ab)
            .unwrap()
            .rolled(&p, &dh_b)
            .unwrap();
        let mut buf = *b"after the roll";
        let tag = tx.seal(&p, 0, b"h", &mut buf).unwrap();
        rx.open(&p, 0, b"h", &mut buf, &tag).unwrap();
        assert_eq!(&buf, b"after the roll");
        let _ = s_ba;
        assert_eq!((tx.generation(), rx.generation()), (1, 1));
    }
}

#[test]
fn a_request_goes_out_again_until_it_is_answered_and_a_duplicate_gets_the_same_answer() {
    let p = Software;
    let (mut da, mut db) = (Drbg::new(&[1; 32]), Drbg::new(&[2; 32]));
    let (mut a, mut b) = (Roll::new(true), Roll::new(false));
    assert!(a.pending().is_none());
    let request = a.start(&mut env(&p, &mut da)).unwrap();
    assert_eq!(a.pending(), Some(request), "offered again while unanswered");
    assert_eq!(
        a.start(&mut env(&p, &mut da)).unwrap_err(),
        Failure::UnexpectedMessage,
        "one roll at a time"
    );
    let first = b.on_request(&mut env(&p, &mut db), &request, 10).unwrap();
    assert!(first.dh.is_some());
    // The answer was lost: the request arrives again and gets the same answer and no second key.
    let again = b.on_request(&mut env(&p, &mut db), &request, 99).unwrap();
    assert!(again.dh.is_none());
    assert_eq!(again.answer, first.answer, "the first switch number stands");
    assert_eq!(b.rolls(), 1);
    // The answer completes the roll once; a repeat is stale.
    let done = a.on_answer(&env(&p, &mut da), &first.answer).unwrap();
    assert_eq!(done.dh.expose(), first.dh.as_ref().unwrap().expose());
    assert_eq!(
        a.on_answer(&env(&p, &mut da), &first.answer).unwrap_err(),
        Failure::UnexpectedMessage
    );
    assert!(a.pending().is_none());
    // A request is not an answer and an answer is not a request.
    assert_eq!(
        a.on_answer(&env(&p, &mut da), &request).unwrap_err(),
        Failure::UnexpectedMessage
    );
    assert_eq!(
        b.on_request(&mut env(&p, &mut db), &first.answer, 1).unwrap_err(),
        Failure::UnexpectedMessage
    );
}

#[test]
fn when_both_sides_ask_at_once_the_dialing_side_wins() {
    let p = Software;
    let (mut da, mut db) = (Drbg::new(&[1; 32]), Drbg::new(&[2; 32]));
    let (mut dialer, mut acceptor) = (Roll::new(true), Roll::new(false));
    let from_dialer = dialer.start(&mut env(&p, &mut da)).unwrap();
    let from_acceptor = acceptor.start(&mut env(&p, &mut db)).unwrap();
    // The dialer ignores the acceptor's request and keeps its own out.
    assert_eq!(
        dialer.on_request(&mut env(&p, &mut da), &from_acceptor, 5).unwrap_err(),
        Failure::UnexpectedMessage
    );
    assert_eq!(dialer.pending(), Some(from_dialer));
    // The acceptor drops its own and answers the dialer's.
    let answered = acceptor.on_request(&mut env(&p, &mut db), &from_dialer, 5).unwrap();
    assert!(acceptor.pending().is_none());
    let done = dialer.on_answer(&env(&p, &mut da), &answered.answer).unwrap();
    assert_eq!(done.dh.expose(), answered.dh.unwrap().expose());
}

#[test]
fn an_answer_to_another_request_is_ignored() {
    let p = Software;
    let (mut da, mut db) = (Drbg::new(&[1; 32]), Drbg::new(&[2; 32]));
    let (mut a, mut b) = (Roll::new(true), Roll::new(false));
    // The first roll completes; its answer is still on the network.
    let first = a.start(&mut env(&p, &mut da)).unwrap();
    let old = b.on_request(&mut env(&p, &mut db), &first, 10).unwrap();
    a.on_answer(&env(&p, &mut da), &old.answer).unwrap();
    // A second roll is out when the old answer arrives again: it is ignored and the second request stays out.
    let second = a.start(&mut env(&p, &mut da)).unwrap();
    assert_ne!(old.answer.echo, request_id(&second.share));
    assert_eq!(old.answer.echo, request_id(&first.share));
    assert_eq!(
        a.on_answer(&env(&p, &mut da), &old.answer).unwrap_err(),
        Failure::UnexpectedMessage
    );
    assert_eq!(a.pending(), Some(second));
    assert_eq!(a.rolls(), 1, "the ignored answer completed nothing");
    // The answer to the second request completes it, and both sides hold the same value.
    let fresh = b.on_request(&mut env(&p, &mut db), &second, 20).unwrap();
    let done = a.on_answer(&env(&p, &mut da), &fresh.answer).unwrap();
    assert_eq!(done.dh.expose(), fresh.dh.unwrap().expose());
    // An answer whose echo names no request is ignored too.
    let third = a.start(&mut env(&p, &mut da)).unwrap();
    let mut forged = b.on_request(&mut env(&p, &mut db), &third, 30).unwrap().answer;
    forged.echo[0] ^= 1;
    assert_eq!(
        a.on_answer(&env(&p, &mut da), &forged).unwrap_err(),
        Failure::UnexpectedMessage
    );
    assert_eq!(a.pending(), Some(third));
}

#[test]
fn the_echo_is_bound_into_the_derived_value() {
    let p = Software;
    let (mut da, mut db) = (Drbg::new(&[1; 32]), Drbg::new(&[2; 32]));
    let (mut a, mut b) = (Roll::new(true), Roll::new(false));
    // The requester's secret is the first draw of its generator; the plain Diffie-Hellman value is not the result.
    let seed = env(&p, &mut Drbg::new(&[1; 32])).random::<32>().unwrap();
    let request = a.start(&mut env(&p, &mut da)).unwrap();
    let answered = b.on_request(&mut env(&p, &mut db), &request, 1).unwrap();
    let raw = p.x25519_dh(&p.x25519_secret(&seed), &answered.answer.share).unwrap();
    let done = a.on_answer(&env(&p, &mut da), &answered.answer).unwrap();
    assert_ne!(done.dh.expose(), raw.expose());
    assert_eq!(
        done.dh.expose(),
        &pinc_crypto::extract(raw.expose(), &request_id(&request.share)),
        "the value is extract(dh, request id)"
    );
}

#[test]
fn a_request_with_a_weak_share_is_refused() {
    let p = Software;
    let mut db = Drbg::new(&[2; 32]);
    let mut b = Roll::new(false);
    let weak = Rekey {
        answer: false,
        share: [0; 32],
        echo: [0; 8],
        switch_pn: 0,
    };
    assert_eq!(
        b.on_request(&mut env(&p, &mut db), &weak, 1).unwrap_err(),
        Failure::InvalidPeerKey
    );
    assert!(b.is_idle());
}

#[test]
fn a_roll_does_not_follow_from_the_old_secret_alone() {
    let p = Software;
    // Two rolls from the same old secret with different fresh values give unrelated keys, so an attacker who
    // stole the old secret but did not take part in the exchange cannot derive the new one.
    let old = Secret::new([5; 32]);
    let (mut a1, mut b1) = (Roll::new(true), Roll::new(false));
    let (mut a2, mut b2) = (Roll::new(true), Roll::new(false));
    let (dh1, _, _) = exchange(&mut a1, &mut b1, 1);
    let (da, db) = (Drbg::new(&[8; 32]), Drbg::new(&[9; 32]));
    let _ = (da, db);
    let (dh2, _, _) = {
        let (mut x, mut y) = (Drbg::new(&[3; 32]), Drbg::new(&[4; 32]));
        let request = a2.start(&mut env(&p, &mut x)).unwrap();
        let answered = b2.on_request(&mut env(&p, &mut y), &request, 1).unwrap();
        let done = a2.on_answer(&env(&p, &mut x), &answered.answer).unwrap();
        (done.dh, answered.dh.unwrap(), answered.answer)
    };
    assert_ne!(dh1.expose(), dh2.expose());
    assert_ne!(roll_secret(&old, &dh1).expose(), roll_secret(&old, &dh2).expose());
    // The next secret also differs from the old one run through a hash-only step.
    let mut hash_only = [0u8; 32];
    pinc_crypto::expand(old.expose(), "PINC 2026 v1 key roll", &[], &mut hash_only);
    assert_ne!(&hash_only, roll_secret(&old, &dh1).expose());
}

#[test]
fn a_roll_is_due_at_the_aead_limit_at_the_configured_count_and_at_ten_minutes() {
    let p = Software;
    let secret = Secret::new([3; 32]);
    let limits = Limits {
        aes_gcm_packets: 4,
        chacha_failures: 3,
    };
    let key = |aead| PacketKey::from_secret(&p, aead, &secret).unwrap().with_limits(limits);
    let mut buf = [0u8; 8];
    // Fresh keys are not due before the age, and are due at it.
    let (tx, rx) = (key(Aead::Aes128Gcm), key(Aead::Aes128Gcm));
    assert!(!due(&tx, &rx, MAX_KEY_AGE_NS - 1, 1 << 21));
    assert!(due(&tx, &rx, MAX_KEY_AGE_NS, 1 << 21));
    assert_eq!(MAX_KEY_AGE_NS, 600_000_000_000);
    // The configured packet count.
    let mut tx = key(Aead::Aes128Gcm);
    for pn in 0..2 {
        tx.seal(&p, pn, b"", &mut buf).unwrap();
    }
    assert!(!due(&tx, &rx, 0, 3));
    assert!(due(&tx, &rx, 0, 2));
    // The AES-GCM limit itself.
    for pn in 2..4 {
        tx.seal(&p, pn, b"", &mut buf).unwrap();
    }
    assert!(tx.limit_reached());
    assert!(due(&tx, &rx, 0, u64::MAX));
    // The ChaCha20-Poly1305 failed-open count, on the receiving key.
    let (tx, mut rx) = (key(Aead::ChaCha20Poly1305), key(Aead::ChaCha20Poly1305));
    let forged = [0u8; 16];
    for n in 0..3 {
        assert!(!due(&tx, &rx, 0, u64::MAX), "{n} failures");
        let mut copy = buf;
        rx.open(&p, 0, b"", &mut copy, &forged).unwrap_err();
    }
    assert!(rx.limit_reached());
    assert!(due(&tx, &rx, 0, u64::MAX));
    // The protocol's own limits.
    assert_eq!(Limits::default().aes_gcm_packets, 1 << 22);
}

#[test]
fn rolling_allocates_nothing() {
    let p = Software;
    let (mut a, mut b) = (Roll::new(true), Roll::new(false));
    let (mut da, mut db) = (Drbg::new(&[1; 32]), Drbg::new(&[2; 32]));
    let secret = Secret::new([4; 32]);
    let key = PacketKey::from_secret(&p, Aead::Aes128Gcm, &secret).unwrap();
    let mut body = [0u8; MAX_REKEY_LEN];
    let stats = pinc_tests::measure(|| {
        let request = a.start(&mut env(&p, &mut da)).unwrap();
        let n = request.encode(&mut body).unwrap();
        let request = Rekey::decode(&body[..n]).unwrap();
        let answered = b.on_request(&mut env(&p, &mut db), &request, 7).unwrap();
        let done = a.on_answer(&env(&p, &mut da), &answered.answer).unwrap();
        let next = key.rolled(&p, &done.dh).unwrap();
        drop(next);
    });
    assert_eq!(stats.count(), 0, "{stats:?}");
}

pinc_tests::install_counting_allocator!();
