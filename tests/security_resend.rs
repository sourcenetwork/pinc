//! The resend rules of the initiator: the short Initial in a resend after a full first Initial while the host allows it,
//! and the prekey reject (the full Initial once, short resends after it, the host told of each reject).
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

use pinc_crypto::IdentityAlg;
use pinc_security::{Env, Output, ResponderStores};

mod sec_common;
use sec_common::{ALPN, World, big_stack};

#[test]
fn a_resend_after_a_full_initial_is_short_while_the_host_allows_it() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        // The message types sent when the loss timer fires at each of `times` after the first send at `w.now`.
        let sent = |w: &mut World, until: Option<u64>, times: &[u64]| {
            let dial = w.dial();
            let mut i = w.initiator_with(dial, ALPN, false, false);
            if let Some(until) = until {
                i.set_short_until(until);
            }
            let mut seen = vec![];
            let Some(Output::Send { data, .. }) = i.poll_output() else {
                panic!("no first message")
            };
            seen.push(data[0]);
            for t in times {
                let mut env = Env {
                    provider: &w.i_prov,
                    now: *t,
                    drbg: &mut w.i_drbg,
                };
                i.retransmit(&mut env).unwrap();
                let Some(Output::Send { data, .. }) = i.poll_output() else {
                    panic!("nothing to send at {t}")
                };
                seen.push(data[0]);
            }
            seen
        };
        let t0 = w.now;
        let ms = |n: u64| t0 + n * 1_000_000;
        // A full first Initial: the resends are short, except the third and sixth send, which carry the full prekey.
        let times = [ms(500), ms(1500), ms(3500), ms(7500), ms(15_500), ms(23_500)];
        assert_eq!(sent(&mut w, Some(u64::MAX), &times), vec![1, 2, 1, 2, 2, 1, 2]);
        // Short Initials stop where the host's allowance ends: the resends at 3.5 s and later are full.
        assert_eq!(sent(&mut w, Some(ms(3000)), &times), vec![1, 2, 1, 1, 1, 1, 1]);
        // A host that never allows them, or never said (the default after a full first Initial): all full.
        assert_eq!(sent(&mut w, Some(0), &times), vec![1; 7]);
        assert_eq!(sent(&mut w, None, &times), vec![1; 7]);
    });
}

/// An initiator that sent the short Initial to a responder that never saw its prekey, and that responder's reject.
fn short_initial_and_its_reject(w: &mut World) -> (pinc_security::Initiator, Vec<u8>) {
    let dial = w.dial();
    let mut i = w.initiator_with(dial, ALPN, true, false);
    let mut r = w.responder();
    let mut stores: ResponderStores<4, 4> = ResponderStores::default();
    let Some(Output::Send { data, .. }) = i.poll_output() else {
        panic!("no first message")
    };
    assert_eq!(data[0], 2, "the first send is the short Initial");
    let mut env = Env {
        provider: &w.r_prov,
        now: w.now,
        drbg: &mut w.r_drbg,
    };
    r.handle(&mut env, &mut stores, data).unwrap();
    let Some(Output::Send { data, .. }) = r.poll_output() else {
        panic!("no reject")
    };
    assert_eq!(data[0], 3, "the responder rejects");
    (i, data.to_vec())
}

#[test]
fn a_prekey_reject_gets_the_full_initial_once_and_the_resends_stay_short() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let (mut i, reject) = short_initial_and_its_reject(&mut w);
        let t0 = w.now;
        let ms = |n: u64| t0 + n * 1_000_000;
        // What the initiator queues when `reject` arrives at `now`, and for each loss timer at `now`.
        let mut next = |i: &mut pinc_security::Initiator, now: u64, retx: bool| {
            let mut env = Env {
                provider: &w.i_prov,
                now,
                drbg: &mut w.i_drbg,
            };
            let r = if retx {
                i.retransmit(&mut env)
            } else {
                i.handle(&mut env, &reject)
            };
            assert!(r.is_ok(), "{r:?} at {} ms", (now - t0) / 1_000_000);
            i.poll_output().map(|o| match o {
                Output::Send { data, .. } => data[0],
                _ => panic!("not a message"),
            })
        };
        // The reject is answered with the full Initial at once ...
        assert_eq!(next(&mut i, ms(20), false), Some(1));
        // ... a second one right behind it is taken and changes nothing, one 500 ms later brings the full Initial again.
        assert_eq!(next(&mut i, ms(30), false), None);
        assert_eq!(next(&mut i, ms(520), false), Some(1));
        // The resends that follow are short, except the third and the sixth send.
        let seen: Vec<_> = (0..5).map(|n| next(&mut i, ms(600 + n * 500), true)).collect();
        assert_eq!(seen, vec![Some(2), Some(1), Some(2), Some(2), Some(1)]);
    });
}

#[test]
fn the_host_sets_the_gap_between_full_initials_for_rejects_and_hears_of_each_reject() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let (mut i, reject) = short_initial_and_its_reject(&mut w);
        let t0 = w.now;
        let ms = |n: u64| t0 + n * 1_000_000;
        assert!(!i.take_prekey_rejected(), "no reject yet");
        i.set_reject_gap(2_000 * 1_000_000);
        let mut sent_at = |i: &mut pinc_security::Initiator, now: u64| {
            let mut env = Env {
                provider: &w.i_prov,
                now,
                drbg: &mut w.i_drbg,
            };
            i.handle(&mut env, &reject).unwrap();
            i.poll_output().is_some()
        };
        assert!(sent_at(&mut i, ms(20)));
        assert!(i.take_prekey_rejected());
        assert!(!i.take_prekey_rejected(), "told once");
        assert!(!sent_at(&mut i, ms(1500)), "inside the gap");
        assert!(i.take_prekey_rejected(), "but the host is told of every reject");
        assert!(sent_at(&mut i, ms(2020)));
    });
}
