//! The full handshake, the prekey short Initial, tampering, the transcript binding, deferred key requests and allocation.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::trivially_copy_pass_by_ref,
    clippy::range_plus_one,
    clippy::assert_is_empty,
    clippy::needless_pass_by_value,
    clippy::similar_names,
    clippy::items_after_statements,
    unreachable_pub
)]

use vinc_crypto::provider::KEM_ENCAPS_KEY_LEN;
use vinc_crypto::{Aead, Drbg, IdentityAlg, NodeId, Software};
use vinc_security::message::{MAX_MESSAGE_LEN, min_initial_len, reply_len};
use vinc_security::{
    CreditRecord, Env, Event, Failure, InitialForm, KeyRequest, KeyResponse, Output, PrekeyCache, ResponderStores,
    SoftKeys,
};

mod sec_common;
use sec_common::{ALGS, ALPN, ALPN_B, Caps, Tamper, World, assert_data_flows, assert_same_keys, big_stack, keypair};

vinc_tests::install_counting_allocator!();

const HW: [(bool, bool); 4] = [(true, true), (true, false), (false, true), (false, false)];

fn full_matrix(alg: IdentityAlg) {
    big_stack(move || {
        for (i_hw, r_hw) in HW {
            let mut w = World::new(alg, alg, i_hw, r_hw);
            let out = w.full();
            let (i, r) = (out.i_est().unwrap(), out.r_est().unwrap());
            assert_same_keys(i, r);
            let want = if i_hw && r_hw {
                Aead::Aes128Gcm
            } else {
                Aead::ChaCha20Poly1305
            };
            assert_eq!(i.traffic.aead, want, "{alg:?} {i_hw} {r_hw}");
            assert_eq!(i.peer, w.rp.id.node_id());
            assert_eq!(r.peer, w.ip.id.node_id());
            assert!(!i.resumed && !r.resumed);
            assert!(i.tickets.entries().is_empty());
            assert_eq!(r.tickets.entries().len(), 1);
            assert_eq!(out.types(), vec![1, 4, 5]);
            assert_data_flows(&w.i_prov, &w.r_prov, i, r);
            // The responder cached the prekey only after the initiator authenticated.
            assert_eq!(w.stores.prekeys.len(), 1);
            assert_eq!(w.stores.tickets.len(), 1);
        }
    });
}

#[test]
fn full_handshake_ed25519() {
    full_matrix(IdentityAlg::Ed25519);
}
#[test]
fn full_handshake_p256() {
    full_matrix(IdentityAlg::EcdsaP256);
}
#[test]
fn full_handshake_ml_dsa_65() {
    full_matrix(IdentityAlg::MlDsa65);
}
#[test]
fn full_handshake_hybrid() {
    full_matrix(IdentityAlg::Hybrid);
}

#[test]
fn full_handshake_mixed_algorithms() {
    big_stack(|| {
        for (a, b) in [
            (IdentityAlg::Ed25519, IdentityAlg::Hybrid),
            (IdentityAlg::MlDsa65, IdentityAlg::EcdsaP256),
            (IdentityAlg::Hybrid, IdentityAlg::Ed25519),
        ] {
            let mut w = World::new(a, b, true, true);
            let out = w.full();
            assert_same_keys(out.i_est().unwrap(), out.r_est().unwrap());
            assert_data_flows(&w.i_prov, &w.r_prov, out.i_est().unwrap(), out.r_est().unwrap());
        }
    });
}

#[test]
fn message_sizes_and_padding() {
    big_stack(|| {
        for alg in ALGS {
            let mut w = World::new(IdentityAlg::Ed25519, alg, false, false);
            let out = w.full();
            let (init, reply, finish) = (&out.msgs[0], &out.msgs[1], &out.msgs[2]);
            // Initial: type, version(1), dcid(16), scid(8), alpn(6), offer, e_I, pk_I, credit(6).
            assert_eq!(init.len(), 1 + 1 + 17 + 9 + 7 + 1 + 32 + 1184 + 6);
            // The sealed part of the Reply carries the credit record (6) and the tag (16).
            let sealed = 1 + 2 + alg.public_key_len() + 2 + alg.signature_len() + 6 + 16;
            // Reply: type, scid(8), aead, e_R, ct, sealed.
            assert_eq!(reply.len(), 1 + 9 + 1 + 32 + 1088 + 2 + sealed);
            assert!(reply.len() <= reply_len(alg));
            // The Finish carries no credit record.
            assert_eq!(finish.len(), 1 + 2 + (1 + 2 + 32 + 2 + 64 + 16));
            // Three times the padded Initial covers the Reply and its per-datagram overhead.
            for form in [InitialForm::Full, InitialForm::Short] {
                let min = min_initial_len(form, alg);
                let datagrams = reply_len(alg).div_ceil(1200);
                assert!(3 * min >= reply_len(alg) + 48 * datagrams, "{alg:?} {form:?}");
            }
            let (full, short) = (
                min_initial_len(InitialForm::Full, alg),
                min_initial_len(InitialForm::Short, alg),
            );
            match alg {
                IdentityAlg::Ed25519 => {
                    // The short Initial is 464 bytes: 3 x 464 = 1392 covers the 1268-byte Reply (two datagrams, 48
                    // bytes of overhead each) with room to spare, and 463 would not.
                    assert_eq!((full, short), (1200, 464));
                    assert_eq!(reply_len(alg), 1268);
                    assert_eq!((reply_len(alg) + 2 * 48).div_ceil(3), 455);
                    assert!(3 * short >= reply_len(alg) + 2 * 48);
                }
                IdentityAlg::EcdsaP256 => assert!(full == 1200 && short >= 464),
                _ => assert!(full > 1200 && short > 464 && full == short),
            }
            assert!(reply_len(IdentityAlg::Hybrid) <= MAX_MESSAGE_LEN);
        }
    });
}

#[test]
fn padding_is_reported_with_the_message() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::MlDsa65, false, false);
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, false, false);
        let Some(Output::Send { min_len, .. }) = i.poll_output() else {
            panic!("no message")
        };
        assert_eq!(min_len, min_initial_len(InitialForm::Full, IdentityAlg::MlDsa65));
        let mut i = w.initiator_with(dial, ALPN, true, false);
        let Some(Output::Send { min_len, data }) = i.poll_output() else {
            panic!("no message")
        };
        assert_eq!(data[0], 2);
        assert_eq!(min_len, min_initial_len(InitialForm::Short, IdentityAlg::MlDsa65));
    });
}

#[test]
fn prekey_short_hit() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        w.full();
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, true, false);
        let mut r = w.responder();
        let out = w.run(&mut i, &mut r, None);
        assert!(out.both_established(), "{:?} {:?}", out.i_errs, out.r_errs);
        assert_eq!(out.types(), vec![2, 4, 5]);
        assert!(out.msgs[0].len() < 200, "the short Initial is small");
        assert_same_keys(out.i_est().unwrap(), out.r_est().unwrap());
    });
}

#[test]
fn prekey_miss_falls_back_to_the_full_initial() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let dial = w.dial();
        // The responder never saw this prekey.
        let mut i = w.initiator_with(dial, ALPN, true, false);
        let mut r = w.responder();
        let out = w.run(&mut i, &mut r, None);
        assert!(out.both_established(), "{:?} {:?}", out.i_errs, out.r_errs);
        assert_eq!(out.types(), vec![2, 3, 1, 4, 5]);
        assert_eq!(out.msgs[1].len(), 17, "the reject is header-only");
        assert_same_keys(out.i_est().unwrap(), out.r_est().unwrap());
    });
}

#[test]
fn prekey_cache_of_capacity_zero_always_misses() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let mut stores: ResponderStores<0, 4> = ResponderStores::default();
        for round in 0..2 {
            let dial = w.dial();
            let mut i = w.initiator_with(dial, ALPN, round == 1, false);
            let mut r = w.responder();
            let mut env_i = Env {
                provider: &w.i_prov,
                now: w.now,
                drbg: &mut w.i_drbg,
            };
            let mut env_r = Env {
                provider: &w.r_prov,
                now: w.now,
                drbg: &mut w.r_drbg,
            };
            let soft_i = SoftKeys {
                signer: Some((vinc_security::KeyHandle(1), &w.ip.kp)),
                prekeys: Some(&w.prekeys),
            };
            let soft_r = SoftKeys {
                signer: Some((vinc_security::KeyHandle(1), &w.rp.kp)),
                prekeys: None,
            };
            let mut types = vec![];
            let mut established = (false, false);
            let mut to_r: Vec<Vec<u8>> = vec![];
            let mut to_i: Vec<Vec<u8>> = vec![];
            loop {
                while i.answer_soft(&mut env_i, &soft_i).unwrap() {}
                while let Some(o) = i.poll_output() {
                    match o {
                        Output::Send { data, .. } => {
                            types.push(data[0]);
                            to_r.push(data.to_vec());
                        }
                        Output::Event(Event::Established(_)) => established.0 = true,
                        _ => {}
                    }
                }
                if let Some(m) = to_r.pop() {
                    r.handle(&mut env_r, &mut stores, &m).unwrap();
                    while r.answer_soft(&mut env_r, &soft_r).unwrap() {}
                    while let Some(o) = r.poll_output() {
                        match o {
                            Output::Send { data, .. } => {
                                types.push(data[0]);
                                to_i.push(data.to_vec());
                            }
                            Output::Event(Event::Established(_)) => established.1 = true,
                            _ => {}
                        }
                    }
                }
                if let Some(m) = to_i.pop() {
                    i.handle(&mut env_i, &m).unwrap();
                    continue;
                }
                if to_r.is_empty() {
                    break;
                }
            }
            assert_eq!(established, (true, true));
            assert_eq!(stores.prekeys.len(), 0);
            assert_eq!(stores.prekeys.capacity(), 0);
            if round == 1 {
                assert_eq!(types, vec![2, 3, 1, 4, 5]);
            }
        }
    });
}

#[test]
fn prekey_cache_is_a_bounded_lru() {
    let mut c: PrekeyCache<2> = PrekeyCache::new();
    let key = |b: u8| [b; KEM_ENCAPS_KEY_LEN];
    c.insert([1; 32], &key(1));
    c.insert([2; 32], &key(2));
    assert!(c.get(&[1; 32]).is_some(), "touch 1, so 2 is the least recently used");
    c.insert([3; 32], &key(3));
    assert_eq!(c.len(), 2);
    assert!(c.get(&[2; 32]).is_none());
    assert_eq!(c.get(&[1; 32]).unwrap()[0], 1);
    assert_eq!(c.get(&[3; 32]).unwrap()[0], 3);
    c.insert([3; 32], &key(9));
    assert_eq!(c.len(), 2, "re-inserting a hash does not grow the cache");
}

#[test]
fn every_third_retransmit_carries_the_full_prekey() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, true, false);
        let mut env = Env {
            provider: &w.i_prov,
            now: w.now,
            drbg: &mut w.i_drbg,
        };
        let mut seen = vec![];
        for n in 0..7 {
            if n > 0 {
                i.retransmit(&mut env).unwrap();
            }
            let Some(Output::Send { data, .. }) = i.poll_output() else {
                panic!("nothing to send at {n}")
            };
            seen.push(data[0]);
            assert!(i.poll_output().is_none());
        }
        // Sends 1 to 7 are short, short, full, short, short, full, short: the full prekey goes on sends 3, 6, 9.
        assert_eq!(seen, vec![2, 2, 1, 2, 2, 1, 2]);
    });
}

#[test]
fn a_repeated_initial_gets_the_same_reply_and_the_finish_can_be_retransmitted() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let mut i = w.initiator();
        let mut r = w.responder();
        let Self_ { first, reply } = {
            let Some(Output::Send { data, .. }) = i.poll_output() else {
                panic!()
            };
            let first = data.to_vec();
            let mut env_r = Env {
                provider: &w.r_prov,
                now: w.now,
                drbg: &mut w.r_drbg,
            };
            let soft_r = SoftKeys {
                signer: Some((vinc_security::KeyHandle(1), &w.rp.kp)),
                prekeys: None,
            };
            r.handle(&mut env_r, &mut w.stores, &first).unwrap();
            assert!(r.answer_soft(&mut env_r, &soft_r).unwrap());
            let Some(Output::Send { data, .. }) = r.poll_output() else {
                panic!()
            };
            Self_ {
                first,
                reply: data.to_vec(),
            }
        };
        let mut env_r = Env {
            provider: &w.r_prov,
            now: w.now,
            drbg: &mut w.r_drbg,
        };
        // The same Initial again, and the loss timer: the Reply is queued again, identical.
        r.handle(&mut env_r, &mut w.stores, &first).unwrap();
        let Some(Output::Send { data, .. }) = r.poll_output() else {
            panic!("no resend")
        };
        assert_eq!(data, reply.as_slice());
        r.retransmit();
        let Some(Output::Send { data, .. }) = r.poll_output() else {
            panic!("no resend")
        };
        assert_eq!(data, reply.as_slice());
        // A different Initial for this connection is dropped, not fatal.
        let mut other = first.clone();
        other[10] ^= 1;
        assert_eq!(
            r.handle(&mut env_r, &mut w.stores, &other),
            Err(Failure::DifferentFirst)
        );
        assert!(r.poll_output().is_none());
    });
}

struct Self_ {
    first: Vec<u8>,
    reply: Vec<u8>,
}

#[test]
fn the_finish_is_retransmitted_on_request() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let mut i = w.initiator();
        let mut r = w.responder();
        let out = w.run(&mut i, &mut r, None);
        assert!(out.both_established());
        let mut env = Env {
            provider: &w.i_prov,
            now: w.now,
            drbg: &mut w.i_drbg,
        };
        i.retransmit(&mut env).unwrap();
        let Some(Output::Send { data, .. }) = i.poll_output() else {
            panic!("no resend")
        };
        assert_eq!(data, out.msgs[2].as_slice());
        // Once the transport shed the handshake there is nothing left to send again.
        i.shed();
        i.retransmit(&mut env).unwrap();
        assert!(i.poll_output().is_none());
    });
}

/// Which positions of a `len`-byte message to try: all of them when `stride` is 1, otherwise the first and last 48
/// bytes and every `stride`-th byte (ML-DSA signatures and keys are long and slow to verify in a debug build).
fn positions(len: usize, stride: usize) -> impl Iterator<Item = usize> {
    (0..len).filter(move |at| *at < 48 || at + 48 >= len || at.is_multiple_of(stride))
}

fn run_tampered(w: &mut World, t: &Tamper) -> sec_common::Outcome {
    let mut i = w.initiator();
    let mut r = w.responder();
    w.run(&mut i, &mut r, Some(t))
}

/// Flip every byte of message `msg`: the handshake must not establish on both sides.
fn flips(alg: IdentityAlg, msg: usize, stride: usize) {
    big_stack(move || {
        let mut w = World::new(alg, alg, false, false);
        let base = w.full();
        for byte in positions(base.msgs[msg].len(), stride) {
            let out = run_tampered(&mut w, &Tamper::flip(msg, byte));
            assert!(!out.both_established(), "{alg:?} message {msg} byte {byte}");
            match msg {
                0 | 1 => assert!(out.i_est().is_none(), "{alg:?} message {msg} byte {byte}"),
                _ => assert!(out.r_est().is_none(), "{alg:?} message {msg} byte {byte}"),
            }
        }
    });
}

/// A message flipped in flight fails to authenticate and is dropped on both sides; the sender's resend then completes
/// the handshake, with keys that carry data.
#[test]
fn a_damaged_reply_or_finish_is_dropped_and_the_resend_completes_the_handshake() {
    big_stack(|| {
        for alg in [IdentityAlg::Ed25519, IdentityAlg::Hybrid] {
            for msg in [1, 2] {
                let mut w = World::new(alg, alg, false, false);
                let len = w.full().msgs[msg].len();
                // A byte of the sealed part: past the header, so it is the tag check that refuses it.
                let byte = len - 5;
                let mut i = w.initiator();
                let mut r = w.responder();
                let out = w.run(&mut i, &mut r, Some(&Tamper::flip(msg, byte)));
                assert!(!out.both_established(), "{alg:?} message {msg}");
                assert!(
                    out.i_failed().is_none() && out.r_failed().is_none(),
                    "{alg:?} message {msg}"
                );
                let dropped = if msg == 1 { &out.i_errs } else { &out.r_errs };
                assert!(dropped.contains(&Failure::Authentication), "{alg:?} message {msg}");
                // The loss timer fires: the initiator sends its last flight again.
                let mut env = Env {
                    provider: &w.i_prov,
                    now: w.now,
                    drbg: &mut w.i_drbg,
                };
                i.retransmit(&mut env).unwrap();
                let again = w.run(&mut i, &mut r, None);
                assert!(
                    again.i_est().is_some() || out.i_est().is_some(),
                    "{alg:?} message {msg}: initiator"
                );
                assert!(again.r_est().is_some(), "{alg:?} message {msg}: responder");
                let (i_est, r_est) = (again.i_est().or(out.i_est()).unwrap(), again.r_est().unwrap());
                assert_eq!(i_est.traffic.send.expose(), r_est.traffic.recv.expose());
                assert_eq!(i_est.traffic.recv.expose(), r_est.traffic.send.expose());
            }
        }
    });
}

/// Truncate message `msg` at every length, and append a byte: the handshake must not establish.
fn cuts(alg: IdentityAlg, msg: usize, stride: usize) {
    big_stack(move || {
        let mut w = World::new(alg, alg, false, false);
        let base = w.full();
        for cut in positions(base.msgs[msg].len(), stride) {
            let out = run_tampered(&mut w, &Tamper::truncate(msg, cut));
            assert!(!out.both_established(), "{alg:?} message {msg} cut {cut}");
        }
        let out = run_tampered(&mut w, &Tamper::extend(msg));
        assert!(!out.both_established(), "{alg:?} message {msg} extended");
    });
}

macro_rules! tamper_tests {
    ($($name:ident: $alg:expr, $stride:expr;)*) => {
        mod tamper {
            use super::*;
            $(
                mod $name {
                    use super::*;
                    #[test] fn flip_initial() { flips($alg, 0, $stride); }
                    #[test] fn flip_reply() { flips($alg, 1, $stride); }
                    #[test] fn flip_finish() { flips($alg, 2, $stride); }
                    #[test] fn cut_initial() { cuts($alg, 0, $stride); }
                    #[test] fn cut_reply() { cuts($alg, 1, $stride); }
                    #[test] fn cut_finish() { cuts($alg, 2, $stride); }
                }
            )*
        }
    };
}

tamper_tests! {
    ed25519: IdentityAlg::Ed25519, 1;
    p256: IdentityAlg::EcdsaP256, 1;
    ml_dsa_65: IdentityAlg::MlDsa65, 53;
    hybrid: IdentityAlg::Hybrid, 53;
}

#[test]
fn a_wrong_dialed_node_id_fails() {
    big_stack(|| {
        for alg in ALGS {
            let mut w = World::new(IdentityAlg::Ed25519, alg, false, false);
            let other = keypair(alg, 0x77).node_id();
            let mut i = w.initiator_with(other, ALPN, false, false);
            let mut r = w.responder();
            let out = w.run(&mut i, &mut r, None);
            assert_eq!(out.i_failed(), Some(Failure::WrongPeer), "{alg:?}");
            assert!(out.i_est().is_none() && out.r_est().is_none());
            // The initiator never sent its identity.
            assert_eq!(out.types(), vec![1, 4]);
            // A later input is refused.
            assert_eq!(out.i_errs, vec![Failure::WrongPeer]);
        }
        // The right key under another algorithm tag is another node too.
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let mut dial = w.dial();
        dial = NodeId {
            alg: IdentityAlg::EcdsaP256,
            bytes: dial.bytes,
        };
        let mut i = w.initiator_with(dial, ALPN, false, false);
        let mut r = w.responder();
        let out = w.run(&mut i, &mut r, None);
        assert_eq!(out.i_failed(), Some(Failure::WrongPeer));
    });
}

#[test]
fn the_transcript_binds_alpn_connection_ids_version_and_the_aead_offer() {
    big_stack(|| {
        // The initial message layout: type(1) version(1) dcid(1+16) scid(1+8) alpn(1+6) offer(1) e(32) pk(1184) credit(6);
        // the offsets below are those of the bytes after each length prefix.
        let (v, dcid, scid, alpn, offer, e) = (1, 3, 20, 29, 35, 36);
        let mk = |t: Tamper, i_hw: bool, r_hw: bool| {
            let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, i_hw, r_hw);
            let mut i = w.initiator();
            let mut r = w.responder();
            w.run(&mut i, &mut r, Some(&t))
        };
        // ALPN: the responder serves both, the attacker swaps one for the other.
        let out = mk(
            Tamper::custom(0, move |m| m[alpn..alpn + 6].copy_from_slice(ALPN_B)),
            false,
            false,
        );
        assert!(out.i_dropped_unauthentic(), "alpn");
        assert!(out.r_est().is_none());
        // A connection id on either side.
        for at in [dcid, scid] {
            let out = mk(Tamper::flip(0, at), false, false);
            assert!(out.i_dropped_unauthentic(), "cid byte {at}");
        }
        // The version is checked before anything else.
        let out = mk(Tamper::flip(0, v), false, false);
        assert_eq!(out.r_failed(), Some(Failure::UnsupportedVersion));
        // The offer: widened by the attacker, the responder picks ChaCha (no hardware AES) and the transcripts differ.
        let out = mk(Tamper::custom(0, move |m| m[offer] = 3), false, false);
        assert!(out.i_dropped_unauthentic(), "offer");
        // With hardware AES at the responder it picks AES, which the initiator never offered.
        let out = mk(Tamper::custom(0, move |m| m[offer] = 3), false, true);
        assert_eq!(out.i_failed(), Some(Failure::NoCommonAead), "offer, hardware");
        // The key share.
        let out = mk(Tamper::flip(0, e), false, false);
        assert!(out.i_dropped_unauthentic(), "e_I");
        // The responder's choice, forged in the Reply (type, scid(1+8), aead).
        let out = mk(Tamper::custom(1, |m| m[10] = 2), false, false);
        assert_eq!(out.i_failed(), Some(Failure::NoCommonAead), "aead choice");
    });
}

#[test]
fn the_credit_record_is_part_of_the_transcript() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        w.i_credit = CreditRecord::new(1_310_720, 100, 1200);
        let out = w.full();
        assert!(out.both_established());
        // The record is the last 6 bytes of the Initial; flipping any byte of it breaks the handshake.
        let at = out.msgs[0].len() - 6;
        assert_eq!(out.msgs[0][at..], w.i_credit.encode());
        for off in 0..6 {
            let mut i = w.initiator();
            let mut r = w.responder();
            let t = Tamper::flip(0, at + off);
            let out = w.run(&mut i, &mut r, Some(&t));
            assert!(out.i_dropped_unauthentic(), "initiator record byte {off}");
        }
    });
}

#[test]
fn an_unknown_alpn_is_refused() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let dial = w.dial();
        let mut i = w.initiator_with(dial, b"other", false, false);
        let mut r = w.responder();
        let out = w.run(&mut i, &mut r, None);
        assert_eq!(out.r_failed(), Some(Failure::UnknownAlpn));
        assert!(out.i_est().is_none());
    });
}

#[test]
fn the_sub_session_secret_binds_its_inputs() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let out = w.full();
        let (i, r) = (out.i_est().unwrap(), out.r_est().unwrap());
        let a = i.traffic.sub_session(b"app", b"cc", b"cs");
        let b = r.traffic.sub_session(b"app", b"cc", b"cs");
        assert_eq!(a.send, b.recv);
        assert_eq!(a.recv, b.send);
        assert_ne!(a.send, i.traffic.send);
        for (x, y, z) in [
            (&b"ap"[..], &b"pcc"[..], &b"cs"[..]),
            (b"app", b"c", b"ccs"),
            (b"app", b"cc", b"cS"),
            (b"", b"appcc", b"cs"),
        ] {
            assert_ne!(i.traffic.sub_session(x, y, z).send, a.send, "{x:?} {y:?} {z:?}");
        }
    });
}

#[test]
fn key_requests_can_be_answered_many_polls_later() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Hybrid, false, false);
        let mut i = w.initiator();
        let mut r = w.responder();
        let mut env_i = Env {
            provider: &w.i_prov,
            now: w.now,
            drbg: &mut w.i_drbg,
        };
        let mut env_r = Env {
            provider: &w.r_prov,
            now: w.now,
            drbg: &mut w.r_drbg,
        };
        let Some(Output::Send { data, .. }) = i.poll_output() else {
            panic!()
        };
        let initial = data.to_vec();
        r.handle(&mut env_r, &mut w.stores, &initial).unwrap();
        // The responder asks for a signature once; asking again yields nothing while it waits.
        let Some(Output::Key(KeyRequest::Sign { key, alg, message })) = r.poll_output() else {
            panic!("no sign request")
        };
        let (key, message) = (key, message.to_vec());
        assert_eq!(alg, IdentityAlg::Hybrid);
        for _ in 0..10 {
            assert!(r.poll_output().is_none(), "no output while the key is pending");
        }
        // A response of the wrong kind is refused and changes nothing.
        let wrong = KeyResponse::SharedSecret(vinc_crypto::Secret::new([0; 32]));
        assert_eq!(
            r.on_key_response(&mut env_r, wrong),
            Err(Failure::UnexpectedKeyResponse)
        );
        assert!(r.poll_output().is_none());
        let mut sig = vec![0u8; 4000];
        let n = w.rp.kp.sign(&message, &mut sig).unwrap();
        assert_eq!(key, vinc_security::KeyHandle(1));
        r.on_key_response(&mut env_r, KeyResponse::Signature(&sig[..n]))
            .unwrap();
        let Some(Output::Send { data, .. }) = r.poll_output() else {
            panic!("no reply")
        };
        let reply = data.to_vec();
        // The initiator asks to decapsulate, then, after another delay, to sign.
        i.handle(&mut env_i, &reply).unwrap();
        let Some(Output::Key(KeyRequest::Decapsulate { key, ct })) = i.poll_output() else {
            panic!("no decapsulate request")
        };
        let ss = w.prekeys.decapsulate(&w.i_prov, key, ct).unwrap();
        for _ in 0..10 {
            assert!(i.poll_output().is_none());
        }
        i.on_key_response(&mut env_i, KeyResponse::SharedSecret(ss)).unwrap();
        let Some(Output::Key(KeyRequest::Sign { message, .. })) = i.poll_output() else {
            panic!("no sign request")
        };
        let message = message.to_vec();
        for _ in 0..10 {
            assert!(i.poll_output().is_none());
        }
        let n = w.ip.kp.sign(&message, &mut sig).unwrap();
        i.on_key_response(&mut env_i, KeyResponse::Signature(&sig[..n]))
            .unwrap();
        let Some(Output::Send { data, .. }) = i.poll_output() else {
            panic!("no finish")
        };
        let finish = data.to_vec();
        let Some(Output::Event(Event::Established(ie))) = i.poll_output() else {
            panic!("not established")
        };
        r.handle(&mut env_r, &mut w.stores, &finish).unwrap();
        let Some(Output::Event(Event::Established(re))) = r.poll_output() else {
            panic!("responder not established")
        };
        assert_same_keys(&ie, &re);
    });
}

#[test]
fn a_failed_key_operation_is_fatal_and_reported() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let mut r = w.responder();
        let mut i = w.initiator();
        let mut env_r = Env {
            provider: &w.r_prov,
            now: w.now,
            drbg: &mut w.r_drbg,
        };
        let Some(Output::Send { data, .. }) = i.poll_output() else {
            panic!()
        };
        r.handle(&mut env_r, &mut w.stores, data).unwrap();
        assert!(matches!(r.poll_output(), Some(Output::Key(_))));
        assert_eq!(
            r.on_key_response(&mut env_r, KeyResponse::Failed),
            Err(Failure::KeyOperation)
        );
        assert!(matches!(
            r.poll_output(),
            Some(Output::Event(Event::Failed(Failure::KeyOperation)))
        ));
        assert!(r.poll_output().is_none());
        assert_eq!(r.handle(&mut env_r, &mut w.stores, data), Err(Failure::Closed));
    });
}

#[test]
fn a_response_without_a_request_is_refused() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let mut r = w.responder();
        let mut env_r = Env {
            provider: &w.r_prov,
            now: w.now,
            drbg: &mut w.r_drbg,
        };
        assert_eq!(
            r.on_key_response(&mut env_r, KeyResponse::Signature(&[0; 64])),
            Err(Failure::UnexpectedKeyResponse)
        );
    });
}

#[test]
fn garbage_input_never_panics() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false);
        let mut rng = vinc_tests::SplitMix64::new(7);
        let mut r = w.responder();
        let mut i = w.initiator();
        let mut env_r = Env {
            provider: &w.r_prov,
            now: w.now,
            drbg: &mut w.r_drbg,
        };
        let mut env_i = Env {
            provider: &w.i_prov,
            now: w.now,
            drbg: &mut w.i_drbg,
        };
        for n in 0..400usize {
            let mut buf = vec![0u8; n % 90];
            rng.fill(&mut buf);
            if let Some(b) = buf.first_mut() {
                *b = (n % 9) as u8;
            }
            let _ = r.handle(&mut env_r, &mut w.stores, &buf);
            let _ = i.handle(&mut env_i, &buf);
            let _ = r.on_key_response(&mut env_r, KeyResponse::Failed);
        }
    });
}

#[test]
fn identical_seeds_give_identical_messages() {
    big_stack(|| {
        let a = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false)
            .full()
            .msgs;
        let b = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false)
            .full()
            .msgs;
        assert_eq!(a, b);
        let _ = (Drbg::new(&[0; 32]), Software, Caps(Software, false));
    });
}

/// Copy the next message out of a machine into a fixed buffer.
macro_rules! take_send {
    ($m:expr, $buf:expr) => {{
        let Some(Output::Send { data, .. }) = $m.poll_output() else {
            panic!("no message")
        };
        let n = data.len();
        $buf[..n].copy_from_slice(data);
        n
    }};
}

#[test]
fn a_full_handshake_run_allocates_nothing() {
    big_stack(|| {
        for alg in [IdentityAlg::Ed25519, IdentityAlg::Hybrid] {
            let mut w = World::new(alg, alg, true, true);
            let dial = w.dial();
            let prekey = {
                let mut env = Env {
                    provider: &w.i_prov,
                    now: w.now,
                    drbg: &mut w.i_drbg,
                };
                w.prekeys.acquire(&mut env).unwrap()
            };
            let mut r_cfg = vinc_security::ResponderConfig::new(
                w.rp.id,
                vinc_security::ConnId::new(b"respond0").unwrap(),
                vinc_security::AlpnList::new(&[ALPN]).unwrap(),
            );
            r_cfg.tickets_per_session = 1;
            let mut stores = Box::new(ResponderStores::<4, 4>::default());
            let mut buf = vec![0u8; MAX_MESSAGE_LEN];
            let soft_i = SoftKeys {
                signer: Some((vinc_security::KeyHandle(1), &w.ip.kp)),
                prekeys: Some(&w.prekeys),
            };
            let soft_r = SoftKeys {
                signer: Some((vinc_security::KeyHandle(1), &w.rp.kp)),
                prekeys: None,
            };
            let mut env_i = Env {
                provider: &w.i_prov,
                now: w.now,
                drbg: &mut w.i_drbg,
            };
            let mut env_r = Env {
                provider: &w.r_prov,
                now: w.now,
                drbg: &mut w.r_drbg,
            };
            let mut established = 0;
            let stats = vinc_tests::measure(|| {
                let mut i = vinc_security::Initiator::new(
                    &mut env_i,
                    vinc_security::InitiatorParams {
                        peer: dial,
                        alpn: ALPN,
                        scid: vinc_security::ConnId::new(b"initiat0").unwrap(),
                        identity: &w.ip.id,
                        prekey: &prekey,
                        peer_has_prekey: false,
                        ticket: None,
                        credit: vinc_security::CreditRecord::NONE,
                    },
                )
                .unwrap();
                let mut r = vinc_security::Responder::new(r_cfg.clone());
                let n = take_send!(i, buf);
                r.handle(&mut env_r, &mut stores, &buf[..n]).unwrap();
                assert!(r.answer_soft(&mut env_r, &soft_r).unwrap());
                let n = take_send!(r, buf);
                i.handle(&mut env_i, &buf[..n]).unwrap();
                assert!(i.answer_soft(&mut env_i, &soft_i).unwrap());
                assert!(i.answer_soft(&mut env_i, &soft_i).unwrap());
                let n = take_send!(i, buf);
                if matches!(i.poll_output(), Some(Output::Event(Event::Established(_)))) {
                    established += 1;
                }
                r.handle(&mut env_r, &mut stores, &buf[..n]).unwrap();
                if matches!(r.poll_output(), Some(Output::Event(Event::Established(_)))) {
                    established += 1;
                }
            });
            assert_eq!(established, 2);
            assert_eq!(stats.count(), 0, "{alg:?}: {stats:?}");
        }
    });
}
