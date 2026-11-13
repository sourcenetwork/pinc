//! Resumption that does not go to plan, and tickets that go both ways: the fallback to a full handshake after three
//! unanswered Hellos, a late resume Reply that still completes, a lost resume Reply that is sent again, the ticket
//! the initiator issues to the responder, and the export and restore of the initiator's tickets.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::assert_is_empty,
    unreachable_pub
)]

use vinc_crypto::IdentityAlg;
use vinc_keystore::{KeyStore, SoftwareStore};
use vinc_security::responder::RESEND_BUDGET;
use vinc_security::tickets::MAX_EXPORT_ENTRY_LEN;
use vinc_security::{
    ClientTickets, Env, Established, Event, Failure, Initiator, Output, Responder, ResponderStores, ServerTickets,
    SoftKeys,
};

mod sec_common;
use sec_common::{ALPN, World, assert_same_keys, big_stack};

fn world() -> World {
    World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false)
}

/// Everything a machine has queued: its messages and its events.
fn drain_i(m: &mut Initiator) -> (Vec<Vec<u8>>, Vec<Event>) {
    let (mut sent, mut events) = (vec![], vec![]);
    while let Some(o) = m.poll_output() {
        match o {
            Output::Send { data, .. } => sent.push(data.to_vec()),
            Output::Event(e) => events.push(e),
            Output::Key(_) => {}
        }
    }
    (sent, events)
}

fn drain_r(m: &mut Responder) -> (Vec<Vec<u8>>, Vec<Event>) {
    let (mut sent, mut events) = (vec![], vec![]);
    while let Some(o) = m.poll_output() {
        match o {
            Output::Send { data, .. } => sent.push(data.to_vec()),
            Output::Event(e) => events.push(e),
            Output::Key(_) => {}
        }
    }
    (sent, events)
}

fn established(events: &[Event]) -> Option<&Established> {
    events.iter().find_map(|e| match e {
        Event::Established(est) => Some(est),
        _ => None,
    })
}

/// A resumption in which the responder got the Hello and answered, and the answer is held back.
struct Held {
    w: World,
    i: Initiator,
    r: Responder,
    hello: Vec<u8>,
    reply: Vec<u8>,
    r_est: Established,
}

fn hello_answered_but_reply_held() -> Held {
    let mut w = world();
    w.full();
    let dial = w.dial();
    let mut i = w.initiator_with(dial, ALPN, false, true);
    let mut r = w.responder();
    let (sent, events) = drain_i(&mut i);
    assert_eq!(sent.len(), 1);
    assert!(matches!(events[0], Event::EarlyKeys(_)));
    let hello = sent[0].clone();
    assert_eq!(hello[0], 6);
    let mut env = Env {
        provider: &w.r_prov,
        now: w.now,
        drbg: &mut w.r_drbg,
    };
    r.handle(&mut env, &mut w.stores, &hello).unwrap();
    let (sent, events) = drain_r(&mut r);
    let r_est = established(&events)
        .expect("the responder is established at the Hello")
        .clone();
    assert_eq!(sent.len(), 1);
    Held {
        reply: sent[0].clone(),
        w,
        i,
        r,
        hello,
        r_est,
    }
}

fn retransmit(w: &mut World, i: &mut Initiator) -> (Vec<Vec<u8>>, Vec<Event>) {
    let mut env = Env {
        provider: &w.i_prov,
        now: w.now,
        drbg: &mut w.i_drbg,
    };
    i.retransmit(&mut env).unwrap();
    drain_i(i)
}

#[test]
fn an_unanswered_hello_is_sent_twice_then_a_full_initial_takes_over() {
    big_stack(|| {
        let mut h = hello_answered_but_reply_held();
        // The first retransmission repeats the Hello byte for byte (send 2).
        let (sent, events) = retransmit(&mut h.w, &mut h.i);
        assert_eq!(sent, vec![h.hello.clone()]);
        assert!(events.is_empty());
        // Send 3 is a full Initial under the same destination id, and the caller is told so it can send its early
        // data again.
        let (sent, events) = retransmit(&mut h.w, &mut h.i);
        assert_eq!(sent.len(), 1);
        let init = &sent[0];
        assert_eq!(init[0], 1, "a full Initial");
        let dcid = 2..2 + 1 + 16;
        assert_eq!(init[dcid.clone()], h.hello[dcid], "the destination id is kept");
        assert!(matches!(events[..], [Event::ResumeRejected]));
        // From here the schedule is that of a full Initial: sends 4 and 5 repeat it, as D-0025 keeps full retries.
        for _ in 0..2 {
            let (sent, _) = retransmit(&mut h.w, &mut h.i);
            assert_eq!(sent.len(), 1);
            assert_eq!(sent[0][0], 1);
        }
    });
}

#[test]
fn the_full_handshake_that_follows_a_hello_starts_with_the_short_initial_for_a_peer_known_to_cache_the_prekey() {
    big_stack(|| {
        let mut w = world();
        let dial = w.dial();
        // The Hello goes unanswered: send 3 is the Initial that takes over, short here because the host knows the
        // peer caches the prekey; the resends after it follow the rule of the Initial (the full prekey on the third).
        w.full();
        let mut i = w.initiator_with(dial, ALPN, true, true);
        assert_eq!(drain_i(&mut i).0[0][0], 6);
        assert_eq!(retransmit(&mut w, &mut i).0[0][0], 6);
        let (sent, events) = retransmit(&mut w, &mut i);
        assert_eq!(sent[0][0], 2, "the short Initial");
        assert!(matches!(events[..], [Event::ResumeRejected]));
        let seen: Vec<u8> = (0..3).map(|_| retransmit(&mut w, &mut i).0[0][0]).collect();
        assert_eq!(seen, vec![2, 1, 2]);
        // A host that does not allow short Initials when the Hello gives way gets the full one.
        w.full();
        let mut i = w.initiator_with(dial, ALPN, true, true);
        drain_i(&mut i);
        retransmit(&mut w, &mut i);
        i.set_short_until(0);
        assert_eq!(retransmit(&mut w, &mut i).0[0][0], 1, "the full Initial");
        // Without the knowledge it is full, as before.
        w.full();
        let mut i = w.initiator_with(dial, ALPN, false, true);
        drain_i(&mut i);
        retransmit(&mut w, &mut i);
        assert_eq!(retransmit(&mut w, &mut i).0[0][0], 1);
    });
}

#[test]
fn the_full_handshake_that_follows_a_rejected_hello_starts_with_the_short_initial_for_a_peer_known_to_cache_the_prekey()
{
    big_stack(|| {
        let mut w = world();
        let dial = w.dial();
        for (known, first) in [(true, 2), (false, 1)] {
            w.full();
            let mut i = w.initiator_with(dial, ALPN, known, true);
            let hello = drain_i(&mut i).0.remove(0);
            // A responder that holds no ticket rejects the Hello.
            let mut r = w.responder();
            let mut stores: ResponderStores<4, 4> = ResponderStores::default();
            let mut env = Env {
                provider: &w.r_prov,
                now: w.now,
                drbg: &mut w.r_drbg,
            };
            r.handle(&mut env, &mut stores, &hello).unwrap();
            let reject = drain_r(&mut r).0.remove(0);
            assert_eq!(reject[0], 8);
            let mut env = Env {
                provider: &w.i_prov,
                now: w.now,
                drbg: &mut w.i_drbg,
            };
            i.handle(&mut env, &reject).unwrap();
            let (sent, events) = drain_i(&mut i);
            assert!(matches!(events[..], [Event::ResumeRejected]));
            assert_eq!(sent[0][0], first, "known to cache the prekey: {known}");
        }
    });
}

#[test]
fn a_late_resume_reply_still_completes_the_resumption() {
    big_stack(|| {
        let mut h = hello_answered_but_reply_held();
        retransmit(&mut h.w, &mut h.i);
        retransmit(&mut h.w, &mut h.i);
        // The reply to the first Hello finally arrives: the full handshake is abandoned and the session is resumed.
        let mut env = Env {
            provider: &h.w.i_prov,
            now: h.w.now,
            drbg: &mut h.w.i_drbg,
        };
        h.i.handle(&mut env, &h.reply).unwrap();
        let (sent, events) = drain_i(&mut h.i);
        assert!(sent.is_empty(), "nothing more to send");
        let est = established(&events).expect("established by the late reply");
        assert!(est.resumed);
        assert_same_keys(est, &h.r_est);
        assert_eq!(est.cid_secret.expose(), h.r_est.cid_secret.expose());
        // The machine is done: a repeat of the reply is not a new session.
        assert_eq!(h.i.handle(&mut env, &h.reply), Err(Failure::UnexpectedMessage));
    });
}

#[test]
fn a_forged_late_reply_changes_nothing() {
    big_stack(|| {
        let mut h = hello_answered_but_reply_held();
        retransmit(&mut h.w, &mut h.i);
        retransmit(&mut h.w, &mut h.i);
        let mut forged = h.reply.clone();
        let last = forged.len() - 1;
        forged[last] ^= 1;
        let mut env = Env {
            provider: &h.w.i_prov,
            now: h.w.now,
            drbg: &mut h.w.i_drbg,
        };
        let err = h.i.handle(&mut env, &forged).unwrap_err();
        assert_eq!(err, Failure::UnexpectedMessage, "dropped, not fatal");
        assert!(drain_i(&mut h.i).1.is_empty());
        // The full handshake goes on: the real late reply still works afterwards.
        h.i.handle(&mut env, &h.reply).unwrap();
        assert!(established(&drain_i(&mut h.i).1).unwrap().resumed);
    });
}

#[test]
fn a_resumed_responder_sends_its_reply_again_to_a_repeated_hello() {
    big_stack(|| {
        let mut h = hello_answered_but_reply_held();
        assert!(h.r.keeps_reply());
        let mut env = Env {
            provider: &h.w.r_prov,
            now: h.w.now,
            drbg: &mut h.w.r_drbg,
        };
        h.r.handle(&mut env, &mut h.w.stores, &h.hello).unwrap();
        let (sent, events) = drain_r(&mut h.r);
        assert_eq!(sent, vec![h.reply.clone()], "the same reply, byte for byte");
        assert!(events.is_empty(), "no second session");
        // A different Hello is not a repeat.
        let mut other = h.hello.clone();
        other[5] ^= 1;
        assert!(h.r.handle(&mut env, &mut h.w.stores, &other).is_err());
        // The repeats are bounded by bytes: the reply is not an unlimited reflector.
        let len = h.hello.len();
        let mut answered = 1;
        loop {
            match h.r.handle(&mut env, &mut h.w.stores, &h.hello) {
                Ok(()) => {
                    answered += 1;
                    drain_r(&mut h.r);
                }
                Err(e) => {
                    assert_eq!(e, Failure::UnexpectedMessage);
                    break;
                }
            }
        }
        // The altered Hello above was charged too, so the budget is spent in whole repeats of `len` bytes.
        assert!((answered + 1) * len <= RESEND_BUDGET && (answered + 2) * len > RESEND_BUDGET);
        // Once the transport knows the initiator holds the session, the reply is released.
        h.r.shed();
        assert!(!h.r.keeps_reply());
        assert!(h.r.handle(&mut env, &mut h.w.stores, &h.hello).is_err());
    });
}

#[test]
fn a_resumed_responder_answers_a_full_initial_under_the_same_ids_with_its_reply() {
    big_stack(|| {
        let mut h = hello_answered_but_reply_held();
        retransmit(&mut h.w, &mut h.i);
        let (sent, _) = retransmit(&mut h.w, &mut h.i);
        let initial = sent[0].clone();
        let mut env = Env {
            provider: &h.w.r_prov,
            now: h.w.now,
            drbg: &mut h.w.r_drbg,
        };
        h.r.handle(&mut env, &mut h.w.stores, &initial).unwrap();
        let (sent, _) = drain_r(&mut h.r);
        assert_eq!(sent, vec![h.reply.clone()]);
        assert!(
            h.reply.len() <= 3 * initial.len(),
            "never more than three times what arrived"
        );
        // An Initial under other ids is not for this session.
        let mut elsewhere = initial.clone();
        elsewhere[5] ^= 1;
        assert!(h.r.handle(&mut env, &mut h.w.stores, &elsewhere).is_err());
        assert!(drain_r(&mut h.r).0.is_empty());
    });
}

#[test]
fn a_lost_resume_reply_is_recovered_by_the_hello_timer() {
    big_stack(|| {
        // The same, end to end: the reply is lost, the initiator's timer repeats the Hello, the responder answers it
        // again, and the initiator resumes without a full handshake.
        let mut h = hello_answered_but_reply_held();
        let (sent, _) = retransmit(&mut h.w, &mut h.i);
        assert_eq!(sent, vec![h.hello.clone()]);
        let mut env_r = Env {
            provider: &h.w.r_prov,
            now: h.w.now,
            drbg: &mut h.w.r_drbg,
        };
        h.r.handle(&mut env_r, &mut h.w.stores, &sent[0]).unwrap();
        let (again, _) = drain_r(&mut h.r);
        let mut env_i = Env {
            provider: &h.w.i_prov,
            now: h.w.now,
            drbg: &mut h.w.i_drbg,
        };
        h.i.handle(&mut env_i, &again[0]).unwrap();
        let (_, events) = drain_i(&mut h.i);
        let est = established(&events).unwrap();
        assert!(est.resumed);
        assert_same_keys(est, &h.r_est);
    });
}

#[test]
fn the_initiator_issues_a_ticket_to_the_responder_which_can_then_resume_towards_it() {
    big_stack(|| {
        let mut w = world();
        let first = w.full();
        let (i_est, r_est) = (first.i_est().unwrap().clone(), first.r_est().unwrap().clone());
        // The initiator issues one ticket and sends it inside the session; the responder keeps it.
        let mut env_i = Env {
            provider: &w.i_prov,
            now: w.now,
            drbg: &mut w.i_drbg,
        };
        let mut issued: ServerTickets<{ sec_common::TK }> = ServerTickets::new();
        let batch = issued.issue_batch(&mut env_i, &i_est, 1, 3600).unwrap();
        assert_eq!(batch.entries().len(), 1);
        let mut kept: ClientTickets<{ sec_common::TK }> = ClientTickets::new();
        kept.accept_batch(&r_est, &batch, w.now);
        assert_eq!(kept.len(), 1);
        // Now the roles are swapped: the old responder dials the old initiator with that ticket.
        std::mem::swap(&mut w.ip, &mut w.rp);
        std::mem::swap(&mut w.i_prov, &mut w.r_prov);
        std::mem::swap(&mut w.i_drbg, &mut w.r_drbg);
        w.stores = ResponderStores::default();
        w.stores.tickets = issued;
        w.client = kept;
        let dial = w.dial();
        assert_eq!(dial, r_est.peer, "the old responder dials the old initiator");
        let mut ini = w.initiator_with(dial, ALPN, false, true);
        let mut rsp = w.responder();
        let out = w.run(&mut ini, &mut rsp, None);
        assert!(out.both_established(), "{:?} {:?}", out.i_errs, out.r_errs);
        assert_eq!(out.types(), vec![6, 7], "a resumption, in the other direction");
        assert!(out.i_est().unwrap().resumed && out.r_est().unwrap().resumed);
        assert_same_keys(out.i_est().unwrap(), out.r_est().unwrap());
    });
}

#[test]
fn tickets_are_exported_sealed_and_restored() {
    big_stack(|| {
        let mut w = world();
        w.full();
        let mut buf = vec![0u8; 2 + 3 * MAX_EXPORT_ENTRY_LEN];
        let n = w.client.export(w.now, 3, &mut buf).unwrap();
        assert_eq!(buf[..2], [1, 1], "version 1, one ticket");
        // The caller seals the bytes with the key store before they are persisted, and unseals them after.
        let mut store = SoftwareStore::new().unwrap();
        let sealed = store.seal(&buf[..n]).unwrap();
        assert!(
            !sealed.windows(32).any(|win| buf[..n].windows(32).any(|p| p == win)),
            "no secret in the clear"
        );
        let plain = store.unseal(&sealed).unwrap();
        let mut restored: ClientTickets<{ sec_common::TK }> = ClientTickets::new();
        assert_eq!(restored.restore(&plain, w.now).unwrap(), 1);
        w.client = restored;
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, false, true);
        let mut r = w.responder();
        let out = w.run(&mut i, &mut r, None);
        assert_eq!(out.types(), vec![6, 7], "the restored ticket resumes");
        assert!(out.both_established());
        // Malformed or altered state stores nothing.
        let mut other: ClientTickets<4> = ClientTickets::new();
        for cut in [0, 1, 2, n - 1] {
            assert!(other.restore(&plain[..cut], w.now).is_err(), "cut at {cut}");
        }
        let mut longer = plain.to_vec();
        longer.push(0);
        assert!(other.restore(&longer, w.now).is_err());
        let mut bad_version = plain.to_vec();
        bad_version[0] = 9;
        assert!(other.restore(&bad_version, w.now).is_err());
        assert!(other.is_empty());
        // An expired ticket is neither exported nor restored.
        let mut w2 = world();
        w2.full();
        let mut b2 = vec![0u8; 2 + MAX_EXPORT_ENTRY_LEN];
        let late = w2.now + 90_000 * 1_000_000_000;
        let n2 = w2.client.export(late, 3, &mut b2).unwrap();
        assert_eq!(b2[..n2], [1, 0]);
        assert_eq!(other.restore(&plain, late).unwrap(), 0);
        // The buffer must be big enough.
        assert!(w2.client.export(w2.now, 3, &mut b2[..10]).is_err());
    });
}

#[test]
fn an_export_keeps_the_newest_tickets_and_a_server_store_has_no_export() {
    big_stack(|| {
        let mut w = world();
        let out = w.full();
        let mut kept: ClientTickets<8> = ClientTickets::new();
        let mut est = out.i_est().unwrap().clone();
        for n in 0..5u8 {
            est.peer = vinc_crypto::NodeId {
                alg: IdentityAlg::Ed25519,
                bytes: [n + 1; 32],
            };
            kept.accept_batch(&est, &out.r_est().unwrap().tickets, w.now + u64::from(n));
        }
        assert_eq!(kept.len(), 5);
        let mut buf = vec![0u8; 2 + 5 * MAX_EXPORT_ENTRY_LEN];
        let n = kept.export(w.now, 3, &mut buf).unwrap();
        assert_eq!(buf[..2], [1, 3], "at most 3, the newest");
        let mut back: ClientTickets<8> = ClientTickets::new();
        assert_eq!(back.restore(&buf[..n], w.now).unwrap(), 3);
        for n in 0..5u8 {
            let peer = vinc_crypto::NodeId {
                alg: IdentityAlg::Ed25519,
                bytes: [n + 1; 32],
            };
            assert_eq!(back.take(&peer, ALPN, w.now).is_some(), n >= 2, "peer {n}");
        }
    });
}

#[test]
fn soft_keys_still_answer_for_a_fallen_back_handshake() {
    big_stack(|| {
        // After the fallback the machine runs the whole full handshake from its own Initial.
        let mut h = hello_answered_but_reply_held();
        retransmit(&mut h.w, &mut h.i);
        let (sent, _) = retransmit(&mut h.w, &mut h.i);
        let mut rsp = h.w.responder();
        let soft_i = SoftKeys {
            signer: Some((vinc_security::KeyHandle(1), &h.w.ip.kp)),
            prekeys: Some(&h.w.prekeys),
        };
        let soft_r = SoftKeys {
            signer: Some((vinc_security::KeyHandle(1), &h.w.rp.kp)),
            prekeys: None,
        };
        let mut env_r = Env {
            provider: &h.w.r_prov,
            now: h.w.now,
            drbg: &mut h.w.r_drbg,
        };
        // A fresh responder (no session for the Hello) takes the Initial.
        rsp.handle(&mut env_r, &mut h.w.stores, &sent[0]).unwrap();
        assert!(rsp.answer_soft(&mut env_r, &soft_r).unwrap());
        let (reply, _) = drain_r(&mut rsp);
        let mut env_i = Env {
            provider: &h.w.i_prov,
            now: h.w.now,
            drbg: &mut h.w.i_drbg,
        };
        h.i.handle(&mut env_i, &reply[0]).unwrap();
        while h.i.answer_soft(&mut env_i, &soft_i).unwrap() {}
        let (finish, events) = drain_i(&mut h.i);
        let est = established(&events).unwrap();
        assert!(!est.resumed);
        rsp.handle(&mut env_r, &mut h.w.stores, &finish[0]).unwrap();
        let (_, events) = drain_r(&mut rsp);
        assert_same_keys(est, established(&events).unwrap());
    });
}
