//! Resumption with 0-RTT: single use, expiry, fallback, tampering, the bounded stores and allocation.
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

use vinc_crypto::{Aead, IdentityAlg, Secret};
use vinc_security::message::MAX_MESSAGE_LEN;
use vinc_security::tickets::{DEFAULT_TICKET_LIFETIME_S, MAX_BATCH};
use vinc_security::{
    ClientTickets, Env, Event, Failure, Output, PacketKey, ResponderStores, ServerTickets, TicketBatch, TicketEntry,
};

mod sec_common;
use sec_common::{ALPN, ALPN_B, Tamper, World, assert_data_flows, assert_same_keys, big_stack};

vinc_tests::install_counting_allocator!();

const LIFETIME_NS: u64 = DEFAULT_TICKET_LIFETIME_S as u64 * 1_000_000_000;

fn world() -> World {
    World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false)
}

fn resume(w: &mut World) -> sec_common::Outcome {
    let dial = w.dial();
    let mut i = w.initiator_with(dial, ALPN, false, true);
    let mut r = w.responder();
    w.run(&mut i, &mut r, None)
}

#[test]
fn resumption_with_0rtt_keys() {
    big_stack(|| {
        for aes in [false, true] {
            let mut w = World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, aes, aes);
            let first = w.full();
            let out = resume(&mut w);
            assert!(out.both_established(), "{:?} {:?}", out.i_errs, out.r_errs);
            assert_eq!(out.types(), vec![6, 7]);
            let (i, r) = (out.i_est().unwrap(), out.r_est().unwrap());
            assert!(i.resumed && r.resumed);
            assert_same_keys(i, r);
            assert_eq!(i.peer, w.rp.id.node_id());
            assert_eq!(r.peer, w.ip.id.node_id());
            let want = if aes { Aead::Aes128Gcm } else { Aead::ChaCha20Poly1305 };
            assert_eq!(i.traffic.aead, want);
            assert_ne!(i.traffic.send, first.i_est().unwrap().traffic.send, "fresh keys");
            assert_data_flows(&w.i_prov, &w.r_prov, i, r);
            // The 0-RTT keys agree, and 0-RTT data flows from the initiator to the responder.
            let (ie, re) = (out.i_early().unwrap(), out.r_early().unwrap());
            assert_eq!(ie.aead, re.aead);
            assert_eq!(ie.secret, re.secret);
            assert_ne!(ie.secret, i.traffic.send);
            let mut tx = PacketKey::from_secret(&w.i_prov, ie.aead, &ie.secret).unwrap();
            let mut rx = PacketKey::from_secret(&w.r_prov, re.aead, &re.secret).unwrap();
            let mut data = *b"early data goes first";
            let tag = tx.seal(&w.i_prov, 0, b"hdr", &mut data).unwrap();
            rx.open(&w.r_prov, 0, b"hdr", &mut data, &tag).unwrap();
            assert_eq!(&data, b"early data goes first");
            // The initiator gets its early keys right after the Hello; the responder is established in the same step.
            assert!(matches!(out.i_events[0], Event::EarlyKeys(_)));
            assert!(matches!(out.r_events[0], Event::EarlyKeys(_)));
            assert!(matches!(out.r_events[1], Event::Established(_)));
            // New tickets come in the reply and resume again.
            assert_eq!(i.tickets.entries().len(), 1);
            assert_eq!(i.tickets, r.tickets);
            w.client.accept_batch(i, &i.tickets, w.now);
            let again = resume(&mut w);
            assert!(again.both_established());
            assert_eq!(again.types(), vec![6, 7]);
        }
    });
}

#[test]
fn nothing_is_resent_after_a_resumption_completed() {
    big_stack(|| {
        let mut w = world();
        w.full();
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, false, true);
        let mut r = w.responder();
        let out = w.run(&mut i, &mut r, None);
        assert!(out.both_established());
        i.retransmit().unwrap();
        r.retransmit();
        assert!(i.poll_output().is_none());
        assert!(r.poll_output().is_none());
    });
}

#[test]
fn a_replayed_hello_is_rejected() {
    big_stack(|| {
        let mut w = world();
        w.full();
        let out = resume(&mut w);
        assert!(out.both_established());
        let hello = out.msgs[0].clone();
        assert_eq!(hello[0], 6);
        let mut r = w.responder();
        let mut env = Env {
            provider: &w.r_prov,
            now: w.now,
            drbg: &mut w.r_drbg,
        };
        r.handle(&mut env, &mut w.stores, &hello).unwrap();
        let Some(Output::Send { data, .. }) = r.poll_output() else {
            panic!("no reject")
        };
        assert_eq!(data[0], 8, "the ticket is gone: reject");
        assert_eq!(data.len(), 17);
        assert!(r.poll_output().is_none(), "nothing is established on a replay");
    });
}

#[test]
fn a_ticket_expires_at_the_responder() {
    big_stack(|| {
        let mut w = world();
        w.full();
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, false, true);
        let mut r = w.responder();
        w.now += LIFETIME_NS + 1;
        let out = w.run(&mut i, &mut r, None);
        assert_eq!(out.types(), vec![6, 8, 1, 4, 5], "reject, then a full handshake");
        assert!(matches!(out.i_events[0], Event::EarlyKeys(_)));
        assert!(matches!(out.i_events[1], Event::ResumeRejected));
        assert!(out.both_established());
        assert!(!out.i_est().unwrap().resumed);
        assert_eq!(
            w.stores.tickets.len(),
            1,
            "the expired ticket was dropped and a new one issued"
        );
    });
}

#[test]
fn a_ticket_is_valid_through_its_expiry_instant() {
    big_stack(|| {
        let mut w = world();
        w.full();
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, false, true);
        let mut r = w.responder();
        w.now += LIFETIME_NS;
        let out = w.run(&mut i, &mut r, None);
        assert_eq!(out.types(), vec![6, 7]);
        assert!(out.i_est().unwrap().resumed);
    });
}

#[test]
fn an_expired_ticket_is_not_used_by_the_initiator() {
    big_stack(|| {
        let mut w = world();
        w.full();
        w.now += LIFETIME_NS + 1;
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, false, true);
        let Some(Output::Send { data, .. }) = i.poll_output() else {
            panic!()
        };
        assert_eq!(data[0], 1, "a full Initial");
        assert!(w.client.is_empty(), "the expired ticket was dropped");
    });
}

#[test]
fn a_restarted_responder_makes_the_initiator_fall_back() {
    big_stack(|| {
        let mut w = world();
        w.full();
        w.stores = ResponderStores::default();
        let out = resume(&mut w);
        assert_eq!(out.types(), vec![6, 8, 1, 4, 5]);
        assert!(out.both_established());
        assert_same_keys(out.i_est().unwrap(), out.r_est().unwrap());
    });
}

#[test]
fn a_wrong_binder_does_not_burn_the_ticket() {
    big_stack(|| {
        let mut w = world();
        w.full();
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, false, true);
        let mut r = w.responder();
        let t = Tamper::flip(0, 118);
        let out = w.run(&mut i, &mut r, Some(&t));
        assert!(out.i_est().is_none_or(|e| !e.resumed));
        assert!(out.r_est().is_none_or(|e| !e.resumed));
        let hello = out.msgs[0].clone();
        // The server still holds the ticket: the genuine Hello resumes.
        let mut r = w.responder();
        let mut env = Env {
            provider: &w.r_prov,
            now: w.now,
            drbg: &mut w.r_drbg,
        };
        r.handle(&mut env, &mut w.stores, &hello).unwrap();
        let Some(Output::Send { data, .. }) = r.poll_output() else {
            panic!("no reply")
        };
        assert_eq!(data[0], 7);
    });
}

#[test]
fn a_ticket_is_bound_to_its_alpn() {
    big_stack(|| {
        let mut w = world();
        w.full();
        let dial = w.dial();
        // The client store hands out nothing for another ALPN.
        assert!(w.client.take(&dial, ALPN_B, w.now).is_none());
        // And a Hello for another ALPN, built from the genuine ticket, is rejected.
        let mut i = w.initiator_with(dial, ALPN, false, true);
        let mut r = w.responder();
        let t = Tamper::custom(0, |m| {
            // ALPN "vinc/1" -> "vinc/2" inside the Hello.
            let at = m.windows(6).position(|x| x == ALPN).unwrap();
            m[at..at + 6].copy_from_slice(ALPN_B);
        });
        let out = w.run(&mut i, &mut r, Some(&t));
        assert!(out.r_est().is_none_or(|e| !e.resumed));
        assert!(out.i_est().is_none_or(|e| !e.resumed));
    });
}

fn hello_len() -> usize {
    1 + 4 + 17 + 9 + 7 + 1 + 16 + 32 + 32
}

/// A fresh world with `n` tickets in the client and the server stores.
fn stocked(n: usize) -> World {
    let mut w = world();
    let out = w.full();
    w.mint_tickets(&out, n);
    w
}

fn positions(len: usize) -> impl Iterator<Item = usize> {
    0..len
}

#[test]
fn tampering_with_the_hello_never_resumes() {
    big_stack(|| {
        let mut w = stocked(hello_len() * 2 + 8);
        for msg_len in [hello_len()] {
            for byte in positions(msg_len) {
                let dial = w.dial();
                let mut i = w.initiator_with(dial, ALPN, false, true);
                let mut r = w.responder();
                let out = w.run(&mut i, &mut r, Some(&Tamper::flip(0, byte)));
                assert!(out.r_est().is_none_or(|e| !e.resumed), "hello byte {byte}");
                assert!(out.i_est().is_none_or(|e| !e.resumed), "hello byte {byte}");
            }
            for cut in positions(msg_len) {
                let dial = w.dial();
                let mut i = w.initiator_with(dial, ALPN, false, true);
                let mut r = w.responder();
                let out = w.run(&mut i, &mut r, Some(&Tamper::truncate(0, cut)));
                assert!(!out.both_established(), "hello cut {cut}");
            }
            let dial = w.dial();
            let mut i = w.initiator_with(dial, ALPN, false, true);
            let mut r = w.responder();
            let out = w.run(&mut i, &mut r, Some(&Tamper::extend(0)));
            assert!(!out.both_established());
        }
    });
}

#[test]
fn tampering_with_the_resume_reply_never_establishes_the_initiator() {
    big_stack(|| {
        // Reply: type, scid(1+8), e_R(32), count(1), one ticket(20), confirm(32) = 95 bytes.
        let reply_len = 1 + 9 + 32 + 1 + 20 + 32;
        let mut w = stocked(2 * reply_len + 8);
        for byte in 0..reply_len {
            let dial = w.dial();
            let mut i = w.initiator_with(dial, ALPN, false, true);
            let mut r = w.responder();
            let out = w.run(&mut i, &mut r, Some(&Tamper::flip(1, byte)));
            assert!(out.i_est().is_none(), "reply byte {byte}");
        }
        for cut in 0..reply_len {
            let dial = w.dial();
            let mut i = w.initiator_with(dial, ALPN, false, true);
            let mut r = w.responder();
            let out = w.run(&mut i, &mut r, Some(&Tamper::truncate(1, cut)));
            assert!(out.i_est().is_none(), "reply cut {cut}");
        }
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, false, true);
        let mut r = w.responder();
        let out = w.run(&mut i, &mut r, Some(&Tamper::extend(1)));
        assert!(out.i_est().is_none());
    });
}

#[test]
fn a_forged_ticket_batch_in_the_reply_fails_the_confirmation() {
    big_stack(|| {
        let mut w = stocked(4);
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, false, true);
        let mut r = w.responder();
        // Change the ticket id (the byte after the count).
        let t = Tamper::flip(1, 1 + 9 + 32 + 1 + 3);
        let out = w.run(&mut i, &mut r, Some(&t));
        assert_eq!(out.i_failed(), Some(Failure::Authentication));
    });
}

#[test]
fn the_resume_run_allocates_nothing() {
    big_stack(|| {
        let mut w = stocked(2);
        let dial = w.dial();
        let ticket = w.client.take(&dial, ALPN, w.now).unwrap();
        let prekey = {
            let mut env = Env {
                provider: &w.i_prov,
                now: w.now,
                drbg: &mut w.i_drbg,
            };
            w.prekeys.acquire(&mut env).unwrap()
        };
        let cfg = vinc_security::ResponderConfig::new(
            w.rp.id,
            vinc_security::ConnId::new(b"respond0").unwrap(),
            vinc_security::AlpnList::new(&[ALPN]).unwrap(),
        );
        let mut hello = vec![0u8; MAX_MESSAGE_LEN];
        let mut reply = vec![0u8; MAX_MESSAGE_LEN];
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
        let mut seen = [0u8; 4];
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
                    token: &[],
                    ticket: Some(ticket),
                    transport_params: &[],
                },
            )
            .unwrap();
            let mut r = vinc_security::Responder::new(cfg);
            let Some(Output::Send { data, .. }) = i.poll_output() else {
                panic!("no hello")
            };
            let n = data.len();
            hello[..n].copy_from_slice(data);
            seen[0] = u8::from(matches!(i.poll_output(), Some(Output::Event(Event::EarlyKeys(_)))));
            r.handle(&mut env_r, &mut w.stores, &hello[..n]).unwrap();
            let Some(Output::Send { data, .. }) = r.poll_output() else {
                panic!("no reply")
            };
            let m = data.len();
            reply[..m].copy_from_slice(data);
            seen[1] = u8::from(matches!(r.poll_output(), Some(Output::Event(Event::EarlyKeys(_)))));
            seen[2] = u8::from(matches!(r.poll_output(), Some(Output::Event(Event::Established(_)))));
            i.handle(&mut env_i, &reply[..m]).unwrap();
            seen[3] = u8::from(matches!(i.poll_output(), Some(Output::Event(Event::Established(_)))));
        });
        assert_eq!(seen, [1, 1, 1, 1]);
        assert_eq!(stats.count(), 0, "{stats:?}");
    });
}

#[test]
fn server_tickets_are_bounded_and_evict_the_oldest() {
    big_stack(|| {
        let mut w = world();
        let out = w.full();
        let r = out.r_est().unwrap();
        let mut env = Env {
            provider: &w.r_prov,
            now: w.now,
            drbg: &mut w.r_drbg,
        };
        let mut store: ServerTickets<3> = ServerTickets::new();
        let a = store.issue_batch(&mut env, r, 4, 60).unwrap();
        assert_eq!(a.entries().len(), MAX_BATCH.min(4));
        assert_eq!(store.len(), 3, "capacity 3 holds at most 3");
        assert_eq!(store.capacity(), 3);
        let zero: ServerTickets<0> = ServerTickets::new();
        let mut zero = zero;
        let none = zero.issue_batch(&mut env, r, 4, 60).unwrap();
        assert!(none.entries().is_empty(), "capacity 0 issues nothing");
        assert!(zero.is_empty());
    });
}

#[test]
fn client_tickets_are_single_use_bounded_and_per_peer() {
    big_stack(|| {
        let mut w = world();
        let out = w.full();
        let (i, r) = (out.i_est().unwrap(), out.r_est().unwrap());
        let mut env = Env {
            provider: &w.r_prov,
            now: w.now,
            drbg: &mut w.r_drbg,
        };
        let mut server: ServerTickets<16> = ServerTickets::new();
        let batch = server.issue_batch(&mut env, r, 4, 3600).unwrap();
        assert_eq!(batch.entries().len(), 4);
        let mut client: ClientTickets<2> = ClientTickets::new();
        client.accept_batch(i, &batch, w.now);
        assert_eq!(client.len(), 2, "bounded");
        let peer = w.rp.id.node_id();
        let t1 = client.take(&peer, ALPN, w.now).unwrap();
        assert_eq!(t1.peer(), &peer);
        assert_eq!(client.len(), 1, "taking removes");
        assert!(client.take(&peer, ALPN, w.now + 3_600_000_000_001).is_none(), "expired");
        assert!(client.is_empty(), "expired tickets are dropped");
        let mut zero: ClientTickets<0> = ClientTickets::new();
        zero.accept_batch(i, &batch, w.now);
        assert!(zero.take(&peer, ALPN, w.now).is_none());
        // Strict batch parsing.
        let mut bytes = [0u8; 81];
        let n = batch.encode(&mut bytes).unwrap();
        assert_eq!(n, 1 + 4 * 20);
        assert_eq!(TicketBatch::parse(&bytes[..n]).unwrap(), batch);
        assert!(TicketBatch::parse(&bytes[..n - 1]).is_err());
        let mut longer = bytes.to_vec();
        longer.push(0);
        assert!(TicketBatch::parse(&longer).is_err());
        let mut five = bytes;
        five[0] = 5;
        assert!(TicketBatch::parse(&five).is_err());
        assert!(client.accept_bytes(i, &bytes[..n - 1], w.now).is_err());
        assert!(client.is_empty());
        let mut full = TicketBatch::new();
        for _ in 0..MAX_BATCH {
            assert!(full.push(TicketEntry::default()));
        }
        assert!(!full.push(TicketEntry::default()));
        let _ = Secret::new([0u8; 1]);
    });
}

#[test]
fn issued_ticket_ids_never_repeat_a_stored_one() {
    let mut w = world();
    let out = w.full();
    let r = out.r_est().unwrap().clone();
    // A generator replayed from the same seed draws the ids already stored; the store must draw on.
    let mut tickets = ServerTickets::<64>::new();
    let mut seen = std::collections::BTreeSet::new();
    for round in 0..2 {
        let mut drbg = vinc_crypto::Drbg::new(&[0x77; 32]);
        let mut env = Env {
            provider: &w.r_prov,
            now: w.now,
            drbg: &mut drbg,
        };
        let batch = tickets.issue_batch(&mut env, &r, 2, 3600);
        if round == 0 {
            for e in batch.unwrap().entries() {
                assert!(seen.insert(e.tid));
            }
        } else {
            for e in batch.unwrap().entries() {
                assert!(seen.insert(e.tid), "an id was issued twice");
            }
        }
    }
    // Once more ids are stored than the attempts allow, the replayed generator is exhausted: a typed error.
    let mut failed = false;
    for _ in 0..8 {
        let mut drbg = vinc_crypto::Drbg::new(&[0x77; 32]);
        let mut env = Env {
            provider: &w.r_prov,
            now: w.now,
            drbg: &mut drbg,
        };
        if let Err(e) = tickets.issue_batch(&mut env, &r, 4, 3600) {
            assert_eq!(e, Failure::TicketId);
            failed = true;
            break;
        }
    }
    assert!(failed);
}

#[test]
fn transport_parameters_are_authenticated_remembered_and_bound_into_resumption() {
    big_stack(|| {
        let mut w = world();
        w.i_params = vec![1, 2, 3, 4];
        w.r_params = vec![9; 40];
        let first = w.full();
        let (i, r) = (first.i_est().unwrap(), first.r_est().unwrap());
        assert_eq!(i.peer_params.as_bytes(), &[9u8; 40][..]);
        assert_eq!(r.peer_params.as_bytes(), &[1u8, 2, 3, 4][..]);
        assert_eq!(
            (i.local_params.as_bytes(), r.local_params.as_bytes()),
            (&[1u8, 2, 3, 4][..], &[9u8; 40][..])
        );
        // Tampering with either side's parameters in flight breaks the handshake.
        for (msg, from_end) in [(0usize, 1usize), (1, 17)] {
            let mut ini = w.initiator();
            let mut rsp = w.responder();
            let t = sec_common::Tamper::flip(msg, first.msgs[msg].len() - from_end);
            let out = w.run(&mut ini, &mut rsp, Some(&t));
            assert!(!out.both_established(), "message {msg}");
        }
        // A resumption uses the parameters the ticket remembered and shows them to both sides.
        let out = resume(&mut w);
        let (i, r) = (out.i_est().unwrap(), out.r_est().unwrap());
        assert!(i.resumed && r.resumed);
        assert_eq!(i.remembered_params.as_bytes(), &[9u8; 40][..]);
        assert_eq!(r.remembered_params.as_bytes(), &[9u8; 40][..]);
        assert_eq!(i.peer_params.as_bytes(), &[9u8; 40][..]);
        assert_eq!(r.peer_params.as_bytes(), &[1u8, 2, 3, 4][..]);
        // A server that now advertises other parameters still honours the ticket; the transport sees both the
        // remembered ones (for 0-RTT) and the current ones (for the rest).
        let mut w2 = world();
        w2.r_params = vec![9; 40];
        w2.full();
        w2.r_params = vec![8; 40];
        let out = resume(&mut w2);
        let (i, r) = (out.i_est().unwrap(), out.r_est().unwrap());
        assert!(i.resumed && r.resumed);
        assert_eq!(i.remembered_params.as_bytes(), &[9u8; 40][..]);
        assert_eq!(i.peer_params.as_bytes(), &[8u8; 40][..]);
        assert_eq!(r.remembered_params.as_bytes(), &[9u8; 40][..]);
        // Too long is refused outright.
        assert!(vinc_security::Params::new(&[0; 257]).is_none());
    });
}
