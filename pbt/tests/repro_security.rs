//! Reproducers of the `pinc-security` bugs the properties of `secstate.rs` found, one plain test each. Every test
//! asserts the documented behaviour and fails on the code of `21e83b64`.
#![allow(clippy::unwrap_used, clippy::cast_possible_truncation, missing_docs)]

use pinc_crypto::provider::KEM_ENCAPS_KEY_LEN;
use pinc_crypto::{Aead, Drbg, IdentityAlg, Keypair, NodeId, Secret, Software};
use pinc_security::message::{Initial, MessageType, PrekeyField};
use pinc_security::responder::{Screen, screen_first};
use pinc_security::tickets::MAX_EXPORT_ENTRY_LEN;
use pinc_security::{
    AeadSet, AlpnList, AmpBudget, Alpn, ClientTickets, ConnId, CreditRecord, Env, Established, Initiator,
    InitiatorParams, KeyHandle, LocalIdentity, Output, PrekeyInfo, Responder, ResponderConfig, ResponderStores, Roll,
    Ticket, TicketBatch, TicketEntry, Traffic, VERSION,
};
use pinc_wire::Writer;

const T0: u64 = 1_000_000_000_000;
const ALPN: &[u8] = b"pinc/1";

fn node(i: u16) -> NodeId {
    let mut bytes = [0u8; 32];
    bytes[..2].copy_from_slice(&i.to_be_bytes());
    bytes[31] = 0xa5;
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes,
    }
}

fn session(peer: NodeId, resume: [u8; 32], credit: CreditRecord) -> Established {
    Established {
        peer,
        alpn: Alpn::new(ALPN).unwrap(),
        traffic: Traffic {
            aead: Aead::Aes128Gcm,
            send: Secret::new([1; 32]),
            recv: Secret::new([2; 32]),
        },
        resume: Secret::new(resume),
        tickets: TicketBatch::new(),
        resumed: false,
        peer_credit: credit,
        local_credit: credit,
        remembered_credit: CreditRecord::NONE,
        cid_secret: Secret::new([3; 32]),
    }
}

fn one(tid: u8, lifetime_s: u32) -> TicketBatch {
    let mut b = TicketBatch::new();
    b.push(TicketEntry {
        tid: [tid; 16],
        lifetime_s,
    });
    b
}

/// A state as `ClientTickets::export` writes it, of `peers` (one ticket each, oldest first), valid for an hour.
fn export_state(peers: &[u16]) -> Vec<u8> {
    let mut s: ClientTickets<8> = ClientTickets::new();
    for (i, p) in peers.iter().enumerate() {
        s.accept_batch(&session(node(*p), [i as u8; 32], CreditRecord::NONE), &one(i as u8, 3600), T0);
    }
    let mut buf = vec![0u8; 2 + 8 * MAX_EXPORT_ENTRY_LEN];
    let n = s.export(T0, 8, &mut buf).unwrap();
    buf.truncate(n);
    buf
}

fn identity(tag: u8) -> (Keypair, LocalIdentity) {
    let alg = IdentityAlg::Ed25519;
    let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    (kp, id)
}

/// The resume Hello a dialer holding `ticket` sends.
fn hello(ticket: Ticket, server: NodeId) -> Vec<u8> {
    let p = Software;
    let mut drbg = Drbg::new(&[0x44; 32]);
    let mut env = Env {
        provider: &p,
        now: T0,
        drbg: &mut drbg,
    };
    let (_, me) = identity(0x31);
    let prekey = PrekeyInfo::new([0; KEM_ENCAPS_KEY_LEN], KeyHandle(0));
    let mut i = Initiator::new(
        &mut env,
        InitiatorParams {
            peer: server,
            alpn: ALPN,
            scid: ConnId::new(b"initiat0").unwrap(),
            identity: &me,
            prekey: &prekey,
            peer_has_prekey: false,
            ticket: Some(ticket),
            credit: CreditRecord::NONE,
        },
    )
    .unwrap();
    for _ in 0..8 {
        if let Some(Output::Send { data, .. }) = i.poll_output() {
            return data.to_vec();
        }
    }
    panic!("the initiator sent nothing");
}

fn short_initial(hash: &[u8; 32]) -> Vec<u8> {
    let m = Initial {
        version: VERSION,
        dcid: ConnId::new(b"respond0").unwrap(),
        scid: ConnId::new(b"initiat0").unwrap(),
        alpn: ALPN,
        aead_offer: AeadSet::from_bits(3).unwrap(),
        e: [9; 32],
        prekey: PrekeyField::Hash(hash),
        credit: CreditRecord::NONE,
    };
    let mut buf = vec![0u8; 2048];
    let mut w = Writer::new(&mut buf);
    m.write(&mut w).unwrap();
    w.written().to_vec()
}

/// Expected: a [`ClientTickets`] of any capacity exports into a buffer of `2 + max * MAX_EXPORT_ENTRY_LEN` bytes;
/// `export` documents one error, "[`WireError::BufferTooSmall`] if `out` cannot hold the state; size it with
/// `2 + max * MAX_EXPORT_ENTRY_LEN`", and `ClientTickets<N>` takes any `N`.
/// Actual: with 256 or more live tickets and `max` of 256 or more, `export` returns `WireError::VarintOverflow`, so a
/// node with a large store cannot persist its tickets at all; the one-byte count of the format cannot carry 256.
/// Suspected fault: `crates/pinc-security/src/tickets.rs:478` (`u8::try_from(count)`, where `count` is not capped to
/// 255), and the format's `count(1)` field. Triggered by the local application (a store with `N >= 256`, default 48).
/// Property: `secstate::a_large_store_exports_and_restores_its_newest_tickets`.
#[test]
fn client_tickets_export_of_256_tickets_fails() {
    let mut s: Box<ClientTickets<256>> = Box::default();
    for i in 0..256u16 {
        s.accept_batch(&session(node(i), [i as u8; 32], CreditRecord::NONE), &one(i as u8, 3600), T0);
    }
    let mut buf = vec![0u8; 2 + 256 * MAX_EXPORT_ENTRY_LEN];
    let r = s.export(T0, 256, &mut buf);
    assert!(r.is_ok(), "export into the documented buffer failed: {r:?}");
}

/// Expected: `restore` "Returns how many were stored", and "`N = 0` is valid and stores nothing", so a store of
/// capacity 0 returns 0.
/// Actual: it returns the number of unexpired entries of the state (here 1) while the store holds none; with two
/// entries of one peer it returns 2 while one is stored (the second replaced the first).
/// Suspected fault: `crates/pinc-security/src/tickets.rs:515-517`, `stored` counts calls to `insert`, not tickets
/// kept. Triggered by the local application; a caller that logs or meters the count reports tickets it does not
/// have. Property: `secstate::restore_returns_how_many_tickets_it_stored`.
#[test]
fn restore_counts_tickets_it_did_not_store() {
    let state = export_state(&[0]);
    let mut none: ClientTickets<0> = ClientTickets::new();
    assert_eq!(none.restore(&state, T0), Ok(none.len()), "a store of capacity 0 reported a stored ticket");
    let mut two = export_state(&[0, 1]);
    // The second entry names the first entry's peer, as a state merged from two stores can.
    let entry = (two.len() - 2) / 2;
    let first_node = two[3..35].to_vec();
    two[2 + entry + 1..2 + entry + 33].copy_from_slice(&first_node);
    let mut s: ClientTickets<8> = ClientTickets::new();
    assert_eq!(s.restore(&two, T0), Ok(s.len()), "restore reported two tickets of one peer as stored");
}

/// Expected: `ServerTickets::issue_batch` issues "`count` ... fresh single-use tickets for `session` and store[s]
/// them ... it holds fewer tickets than asked (none, if `N` is 0) when the store has no room": every ticket of the
/// batch is in the store.
/// Actual: on a store of capacity 1, a batch of 2 holds 2 tickets, and the first no longer opens a resumption: the
/// second evicted it inside the same call. The batch hands out tickets that were never kept (harmless for this
/// crate's `ClientTickets`, which keeps only the last of a batch, but not what the batch says).
/// Suspected fault: `crates/pinc-security/src/tickets.rs:285-302`, `victim` may pick a slot filled earlier in the
/// same batch. Triggered by the local configuration (`tickets_per_session` above the server store's capacity).
/// Property: `secstate::every_ticket_a_batch_hands_out_opens`.
#[test]
fn issue_batch_hands_out_a_ticket_it_already_evicted() {
    let p = Software;
    let mut drbg = Drbg::new(&[0x66; 32]);
    let (_, sid) = identity(0x32);
    let server = sid.node_id();
    let credit = CreditRecord::new(1 << 20, 8, 1200);
    let mut stores: Box<ResponderStores<2, 1>> = Box::default();
    let mut env = Env {
        provider: &p,
        now: T0,
        drbg: &mut drbg,
    };
    let batch = stores.tickets.issue_batch(&mut env, &session(node(7), [0x5c; 32], credit), 2, 3600).unwrap();
    let first = *batch.entries().first().unwrap();
    let mut one_ticket = TicketBatch::new();
    one_ticket.push(first);
    let mut ct: ClientTickets<1> = ClientTickets::new();
    ct.accept_batch(&session(server, [0x5c; 32], credit), &one_ticket, T0);
    let m = hello(ct.take(&server, ALPN, T0).unwrap(), server);
    let s = screen_first(
        &mut stores,
        &AlpnList::new(&[ALPN]).unwrap(),
        AeadSet::from_bits(3).unwrap(),
        T0,
        MessageType::ResumeHello,
        &m,
    );
    assert_eq!(s, Screen::Admit { resume: true }, "the first ticket of the batch is not in the store");
}

/// Expected: `screen_first` decides "without taking a ticket or keeping any state", and the responder doc says "an
/// unauthenticated peer cannot evict cached prekeys".
/// Actual: screening a short Initial looks its hash up with `PrekeyCache::get`, which refreshes the entry's
/// recency. Cache of 2 holding A then B: a screened short Initial naming A makes the next authenticated insert evict
/// B instead of A. The prekey hash crosses the wire in every short Initial, so an unauthenticated sender that saw one
/// can keep chosen entries fresh and steer evictions onto other initiators, which then pay the fallback round trip.
/// Suspected fault: `crates/pinc-security/src/responder.rs:708` (and `:334` for the responder's own lookup), through
/// `crates/pinc-security/src/cache.rs:70-74`. Triggered by an unauthenticated remote peer.
/// Property: `secstate::screening_short_initials_changes_no_cached_prekey`.
#[test]
fn screen_first_refreshes_a_cached_prekey() {
    let mut stores: Box<ResponderStores<2, 1>> = Box::default();
    let (a, b, c) = ([0xa0; 32], [0xb0; 32], [0xc0; 32]);
    stores.prekeys.insert(a, &[1; KEM_ENCAPS_KEY_LEN]);
    stores.prekeys.insert(b, &[2; KEM_ENCAPS_KEY_LEN]);
    let _ = screen_first(
        &mut stores,
        &AlpnList::new(&[ALPN]).unwrap(),
        AeadSet::from_bits(3).unwrap(),
        T0,
        MessageType::ShortInitial,
        &short_initial(&a),
    );
    stores.prekeys.insert(c, &[3; KEM_ENCAPS_KEY_LEN]);
    assert!(stores.prekeys.get(&b).is_some(), "screening changed which prekey the next insert evicted");
}

/// Expected: `Screen::Drop`: "The responder would not answer at all: ... a Hello whose ticket opens but whose binder
/// does not verify", and `screen_first` decides "as the [`Responder`] would on its first message".
/// Actual: the `Responder` answers such a Hello (here: an honest Hello with one byte of its destination id changed,
/// so the binder no longer verifies) with a 17-byte ResumeReject, while the screen drops it. The two disagree; the
/// screen's comment gives the reason for silence, which the responder does not follow.
/// Suspected fault: `crates/pinc-security/src/responder.rs:530` (`Ticket::Binder` grouped with `Missing` and
/// `Mismatch`) against `:729`. Triggered by an on-path remote peer that changes a Hello; in `pinc-core` the screen
/// runs first, so the responder path is reached only where the screen is not used.
/// Property: `secstate::the_screen_decides_as_the_responder_would`.
#[test]
fn responder_rejects_a_wrong_binder_hello_the_screen_drops() {
    let p = Software;
    let mut drbg = Drbg::new(&[0x67; 32]);
    let (_, sid) = identity(0x32);
    let server = sid.node_id();
    let credit = CreditRecord::new(1 << 20, 8, 1200);
    let mut stores: Box<ResponderStores<2, 8>> = Box::default();
    let mut env = Env {
        provider: &p,
        now: T0,
        drbg: &mut drbg,
    };
    let batch = stores.tickets.issue_batch(&mut env, &session(node(7), [0x5c; 32], credit), 1, 3600).unwrap();
    let mut ct: ClientTickets<1> = ClientTickets::new();
    ct.accept_batch(&session(server, [0x5c; 32], credit), &batch, T0);
    let mut m = hello(ct.take(&server, ALPN, T0).unwrap(), server);
    m[3] = 0;
    let alpns = AlpnList::new(&[ALPN]).unwrap();
    let screen = screen_first(&mut stores, &alpns, AeadSet::from_bits(3).unwrap(), T0, MessageType::ResumeHello, &m);
    assert_eq!(screen, Screen::Drop);
    let mut r = Responder::new(ResponderConfig::new(sid, ConnId::new(b"respond0").unwrap(), alpns));
    let _ = r.handle(&mut env, &mut stores, &m);
    let mut sent = Vec::new();
    while let Some(o) = r.poll_output() {
        if let Output::Send { data, .. } = o {
            sent.push(data.to_vec());
        }
    }
    assert!(sent.is_empty(), "the responder answered a Hello the screen drops: {sent:?}");
}

/// Expected: "A caller that sends only when [`AmpBudget::can_send`] holds keeps `tx <= 3 * rx` for the whole
/// unvalidated phase. Counters saturate, and the comparison is done in 128 bits, so no input overflows it."
/// Actual: once `tx` saturates at `u64::MAX` it stops growing, so `can_send` keeps allowing sends: after receiving
/// `u64::MAX` bytes, four sends of `u64::MAX` are all allowed, `4 * (2^64 - 1)` bytes against a budget of
/// `3 * (2^64 - 1)`. The bound holds for every count a real path can reach (it needs more than 2^65 bytes sent);
/// the doc's "for the whole unvalidated phase" does not.
/// Suspected fault: `crates/pinc-security/src/amp.rs:37-39` (a saturated `tx` no longer counts sends; refusing every
/// send once `tx` saturates would keep the bound). Triggered by the local caller only, with counts near 2^64.
/// Property: `secstate::the_amplification_budget_keeps_three_times_the_true_received_count`.
#[test]
fn amp_budget_allows_more_than_three_times_after_saturation() {
    let mut b = AmpBudget::new();
    b.on_receive(u64::MAX);
    let mut sent = 0u128;
    for _ in 0..4 {
        if b.can_send(u64::MAX) {
            b.on_send(u64::MAX);
            sent += u128::from(u64::MAX);
        }
    }
    assert!(sent <= 3 * u128::from(u64::MAX), "an unvalidated path sent {sent} bytes after receiving 2^64 - 1");
}

fn env_drbg() -> Drbg {
    Drbg::new(&[0x71; 32])
}

/// Expected: keyroll module doc: "A duplicate request (the answer was lost) gets the same answer again and no new
/// key ... each request share is used for one roll"; `Answered::dh` is "`None` for a duplicate request".
/// Actual: `Roll` remembers only the last request it answered. The dialer requests R1; the acceptor answers it; the
/// dialer completes and requests R2; the acceptor answers R2; a late copy of R1 then arrives and the acceptor answers
/// it with a new share and a new `dh`, rolling its keys a second time for R1 while the dialer (idle) refuses the
/// answer: the two sides' keys part.
/// Suspected fault: `crates/pinc-security/src/keyroll.rs:216-222` and `:305` (one remembered request). Through
/// `pinc-transport` this is not reachable as far as read: `conn/keys.rs:291` refuses a request while a staged key
/// waits and the transport drops requests under an old key generation. Triggered by a reordering network, for any
/// other user of the public `Roll`. Property: `secstate::each_roll_request_rolls_the_keys_once_on_both_sides`.
#[test]
fn roll_answers_a_stale_request_with_a_new_key() {
    let p = Software;
    let mut drbg = env_drbg();
    let mut env = Env {
        provider: &p,
        now: T0,
        drbg: &mut drbg,
    };
    let mut dialer = Roll::new(true);
    let mut acceptor = Roll::new(false);
    let r1 = dialer.start(&mut env).unwrap();
    let a1 = acceptor.on_request(&mut env, &r1, 10).unwrap();
    dialer.on_answer(&env, &a1.answer).unwrap();
    let r2 = dialer.start(&mut env).unwrap();
    let a2 = acceptor.on_request(&mut env, &r2, 20).unwrap();
    dialer.on_answer(&env, &a2.answer).unwrap();
    let late = acceptor.on_request(&mut env, &r1, 30);
    assert!(
        !late.is_ok_and(|a| a.dh.is_some()),
        "a late copy of an answered request rolled the keys again"
    );
}

/// Expected: "If both sides ask at once, the dialing side's request wins and the other side drops its own and
/// answers", "each request share is used for one roll", and both sides of a roll mix in the same value.
/// Actual: the acceptor requests R1; the dialer (idle) answers it and rolls with R1's value; before that answer
/// arrives the dialer requests R2; the acceptor, with R1 still out, drops R1 and answers R2. The dialer rolled for R1,
/// the acceptor never will (the answer to R1 now finds it idle): the first roll each side makes differs.
/// Suspected fault: `crates/pinc-security/src/keyroll.rs:283-288` (the acceptor drops a request the dialer may
/// already have answered). Through `pinc-transport` not reachable as far as read: `conn/keys.rs:202-208` starts a
/// roll only with no staged key, which the dialer has until the acceptor moved. Triggered by the timing of the two
/// sides, for any other user of the public `Roll`. Property: `secstate::each_roll_request_rolls_the_keys_once_on_both_sides`.
#[test]
fn roll_acceptor_drops_a_request_the_dialer_answered() {
    let p = Software;
    let mut drbg = env_drbg();
    let mut env = Env {
        provider: &p,
        now: T0,
        drbg: &mut drbg,
    };
    let mut dialer = Roll::new(true);
    let mut acceptor = Roll::new(false);
    let r1 = acceptor.start(&mut env).unwrap();
    let a1 = dialer.on_request(&mut env, &r1, 10).unwrap();
    let dialer_first = *a1.dh.unwrap().expose();
    let r2 = dialer.start(&mut env).unwrap();
    let a2 = acceptor.on_request(&mut env, &r2, 20).unwrap();
    let acceptor_first = a2
        .dh
        .map(|d| *d.expose())
        .or_else(|| acceptor.on_answer(&env, &a1.answer).ok().map(|c| *c.dh.expose()));
    assert_eq!(acceptor_first, Some(dialer_first), "the two sides' first rolls used different values");
}
