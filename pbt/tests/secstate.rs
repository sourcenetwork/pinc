//! `pinc-security`, second pass: the bounded tables and counters against reference models, and the endpoint's screen
//! of first messages against the responder it stands in for.
//!
//! Where the expected behaviour comes from:
//! - `cache` module doc: "it never holds more than `N` entries; a lookup refreshes the entry's recency; inserting into
//!   a full cache evicts the least recently used entry; `N = 0` is valid and caches nothing".
//! - `amp` module doc: "a send of `n` bytes is allowed only while `tx + n + OVERHEAD <= 3 * rx` ... A caller that sends
//!   only when [`AmpBudget::can_send`] holds keeps `tx <= 3 * rx` for the whole unvalidated phase. Counters saturate,
//!   and the comparison is done in 128 bits, so no input overflows it."
//! - `credit` module doc: "every 6-byte string decodes to exactly one record that re-encodes to the same bytes";
//!   `CreditRecord::new`: "rounded down to whole units, saturating at the largest the field holds"; `covers`: "every
//!   limit of this record is at least `other`'s".
//! - `tickets` module doc: "a [`ClientTickets`] store holds one ticket per peer, the newest replacing the older, for at
//!   most `N` peers, evicting expired and then the oldest; `N = 0` is valid and stores nothing"; `take`: "Take the
//!   unexpired ticket for `peer` if it is for `alpn`, removing it ... Expired tickets are dropped on the way";
//!   `export`: "the newest at most `max` unexpired tickets, oldest first ... [`WireError::BufferTooSmall`] if `out`
//!   cannot hold the state; size it with `2 + max * MAX_EXPORT_ENTRY_LEN`"; `restore`: "every entry that has not
//!   expired by `now` is stored as [`ClientTickets::accept_batch`] stores tickets. Returns how many were stored ... A
//!   [`WireError`] if `bytes` is not exactly one well-formed state; nothing is stored then"; `ServerTickets::issue_batch`:
//!   "Issue `count` (at most [`MAX_BATCH`]) fresh single-use tickets for `session` and store them ... it holds fewer
//!   tickets than asked (none, if `N` is 0) when the store has no room".
//! - `responder::screen_first`: "Decide what to do with `message` ... as the [`Responder`] would on its first message,
//!   without taking a ticket or keeping any state"; `Screen::Reject`: "The responder would only answer with this
//!   reject (its message bytes) and keep nothing"; `Screen::Drop`: "The responder would not answer at all".
//! - `keyroll` module doc: "A duplicate request (the answer was lost) gets the same answer again and no new key ...
//!   each request share is used for one roll"; `Answered::dh`: "`None` for a duplicate request (the keys already
//!   rolled)".
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    missing_docs
)]

use std::collections::HashMap;

use ephyra::prelude::*;
use ephyra::check_generator;
use pinc_crypto::provider::KEM_ENCAPS_KEY_LEN;
use pinc_crypto::{Aead, Drbg, IdentityAlg, Keypair, NodeId, Secret, Software};
use pinc_security::keyroll::Rekey;
use pinc_security::message::{Initial, MessageType, PrekeyField};
use pinc_security::responder::{Screen, screen_first};
use pinc_security::tickets::MAX_EXPORT_ENTRY_LEN;
use pinc_security::{
    AeadSet, AlpnList, AmpBudget, Alpn, ClientTickets, ConnId, CreditRecord, Env, Established, Event, Initiator,
    InitiatorParams, KeyHandle, LocalIdentity, Output, PrekeyCache, PrekeyInfo, Responder, ResponderConfig,
    ResponderStores, Roll, TicketBatch, TicketEntry, Traffic, VERSION, WINDOW_UNIT,
};
use pinc_wire::Writer;

const T0: u64 = 1_000_000_000_000;
const NS: u64 = 1_000_000_000;

// ---------------------------------------------------------------------------------------------------------------
// The prekey cache against a list in recency order.

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum CacheOp {
    Get(#[ephyra(gen = gens::int(0u8..=11))] u8),
    Insert(#[ephyra(gen = gens::int(0u8..=11))] u8),
}

/// The key cached under hash `k`: a function of the hash, as a real prekey and its hash are.
fn cache_key(k: u8) -> [u8; KEM_ENCAPS_KEY_LEN] {
    let mut key = [k; KEM_ENCAPS_KEY_LEN];
    key[0] = k.wrapping_mul(31).wrapping_add(7);
    key
}

fn lru_run<const N: usize>(ops: &[CacheOp]) {
    let mut real: Box<PrekeyCache<N>> = Box::default();
    // Least recently used first.
    let mut model: Vec<u8> = Vec::new();
    for op in ops {
        match op {
            CacheOp::Get(k) => {
                let got = real.get(&[*k; 32]).copied();
                let pos = model.iter().position(|m| m == k);
                assert_eq!(got.is_some(), pos.is_some(), "N={N}: a lookup of {k} disagrees with the LRU model");
                if let Some(p) = pos {
                    assert_eq!(got, Some(cache_key(*k)), "N={N}: a lookup returned another key");
                    let m = model.remove(p);
                    model.push(m);
                }
            },
            CacheOp::Insert(k) => {
                real.insert([*k; 32], &cache_key(*k));
                if let Some(p) = model.iter().position(|m| m == k) {
                    model.remove(p);
                } else if model.len() == N && N > 0 {
                    model.remove(0);
                }
                if N > 0 {
                    model.push(*k);
                }
            },
        }
        assert_eq!(real.len(), model.len(), "N={N}: the cache holds another number of entries than the model");
        assert!(real.len() <= N, "N={N}: the cache holds more than its capacity");
    }
}

fn cache_runs() -> impl Gen<Value = (u8, Vec<CacheOp>)> {
    (gens::int(0u8..=4), gens::vec(ephyra::any::<CacheOp>()).len(0..=60))
}

/// Every lookup and insert of a prekey cache of capacity 0, 1, 2, 3 and 8 agrees with a list kept in recency order.
#[ephyra::test(gen = cache_runs(), tests = 3000)]
fn the_prekey_cache_is_the_lru_its_doc_describes(run: (u8, Vec<CacheOp>)) {
    let (n, ops) = run;
    match n {
        0 => lru_run::<0>(&ops),
        1 => lru_run::<1>(&ops),
        2 => lru_run::<2>(&ops),
        3 => lru_run::<3>(&ops),
        _ => lru_run::<8>(&ops),
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The amplification budget against the true counts.

fn amount(g: &mut Source) -> u64 {
    match g.int(0u8..=4) {
        0 => g.int(0u64..=4000),
        1 => u64::MAX - g.int(0u64..=4000),
        2 => u64::MAX / 3 + g.int(0u64..=4000) - 2000,
        3 => g.int(0u64..=u64::MAX),
        _ => u64::MAX,
    }
}

fn amounts() -> impl Gen<Value = u64> {
    amount
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum AmpOp {
    Receive(#[ephyra(gen = amounts())] u64),
    /// Send `n` bytes if the budget allows it, as the doc's caller does.
    Send(#[ephyra(gen = amounts())] u64),
    Validate,
}

fn amp_runs() -> impl Gen<Value = Vec<AmpOp>> {
    gens::vec(ephyra::any::<AmpOp>()).len(0..=24)
}

/// A caller that sends only when the budget allows it never sends more than three times what it received before
/// validation, counting in 128 bits; below saturation, the budget allows exactly what the formula of the doc allows.
#[ephyra::test(gen = amp_runs(), tests = 20_000)]
fn the_amplification_budget_keeps_three_times_the_true_received_count(ops: Vec<AmpOp>) {
    let mut b = AmpBudget::new();
    let (mut rx, mut tx, mut validated) = (0u128, 0u128, false);
    for op in &ops {
        match op {
            AmpOp::Receive(n) => {
                b.on_receive(*n);
                rx += u128::from(*n);
            },
            AmpOp::Send(n) => {
                let allowed = b.can_send(*n);
                if !validated && rx <= u128::from(u64::MAX) && tx <= u128::from(u64::MAX) {
                    let formula = tx + u128::from(*n) + 48 <= 3 * rx;
                    assert_eq!(allowed, formula, "the budget disagrees with tx + n + 48 <= 3 * rx");
                }
                if allowed {
                    b.on_send(*n);
                    tx += u128::from(*n);
                }
            },
            AmpOp::Validate => {
                b.validate();
                validated = true;
            },
        }
        assert_eq!(u128::from(b.received()), rx.min(u128::from(u64::MAX)), "received() is not the saturated count");
        assert_eq!(u128::from(b.sent()), tx.min(u128::from(u64::MAX)), "sent() is not the saturated count");
        if !validated {
            ephyra::signature("tx above 3 rx");
            assert!(tx <= 3 * rx, "an unvalidated path sent {tx} bytes after receiving {rx}");
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The credit record.

fn credit_inputs() -> impl Gen<Value = ([u8; 6], [u8; 6], [u8; 6], u64)> {
    (
        |g: &mut Source| -> [u8; 6] { core::array::from_fn(|_| g.int(0u8..=255)) },
        |g: &mut Source| -> [u8; 6] { core::array::from_fn(|_| g.int(0u8..=255)) },
        |g: &mut Source| -> [u8; 6] { core::array::from_fn(|_| g.int(0u8..=255)) },
        amounts(),
    )
}

/// Every 6-byte string is one record and back, `new` rounds the window down and saturates, and `covers` is the
/// field-wise order (reflexive, antisymmetric, transitive).
#[ephyra::test(gen = credit_inputs(), tests = 5000)]
fn a_credit_record_round_trips_and_covers_is_the_fieldwise_order(x: ([u8; 6], [u8; 6], [u8; 6], u64)) {
    let (a, b, c, w) = x;
    let (ra, rb, rc) = (CreditRecord::decode(&a), CreditRecord::decode(&b), CreditRecord::decode(&c));
    assert_eq!(ra.encode(), a, "a record does not re-encode to its bytes");
    assert_eq!(CreditRecord::decode(&ra.encode()), ra, "a record does not decode from its encoding");
    let n = CreditRecord::new(w, ra.max_streams, ra.max_datagram);
    let units = (w / WINDOW_UNIT).min(u64::from(u16::MAX));
    assert_eq!(u64::from(n.window_units), units, "new() does not round the window down and saturate");
    assert!(ra.covers(&ra), "covers is not reflexive");
    if ra.covers(&rb) && rb.covers(&ra) {
        assert_eq!(ra, rb, "covers is not antisymmetric");
    }
    if ra.covers(&rb) && rb.covers(&rc) {
        assert!(ra.covers(&rc), "covers is not transitive");
    }
    let fieldwise =
        ra.window_units >= rb.window_units && ra.max_streams >= rb.max_streams && ra.max_datagram >= rb.max_datagram;
    assert_eq!(ra.covers(&rb), fieldwise, "covers is not the field-wise order");
}

// ---------------------------------------------------------------------------------------------------------------
// The client ticket store against a list in age order, observed through its export.

const ALPNS: [&[u8]; 2] = [b"pinc/1", b"pinc/2"];

fn node(i: u16) -> NodeId {
    let mut bytes = [0u8; 32];
    bytes[..2].copy_from_slice(&i.to_be_bytes());
    bytes[31] = 0xa5;
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes,
    }
}

/// A session as `ClientTickets::accept_batch` and `ServerTickets::issue_batch` read it.
fn session(peer: NodeId, alpn: &[u8], aead: Aead, resume: [u8; 32], peer_credit: CreditRecord) -> Established {
    Established {
        peer,
        alpn: Alpn::new(alpn).unwrap(),
        traffic: Traffic {
            aead,
            send: Secret::new([1; 32]),
            recv: Secret::new([2; 32]),
        },
        resume: Secret::new(resume),
        tickets: TicketBatch::new(),
        resumed: false,
        peer_credit,
        local_credit: peer_credit,
        remembered_credit: CreditRecord::NONE,
        cid_secret: Secret::new([3; 32]),
    }
}

/// One exported ticket, as the export's documented layout gives it.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Entry {
    alg: u8,
    node: [u8; 32],
    alpn: Vec<u8>,
    tid: [u8; 16],
    psk: [u8; 32],
    aead: u8,
    expiry: u64,
    credit: [u8; 6],
}

/// The entries of an export, by its documented layout; `None` if the bytes do not follow it.
fn parse_export(b: &[u8]) -> Option<Vec<Entry>> {
    let mut r = pinc_wire::Reader::new(b);
    if r.read_u8().ok()? != 1 {
        return None;
    }
    let count = r.read_u8().ok()?;
    let mut out = Vec::new();
    for _ in 0..count {
        let alg = r.read_u8().ok()?;
        let node = r.read_array::<32>().ok()?;
        let n = usize::from(r.read_u8().ok()?);
        let alpn = r.read_bytes(n).ok()?.to_vec();
        out.push(Entry {
            alg,
            node,
            alpn,
            tid: r.read_array::<16>().ok()?,
            psk: r.read_array::<32>().ok()?,
            aead: r.read_u8().ok()?,
            expiry: r.read_u64().ok()?,
            credit: r.read_array::<6>().ok()?,
        });
    }
    r.is_empty().then_some(out)
}

fn write_export(entries: &[Entry]) -> Vec<u8> {
    let mut buf = vec![0u8; 2 + entries.len() * MAX_EXPORT_ENTRY_LEN];
    let mut w = Writer::new(&mut buf);
    w.put_u8(1).unwrap();
    w.put_u8(entries.len() as u8).unwrap();
    for e in entries {
        w.put_u8(e.alg).unwrap();
        w.put_slice(&e.node).unwrap();
        w.put_u8(e.alpn.len() as u8).unwrap();
        w.put_slice(&e.alpn).unwrap();
        w.put_slice(&e.tid).unwrap();
        w.put_slice(&e.psk).unwrap();
        w.put_u8(e.aead).unwrap();
        w.put_u64(e.expiry).unwrap();
        w.put_slice(&e.credit).unwrap();
    }
    let n = w.written().len();
    buf.truncate(n);
    buf
}

/// Everything the store holds, oldest first: an export at time 0, when nothing has expired.
fn contents<const N: usize>(s: &ClientTickets<N>) -> Vec<Entry> {
    let mut buf = vec![0u8; 2 + N * MAX_EXPORT_ENTRY_LEN];
    let n = s.export(0, N, &mut buf).unwrap();
    parse_export(&buf[..n]).expect("an export does not follow its documented layout")
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum TicketOp {
    /// A batch from peer `p` for ALPN `a`, each entry `(tid seed, lifetime in seconds)`.
    Accept(
        #[ephyra(gen = gens::int(0u16..=9))] u16,
        #[ephyra(gen = gens::int(0u8..=1))] u8,
        #[ephyra(gen = gens::vec((gens::int(0u8..=255), gens::int(0u32..=40))).len(0..=4))] Vec<(u8, u32)>,
    ),
    Take(#[ephyra(gen = gens::int(0u16..=9))] u16, #[ephyra(gen = gens::int(0u8..=1))] u8),
    /// Time passes, in seconds.
    Wait(#[ephyra(gen = gens::int(0u64..=30))] u64),
    /// Export the newest `max` unexpired tickets and restore them into a new store, which replaces this one.
    Persist(#[ephyra(gen = gens::int(0usize..=9))] usize),
    /// Restore a changed copy of the current export into this store.
    Hostile(#[ephyra(gen = gens::vec(ephyra::any::<Edit>()).len(1..=3))] Vec<Edit>),
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Edit {
    Flip(#[ephyra(gen = gens::int(0u16..=2000))] u16, #[ephyra(gen = gens::int(0u8..=7))] u8),
    Set(#[ephyra(gen = gens::int(0u16..=2000))] u16, u8),
    Cut(#[ephyra(gen = gens::int(0u16..=2000))] u16),
    Insert(#[ephyra(gen = gens::int(0u16..=2000))] u16, u8),
}

fn apply(m: &[u8], edits: &[Edit]) -> Vec<u8> {
    let mut out = m.to_vec();
    for e in edits {
        let n = out.len();
        if n == 0 {
            break;
        }
        let at = |p: &u16| usize::from(*p) % n;
        match e {
            Edit::Flip(p, b) => out[at(p)] ^= 1 << b,
            Edit::Set(p, v) => out[at(p)] = *v,
            Edit::Cut(p) => out.truncate(at(p)),
            Edit::Insert(p, v) => out.insert(at(p), *v),
        }
    }
    out
}

/// The stores the documented insert may leave: the peer's older ticket replaced and the new one the newest, else the
/// new one added while there is room, else any one expired ticket or else the oldest making room.
fn inserted(model: &[Entry], e: Entry, now: u64, cap: usize) -> Vec<Vec<Entry>> {
    if cap == 0 {
        return vec![model.to_vec()];
    }
    let mut base = model.to_vec();
    if let Some(p) = base.iter().position(|m| m.node == e.node && m.alg == e.alg) {
        base.remove(p);
        base.push(e);
        return vec![base];
    }
    if base.len() < cap {
        base.push(e);
        return vec![base];
    }
    let expired: Vec<usize> = (0..base.len()).filter(|&i| base[i].expiry < now).collect();
    let victims = if expired.is_empty() { vec![0] } else { expired };
    victims
        .into_iter()
        .map(|v| {
            let mut s = base.clone();
            s.remove(v);
            s.push(e.clone());
            s
        })
        .collect()
}

fn insert_all(model: &[Entry], es: &[Entry], now: u64, cap: usize, real: &[Entry]) -> bool {
    // A breadth of possible stores, pruned to the ones that can still end as `real`.
    let mut states = vec![model.to_vec()];
    for e in es {
        let mut next: Vec<Vec<Entry>> = states
            .iter()
            .flat_map(|s| inserted(s, e.clone(), now, cap))
            .collect();
        next.dedup();
        next.truncate(64);
        states = next;
    }
    states.iter().any(|s| s == real)
}

fn ticket_run<const N: usize>(ops: &[TicketOp]) {
    let mut real: Box<ClientTickets<N>> = Box::default();
    let mut model: Vec<Entry> = Vec::new();
    let mut now = T0;
    let mut serial = 0u8;
    for op in ops {
        match op {
            TicketOp::Accept(p, a, entries) => {
                serial = serial.wrapping_add(1);
                let resume = [serial; 32];
                let credit = CreditRecord::new(u64::from(serial) * WINDOW_UNIT, u16::from(*a), 1200);
                let s = session(node(*p), ALPNS[usize::from(*a)], Aead::Aes128Gcm, resume, credit);
                let mut batch = TicketBatch::new();
                for (seed, life) in entries {
                    batch.push(TicketEntry {
                        tid: [*seed; 16],
                        lifetime_s: *life,
                    });
                }
                real.accept_batch(&s, &batch, now);
                let after = contents(&real);
                // The new entries, as they read back: a tid and an expiry the model knows, the psk the store derived.
                let news: Vec<Entry> = entries
                    .iter()
                    .map(|(seed, life)| {
                        let found = after.iter().find(|e| {
                            e.alg == IdentityAlg::Ed25519.tag() && e.tid == [*seed; 16] && e.node == node(*p).bytes
                        });
                        Entry {
                            alg: IdentityAlg::Ed25519.tag(),
                            node: node(*p).bytes,
                            alpn: ALPNS[usize::from(*a)].to_vec(),
                            tid: [*seed; 16],
                            psk: found.map_or([0; 32], |e| e.psk),
                            aead: found.map_or(0, |e| e.aead),
                            expiry: now + u64::from(*life) * NS,
                            credit: credit.encode(),
                        }
                    })
                    .collect();
                // Only the last of a batch can still be there: the earlier ones were replaced by it.
                let news = news.last().cloned().into_iter().collect::<Vec<_>>();
                assert!(
                    insert_all(&model, &news, now, N, &after),
                    "N={N}: accept_batch left a store the documented insert cannot leave\nmodel {model:?}\nreal {after:?}"
                );
                model = after;
            },
            TicketOp::Take(p, a) => {
                let got = real.take(&node(*p), ALPNS[usize::from(*a)], now);
                model.retain(|e| e.expiry >= now);
                let at = model
                    .iter()
                    .position(|e| e.alg == IdentityAlg::Ed25519.tag() && e.node == node(*p).bytes && e.alpn == ALPNS[usize::from(*a)]);
                assert_eq!(got.is_some(), at.is_some(), "N={N}: take disagrees with the model");
                if let (Some(t), Some(i)) = (got, at) {
                    let want = model.remove(i);
                    assert_eq!(t.peer(), &node(*p), "N={N}: take returned another peer's ticket");
                    assert_eq!(t.expiry(), want.expiry, "N={N}: take returned another expiry");
                    assert_eq!(t.peer_credit().encode(), want.credit, "N={N}: take returned another credit record");
                }
                assert_eq!(contents(&real), model, "N={N}: take left another store than the model");
            },
            TicketOp::Wait(s) => now += s * NS,
            TicketOp::Persist(max) => {
                let mut buf = vec![0u8; 2 + max * MAX_EXPORT_ENTRY_LEN];
                let n = real.export(now, *max, &mut buf).unwrap();
                let live: Vec<Entry> = model.iter().filter(|e| e.expiry >= now).cloned().collect();
                let want: Vec<Entry> = live[live.len().saturating_sub(*max)..].to_vec();
                assert_eq!(parse_export(&buf[..n]), Some(want.clone()), "N={N}: the export is not the newest {max}");
                let mut back: Box<ClientTickets<N>> = Box::default();
                back.restore(&buf[..n], now).unwrap();
                assert_eq!(contents(&back), want, "N={N}: a restore does not give back what was exported");
                real = back;
                model = want;
            },
            TicketOp::Hostile(edits) => {
                let state = write_export(&model);
                let m = apply(&state, edits);
                let r = real.restore(&m, now);
                let after = contents(&real);
                match (r, parse_export(&m)) {
                    (Err(_), _) => assert_eq!(after, model, "N={N}: a refused restore changed the store"),
                    (Ok(_), None) => panic!("N={N}: restore took bytes that do not follow the layout"),
                    (Ok(_), Some(es)) => {
                        let live: Vec<Entry> = es.into_iter().filter(|e| e.expiry >= now).collect();
                        assert!(
                            insert_all(&model, &live, now, N, &after),
                            "N={N}: a restore left a store the documented insert cannot leave"
                        );
                        model = after;
                    },
                }
            },
        }
        assert!(model.len() <= N, "N={N}: more tickets than the capacity");
        // A peer is its algorithm and its key: a state may name the same bytes under two algorithms.
        let mut peers: Vec<(u8, [u8; 32])> = model.iter().map(|e| (e.alg, e.node)).collect();
        peers.sort_unstable();
        peers.dedup();
        assert_eq!(peers.len(), model.len(), "N={N}: two tickets of one peer");
    }
}

fn ticket_runs() -> impl Gen<Value = (u8, Vec<TicketOp>)> {
    (gens::int(0u8..=4), gens::vec(ephyra::any::<TicketOp>()).len(0..=40))
}

/// The ticket runs the generator makes stay in their documented ranges.
#[test]
fn the_ticket_run_generator_stays_in_range() {
    let ok = |x: &(u8, Vec<TicketOp>)| {
        x.0 <= 4
            && x.1.len() <= 40
            && x.1.iter().all(|op| match op {
                TicketOp::Accept(p, a, es) => *p <= 9 && *a <= 1 && es.len() <= 4 && es.iter().all(|e| e.1 <= 40),
                TicketOp::Take(p, a) => *p <= 9 && *a <= 1,
                TicketOp::Wait(s) => *s <= 30,
                TicketOp::Persist(m) => *m <= 9,
                TicketOp::Hostile(es) => (1..=3).contains(&es.len()),
            })
    };
    check_generator(&Config::default().tests(3000), ticket_runs(), ok).assert_passed();
}

/// The client store against a model in age order, for capacities 0, 1, 2, 3 and 8: accepting batches from ten peers,
/// taking, time passing, persisting through export and restore, and restoring hostile copies of a state.
#[ephyra::test(gen = ticket_runs(), tests = 2000)]
fn the_client_ticket_store_follows_its_documented_model(run: (u8, Vec<TicketOp>)) {
    let (n, ops) = run;
    match n {
        0 => ticket_run::<0>(&ops),
        1 => ticket_run::<1>(&ops),
        2 => ticket_run::<2>(&ops),
        3 => ticket_run::<3>(&ops),
        _ => ticket_run::<8>(&ops),
    }
}

fn restore_inputs() -> impl Gen<Value = (u8, Vec<(u16, u8)>, u64)> {
    (
        gens::int(0u8..=3),
        gens::vec((gens::int(0u16..=5), gens::int(0u8..=20))).len(0..=8),
        gens::int(0u64..=20),
    )
}

/// What `restore` returns is how many tickets of the state are in the store afterwards ("Returns how many were
/// stored"), for a state written by `export` of a store of the same peers and for a store of capacity 0 ("stores
/// nothing").
#[ephyra::test(gen = restore_inputs(), tests = 2000)]
fn restore_returns_how_many_tickets_it_stored(x: (u8, Vec<(u16, u8)>, u64)) {
    let (n, tickets, wait) = x;
    // A state of these tickets, oldest first, as an export writes it (one peer may appear twice: two stores merged).
    let entries: Vec<Entry> = tickets
        .iter()
        .enumerate()
        .map(|(i, (p, life))| Entry {
            alg: IdentityAlg::Ed25519.tag(),
            node: node(*p).bytes,
            alpn: ALPNS[0].to_vec(),
            tid: [i as u8; 16],
            psk: [0x77; 32],
            aead: 1,
            expiry: T0 + u64::from(*life) * NS,
            credit: [0, 1, 0, 2, 0, 3],
        })
        .collect();
    let state = write_export(&entries);
    let now = T0 + wait * NS;
    fn check<const N: usize>(state: &[u8], now: u64) {
        let mut s: Box<ClientTickets<N>> = Box::default();
        let r = s.restore(state, now).unwrap();
        let ours = parse_export(state).unwrap();
        let after = contents(&s);
        let stored = after.iter().filter(|e| ours.contains(e)).count();
        ephyra::signature(if N == 0 { "capacity 0" } else { "replaced or evicted" });
        assert_eq!(r, stored, "N={N}: restore returned {r}, the store holds {stored} of the state's tickets");
    }
    match n {
        0 => check::<0>(&state, now),
        1 => check::<1>(&state, now),
        2 => check::<2>(&state, now),
        _ => check::<8>(&state, now),
    }
}

fn export_sizes() -> impl Gen<Value = (usize, usize)> {
    (
        |g: &mut Source| *g.pick(&[0usize, 1, 2, 254, 255, 256, 257, 300]),
        |g: &mut Source| *g.pick(&[0usize, 1, 255, 256, 300]),
    )
}

/// A store of up to 300 peers exports its newest `max` tickets into a buffer of the documented size, and a store of
/// the same capacity restores them, for counts on both sides of 255.
#[ephyra::test(gen = export_sizes(), tests = 60)]
fn a_large_store_exports_and_restores_its_newest_tickets(x: (usize, usize)) {
    let (live, max) = x;
    let mut s: Box<ClientTickets<300>> = Box::default();
    for i in 0..live {
        let peer = node(i as u16);
        let sess = session(peer, ALPNS[0], Aead::ChaCha20Poly1305, [i as u8; 32], CreditRecord::NONE);
        let mut b = TicketBatch::new();
        b.push(TicketEntry {
            tid: [i as u8; 16],
            lifetime_s: 3600,
        });
        s.accept_batch(&sess, &b, T0);
    }
    let mut buf = vec![0u8; 2 + max * MAX_EXPORT_ENTRY_LEN];
    let r = s.export(T0, max, &mut buf);
    ephyra::signature(if live.min(max) > 255 { "more than 255" } else { "at most 255" });
    assert!(r.is_ok(), "export of {} tickets into the documented buffer failed: {r:?}", live.min(max));
    let n = r.unwrap();
    let mut back: Box<ClientTickets<300>> = Box::default();
    let got = back.restore(&buf[..n], T0);
    assert_eq!(got, Ok(live.min(max)), "a restore of the export did not store every exported ticket");
    assert_eq!(back.len(), live.min(max), "the restored store holds another number of tickets");
}

// ---------------------------------------------------------------------------------------------------------------
// The server store, checked through redemption, and the screen against the responder.

type Stores = ResponderStores<2, 8>;
const ALPN: &[u8] = b"pinc/1";

fn identity(tag: u8) -> (Keypair, LocalIdentity) {
    let alg = IdentityAlg::Ed25519;
    let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    (kp, id)
}

fn responder(id: LocalIdentity) -> Responder {
    Responder::new(ResponderConfig::new(
        id,
        ConnId::new(b"respond0").unwrap(),
        AlpnList::new(&ALPNS).unwrap(),
    ))
}

/// The first message a dialer holding `ticket` sends at `now`.
fn hello(ticket: pinc_security::Ticket, server: NodeId, alpn: &[u8], now: u64) -> Vec<u8> {
    let p = Software;
    let mut drbg = Drbg::new(&[0x44; 32]);
    let mut env = Env {
        provider: &p,
        now,
        drbg: &mut drbg,
    };
    let (_, me) = identity(0x31);
    let prekey = PrekeyInfo::new([0; KEM_ENCAPS_KEY_LEN], KeyHandle(0));
    let mut i = Initiator::new(
        &mut env,
        InitiatorParams {
            peer: server,
            alpn,
            scid: ConnId::new(b"initiat0").unwrap(),
            identity: &me,
            prekey: &prekey,
            peer_has_prekey: false,
            ticket: Some(ticket),
            credit: CreditRecord::NONE,
        },
    )
    .unwrap();
    loop {
        match i.poll_output() {
            Some(Output::Send { data, .. }) => return data.to_vec(),
            Some(_) => {},
            None => panic!("the initiator sent nothing"),
        }
    }
}

/// Issue `count` tickets on a server store of capacity `N` and see whether each one still opens a resumption.
fn issue_and_redeem<const N: usize>(count: usize, before: usize) -> Vec<bool> {
    let p = Software;
    let mut drbg = Drbg::new(&[0x66; 32]);
    let (_, sid) = identity(0x32);
    let server = sid.node_id();
    let client = node(7);
    let credit = CreditRecord::new(1 << 20, 8, 1200);
    let mut stores: Box<ResponderStores<2, N>> = Box::default();
    let mut env = Env {
        provider: &p,
        now: T0,
        drbg: &mut drbg,
    };
    // Other sessions' tickets fill some of the store first.
    for k in 0..before {
        let other = session(node(100 + k as u16), ALPN, Aead::Aes128Gcm, [0x10 + k as u8; 32], credit);
        stores.tickets.issue_batch(&mut env, &other, 1, 3600).unwrap();
    }
    let srv = session(client, ALPN, Aead::Aes128Gcm, [0x5c; 32], credit);
    let batch = stores.tickets.issue_batch(&mut env, &srv, count, 3600).unwrap();
    assert_eq!(
        batch.entries().len(),
        if N == 0 { 0 } else { count.min(4) },
        "N={N}: a batch of {count} holds {} tickets",
        batch.entries().len()
    );
    let cli = session(server, ALPN, Aead::Aes128Gcm, [0x5c; 32], credit);
    batch
        .entries()
        .iter()
        .map(|e| {
            let mut one = TicketBatch::new();
            one.push(*e);
            let mut ct: ClientTickets<1> = ClientTickets::new();
            ct.accept_batch(&cli, &one, T0);
            let t = ct.take(&server, ALPN, T0).unwrap();
            let m = hello(t, server, ALPN, T0);
            let s = screen_first(
                &mut stores,
                &AlpnList::new(&ALPNS).unwrap(),
                AeadSet::from_bits(3).unwrap(),
                T0,
                MessageType::ResumeHello,
                &m,
            );
            s == Screen::Admit { resume: true }
        })
        .collect()
}

fn issue_inputs() -> impl Gen<Value = (u8, usize, usize)> {
    (gens::int(0u8..=3), gens::int(0usize..=4), gens::int(0usize..=9))
}

/// Every ticket of a batch that `issue_batch` returns is stored: it opens a resumption right after the batch, whatever
/// the capacity, the batch size and the other sessions' tickets already there.
#[ephyra::test(gen = issue_inputs(), tests = 300)]
fn every_ticket_a_batch_hands_out_opens(x: (u8, usize, usize)) {
    let (n, count, before) = x;
    let opens = match n {
        0 => issue_and_redeem::<1>(count, before),
        1 => issue_and_redeem::<2>(count, before),
        2 => issue_and_redeem::<3>(count, before),
        _ => issue_and_redeem::<8>(count, before),
    };
    ephyra::signature("a handed-out ticket was already evicted");
    assert!(opens.iter().all(|o| *o), "N: a batch of {count} handed out tickets that do not open: {opens:?}");
}

/// How the screened first message is built.
#[derive(Clone, Debug, ephyra::Arbitrary)]
struct ScreenCase {
    /// 0: a resume Hello; 1: a short Initial.
    #[ephyra(gen = gens::int(0u8..=1))]
    kind: u8,
    /// The ticket's lifetime and how much later the Hello arrives, in seconds.
    #[ephyra(gen = gens::int(0u32..=4))]
    lifetime_s: u32,
    #[ephyra(gen = gens::int(0u64..=6))]
    later_s: u64,
    /// The store's ticket is for the other ALPN or the other cipher than the Hello's.
    alpn_mismatch: bool,
    aead_mismatch: bool,
    /// The short Initial names a cached prekey.
    cached: bool,
    #[ephyra(gen = gens::int(0u8..=7))]
    offer_or_version: u8,
    #[ephyra(gen = gens::vec(ephyra::any::<Edit>()).len(0..=2))]
    edits: Vec<Edit>,
}

fn short_initial(hash: &[u8; 32], version: u8, offer: u8, alpn: &[u8]) -> Vec<u8> {
    let m = Initial {
        version,
        dcid: ConnId::new(b"respond0").unwrap(),
        scid: ConnId::new(b"initiat0").unwrap(),
        alpn,
        aead_offer: AeadSet::from_bits(offer).unwrap(),
        e: [9; 32],
        prekey: PrekeyField::Hash(hash),
        credit: CreditRecord::NONE,
    };
    let mut buf = vec![0u8; 2048];
    let mut w = Writer::new(&mut buf);
    m.write(&mut w).unwrap();
    w.written().to_vec()
}

/// The screen's verdict on a first message and what the responder does with the same message on the same stores right
/// after, as the endpoint runs them: a reject is the responder's only answer, a drop gets no answer from it, and an
/// admitted resumption completes.
#[ephyra::test(gen = ephyra::any::<ScreenCase>(), tests = 2000)]
fn the_screen_decides_as_the_responder_would(c: ScreenCase) {
    let p = Software;
    let mut drbg = Drbg::new(&[0x67; 32]);
    let (kp, sid) = identity(0x32);
    let server = sid.node_id();
    let credit = CreditRecord::new(1 << 20, 8, 1200);
    let mut stores: Box<Stores> = Box::default();
    let cached = [0xc1; 32];
    stores.prekeys.insert(cached, &[0x42; KEM_ENCAPS_KEY_LEN]);
    let now = T0 + c.later_s * NS;
    let m = if c.kind == 0 {
        let mut env = Env {
            provider: &p,
            now: T0,
            drbg: &mut drbg,
        };
        let srv_alpn = if c.alpn_mismatch { ALPNS[1] } else { ALPN };
        let srv_aead = if c.aead_mismatch { Aead::ChaCha20Poly1305 } else { Aead::Aes128Gcm };
        let srv = session(node(7), srv_alpn, srv_aead, [0x5c; 32], credit);
        let batch = stores.tickets.issue_batch(&mut env, &srv, 1, c.lifetime_s).unwrap();
        let cli = session(server, ALPN, Aead::Aes128Gcm, [0x5c; 32], credit);
        let mut ct: ClientTickets<1> = ClientTickets::new();
        ct.accept_batch(&cli, &batch, T0);
        hello(ct.take(&server, ALPN, T0).unwrap(), server, ALPN, T0)
    } else {
        let hash = if c.cached { cached } else { [0xd2; 32] };
        let version = if c.offer_or_version == 0 { VERSION.wrapping_add(1) } else { VERSION };
        let offer = 1 + c.offer_or_version % 3;
        short_initial(&hash, version, offer, ALPN)
    };
    let m = apply(&m, &c.edits);
    let kind = if c.kind == 0 { MessageType::ResumeHello } else { MessageType::ShortInitial };
    let alpns = AlpnList::new(&ALPNS).unwrap();
    let verdict = screen_first(&mut stores, &alpns, AeadSet::from_bits(3).unwrap(), now, kind, &m);
    let mut r = responder(sid);
    let mut env = Env {
        provider: &p,
        now,
        drbg: &mut drbg,
    };
    let result = r.handle(&mut env, &mut stores, &m);
    let _ = r.answer_soft(
        &mut env,
        &pinc_security::SoftKeys {
            signer: Some((KeyHandle(1), &kp)),
            prekeys: None,
        },
    );
    let mut sent = Vec::new();
    let mut established = None;
    for _ in 0..16 {
        match r.poll_output() {
            Some(Output::Send { data, .. }) => sent.push(data.to_vec()),
            Some(Output::Event(Event::Established(e))) => established = Some(e),
            Some(_) => {},
            None => break,
        }
    }
    match verdict {
        Screen::Reject(bytes) => {
            ephyra::signature("reject");
            assert_eq!(sent, vec![bytes.to_vec()], "the responder answered a screened reject otherwise: {result:?}");
            assert!(established.is_none(), "the responder completed a message the screen rejects");
        },
        Screen::Drop => {
            ephyra::signature(if MessageType::of(&m) == Ok(MessageType::ResumeHello) { "drop hello" } else { "drop" });
            assert!(sent.is_empty(), "the responder answered a message the screen drops ({result:?}): {sent:?}");
        },
        Screen::Admit { resume: true } => {
            ephyra::signature("admit resume");
            assert!(
                established.as_ref().is_some_and(|e| e.resumed),
                "the responder did not resume an admitted Hello: {result:?}"
            );
        },
        Screen::Admit { resume: false } => {
            ephyra::signature("admit");
            assert!(
                !sent.iter().any(|s| s.first() == Some(&3) || s.first() == Some(&9)),
                "the responder rejected a message the screen admits"
            );
        },
    }
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum ScreenOp {
    /// Cache the prekey with hash `k`.
    Insert(#[ephyra(gen = gens::int(0u8..=5))] u8),
    /// Screen a short Initial naming the prekey with hash `k` (only in the first store).
    Screen(#[ephyra(gen = gens::int(0u8..=5))] u8),
}

/// Screening short Initials keeps no state: two prekey caches fed the same inserts, one of them also screening any
/// short Initials an unauthenticated sender chose, end holding the same prekeys.
#[ephyra::test(gen = gens::vec(ephyra::any::<ScreenOp>()).len(0..=20), tests = 2000)]
fn screening_short_initials_changes_no_cached_prekey(ops: Vec<ScreenOp>) {
    let mut screened: Box<Stores> = Box::default();
    let mut plain: Box<Stores> = Box::default();
    let alpns = AlpnList::new(&ALPNS).unwrap();
    for op in &ops {
        match op {
            ScreenOp::Insert(k) => {
                screened.prekeys.insert([*k; 32], &cache_key(*k));
                plain.prekeys.insert([*k; 32], &cache_key(*k));
            },
            ScreenOp::Screen(k) => {
                let m = short_initial(&[*k; 32], VERSION, 3, ALPN);
                let _ = screen_first(
                    &mut screened,
                    &alpns,
                    AeadSet::from_bits(3).unwrap(),
                    T0,
                    MessageType::ShortInitial,
                    &m,
                );
            },
        }
    }
    let a: Vec<bool> = (0..=5u8).map(|k| screened.prekeys.get(&[k; 32]).is_some()).collect();
    let b: Vec<bool> = (0..=5u8).map(|k| plain.prekeys.get(&[k; 32]).is_some()).collect();
    assert_eq!(a, b, "screening short Initials changed which prekeys the cache holds");
}

// ---------------------------------------------------------------------------------------------------------------
// The key roll between two machines over a network that duplicates, delays and reorders.

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum RollOp {
    /// The side (true: the dialer) starts a roll.
    Start(bool),
    /// The side resends its pending request.
    Resend(bool),
    /// Deliver message `k` of the network, modulo its length, keeping a copy (a duplicate may arrive later).
    Deliver(#[ephyra(gen = gens::int(0u8..=15))] u8),
    /// Lose message `k`.
    Lose(#[ephyra(gen = gens::int(0u8..=15))] u8),
}

/// A roll of each side's keys: the Diffie-Hellman values it mixed in, in order.
struct Side {
    m: Roll,
    rolled: Vec<[u8; 32]>,
    /// Request shares this side answered with a new key.
    answered: HashMap<[u8; 32], usize>,
}

/// Each request share leads to one roll, however often and late copies of it arrive, and every roll one side makes
/// the other makes with the same Diffie-Hellman value.
#[ephyra::test(gen = gens::vec(ephyra::any::<RollOp>()).len(0..=40), tests = 5000)]
fn each_roll_request_rolls_the_keys_once_on_both_sides(ops: Vec<RollOp>) {
    let p = Software;
    let mut drbg = Drbg::new(&[0x71; 32]);
    let mut sides = [
        Side {
            m: Roll::new(false),
            rolled: Vec::new(),
            answered: HashMap::new(),
        },
        Side {
            m: Roll::new(true),
            rolled: Vec::new(),
            answered: HashMap::new(),
        },
    ];
    // (to the dialer, message)
    let mut net: Vec<(bool, Rekey)> = Vec::new();
    let mut pn = 0u64;
    for op in &ops {
        let mut env = Env {
            provider: &p,
            now: T0,
            drbg: &mut drbg,
        };
        match op {
            RollOp::Start(d) => {
                if let Ok(req) = sides[usize::from(*d)].m.start(&mut env) {
                    net.push((!d, req));
                }
            },
            RollOp::Resend(d) => {
                if let Some(req) = sides[usize::from(*d)].m.pending() {
                    net.push((!d, req));
                }
            },
            RollOp::Deliver(k) => {
                if net.is_empty() {
                    continue;
                }
                let (to, msg) = net[usize::from(*k) % net.len()];
                let s = &mut sides[usize::from(to)];
                if msg.answer {
                    if let Ok(c) = s.m.on_answer(&env, &msg) {
                        s.rolled.push(*c.dh.expose());
                    }
                } else {
                    pn += 1;
                    if let Ok(a) = s.m.on_request(&mut env, &msg, pn) {
                        if let Some(dh) = a.dh {
                            s.rolled.push(*dh.expose());
                            *s.answered.entry(msg.share).or_default() += 1;
                        }
                        net.push((!to, a.answer));
                    }
                }
            },
            RollOp::Lose(k) => {
                if !net.is_empty() {
                    let n = net.len();
                    net.remove(usize::from(*k) % n);
                }
            },
        }
        for s in &sides {
            for (share, n) in &s.answered {
                ephyra::signature("a request share answered twice");
                assert!(*n <= 1, "a request share was answered with a new key {n} times: {share:?}");
            }
        }
        let (a, d) = (&sides[0].rolled, &sides[1].rolled);
        let common = a.len().min(d.len());
        ephyra::signature("the sides rolled with different values");
        assert_eq!(a[..common], d[..common], "the two sides rolled with different values");
    }
}
