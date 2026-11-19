//! Tests of the charged store, custody and the custody book.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::assert_is_empty,
    clippy::similar_names,
    clippy::trivially_copy_pass_by_ref,
    clippy::struct_field_names,
    clippy::cast_lossless,
    clippy::range_plus_one,
    clippy::many_single_char_names,
    clippy::items_after_statements,
    clippy::needless_pass_by_value
)]

mod dtn_common;

use dtn_common::{keypair, make, plan, recipient};
use pinc_crypto::IdentityAlg;
use pinc_dtn::custody::{CustodyAck, CustodyBook, CustodyError, Incoming};
use pinc_dtn::head::BundleId;
use pinc_dtn::hlc::Hlc;
use pinc_dtn::store::{Class, Key, Ledger, Space, StoreError};
use proptest::prelude::*;

fn key(n: u8) -> Key {
    Key {
        space: Space::DTN,
        id: [n; 32],
    }
}

#[test]
fn expired_then_transit_oldest_first_and_never_live_custody() {
    let mut l = Ledger::<8>::new(100);
    l.admit(key(1), 30, Class::Custody, 1_000, 0, |_| {}).unwrap();
    l.admit(key(2), 30, Class::Transit, 1_000, 0, |_| {}).unwrap();
    l.admit(key(3), 30, Class::Transit, 50, 0, |_| {}).unwrap();
    assert_eq!(l.used(), 90);
    // 20 bytes needed, 10 free: at time 60 the expired transit (3) goes first and that is enough.
    let mut gone = vec![];
    l.admit(key(4), 30, Class::Transit, 1_000, 60, |e| gone.push(e.key))
        .unwrap();
    assert_eq!(gone, vec![key(3)]);
    // Now 90 used (1, 2, 4). 40 more bytes: evict transit oldest first: 2, then 4 is needed? 90 + 40 - 30 = 100.
    let mut gone = vec![];
    l.admit(key(5), 40, Class::Transit, 1_000, 60, |e| gone.push(e.key))
        .unwrap();
    assert_eq!(gone, vec![key(2)]);
    assert!(l.contains(&key(1)) && l.contains(&key(4)) && l.contains(&key(5)));
    // Custody that would need to evict live custody is refused, and nothing live moves.
    assert_eq!(
        l.admit(key(6), 95, Class::Custody, 1_000, 60, |_| {}).err(),
        Some(StoreError::CustodyRefused)
    );
    assert_eq!(
        l.admit(key(6), 95, Class::Transit, 1_000, 60, |_| {}).err(),
        Some(StoreError::Full)
    );
    assert!(l.contains(&key(4)) && l.contains(&key(5)) && l.used() == 100);
    // Custody that fits by evicting transit succeeds.
    l.admit(key(7), 70, Class::Custody, 1_000, 60, |_| {}).unwrap();
    assert!(l.contains(&key(1)) && l.contains(&key(7)) && !l.contains(&key(4)) && !l.contains(&key(5)));
    // After expiry custody is evictable like anything else.
    l.admit(key(8), 100, Class::Custody, 5_000, 2_000, |_| {}).unwrap();
    assert_eq!(l.len(), 1);
}

#[test]
fn duplicates_unknowns_and_slot_exhaustion() {
    let mut l = Ledger::<2>::new(1_000);
    l.admit(key(1), 1, Class::Custody, 100, 0, |_| {}).unwrap();
    assert_eq!(
        l.admit(key(1), 1, Class::Transit, 100, 0, |_| {}).err(),
        Some(StoreError::Duplicate)
    );
    l.admit(key(2), 1, Class::Transit, 100, 0, |_| {}).unwrap();
    // Slots are the scarce resource: a third transit evicts the older transit.
    let mut gone = vec![];
    l.admit(key(3), 1, Class::Transit, 100, 0, |e| gone.push(e.key))
        .unwrap();
    assert_eq!(gone, vec![key(2)]);
    // Two custody items fill the table; a third custody is refused, nothing evicted.
    l.release(&key(3)).unwrap();
    l.admit(key(4), 1, Class::Custody, 100, 0, |_| {}).unwrap();
    assert_eq!(
        l.admit(key(5), 1, Class::Custody, 100, 0, |_| {}).err(),
        Some(StoreError::CustodyRefused)
    );
    assert_eq!(l.reclass(&key(9), Class::Transit).err(), Some(StoreError::Unknown));
    l.reclass(&key(1), Class::Transit).unwrap();
    l.admit(key(5), 1, Class::Custody, 100, 0, |_| {}).unwrap();
    assert!(!l.contains(&key(1)));
    assert!(l.release(&key(1)).is_none());
}

#[test]
fn an_expired_unswept_key_is_admitted_fresh_and_an_expired_item_is_refused() {
    let mut l = Ledger::<4>::new(100);
    l.admit(key(1), 10, Class::Transit, 50, 0, |_| {}).unwrap();
    // Key 1 expired at 50 but was not swept: the admission sweeps it first and takes the key fresh.
    let mut gone = vec![];
    l.admit(key(1), 10, Class::Transit, 500, 60, |e| gone.push(e.key))
        .unwrap();
    assert_eq!(gone, vec![key(1)]);
    assert_eq!(l.get(&key(1)).map(|e| e.expires), Some(500));
    // An item already expired at admission is refused, not admitted and swept later.
    assert_eq!(
        l.admit(key(2), 10, Class::Transit, 60, 60, |_| {}).err(),
        Some(StoreError::Expired)
    );
    assert!(!l.contains(&key(2)));
    assert_eq!(l.used(), 10);
}

#[test]
fn spaces_share_one_budget() {
    let mut l = Ledger::<4>::new(10);
    let mail = Key {
        space: Space::MAILBOX,
        id: [1; 32],
    };
    let dtn = Key {
        space: Space::DTN,
        id: [1; 32],
    };
    l.admit(mail, 6, Class::Custody, 100, 0, |_| {}).unwrap();
    assert_eq!(
        l.admit(dtn, 6, Class::Custody, 100, 0, |_| {}).err(),
        Some(StoreError::CustodyRefused)
    );
    l.admit(dtn, 4, Class::Transit, 100, 0, |_| {}).unwrap();
    assert_eq!((l.used(), l.budget()), (10, 10));
}

#[derive(Debug, Clone)]
enum Op {
    Admit {
        id: u8,
        bytes: u64,
        custody: bool,
        life: u64,
    },
    Release {
        id: u8,
    },
    Advance {
        dt: u64,
    },
    Reclass {
        id: u8,
        custody: bool,
    },
}

fn op() -> impl Strategy<Value = Op> {
    prop_oneof![
        4 => (0u8..12, 1u64..60, any::<bool>(), 1u64..400)
            .prop_map(|(id, bytes, custody, life)| Op::Admit { id, bytes, custody, life }),
        1 => (0u8..12).prop_map(|id| Op::Release { id }),
        2 => (0u64..120).prop_map(|dt| Op::Advance { dt }),
        1 => (0u8..12, any::<bool>()).prop_map(|(id, custody)| Op::Reclass { id, custody }),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// Whatever the operations, custody is never evicted before it expires, the budget holds, and the ledger
    /// agrees with an independent model.
    #[test]
    fn custody_is_never_evicted_before_expiry(ops in proptest::collection::vec(op(), 1..120)) {
        const BUDGET: u64 = 200;
        let mut ledger = Ledger::<6>::new(BUDGET);
        // Model: id -> (custody, expires), only items the ledger accepted and nobody released.
        let mut model: std::collections::BTreeMap<u8, (bool, u64)> = std::collections::BTreeMap::new();
        let mut now = 0u64;
        for o in ops {
            match o {
                Op::Admit { id, bytes, custody, life } => {
                    let class = if custody { Class::Custody } else { Class::Transit };
                    let mut evicted = vec![];
                    let r = ledger.admit(key(id), bytes, class, now + life, now, |e| evicted.push(*e));
                    for e in &evicted {
                        let (was_custody, expires) = model.remove(&e.key.id[0]).unwrap();
                        // The eviction rule: custody leaves only once expired.
                        prop_assert!(!was_custody || expires <= now, "live custody evicted");
                        prop_assert_eq!(e.class == Class::Custody, was_custody);
                    }
                    if r.is_ok() {
                        model.insert(id, (custody, now + life));
                    }
                }
                Op::Release { id } => {
                    prop_assert_eq!(ledger.release(&key(id)).is_some(), model.remove(&id).is_some());
                }
                Op::Advance { dt } => {
                    now += dt;
                    let mut evicted = vec![];
                    ledger.expire(now, |e| evicted.push(*e));
                    for e in evicted {
                        let (_, expires) = model.remove(&e.key.id[0]).unwrap();
                        prop_assert!(expires <= now);
                    }
                }
                Op::Reclass { id, custody } => {
                    let class = if custody { Class::Custody } else { Class::Transit };
                    let r = ledger.reclass(&key(id), class);
                    prop_assert_eq!(r.is_ok(), model.contains_key(&id));
                    if let Some(m) = model.get_mut(&id) {
                        m.0 = custody;
                    }
                }
            }
            // Invariants after every step.
            prop_assert!(ledger.used() <= BUDGET);
            prop_assert_eq!(ledger.used(), ledger.iter().map(|e| e.bytes).sum::<u64>());
            for (id, (custody, expires)) in &model {
                let present = ledger.contains(&key(*id));
                if *custody && *expires > now {
                    prop_assert!(present, "live custody {id} vanished");
                }
            }
            // Everything the ledger holds is in the model, except items that expired but were not yet swept.
            for e in ledger.iter() {
                prop_assert!(model.contains_key(&e.key.id[0]));
            }
        }
    }
}

fn node(seed: u64) -> (pinc_crypto::Keypair, pinc_crypto::NodeId) {
    let k = keypair(IdentityAlg::Ed25519, seed);
    let id = k.node_id();
    (k, id)
}

#[test]
fn custody_ack_signs_verifies_and_round_trips_for_every_algorithm() {
    let (_, prev) = node(1);
    for (i, alg) in dtn_common::ALGS.into_iter().enumerate() {
        let custodian = keypair(alg, 40 + i as u64);
        let ack = CustodyAck::sign(BundleId([9; 32]), prev, 3, Hlc::new(5, 1), &custodian).unwrap();
        ack.verify().unwrap();
        let mut buf = vec![0; ack.encoded_len() + 1];
        let n = ack.encode(&mut buf).unwrap();
        assert_eq!(n, ack.encoded_len());
        let back = CustodyAck::decode(&buf[..n]).unwrap();
        assert_eq!(back, ack);
        back.verify().unwrap();
        assert!(CustodyAck::decode(&buf[..n + 1]).is_err());
        for at in (0..n).step_by(97).chain([n - 1]) {
            let mut bad = buf[..n].to_vec();
            bad[at] ^= 1;
            assert!(
                !CustodyAck::decode(&bad).is_ok_and(|a| a.verify().is_ok()),
                "{alg:?} byte {at}"
            );
        }
    }
}

#[test]
fn custody_hand_over_relieves_the_previous_custodian() {
    let (_, a) = node(1);
    let (b_key, b) = node(2);
    let (c_key, c) = node(3);
    let id = BundleId([7; 32]);
    let mut la = Ledger::<4>::new(100);
    let mut lb = Ledger::<4>::new(100);
    let (mut ba, mut bb) = (CustodyBook::<4>::new(), CustodyBook::<4>::new());

    // A holds custody from the source; offers it to B.
    ba.accept(
        &mut la,
        Incoming {
            bundle: id,
            bytes: 60,
            expires: 1_000,
            previous: c,
            offer: 0,
        },
        0,
        |_| {},
    )
    .unwrap();
    let offer_id = ba.offer(&id, b).unwrap();
    assert_eq!(ba.owed_to(&id), Some(c));
    // B accepts and owes A an ack.
    let due = bb
        .accept(
            &mut lb,
            Incoming {
                bundle: id,
                bytes: 60,
                expires: 1_000,
                previous: a,
                offer: offer_id,
            },
            0,
            |_| {},
        )
        .unwrap();
    assert_eq!((due.previous, due.offer), (a, offer_id));
    let ack = due.sign(Hlc::new(1, 0), &b_key).unwrap();

    // An ack from the wrong node, or one that does not verify, does not relieve A.
    let stray = CustodyAck::sign(id, a, offer_id, Hlc::new(1, 0), &c_key).unwrap();
    assert_eq!(ba.on_ack(&mut la, &stray).err(), Some(CustodyError::NotOffered));
    let unknown = CustodyAck::sign(BundleId([1; 32]), a, offer_id, Hlc::new(1, 0), &b_key).unwrap();
    assert_eq!(ba.on_ack(&mut la, &unknown).err(), Some(CustodyError::Unknown));
    let mut enc = vec![0; ack.encoded_len()];
    ack.encode(&mut enc).unwrap();
    *enc.last_mut().unwrap() ^= 1;
    let forged = CustodyAck::decode(&enc).unwrap();
    assert!(matches!(ba.on_ack(&mut la, &forged), Err(CustodyError::Ack(_))));
    assert_eq!(
        la.get(&Key {
            space: Space::DTN,
            id: id.0
        })
        .unwrap()
        .class,
        Class::Custody
    );

    ba.on_ack(&mut la, &ack).unwrap();
    assert!(!ba.holds(&id));
    let kept = la
        .get(&Key {
            space: Space::DTN,
            id: id.0,
        })
        .unwrap();
    assert_eq!(
        kept.class,
        Class::Transit,
        "relieved custodian keeps the bytes as evictable transit"
    );
    // B keeps custody until delivery.
    assert!(bb.holds(&id));
    bb.delivered(&mut lb, &id).unwrap();
    assert!(lb.is_empty() && bb.is_empty());
    assert_eq!(bb.delivered(&mut lb, &id).err(), Some(CustodyError::Unknown));
}

#[test]
fn custody_is_refused_when_the_store_cannot_keep_it() {
    let (_, a) = node(1);
    let mut l = Ledger::<4>::new(100);
    let mut book = CustodyBook::<4>::new();
    let one = |n: u8, bytes| Incoming {
        bundle: BundleId([n; 32]),
        bytes,
        expires: 1_000,
        previous: a,
        offer: 0,
    };
    book.accept(&mut l, one(1, 80), 0, |_| {}).unwrap();
    assert_eq!(
        book.accept(&mut l, one(2, 30), 0, |_| {}).err(),
        Some(CustodyError::Store(StoreError::CustodyRefused))
    );
    assert!(!book.holds(&BundleId([2; 32])) && book.len() == 1);
    // The book is bounded too.
    let mut small = CustodyBook::<1>::new();
    let mut l2 = Ledger::<4>::new(100);
    small.accept(&mut l2, one(1, 1), 0, |_| {}).unwrap();
    assert_eq!(
        small.accept(&mut l2, one(2, 1), 0, |_| {}).err(),
        Some(CustodyError::Capacity)
    );
    // Expiry drops the record with the item.
    small.expire(&mut l2, 1_000, |_| {});
    assert!(small.is_empty() && l2.is_empty());
}

#[test]
fn custody_of_a_real_bundle_is_charged_at_its_sealed_size() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let s = make(&sender, &to, plan(2, 1, 0), &dtn_common::bytes(1, 3_000), 3);
    let head = s.signed.head();
    let layout = head.layout().unwrap();
    let mut l = Ledger::<4>::new(layout.total_len());
    let mut book = CustodyBook::<4>::new();
    let inc = Incoming {
        bundle: head.id,
        bytes: layout.total_len(),
        expires: head.expires_at(),
        previous: head.source,
        offer: 0,
    };
    book.accept(&mut l, inc, 0, |_| {}).unwrap();
    assert_eq!(l.used(), layout.total_len());
}

#[test]
fn a_stale_ack_cannot_relieve_a_node_that_is_the_custodian_again() {
    let (a_key, a) = node(1);
    let (b_key, b) = node(2);
    let id = BundleId([7; 32]);
    let (mut la, mut lb) = (Ledger::<4>::new(100), Ledger::<4>::new(100));
    let (mut ba, mut bb) = (CustodyBook::<4>::new(), CustodyBook::<4>::new());
    let inc = |previous, offer| Incoming {
        bundle: id,
        bytes: 10,
        expires: 1_000,
        previous,
        offer,
    };
    // A holds custody, offers it to B (offer 0); B accepts and its ack is delayed.
    ba.accept(&mut la, inc(b, 0), 0, |_| {}).unwrap();
    let first = ba.offer(&id, b).unwrap();
    let late = bb
        .accept(&mut lb, inc(a, first), 0, |_| {})
        .unwrap()
        .sign(Hlc::new(1, 0), &b_key)
        .unwrap();
    // B hands custody back; A holds it already, answers, and is the custodian again.
    let back = bb.offer(&id, a).unwrap();
    let due = ba.accept(&mut la, inc(b, back), 1, |_| {}).unwrap();
    assert_eq!((due.previous, due.offer), (b, back));
    bb.on_ack(&mut lb, &due.sign(Hlc::new(2, 0), &a_key).unwrap()).unwrap();
    // The delayed ack of the first offer arrives: it must not relieve A.
    assert_eq!(ba.on_ack(&mut la, &late).err(), Some(CustodyError::NotOffered));
    assert!(ba.holds(&id));
    // A new offer gets a new id; the old ack stays stale, the matching one relieves.
    let second = ba.offer(&id, b).unwrap();
    assert_ne!(first, second);
    assert_eq!(ba.on_ack(&mut la, &late).err(), Some(CustodyError::NotOffered));
    let fresh = bb
        .accept(&mut lb, inc(a, second), 2, |_| {})
        .unwrap()
        .sign(Hlc::new(3, 0), &b_key)
        .unwrap();
    ba.on_ack(&mut la, &fresh).unwrap();
    assert!(!ba.holds(&id));
}

#[test]
fn the_ack_offer_id_is_signed_and_part_of_the_encoding() {
    let (_, prev) = node(1);
    let custodian = keypair(IdentityAlg::Ed25519, 40);
    let ack = CustodyAck::sign(BundleId([9; 32]), prev, 5, Hlc::new(5, 1), &custodian).unwrap();
    let mut buf = vec![0; ack.encoded_len()];
    ack.encode(&mut buf).unwrap();
    let mut other = CustodyAck::decode(&buf).unwrap();
    assert_eq!(other.offer, 5);
    // The id sits before the 12 bytes of the time: changing it breaks the signature.
    let at = 32 + 33 + 33;
    buf[at + 7] ^= 1;
    other = CustodyAck::decode(&buf).unwrap();
    assert_eq!(other.offer, 4);
    assert!(other.verify().is_err());
}

#[test]
fn an_ack_for_a_dropped_item_reports_the_store_unknown_and_an_expired_bundle_is_not_accepted() {
    let (_, a) = node(1);
    let (b_key, b) = node(2);
    let id = BundleId([7; 32]);
    let mut la = Ledger::<4>::new(100);
    let mut ba = CustodyBook::<4>::new();
    let inc = |expires| Incoming {
        bundle: id,
        bytes: 10,
        expires,
        previous: b,
        offer: 0,
    };
    // Already expired at acceptance: refused with the store's verdict, nothing is kept.
    assert_eq!(
        ba.accept(&mut la, inc(5), 5, |_| {}).err(),
        Some(CustodyError::Store(StoreError::Expired))
    );
    assert!(ba.is_empty() && la.is_empty());
    // accept answers the previous custodian of the incoming offer, even for a bundle already held.
    let due = ba.accept(&mut la, inc(1_000), 0, |_| {}).unwrap();
    assert_eq!(due.previous, b);
    let again = ba
        .accept(
            &mut la,
            Incoming {
                previous: a,
                ..inc(1_000)
            },
            1,
            |_| {},
        )
        .unwrap();
    assert_eq!(again.previous, a);
    assert_eq!(ba.owed_to(&id), Some(b));
    // The ledger dropped the item behind the book's back: the relieving ack reports the store's Unknown.
    let offer = ba.offer(&id, b).unwrap();
    la.release(&id.store_key());
    let ack = CustodyAck::sign(id, a, offer, Hlc::new(1, 0), &b_key).unwrap();
    assert_eq!(
        ba.on_ack(&mut la, &ack).err(),
        Some(CustodyError::Store(StoreError::Unknown))
    );
    assert!(ba.is_empty());
}

#[test]
fn the_next_expiry_is_the_earliest_of_what_is_kept() {
    let mut l = Ledger::<8>::new(100);
    assert_eq!(l.next_expiry(), None);
    l.admit(key(1), 10, Class::Transit, 900, 0, |_| {}).unwrap();
    l.admit(key(2), 10, Class::Custody, 400, 0, |_| {}).unwrap();
    assert_eq!(l.next_expiry(), Some(400));
    l.expire(400, |_| {});
    assert_eq!(l.next_expiry(), Some(900));
}
