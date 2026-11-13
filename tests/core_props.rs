//! Properties of the bounded structures and pure rules: the hash table against a model, the deadline heap against a
//! sorted list, the ledger bound, the keepalive plan and the node round trips.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::collections::BTreeMap;
use std::net::SocketAddr;

use proptest::prelude::*;
use vinc_core::{
    DeadlineHeap, FIRST_RESEND, FLOOR_MAX, KeepaliveInputs, LEDGER_ENTRIES, Ledger, NodeRtt, Role, Table, standby_due,
};
use vinc_crypto::{IdentityAlg, NodeId};

#[derive(Debug, Clone)]
enum Op {
    Insert(u8, u16),
    InsertRoom(u8, u16),
    Remove(u8),
    Touch(u8),
}

fn ops() -> impl Strategy<Value = Vec<Op>> {
    prop::collection::vec(
        prop_oneof![
            (any::<u8>(), any::<u16>()).prop_map(|(k, v)| Op::Insert(k % 24, v)),
            (any::<u8>(), any::<u16>()).prop_map(|(k, v)| Op::InsertRoom(k % 24, v)),
            any::<u8>().prop_map(|k| Op::Remove(k % 24)),
            any::<u8>().prop_map(|k| Op::Touch(k % 24)),
        ],
        0..200,
    )
}

proptest! {
    #[test]
    fn the_table_matches_a_model_with_oldest_first_eviction(ops in ops(), seed in any::<u64>()) {
        const CAP: usize = 8;
        let mut t: Table<u8, u16, CAP> = Table::new(seed);
        let mut order: Vec<u8> = Vec::new(); // oldest first
        let mut model: BTreeMap<u8, u16> = BTreeMap::new();
        for op in ops {
            match op {
                Op::Insert(k, v) => {
                    let evicted = t.insert(k, v);
                    if model.insert(k, v).is_none() {
                        if order.len() == CAP {
                            let old = order.remove(0);
                            model.remove(&old);
                            prop_assert_eq!(evicted.map(|e| e.0), Some(old));
                        } else {
                            prop_assert!(evicted.is_none());
                        }
                        order.push(k);
                    } else {
                        prop_assert!(evicted.is_none());
                    }
                }
                Op::InsertRoom(k, v) => {
                    let ok = t.insert_room(k, v);
                    if let Some(slot) = model.get_mut(&k) {
                        *slot = v;
                        prop_assert!(ok);
                    } else if order.len() < CAP {
                        model.insert(k, v);
                        order.push(k);
                        prop_assert!(ok);
                    } else {
                        prop_assert!(!ok);
                    }
                }
                Op::Remove(k) => {
                    prop_assert_eq!(t.remove(&k), model.remove(&k));
                    order.retain(|x| *x != k);
                }
                Op::Touch(k) => {
                    t.touch(&k);
                    if let Some(p) = order.iter().position(|x| *x == k) {
                        order.remove(p);
                        order.push(k);
                    }
                }
            }
            prop_assert!(t.len() <= CAP);
            prop_assert_eq!(t.len(), model.len());
            prop_assert_eq!(t.iter().map(|(k, _)| *k).collect::<Vec<_>>(), order.clone());
            for (k, v) in &model {
                prop_assert_eq!(t.get(k), Some(v));
            }
        }
    }

    #[test]
    fn the_heap_always_yields_the_earliest_deadline_with_ties_to_the_lower_id(
        ops in prop::collection::vec((0usize..20, prop::option::of(0u64..50)), 0..300)
    ) {
        let mut h: DeadlineHeap<20> = DeadlineHeap::new();
        let mut model = [None::<u64>; 20];
        for (id, at) in ops {
            h.set(id, at);
            model[id] = at;
            let want = model.iter().enumerate().filter_map(|(i, t)| t.map(|t| (t, i))).min();
            prop_assert_eq!(h.peek(), want);
            prop_assert_eq!(h.len(), model.iter().flatten().count());
            prop_assert_eq!(h.deadline(id), at);
        }
    }

    #[test]
    fn an_unvalidated_address_is_never_charged_more_than_three_times_what_it_sent(
        steps in prop::collection::vec((0u8..4, prop::bool::ANY, 1u64..3000), 1..300)
    ) {
        let mut l = Ledger::new(11);
        let addr = |n: u8| -> SocketAddr { ([10, 0, 0, n], 1).into() };
        for (n, receive, bytes) in steps {
            let a = addr(n);
            if receive {
                l.on_receive(a, bytes);
            } else {
                let _ = l.allow_send(a, bytes);
            }
            for k in 0..4u8 {
                if let Some(e) = l.get(&addr(k)).filter(|e| !e.validated) {
                    prop_assert!(e.tx <= 3 * e.rx, "{e:?}");
                }
            }
            prop_assert!(l.len() <= LEDGER_ENTRIES);
        }
    }

    #[test]
    fn the_keepalive_plan_never_plans_the_past(
        role in 0u8..3, dialer in prop::bool::ANY, direct in prop::bool::ANY,
        now in 1_000u64..500_000_000_000,
        back_tx in 0u64..300_000_000_000, back_rx in 0u64..300_000_000_000, back_app in 0u64..300_000_000_000,
        quiet_for in 0u64..20_000_000_000, in_flight in prop::bool::ANY,
    ) {
        let i = KeepaliveInputs {
            role: [Role::Hub, Role::Member, Role::Other][role as usize],
            dialer, direct, now,
            last_tx: now.saturating_sub(back_tx),
            last_rx: now.saturating_sub(back_rx),
            last_app: now.saturating_sub(back_app),
            quiet_until: now + quiet_for,
            in_flight,
        };
        let p = i.plan();
        if let Some(t) = p.ping_at {
            prop_assert!(t >= now, "ping at {t} before now {now}");
            if i.quiet_until > now && !in_flight {
                prop_assert!(t >= i.quiet_until);
            }
        }
        if let Some(r) = p.review_at {
            prop_assert!(r > now);
        }
        if let Some(d) = standby_due(now, i.last_tx, i.last_app) {
            prop_assert!(d >= now && d < i.last_app + 20_000_000_000);
        }
    }

    #[test]
    fn node_round_trips_stay_in_bounds(
        steps in prop::collection::vec((0u8..6, prop_oneof![0u64..2_000_000_000, any::<u64>()], 0u8..3), 0..200)
    ) {
        let mut r = NodeRtt::new(5);
        let node = |b: u8| NodeId { alg: IdentityAlg::Ed25519, bytes: [b; 32] };
        let mut floor_seen = 0;
        for (peer, rtt, what) in steps {
            match what {
                0 => r.note_handshake(node(peer), rtt),
                1 => r.note_peak(rtt),
                _ => r.note_timeout(),
            }
            prop_assert!(r.hs_floor() <= FLOOR_MAX);
            floor_seen = floor_seen.max(r.hs_floor());
            let first = r.first_resend(&node(peer));
            prop_assert!(first >= FIRST_RESEND && first >= r.hs_floor());
            // The connection's own formula max(500 ms, 2 x r) reproduces the node's first resend.
            if let Some(rem) = r.remembered_for(&node(peer)) {
                prop_assert_eq!(FIRST_RESEND.max(rem.saturating_mul(2)), first);
            } else {
                prop_assert_eq!(first, FIRST_RESEND);
            }
            prop_assert!(r.thin_node() == (r.tgr().max(r.lrtt()) >= 250_000_000));
        }
        let _ = floor_seen;
    }
}
