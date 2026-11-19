//! The bounded node tables against a plain map.
#![allow(
    clippy::many_single_char_names,
    clippy::assert_is_empty,
    clippy::decimal_bitwise_operands,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::cast_lossless,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod connect_common;

use std::collections::BTreeMap;

use connect_common::nid;
use pinc_connect::relay::table::{Cache, Table};
use proptest::prelude::*;

#[derive(Debug, Clone)]
enum Op {
    Insert(u8, u32),
    Remove(u8),
    Get(u8),
    RetainOdd,
}

fn ops() -> impl Strategy<Value = Vec<Op>> {
    proptest::collection::vec(
        prop_oneof![
            (0u8..24, any::<u32>()).prop_map(|(k, v)| Op::Insert(k, v)),
            (0u8..24).prop_map(Op::Remove),
            (0u8..24).prop_map(Op::Get),
            Just(Op::RetainOdd),
        ],
        1..300,
    )
}

fn model_check<const N: usize>(ops: &[Op], seed: u64) -> Result<(), TestCaseError> {
    let mut t: Table<u32, N> = Table::new(seed);
    let mut m: BTreeMap<u8, u32> = BTreeMap::new();
    for op in ops {
        match *op {
            Op::Insert(k, v) => {
                let r = t.insert(nid(k), v);
                if m.contains_key(&k) || m.len() < N {
                    prop_assert_eq!(r, Ok(m.insert(k, v)));
                } else {
                    prop_assert_eq!(r, Err(v));
                }
            }
            Op::Remove(k) => prop_assert_eq!(t.remove(&nid(k)), m.remove(&k)),
            Op::Get(k) => prop_assert_eq!(t.get(&nid(k)).copied(), m.get(&k).copied()),
            Op::RetainOdd => {
                t.retain(|_, v| *v % 2 == 1);
                m.retain(|_, v| *v % 2 == 1);
            }
        }
        prop_assert_eq!(t.len(), m.len());
        prop_assert!(t.len() <= N);
        // everything the model holds is reachable, so no probe chain was broken by a deletion
        for (k, v) in &m {
            prop_assert_eq!(t.get(&nid(*k)), Some(v));
        }
        prop_assert_eq!(t.iter().count(), m.len());
    }
    Ok(())
}

proptest! {
    #[test]
    fn a_table_matches_a_map_at_several_capacities(ops in ops(), seed in any::<u64>()) {
        model_check::<1>(&ops, seed)?;
        model_check::<2>(&ops, seed)?;
        model_check::<7>(&ops, seed)?;
        model_check::<16>(&ops, seed)?;
        model_check::<32>(&ops, seed)?;
    }

    #[test]
    fn a_cache_returns_what_it_last_stored_or_nothing(puts in proptest::collection::vec((0u8..40, any::<u32>()), 1..100), seed in any::<u64>()) {
        let mut c: Cache<u32, 8> = Cache::new(seed);
        let mut last: BTreeMap<u8, u32> = BTreeMap::new();
        for (k, v) in puts {
            c.put(nid(k), v);
            last.insert(k, v);
        }
        let hits = (0..40u8).filter(|k| c.get(&nid(*k)).is_some()).count();
        prop_assert!(hits <= 8);
        for k in 0..40u8 {
            if let Some(v) = c.get(&nid(k)) {
                prop_assert_eq!(Some(v), last.get(&k));
            }
        }
    }
}

#[test]
fn a_full_table_gives_the_value_back_and_keeps_serving_what_it_has() {
    let mut t: Table<String, 4> = Table::new(9);
    for k in 0..4u8 {
        assert_eq!(t.insert(nid(k), format!("v{k}")), Ok(None));
    }
    assert!(t.is_full());
    assert_eq!(t.insert(nid(9), "x".into()), Err("x".to_string()));
    assert_eq!(t.insert(nid(2), "new".into()), Ok(Some("v2".into())));
    assert_eq!(t.get(&nid(2)).map(String::as_str), Some("new"));
    assert!(t.get(&nid(9)).is_none());
    assert_eq!(t.remove(&nid(1)).as_deref(), Some("v1"));
    assert_eq!(t.insert(nid(9), "x".into()), Ok(None));
}
