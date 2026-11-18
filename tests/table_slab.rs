//! The sorted slab against a `BTreeMap`: the same long runs of inserts, replacements, removals, bulk removals, lookups,
//! "first at or after", cursor walks that remove and re-insert during the walk, and full-table refusals leave the same
//! contents and the same walk order after every step, for a capacity on each side of the 2-byte and 4-byte index
//! boundary, over a block with spare bytes, and the edges of the index width, of key lengths and of capacity 0.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names
)]

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Bound::{Excluded, Unbounded};

use proptest::prelude::*;
use vinc_table::{Error, SortedSlab, Storage};

/// The least capacity that takes the 4-byte index.
const WIDE: usize = 65_536;

fn kb(k: u64) -> [u8; 8] {
    k.to_be_bytes()
}

fn vb(v: u32) -> [u8; 4] {
    v.to_le_bytes()
}

fn ent(e: Option<(&[u8], &[u8])>) -> Option<(u64, u32)> {
    e.map(|(k, v)| {
        (
            u64::from_be_bytes(k.try_into().unwrap()),
            u32::from_le_bytes(v.try_into().unwrap()),
        )
    })
}

fn mem(n: usize, owned: bool) -> Storage {
    if owned {
        Storage::zeroed(n).unwrap()
    } else {
        // A dirty block: a table must not rely on zeroed bytes.
        Storage::from_static(Box::leak(vec![0xa5u8; n].into_boxed_slice()))
    }
}

/// A slab of 8-byte keys and 4-byte values over a block `spare` bytes longer than it needs.
fn make(cap: usize, spare: usize, owned: bool) -> SortedSlab {
    SortedSlab::new(mem(SortedSlab::bytes(cap, 8, 4) + spare, owned), cap, 8, 4).unwrap()
}

fn same(s: &SortedSlab, m: &BTreeMap<u64, u32>, at: &str) {
    assert_eq!(s.len(), m.len(), "len {at}");
    let got: Vec<_> = s.iter().map(|e| ent(Some(e)).unwrap()).collect();
    let want: Vec<_> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(got, want, "contents or walk order {at}");
    for p in 0..=want.len() {
        assert_eq!(ent(s.entry(p)), want.get(p).copied(), "entry {p} {at}");
    }
    assert_eq!(ent(s.first()), want.first().copied(), "first {at}");
    assert_eq!(ent(s.last()), want.last().copied(), "last {at}");
    assert_eq!(s.is_full(), m.len() == s.capacity(), "full {at}");
}

fn walk(slab: &mut SortedSlab, model: &mut BTreeMap<u64, u32>, salt: u32, domain: u64) {
    let mut cur: Option<u64> = None;
    for step in 0..300 {
        let got = match cur {
            None => slab.first_at_or_after(&[]),
            Some(k) => slab.next_after(&kb(k)),
        };
        let want = match cur {
            None => model.iter().next(),
            Some(k) => model.range((Excluded(k), Unbounded)).next(),
        }
        .map(|(&k, &v)| (k, v));
        assert_eq!(ent(got), want, "cursor step {step}");
        let Some((k, v)) = want else { return };
        match (k as u32 ^ salt ^ step) % 6 {
            0 => {
                assert!(slab.remove(&kb(k)));
                model.remove(&k);
            }
            1 => {
                assert!(slab.remove(&kb(k)));
                model.remove(&k);
                assert_eq!(slab.insert(&kb(k), &vb(v + 1)), Ok(false));
                model.insert(k, v + 1);
            }
            2 => {
                let n = (k + 1 + u64::from(salt % 3)) % domain;
                let r = slab.insert(&kb(n), &vb(step));
                if model.contains_key(&n) {
                    assert_eq!(r, Ok(true));
                    model.insert(n, step);
                } else if model.len() == slab.capacity() {
                    assert_eq!(r, Err(Error::Full));
                } else {
                    assert_eq!(r, Ok(false));
                    model.insert(n, step);
                }
            }
            3 => {
                // Ahead of the cursor, held or not.
                let n = (k + 2) % domain;
                assert_eq!(slab.remove(&kb(n)), model.remove(&n).is_some());
            }
            _ => {}
        }
        same(slab, model, &format!("after walk step {step}"));
        cur = Some(k);
    }
}

/// Removes by `salt` on both sides, adding one to every value kept, and checks the visit order and the count.
fn retain_both(s: &mut SortedSlab, m: &mut BTreeMap<u64, u32>, salt: u32) {
    let want_visits: Vec<u64> = m.keys().copied().collect();
    let before = m.len();
    let mut seen = Vec::new();
    let removed = s.retain(|k, v| {
        let key = u64::from_be_bytes(k.try_into().unwrap());
        seen.push(key);
        let keep = !(key as u32 ^ salt).is_multiple_of(3);
        if keep {
            let n = u32::from_le_bytes((&*v).try_into().unwrap()).wrapping_add(1);
            v.copy_from_slice(&n.to_le_bytes());
        }
        keep
    });
    m.retain(|&k, v| {
        let keep = !(k as u32 ^ salt).is_multiple_of(3);
        if keep {
            *v = v.wrapping_add(1);
        }
        keep
    });
    assert_eq!(seen, want_visits, "retain visits every record once, in key order");
    assert_eq!(removed, before - m.len(), "retain count");
}

fn run_on(slab: &mut SortedSlab, model: &mut BTreeMap<u64, u32>, ops: &[(u8, u16, u16)], cap: usize, domain: u64) {
    same(slab, model, "start");
    for (i, &(op, k, v)) in ops.iter().enumerate() {
        let k = u64::from(k) % domain;
        let v = u32::from(v);
        let at = format!("op {i} ({op} {k} {v})");
        match op % 7 {
            0 | 1 => {
                let r = slab.insert(&kb(k), &vb(v));
                if model.contains_key(&k) {
                    assert_eq!(r, Ok(true), "{at}");
                    model.insert(k, v);
                } else if model.len() == cap {
                    assert_eq!(r, Err(Error::Full), "{at}");
                } else {
                    assert_eq!(r, Ok(false), "{at}");
                    model.insert(k, v);
                }
            }
            2 => assert_eq!(slab.remove(&kb(k)), model.remove(&k).is_some(), "{at}"),
            3 => {
                assert_eq!(
                    ent(slab.first_at_or_after(&kb(k))),
                    model.range(k..).next().map(|(&a, &b)| (a, b)),
                    "{at}"
                );
                assert_eq!(
                    ent(slab.next_after(&kb(k))),
                    model.range((Excluded(k), Unbounded)).next().map(|(&a, &b)| (a, b)),
                    "{at}"
                );
                assert_eq!(
                    slab.get(&kb(k)).map(|b| u32::from_le_bytes(b.try_into().unwrap())),
                    model.get(&k).copied(),
                    "{at}"
                );
                assert_eq!(slab.contains(&kb(k)), model.contains_key(&k), "{at}");
            }
            4 => {
                if let Some(b) = slab.get_mut(&kb(k)) {
                    b.copy_from_slice(&vb(v));
                    *model.get_mut(&k).unwrap() = v;
                } else {
                    assert!(!model.contains_key(&k), "{at}");
                }
            }
            5 => walk(slab, model, v, domain),
            _ => retain_both(slab, model, v),
        }
        same(slab, model, &at);
    }
}

fn run(ops: &[(u8, u16, u16)], cap: usize, domain: u64, spare: usize, owned: bool) {
    run_on(&mut make(cap, spare, owned), &mut BTreeMap::new(), ops, cap, domain);
}

fn xorshift(seed: u64) -> impl FnMut() -> u64 {
    let mut x = seed;
    move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    }
}

fn random_ops(next: &mut impl FnMut() -> u64, n: usize) -> Vec<(u8, u16, u16)> {
    (0..n).map(|_| (next() as u8, next() as u16, next() as u16)).collect()
}

#[test]
fn empty_one_full_and_the_ends() {
    the_ends_at(4);
}

#[test]
fn empty_one_full_and_the_ends_at_the_4_byte_width() {
    the_ends_at(WIDE);
}

fn the_ends_at(cap: usize) {
    let mut s = make(cap, 0, true);
    let mut m = BTreeMap::new();
    same(&s, &m, "empty");
    assert!(s.get(&kb(1)).is_none() && s.first_at_or_after(&kb(0)).is_none() && s.next_after(&kb(0)).is_none());
    assert!(!s.remove(&kb(1)));
    s.insert(&kb(5), &vb(50)).unwrap();
    m.insert(5, 50);
    same(&s, &m, "one");
    assert!(s.remove(&kb(5)));
    m.remove(&5);
    same(&s, &m, "one removed");
    for k in [30u64, 10, 40, 20].into_iter().chain((100..).take(cap - 4)) {
        assert_eq!(s.insert(&kb(k), &vb(k as u32)), Ok(false));
        m.insert(k, k as u32);
    }
    same(&s, &m, "full");
    assert_eq!(s.insert(&kb(25), &vb(1)), Err(Error::Full));
    assert_eq!(s.insert(&kb(25), &[0; 3]), Err(Error::Length));
    assert_eq!(s.insert(&kb(30), &vb(99)), Ok(true), "a held key is replaced when full");
    m.insert(30, 99);
    same(&s, &m, "full replaced");
    let (&last, _) = m.last_key_value().unwrap();
    assert!(s.remove(&kb(last)), "remove the last in key order");
    m.remove(&last);
    same(&s, &m, "last removed");
    assert!(s.remove(&kb(10)), "remove the first in key order");
    m.remove(&10);
    same(&s, &m, "first removed");
    assert_eq!(s.insert(&kb(25), &vb(2)), Ok(false));
    m.insert(25, 2);
    same(&s, &m, "refilled");
    s.clear();
    assert!(s.is_empty() && s.iter().next().is_none());
}

#[test]
fn a_key_of_the_wrong_length_is_refused_and_changes_nothing() {
    let mut s = make(4, 0, true);
    s.insert(&kb(5), &vb(50)).unwrap();
    let m = BTreeMap::from([(5u64, 50u32)]);
    assert_eq!(s.insert(&kb(1)[..7], &vb(1)), Err(Error::Length));
    assert_eq!(s.insert(&[0; 9], &vb(1)), Err(Error::Length));
    same(&s, &m, "after the refusals");
    let short = &kb(5)[..7];
    assert!(s.get(short).is_none() && s.get_mut(short).is_none() && !s.contains(short));
    assert!(!s.remove(short));
    // Queries order a key of another length bytewise: the 7-byte prefix sorts before the 8-byte key.
    assert_eq!(ent(s.first_at_or_after(short)), Some((5, 50)));
    assert_eq!(ent(s.next_after(short)), Some((5, 50)));
    same(&s, &m, "after the queries");
}

#[test]
fn capacity_zero_holds_nothing() {
    for owned in [true, false] {
        let mut s = SortedSlab::new(mem(0, owned), 0, 8, 4).unwrap();
        assert!(s.is_full() && s.is_empty() && s.capacity() == 0);
        assert_eq!(s.insert(&kb(1), &vb(1)), Err(Error::Full));
        assert!(!s.remove(&kb(1)));
        assert_eq!(s.retain(|_, _| true), 0);
        assert!(s.first().is_none() && s.last().is_none() && s.entry(0).is_none());
        assert!(s.first_at_or_after(&[]).is_none() && s.next_after(&[]).is_none());
        assert!(s.iter().next().is_none());
    }
}

#[test]
fn refuses_a_small_block_and_too_many_records() {
    let wide = SortedSlab::bytes(WIDE, 8, 4);
    assert_eq!(
        SortedSlab::new(mem(wide - 1, true), WIDE, 8, 4).unwrap_err(),
        Error::Storage { need: wide }
    );
    let max = usize::try_from(u32::MAX).unwrap();
    assert_eq!(
        SortedSlab::new(mem(0, true), max + 1, 0, 0).unwrap_err(),
        Error::Capacity
    );
    let need = SortedSlab::bytes(8, 8, 4);
    assert_eq!(
        SortedSlab::new(mem(need - 1, true), 8, 8, 4).unwrap_err(),
        Error::Storage { need }
    );
    assert_eq!(
        SortedSlab::new(mem(0, true), usize::MAX, 8, 4).unwrap_err(),
        Error::Capacity
    );
    // A size that saturates is a capacity, not a size to ask for.
    assert_eq!(
        SortedSlab::new(mem(0, true), 100, usize::MAX, 4).unwrap_err(),
        Error::Capacity
    );
}

#[test]
fn the_two_byte_index_ends_at_65535_records() {
    assert_eq!(SortedSlab::bytes(65_535, 4, 0), 65_535 * 6);
    assert_eq!(SortedSlab::bytes(65_536, 4, 0), 65_536 * 8);
    let n = 65_535usize;
    let mut s = SortedSlab::new(mem(SortedSlab::bytes(n, 4, 0), true), n, 4, 0).unwrap();
    for k in 0..65_535u32 {
        assert_eq!(s.insert(&k.to_be_bytes(), &[]), Ok(false));
    }
    assert_eq!(s.insert(&70_000u32.to_be_bytes(), &[]), Err(Error::Full));
    // Slot 65,534 moves into slot 0.
    assert!(s.remove(&0u32.to_be_bytes()));
    assert_eq!(s.get(&65_534u32.to_be_bytes()), Some(&[][..]));
    assert!(
        s.iter()
            .map(|(k, _)| u32::from_be_bytes(k.try_into().unwrap()))
            .eq(1..65_535)
    );
    assert_eq!(s.insert(&70_000u32.to_be_bytes(), &[]), Ok(false));
    assert_eq!(
        s.last().map(|(k, _)| u32::from_be_bytes(k.try_into().unwrap())),
        Some(70_000)
    );
}

#[test]
fn the_four_byte_index_names_slots_past_65535() {
    let n = 70_000usize;
    let mut s = SortedSlab::new(mem(SortedSlab::bytes(n, 4, 4), true), n, 4, 4).unwrap();
    let mut m = BTreeMap::new();
    for k in 0..n as u32 {
        s.insert(&k.to_be_bytes(), &k.to_le_bytes()).unwrap();
        m.insert(k, k);
    }
    for k in [0u32, 69_998, 10] {
        assert!(s.remove(&k.to_be_bytes()));
        m.remove(&k);
    }
    let pairs = |s: &SortedSlab| -> Vec<(u32, u32)> {
        s.iter()
            .map(|(k, v)| {
                (
                    u32::from_be_bytes(k.try_into().unwrap()),
                    u32::from_le_bytes(v.try_into().unwrap()),
                )
            })
            .collect()
    };
    assert_eq!(pairs(&s), m.iter().map(|(&k, &v)| (k, v)).collect::<Vec<_>>());
    assert_eq!(s.get(&69_999u32.to_be_bytes()), Some(&69_999u32.to_le_bytes()[..]));
    assert_eq!(s.get(&69_997u32.to_be_bytes()), Some(&69_997u32.to_le_bytes()[..]));
    assert_eq!(s.get(&69_998u32.to_be_bytes()), None);
    // One pass removes every odd key: the kept records in slots past 65,535 move into the holes below.
    let odd = m.keys().filter(|k| !k.is_multiple_of(2)).count();
    assert_eq!(
        s.retain(|k, _| u32::from_be_bytes(k.try_into().unwrap()).is_multiple_of(2)),
        odd
    );
    m.retain(|k, _| k.is_multiple_of(2));
    let want: Vec<(u32, u32)> = m.iter().map(|(&k, &v)| (k, v)).collect();
    assert!(pairs(&s) == want, "the walk after retain differs from the map");
    assert_eq!(s.get(&69_996u32.to_be_bytes()), Some(&69_996u32.to_le_bytes()[..]));
}

#[test]
fn a_set_has_a_value_of_no_bytes_and_a_key_of_no_bytes_holds_one() {
    let mut s = SortedSlab::new(mem(SortedSlab::bytes(16, 8, 0), true), 16, 8, 0).unwrap();
    let mut m = BTreeSet::new();
    let mut next = xorshift(0x5eed_5eed);
    for i in 0..3000 {
        let k = next() % 30;
        let at = format!("op {i} {k}");
        match next() % 4 {
            0 | 1 => {
                let r = s.insert(&kb(k), &[]);
                if m.contains(&k) {
                    assert_eq!(r, Ok(true), "{at}");
                } else if m.len() == 16 {
                    assert_eq!(r, Err(Error::Full), "{at}");
                } else {
                    assert_eq!(r, Ok(false), "{at}");
                    m.insert(k);
                }
            }
            2 => assert_eq!(s.remove(&kb(k)), m.remove(&k), "{at}"),
            _ => assert_eq!(
                s.first_at_or_after(&kb(k))
                    .map(|(a, _)| u64::from_be_bytes(a.try_into().unwrap())),
                m.range(k..).next().copied(),
                "{at}"
            ),
        }
        assert!(
            s.iter()
                .map(|(a, v)| (u64::from_be_bytes(a.try_into().unwrap()), v.len()))
                .eq(m.iter().map(|&a| (a, 0))),
            "{at}"
        );
    }
    let mut one = SortedSlab::new(mem(SortedSlab::bytes(4, 0, 4), true), 4, 0, 4).unwrap();
    assert_eq!(one.insert(&[], &vb(1)), Ok(false));
    assert_eq!(one.insert(&[], &vb(2)), Ok(true));
    assert_eq!(one.len(), 1);
    assert_eq!(one.get(&[]), Some(&vb(2)[..]));
    assert!(one.remove(&[]) && one.is_empty());
}

#[test]
fn retain_keeps_all_one_none_and_works_on_an_empty_slab() {
    for cap in [8, WIDE] {
        let mut s = make(cap, 0, true);
        let mut m = BTreeMap::new();
        assert_eq!(s.retain(|_, _| panic!("an empty slab has nothing to visit")), 0);
        for k in [30u64, 10, 40, 20, 50] {
            s.insert(&kb(k), &vb(k as u32)).unwrap();
            m.insert(k, k as u32);
        }
        assert_eq!(s.retain(|_, _| true), 0);
        same(&s, &m, "kept all");
        assert_eq!(s.retain(|k, _| k == kb(40)), 4);
        m.retain(|&k, _| k == 40);
        same(&s, &m, "kept one");
        assert_eq!(s.insert(&kb(5), &vb(5)), Ok(false));
        m.insert(5, 5);
        same(&s, &m, "inserted after");
        assert_eq!(s.retain(|_, _| false), 2);
        m.clear();
        same(&s, &m, "kept none");
        assert_eq!(s.insert(&kb(1), &vb(1)), Ok(false));
    }
}

#[test]
fn long_seeded_runs_match_a_btreemap() {
    let mut next = xorshift(0x9e37_79b9_7f4a_7c15);
    for (cap, domain) in [
        (1usize, 3u64),
        (16, 40),
        (64, 70),
        (200, 150),
        (WIDE, 150),
        (WIDE + 4_464, 300),
    ] {
        for spare in [0, 13] {
            let ops = random_ops(&mut next, 3000);
            run(&ops, cap, domain, spare, cap % 2 == 0);
        }
    }
}

#[test]
fn clear_then_a_run_against_a_fresh_map() {
    let mut next = xorshift(0x1357_9bdf_2468_ace0);
    for cap in [16usize, WIDE] {
        let mut s = make(cap, 5, true);
        run_on(&mut s, &mut BTreeMap::new(), &random_ops(&mut next, 1500), cap, 40);
        s.clear();
        let mut fresh = BTreeMap::new();
        same(&s, &fresh, "cleared");
        run_on(&mut s, &mut fresh, &random_ops(&mut next, 1500), cap, 40);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    #[test]
    fn any_run_matches_a_btreemap(
        ops in proptest::collection::vec((any::<u8>(), any::<u16>(), any::<u16>()), 0..400),
        cap in 1usize..40,
        extra in 0u64..30,
        wide in any::<bool>(),
        spare in 0usize..20,
        owned in any::<bool>(),
    ) {
        let real = if wide { WIDE + cap } else { cap };
        run(&ops, real, cap as u64 + extra, spare, owned || wide);
    }
}
