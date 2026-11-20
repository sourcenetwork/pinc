//! The array by position against a plain model (a vector of options), and its stored walk order against a sort of
//! the keys; the slot pool against a model of taken slots with the bytes written to each.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names
)]

use pinc_table::{Array, Error, Pool, Slot, Storage};
use proptest::prelude::*;

fn mem(n: usize, owned: bool) -> Storage {
    if owned {
        Storage::zeroed(n).unwrap()
    } else {
        Storage::from_static(Box::leak(vec![0xa5u8; n].into_boxed_slice()))
    }
}

fn pool_bytes(slots: usize, size: usize) -> usize {
    Pool::<()>::bytes(slots, size)
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

fn walk_of(a: &Array) -> Vec<(usize, u32)> {
    a.iter()
        .map(|(p, b)| (p, u32::from_le_bytes(b.try_into().unwrap())))
        .collect()
}

fn run_array(ops: &[(u8, u8, u32)], places: usize, spare: usize, owned: bool) {
    let mut a = Array::new(mem(Array::bytes(places, 4) + spare, owned), places, 4).unwrap();
    let mut m: Vec<Option<u32>> = vec![None; places];
    for (i, &(op, p, v)) in ops.iter().enumerate() {
        let p = usize::from(p) % (places + 2);
        let at = format!("op {i} ({op} {p} {v})");
        match op % 4 {
            0 | 1 => {
                let got = a.set(p, &v.to_le_bytes());
                match m.get_mut(p) {
                    Some(slot) => {
                        assert_eq!(got, Ok(slot.is_some()), "{at}");
                        *slot = Some(v);
                    }
                    None => assert_eq!(got, Err(Error::Position), "{at}"),
                }
            }
            2 => {
                let was = m.get_mut(p).is_some_and(|s| s.take().is_some());
                assert_eq!(a.remove(p), was, "{at}");
            }
            _ => {
                if let Some(b) = a.get_mut(p) {
                    b.copy_from_slice(&v.to_le_bytes());
                    *m.get_mut(p).unwrap() = Some(v);
                } else {
                    assert!(m.get(p).copied().flatten().is_none(), "{at}");
                }
            }
        }
        for q in 0..places + 2 {
            let got = a.get(q).map(|b| u32::from_le_bytes(b.try_into().unwrap()));
            assert_eq!(got, m.get(q).copied().flatten(), "place {q} {at}");
        }
        assert_eq!(a.len(), m.iter().flatten().count(), "{at}");
        let want: Vec<(usize, u32)> = m.iter().enumerate().filter_map(|(p, v)| v.map(|v| (p, v))).collect();
        assert_eq!(walk_of(&a), want, "identity order {at}");
    }
}

#[test]
fn the_order_follows_the_keys_and_keeps_ties_in_position() {
    let keys = [30u64, 10, 20, 10, 5, 30];
    let mut a = Array::new(mem(Array::bytes(6, 2), true), 6, 2).unwrap();
    assert_eq!(a.order().collect::<Vec<_>>(), vec![0, 1, 2, 3, 4, 5]);
    for p in 0..6 {
        a.set(p, &[p as u8, 0]).unwrap();
    }
    a.remove(2);
    assert_eq!(a.set_order(&keys[..5]), Err(Error::Length));
    a.set_order(&keys).unwrap();
    let mut want: Vec<usize> = (0..6).collect();
    want.sort_by_key(|&p| (keys[p], p));
    assert_eq!(a.order().collect::<Vec<_>>(), want);
    assert_eq!(
        a.iter().map(|(p, _)| p).collect::<Vec<_>>(),
        want.iter().copied().filter(|&p| p != 2).collect::<Vec<_>>()
    );
    assert_eq!(
        Array::new(mem(3, true), 1, 1).unwrap_err().error,
        Error::Storage { need: 4 }
    );
    assert_eq!(Array::new(mem(0, true), 70_000, 0).unwrap_err().error, Error::Capacity);
    // A size that saturates is a capacity, not a size to ask for.
    assert_eq!(
        Array::new(mem(0, true), 100, usize::MAX).unwrap_err().error,
        Error::Capacity
    );
}

#[test]
fn a_record_or_position_of_the_wrong_kind_is_refused_and_changes_nothing() {
    let mut a = Array::new(mem(Array::bytes(4, 4), true), 4, 4).unwrap();
    assert_eq!(a.set(1, &[7; 4]), Ok(false));
    for bad in [&[0u8; 3][..], &[0u8; 5][..], &[][..]] {
        assert_eq!(a.set(1, bad), Err(Error::Length));
        assert_eq!(a.set(2, bad), Err(Error::Length));
    }
    assert_eq!(a.get(1), Some(&[7u8; 4][..]));
    assert!(a.get(2).is_none());
    assert_eq!(a.len(), 1);
    assert_eq!(a.set(4, &[0; 3]), Err(Error::Position));
    assert_eq!(a.set(4, &[0; 4]), Err(Error::Position));
    assert!(a.get(4).is_none() && a.get_mut(4).is_none() && !a.remove(4));
    assert_eq!(a.len(), 1);
}

#[test]
fn set_order_twice_starts_from_the_identity_and_the_order_stays_stable_under_changes() {
    let mut next = xorshift(0x0dd_ba11);
    let mut a = Array::new(mem(Array::bytes(6, 4), false), 6, 4).unwrap();
    let mut present = [false; 6];
    for keys in [[3u8, 1, 2, 1, 0, 3], [0, 0, 0, 1, 1, 1], [5, 4, 3, 2, 1, 0]] {
        a.set_order(&keys).unwrap();
        let mut sorted: Vec<usize> = (0..6).collect();
        sorted.sort_by_key(|&p| (keys[p], p));
        assert_eq!(a.order().collect::<Vec<_>>(), sorted);
        for step in 0u32..200 {
            let p = (next() % 6) as usize;
            if next().is_multiple_of(2) {
                a.set(p, &step.to_le_bytes()).unwrap();
                present[p] = true;
            } else {
                assert_eq!(a.remove(p), present[p]);
                present[p] = false;
            }
            let want: Vec<usize> = sorted.iter().copied().filter(|&q| present[q]).collect();
            assert_eq!(
                a.iter().map(|(q, _)| q).collect::<Vec<_>>(),
                want,
                "keys {keys:?} step {step}"
            );
        }
    }
    // Ties keep position order and a later call does not inherit the earlier order.
    a.set_order(&[3u8, 1, 2, 1, 0, 3]).unwrap();
    a.set_order(&[0u8, 0, 0, 1, 1, 1]).unwrap();
    assert_eq!(a.order().collect::<Vec<_>>(), vec![0, 1, 2, 3, 4, 5]);
}

#[test]
fn the_largest_array_the_order_can_number() {
    let n = 65_535;
    let mut a = Array::new(mem(Array::bytes(n, 0), true), n, 0).unwrap();
    assert_eq!(a.set(65_534, &[]), Ok(false));
    assert_eq!(a.get(65_534), Some(&[][..]));
    assert_eq!(a.iter().map(|(p, _)| p).collect::<Vec<_>>(), vec![65_534]);
    assert_eq!(Array::new(mem(0, true), 65_536, 0).unwrap_err().error, Error::Capacity);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]
    #[test]
    fn any_array_run_matches_a_model(
        ops in proptest::collection::vec((any::<u8>(), any::<u8>(), any::<u32>()), 0..300),
        places in 0usize..12,
        spare in 0usize..20,
        owned in any::<bool>(),
        keys in proptest::collection::vec(0u8..6, 12),
    ) {
        run_array(&ops, places, spare, owned);
        let mut a = Array::new(mem(Array::bytes(places, 1), owned), places, 1).unwrap();
        a.set_order(&keys[..places]).unwrap();
        let mut want: Vec<usize> = (0..places).collect();
        want.sort_by_key(|&p| (keys[p], p));
        prop_assert_eq!(a.order().collect::<Vec<_>>(), want);
    }
}

fn run_pool(ops: &[(u8, u8, u8)], slots: usize, spare: usize, owned: bool) {
    const SIZE: usize = 6;
    let mut p: Pool = Pool::new(mem(pool_bytes(slots, SIZE) + spare, owned), slots, SIZE).unwrap();
    // Every handle ever handed out with the bytes the model says were written to it while taken.
    let mut all: Vec<(Slot, Option<Vec<u8>>)> = Vec::new();
    for (i, &(op, which, v)) in ops.iter().enumerate() {
        let at = format!("op {i} ({op} {which} {v})");
        let taken = all.iter().filter(|(_, b)| b.is_some()).count();
        match op % 4 {
            0 => {
                let got = p.take();
                if taken == slots {
                    assert!(got.is_none(), "{at}");
                } else {
                    let s = got.expect("a free slot");
                    assert!(
                        all.iter().all(|(o, b)| b.is_none() || o.index() != s.index()),
                        "a taken slot was handed out again {at}"
                    );
                    assert_eq!(p.read(s), Some(&[][..]), "nothing is written to a fresh slot {at}");
                    all.push((s, Some(Vec::new())));
                }
            }
            1 if !all.is_empty() => {
                let n = all.len();
                let (s, b) = &mut all[usize::from(which) % n];
                let data = vec![v; usize::from(v) % (SIZE + 1)];
                let got = p.write(*s, &data);
                match b {
                    Some(bytes) => {
                        assert_eq!(got, Ok(()), "{at}");
                        if bytes.len() < data.len() {
                            bytes.resize(data.len(), 0);
                        }
                        bytes[..data.len()].copy_from_slice(&data);
                    }
                    None => assert_eq!(got, Err(Error::Stale), "{at}"),
                }
                assert_eq!(
                    p.write(*s, &[0; SIZE + 1]),
                    Err(if b.is_some() { Error::Length } else { Error::Stale }),
                    "{at}"
                );
            }
            2 if !all.is_empty() => {
                let n = all.len();
                let (s, b) = &mut all[usize::from(which) % n];
                let got = p.give(*s);
                if b.take().is_some() {
                    assert_eq!(got, Ok(()), "{at}");
                } else {
                    assert_eq!(got, Err(Error::Stale), "a second give-back is refused {at}");
                }
            }
            _ => {}
        }
        assert_eq!(p.taken(), all.iter().filter(|(_, b)| b.is_some()).count(), "{at}");
        assert_eq!(p.free() + p.taken(), slots, "{at}");
        for (s, b) in &all {
            assert_eq!(
                p.read(*s),
                b.as_ref().map(Vec::as_slice),
                "bytes of slot {} {at}",
                s.index()
            );
            assert_eq!(Slot::from_bytes(s.to_bytes()), *s, "a handle round-trips {at}");
        }
    }
}

#[test]
fn a_given_back_handle_never_reads_the_next_owners_bytes() {
    let mut p: Pool = Pool::new(mem(pool_bytes(1, 4), true), 1, 4).unwrap();
    let first = p.take().unwrap();
    p.write(first, &[7; 4]).unwrap();
    p.give(first).unwrap();
    assert_eq!(p.give(first), Err(Error::Stale));
    assert!(p.read(first).is_none());
    let second = p.take().unwrap();
    assert_eq!(second.index(), first.index());
    assert_eq!(
        p.read(second),
        Some(&[][..]),
        "the new owner sees none of the last one's bytes"
    );
    p.write(second, &[9; 2]).unwrap();
    assert_eq!(p.read(second), Some(&[9u8; 2][..]), "only what the new owner wrote");
    p.write(second, &[8; 4]).unwrap();
    assert!(
        p.read(first).is_none(),
        "the old handle must not read the new owner's bytes"
    );
    assert_eq!(p.write(first, &[1; 4]), Err(Error::Stale));
    assert_eq!(p.read(second), Some(&[8u8; 4][..]));
    assert_eq!(
        p.give(first),
        Err(Error::Stale),
        "the old handle must not free the new owner's slot"
    );
    assert!(p.take().is_none());
    assert_eq!(
        Pool::<()>::new(mem(15, true), 1, 4).unwrap_err().error,
        Error::Storage { need: 16 }
    );
}

#[test]
fn a_later_shorter_write_keeps_the_written_length() {
    let mut p: Pool = Pool::new(mem(pool_bytes(1, 6), false), 1, 6).unwrap();
    let s = p.take().unwrap();
    p.write(s, &[1; 5]).unwrap();
    p.write(s, &[2; 2]).unwrap();
    assert_eq!(p.read(s), Some(&[2, 2, 1, 1, 1][..]));
}

#[test]
fn a_handle_round_trips_as_bytes_and_a_forged_one_is_refused() {
    let mut p: Pool = Pool::new(mem(pool_bytes(2, 4), true), 2, 4).unwrap();
    let a = p.take().unwrap();
    p.write(a, &[1, 2, 3, 4]).unwrap();
    assert_eq!(a.to_bytes(), [0, 0, 0, 0, 1, 0, 0, 0]);
    let b = Slot::from_bytes(a.to_bytes());
    assert_eq!(b, a);
    assert_eq!(p.read(b), Some(&[1, 2, 3, 4][..]));
    for forged in [
        [0, 0, 0, 0, 3, 0, 0, 0],
        [0, 0, 0, 0, 2, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 1, 0, 0, 0],
        [5, 0, 0, 0, 1, 0, 0, 0],
        [0xff; 8],
        // Free slot 1 at its own, even, generation; and slot 4, past the two slots, whose generation word is slot 0's
        // data `[1, 2, 3, 4]`.
        [1, 0, 0, 0, 0, 0, 0, 0],
        [4, 0, 0, 0, 1, 2, 3, 4],
    ] {
        let f = Slot::from_bytes(forged);
        assert_eq!(p.read(f), None, "{forged:?}");
        assert_eq!(p.write(f, &[9]), Err(Error::Stale), "{forged:?}");
        assert_eq!(p.give(f), Err(Error::Stale), "{forged:?}");
    }
    assert_eq!((p.taken(), p.read(a)), (1, Some(&[1, 2, 3, 4][..])));
    p.give(b).unwrap();
    assert_eq!(p.give(a), Err(Error::Stale));
}

#[test]
fn a_pool_refuses_a_size_it_cannot_number() {
    let max = usize::try_from(u32::MAX).unwrap();
    // The size saturates: a capacity, not a size to ask for.
    assert_eq!(
        Pool::<()>::new(mem(0, true), max, max).unwrap_err().error,
        Error::Capacity
    );
    assert_eq!(
        Pool::<()>::new(mem(0, true), 1, max + 1).unwrap_err().error,
        Error::Capacity
    );
    assert_eq!(
        Pool::<()>::new(mem(0, true), max + 1, 0).unwrap_err().error,
        Error::Capacity
    );
}

#[test]
fn long_seeded_runs_match_the_models() {
    let mut next = xorshift(0x1234_5678_9abc_def1);
    for n in [0usize, 1, 3, 8, 40] {
        for spare in [0, 13] {
            let ops: Vec<(u8, u8, u32)> = (0..4000).map(|_| (next() as u8, next() as u8, next() as u32)).collect();
            run_array(&ops, n, spare, n % 2 == 0);
            let ops: Vec<(u8, u8, u8)> = (0..4000).map(|_| (next() as u8, next() as u8, next() as u8)).collect();
            run_pool(&ops, n, spare, n % 2 == 1);
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]
    #[test]
    fn any_pool_run_matches_a_model(
        ops in proptest::collection::vec((any::<u8>(), any::<u8>(), any::<u8>()), 0..400),
        slots in 0usize..10,
        spare in 0usize..20,
        owned in any::<bool>(),
    ) {
        run_pool(&ops, slots, spare, owned);
    }
}

#[test]
fn a_refused_array_gives_its_block_back() {
    let refused = Array::new(mem(3, false), 1, 1).unwrap_err();
    assert_eq!((refused.error, refused.storage.len()), (Error::Storage { need: 4 }, 3));
    let refused = Array::new(refused.storage, 70_000, 0).unwrap_err();
    assert_eq!((refused.error, refused.storage.len()), (Error::Capacity, 3));
    assert!(Array::new(refused.storage, 1, 0).is_ok());
}

#[test]
fn a_refused_pool_gives_its_block_back() {
    let refused = Pool::<()>::new(mem(15, false), 1, 4).unwrap_err();
    assert_eq!(
        (refused.error, refused.storage.len()),
        (Error::Storage { need: 16 }, 15)
    );
    let max = usize::try_from(u32::MAX).unwrap();
    let refused = Pool::<()>::new(refused.storage, 1, max + 1).unwrap_err();
    assert_eq!((refused.error, refused.storage.len()), (Error::Capacity, 15));
    assert!(Pool::<()>::new(refused.storage, 0, 4).is_ok());
}
