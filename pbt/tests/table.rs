//! `pinc-table`: the sorted slab, the array by position, the ring and the slot pool against std collections, with the
//! whole state compared after every operation.
//!
//! Where the expected behaviour comes from:
//! - the crate documentation: each table "reads and writes its fixed-size records ..., refuses when full", and
//!   `Error`'s "The table is unchanged after any of them".
//! - `SortedSlab`: "a keyed table that walks in key order, as a `BTreeMap` does"; "Keys compare as byte strings";
//!   `next_after` is "The first entry whose key is after `key`"; `retain` "Keeps the records `keep` returns true for and
//!   removes the rest, in one pass in key order; `keep` may change the value. Returns the number removed."
//! - `Array`: "a place is present exactly when it was set and not removed; the order is always a permutation of
//!   `0..places`, the identity until set"; `set_order`: "the positions sorted by `keys[position]`, equal keys in position
//!   order".
//! - `Ring`: "records pop in the order they were pushed", `len <= capacity`.
//! - `Pool`: "A free stack of slot numbers hands slots out" ("slot 0 is handed out first"); "a handle that was given back
//!   (or given back and taken by another) reads and writes nothing and is refused a second give-back"; "`take` sets [the
//!   written length] to 0 and writes no byte, `write` raises it, and `read` returns the written prefix only".

use std::collections::{BTreeMap, VecDeque};

use ephyra::prelude::*;
use pinc_table::{Array, Error, Pool, Ring, Slot, SortedSlab, Storage};

// ---------------------------------------------------------------------------------------------------------------
// The sorted slab.

/// Key bytes from a seed: each byte one of a few values, so keys collide and order matters.
fn key_of(seed: u16, len: usize) -> Vec<u8> {
    (0..len).map(|i| [0u8, 1, 0x7f, 0x80, 0xff][((seed >> (3 * i)) % 5) as usize]).collect()
}

fn val_of(seed: u8, len: usize) -> Vec<u8> {
    (0..len).map(|i| seed.wrapping_add(i as u8)).collect()
}

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum SlabOp {
    Clear,
    Insert(u16, u8),
    InsertBadKey(u16),
    InsertBadVal(u16),
    Remove(u16),
    GetMut(u16, u8),
    Retain(#[ephyra(gen = gens::int(0u8..=3))] u8, bool),
}

fn slab_cases() -> impl Gen<Value = ((usize, usize, usize, usize, bool), Vec<SlabOp>)> {
    (
        (gens::int(0usize..=8), gens::int(0usize..=3), gens::int(0usize..=3), gens::int(0usize..=5), gens::bool_with(0.05)),
        gens::vec(ephyra::any::<SlabOp>()).len(0..=40),
    )
}

/// Whether `retain` keeps a record, a pure function of the key and the op's mode.
fn keeps(mode: u8, key: &[u8]) -> bool {
    let sum: u32 = key.iter().map(|&b| u32::from(b)).sum();
    match mode {
        0 => true,
        1 => false,
        _ => (sum + u32::from(mode)) % 3 != 0,
    }
}

fn check_slab(s: &SortedSlab, m: &BTreeMap<Vec<u8>, Vec<u8>>, cap: usize, klen: usize, step: &str) {
    let got: Vec<(Vec<u8>, Vec<u8>)> = s.iter().map(|(k, v)| (k.to_vec(), v.to_vec())).collect();
    let want: Vec<(Vec<u8>, Vec<u8>)> = m.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
    assert_eq!(got, want, "{step}: contents");
    assert_eq!(s.len(), m.len(), "{step}: len");
    assert_eq!(s.is_empty(), m.is_empty(), "{step}: is_empty");
    assert_eq!(s.is_full(), m.len() == cap, "{step}: is_full");
    assert_eq!(s.capacity(), cap);
    let own = |e: Option<(&[u8], &[u8])>| e.map(|(k, v)| (k.to_vec(), v.to_vec()));
    assert_eq!(own(s.first()), want.first().cloned(), "{step}: first");
    assert_eq!(own(s.last()), want.last().cloned(), "{step}: last");
    for (i, w) in want.iter().enumerate() {
        assert_eq!(own(s.entry(i)), Some(w.clone()), "{step}: entry({i})");
    }
    assert_eq!(own(s.entry(want.len())), None, "{step}: entry past the end");
    // Probes: every key of the key length a 2-bit seed reaches, plus shorter and longer byte strings.
    let mut probes: Vec<Vec<u8>> = (0..64u16).map(|seed| key_of(seed * 37, klen)).collect();
    probes.extend([vec![], vec![0x80], vec![0xff, 0xff, 0xff, 0xff, 0xff], vec![0, 0, 0, 0, 0]]);
    for p in &probes {
        assert_eq!(s.get(p).map(<[u8]>::to_vec), m.get(p).cloned(), "{step}: get({p:?})");
        assert_eq!(s.contains(p), m.contains_key(p), "{step}: contains({p:?})");
        let at_or_after = m.range(p.clone()..).next().map(|(k, v)| (k.clone(), v.clone()));
        assert_eq!(own(s.first_at_or_after(p)), at_or_after, "{step}: first_at_or_after({p:?})");
        let after = m
            .range((std::ops::Bound::Excluded(p.clone()), std::ops::Bound::Unbounded))
            .next()
            .map(|(k, v)| (k.clone(), v.clone()));
        assert_eq!(own(s.next_after(p)), after, "{step}: next_after({p:?})");
    }
}

/// Every operation leaves the slab holding exactly what a `BTreeMap` holds, walked in the same order, and every
/// refusal names the right reason and changes nothing.
#[ephyra::test(gen = slab_cases(), tests = 4_000)]
fn sorted_slab_matches_a_btreemap(case: ((usize, usize, usize, usize, bool), Vec<SlabOp>)) {
    let ((small_cap, klen, vlen, extra, wide), ops) = case;
    // A wide slab (over 65,535 records) has 4-byte index entries; it is filled by the ops only a little.
    let cap = if wide { 65_536 + small_cap } else { small_cap };
    let mem = Storage::zeroed(SortedSlab::bytes(cap, klen, vlen) + extra).expect("allocates");
    let mut s = SortedSlab::new(mem, cap, klen, vlen).expect("a block of the stated size");
    let mut m: BTreeMap<Vec<u8>, Vec<u8>> = BTreeMap::new();
    for (i, op) in ops.iter().enumerate() {
        let step = format!("step {i}: {op:?}");
        match op {
            SlabOp::Clear => {
                s.clear();
                m.clear();
            },
            SlabOp::Insert(k, v) => {
                let (k, v) = (key_of(*k, klen), val_of(*v, vlen));
                let held = m.contains_key(&k);
                let got = s.insert(&k, &v);
                if held {
                    assert_eq!(got, Ok(true), "{step}");
                    m.insert(k, v);
                } else if m.len() == cap {
                    assert_eq!(got, Err(Error::Full), "{step}");
                } else {
                    assert_eq!(got, Ok(false), "{step}");
                    m.insert(k, v);
                }
            },
            SlabOp::InsertBadKey(k) => {
                let k = key_of(*k, klen + 1);
                assert_eq!(s.insert(&k, &val_of(0, vlen)), Err(Error::Length), "{step}");
            },
            SlabOp::InsertBadVal(k) => {
                let k = key_of(*k, klen);
                assert_eq!(s.insert(&k, &val_of(0, vlen + 1)), Err(Error::Length), "{step}");
            },
            SlabOp::Remove(k) => {
                let k = key_of(*k, klen);
                assert_eq!(s.remove(&k), m.remove(&k).is_some(), "{step}");
            },
            SlabOp::GetMut(k, b) => {
                let k = key_of(*k, klen);
                let got = s.get_mut(&k);
                assert_eq!(got.is_some(), m.contains_key(&k), "{step}");
                if let (Some(v), Some(mv)) = (got, m.get_mut(&k)) {
                    assert_eq!(&v[..], &mv[..], "{step}: get_mut value");
                    if let (Some(x), Some(y)) = (v.first_mut(), mv.first_mut()) {
                        *x = *b;
                        *y = *b;
                    }
                }
            },
            SlabOp::Retain(mode, modify) => {
                let mut seen: Vec<Vec<u8>> = Vec::new();
                let removed = s.retain(|k, v| {
                    seen.push(k.to_vec());
                    let keep = keeps(*mode, k);
                    if keep && *modify && let Some(x) = v.first_mut() {
                        *x ^= 0x55;
                    }
                    keep
                });
                let want_seen: Vec<Vec<u8>> = m.keys().cloned().collect();
                assert_eq!(seen, want_seen, "{step}: retain did not visit every record once in key order");
                let before = m.len();
                m.retain(|k, v| {
                    let keep = keeps(*mode, k);
                    if keep && *modify && let Some(x) = v.first_mut() {
                        *x ^= 0x55;
                    }
                    keep
                });
                assert_eq!(removed, before - m.len(), "{step}: retain's count");
            },
        }
        check_slab(&s, &m, cap, klen, &step);
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The ring.

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum RingOp {
    Pop,
    Push(u8),
    PushBad(u8),
    Clear,
}

fn ring_cases() -> impl Gen<Value = ((usize, usize, usize), Vec<RingOp>)> {
    (
        (gens::int(0usize..=6), gens::int(0usize..=3), gens::int(0usize..=4)),
        gens::vec(ephyra::any::<RingOp>()).len(0..=60),
    )
}

/// The ring is a bounded `VecDeque`: pushes refused when full or of the wrong length, pops in push order, wrap-around
/// at every head position.
#[ephyra::test(gen = ring_cases(), tests = 10_000)]
fn ring_matches_a_vecdeque(case: ((usize, usize, usize), Vec<RingOp>)) {
    let ((cap, size, extra), ops) = case;
    let mut r = Ring::new(Storage::zeroed(Ring::bytes(cap, size) + extra).expect("allocates"), cap, size)
        .expect("a block of the stated size");
    let mut m: VecDeque<Vec<u8>> = VecDeque::new();
    for (i, op) in ops.iter().enumerate() {
        match op {
            RingOp::Pop => assert_eq!(r.pop().map(<[u8]>::to_vec), m.pop_front(), "step {i}: pop"),
            RingOp::Push(b) => {
                let rec = val_of(*b, size);
                let got = r.push(&rec);
                if m.len() == cap {
                    assert_eq!(got, Err(Error::Full), "step {i}");
                } else {
                    assert_eq!(got, Ok(()), "step {i}");
                    m.push_back(rec);
                }
            },
            RingOp::PushBad(b) => assert_eq!(r.push(&val_of(*b, size + 1)), Err(Error::Length), "step {i}"),
            RingOp::Clear => {
                r.clear();
                m.clear();
            },
        }
        let got: Vec<Vec<u8>> = r.iter().map(<[u8]>::to_vec).collect();
        assert_eq!(got, m.iter().cloned().collect::<Vec<_>>(), "step {i}: {op:?}");
        assert_eq!(r.len(), m.len());
        assert_eq!(r.is_full(), m.len() == cap);
        assert_eq!(r.is_empty(), m.is_empty());
        assert_eq!(r.peek().map(<[u8]>::to_vec), m.front().cloned());
        for j in 0..=m.len() {
            assert_eq!(r.get(j).map(<[u8]>::to_vec), m.get(j).cloned(), "step {i}: get({j})");
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The array by position.

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum ArrayOp {
    Set(#[ephyra(gen = gens::int(0usize..=9))] usize, u8),
    SetBad(#[ephyra(gen = gens::int(0usize..=9))] usize),
    Remove(#[ephyra(gen = gens::int(0usize..=9))] usize),
    GetMut(#[ephyra(gen = gens::int(0usize..=9))] usize, u8),
    Order(#[ephyra(gen = gens::vec(gens::int(0u8..=3)).len(0..=9))] Vec<u8>),
}

fn array_cases() -> impl Gen<Value = ((usize, usize, usize), Vec<ArrayOp>)> {
    (
        (gens::int(0usize..=8), gens::int(0usize..=3), gens::int(0usize..=4)),
        gens::vec(ephyra::any::<ArrayOp>()).len(0..=40),
    )
}

/// The array is a `Vec<Option<record>>` with a walk order that is the stable sort of the positions by the last keys
/// set (the identity before).
#[ephyra::test(gen = array_cases(), tests = 10_000)]
fn array_matches_a_vec_of_options(case: ((usize, usize, usize), Vec<ArrayOp>)) {
    let ((places, size, extra), ops) = case;
    let mut a = Array::new(Storage::zeroed(Array::bytes(places, size) + extra).expect("allocates"), places, size)
        .expect("a block of the stated size");
    let mut m: Vec<Option<Vec<u8>>> = vec![None; places];
    let mut order: Vec<usize> = (0..places).collect();
    for (i, op) in ops.iter().enumerate() {
        match op {
            ArrayOp::Set(pos, b) => {
                let rec = val_of(*b, size);
                let got = a.set(*pos, &rec);
                match m.get_mut(*pos) {
                    None => assert_eq!(got, Err(Error::Position), "step {i}"),
                    Some(slot) => {
                        assert_eq!(got, Ok(slot.is_some()), "step {i}");
                        *slot = Some(rec);
                    },
                }
            },
            ArrayOp::SetBad(pos) => {
                let want = if *pos >= places { Error::Position } else { Error::Length };
                assert_eq!(a.set(*pos, &val_of(0, size + 1)), Err(want), "step {i}");
            },
            ArrayOp::Remove(pos) => {
                let was = m.get_mut(*pos).and_then(Option::take).is_some();
                assert_eq!(a.remove(*pos), was, "step {i}");
            },
            ArrayOp::GetMut(pos, b) => {
                let got = a.get_mut(*pos);
                let want = m.get_mut(*pos).and_then(Option::as_mut);
                assert_eq!(got.is_some(), want.is_some(), "step {i}");
                if let (Some(g), Some(w)) = (got, want) {
                    assert_eq!(&g[..], &w[..]);
                    if let (Some(x), Some(y)) = (g.first_mut(), w.first_mut()) {
                        *x = *b;
                        *y = *b;
                    }
                }
            },
            ArrayOp::Order(keys) => {
                let got = a.set_order(keys);
                if keys.len() == places {
                    assert_eq!(got, Ok(()), "step {i}");
                    order = (0..places).collect();
                    order.sort_by_key(|&p| keys[p]);
                } else {
                    assert_eq!(got, Err(Error::Length), "step {i}");
                }
            },
        }
        for p in 0..=places {
            assert_eq!(a.get(p).map(<[u8]>::to_vec), m.get(p).cloned().flatten(), "step {i}: get({p})");
        }
        assert_eq!(a.len(), m.iter().flatten().count(), "step {i}: len");
        assert_eq!(a.order().collect::<Vec<_>>(), order, "step {i}: order");
        let walk: Vec<(usize, Vec<u8>)> = a.iter().map(|(p, r)| (p, r.to_vec())).collect();
        let want: Vec<(usize, Vec<u8>)> = order.iter().filter_map(|&p| m[p].clone().map(|r| (p, r))).collect();
        assert_eq!(walk, want, "step {i}: iter");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The slot pool.

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum PoolOp {
    Take,
    Give(#[ephyra(gen = gens::int(0usize..=7))] usize),
    Write(#[ephyra(gen = gens::int(0usize..=7))] usize, #[ephyra(gen = gens::int(0usize..=5))] usize, u8),
    Read(#[ephyra(gen = gens::int(0usize..=7))] usize),
    Forged(u32, u32),
}

fn pool_cases() -> impl Gen<Value = ((usize, usize, usize), Vec<PoolOp>)> {
    (
        (gens::int(0usize..=5), gens::int(0usize..=4), gens::int(0usize..=4)),
        gens::vec(ephyra::any::<PoolOp>()).len(0..=60),
    )
}

/// One slot of the model pool.
#[derive(Debug, Clone, Default)]
struct ModelSlot {
    generation: u32,
    written: Vec<u8>,
}

/// The pool against a model with a free stack, a generation per slot and the written prefix per slot. Every handle
/// ever handed out is kept, so given-back and re-taken handles are exercised.
#[ephyra::test(gen = pool_cases(), tests = 10_000)]
fn pool_matches_a_free_stack_model(case: ((usize, usize, usize), Vec<PoolOp>)) {
    let ((slots, size, extra), ops) = case;
    let mut p: Pool = Pool::new(Storage::zeroed(Pool::<()>::bytes(slots, size) + extra).expect("allocates"), slots, size)
        .expect("a block of the stated size");
    let mut free: Vec<usize> = (0..slots).rev().collect();
    let mut model: Vec<ModelSlot> = vec![ModelSlot::default(); slots];
    let mut handles: Vec<Slot> = Vec::new();
    // Live: the handle's generation is odd (taken) and is the slot's current one.
    let live = |model: &Vec<ModelSlot>, h: Slot| {
        let g = u32::from_le_bytes(h.to_bytes()[4..].try_into().unwrap_or_default());
        g & 1 == 1 && model.get(h.index()).is_some_and(|s| s.generation == g)
    };
    let pick = |handles: &Vec<Slot>, k: usize| handles.get(k % handles.len().max(1)).copied();
    for (i, op) in ops.iter().enumerate() {
        match op {
            PoolOp::Take => {
                let got = p.take();
                match free.pop() {
                    None => assert_eq!(got, None, "step {i}"),
                    Some(idx) => {
                        let s = &mut model[idx];
                        s.generation = s.generation.wrapping_add(1);
                        s.written.clear();
                        let h = got.unwrap_or_else(|| panic!("step {i}: take refused with a free slot"));
                        assert_eq!(h.index(), idx, "step {i}: the free stack order");
                        assert_eq!(h, Slot::from_bytes(h.to_bytes()));
                        assert_eq!(&h.to_bytes()[4..], &s.generation.to_le_bytes(), "step {i}: generation");
                        handles.push(h);
                    },
                }
            },
            PoolOp::Give(k) => {
                let Some(h) = pick(&handles, *k) else { continue };
                let ok = live(&model, h);
                let got = p.give(h);
                if ok {
                    assert_eq!(got, Ok(()), "step {i}");
                    let s = &mut model[h.index()];
                    s.generation = s.generation.wrapping_add(1);
                    free.push(h.index());
                } else {
                    assert_eq!(got, Err(Error::Stale), "step {i}");
                }
            },
            PoolOp::Write(k, n, b) => {
                let Some(h) = pick(&handles, *k) else { continue };
                let data = val_of(*b, *n);
                let got = p.write(h, &data);
                if !live(&model, h) {
                    assert_eq!(got, Err(Error::Stale), "step {i}");
                } else if *n > size {
                    assert_eq!(got, Err(Error::Length), "step {i}");
                } else {
                    assert_eq!(got, Ok(()), "step {i}");
                    let w = &mut model[h.index()].written;
                    if w.len() < data.len() {
                        w.resize(data.len(), 0);
                    }
                    w[..data.len()].copy_from_slice(&data);
                }
            },
            PoolOp::Read(k) => {
                let Some(h) = pick(&handles, *k) else { continue };
                let want = live(&model, h).then(|| model[h.index()].written.clone());
                assert_eq!(p.read(h).map(<[u8]>::to_vec), want, "step {i}");
            },
            PoolOp::Forged(idx, generation) => {
                let mut b = [0u8; 8];
                b[..4].copy_from_slice(&idx.to_le_bytes());
                b[4..].copy_from_slice(&generation.to_le_bytes());
                let h = Slot::from_bytes(b);
                let want = live(&model, h).then(|| model[h.index()].written.clone());
                assert_eq!(p.read(h).map(<[u8]>::to_vec), want, "step {i}: a forged handle");
            },
        }
        assert_eq!(p.free(), free.len(), "step {i}: free");
        assert_eq!(p.taken(), slots - free.len(), "step {i}: taken");
        assert_eq!(p.capacity(), slots);
        assert_eq!(p.slot_size(), size);
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Construction, and empty records with capacities no block could hold for real records.

/// Which table, its two size arguments, and how far the block's length is from what it needs.
fn construction_cases() -> impl Gen<Value = (u8, usize, usize, i8)> {
    let n = gens::frequency(vec![(4, gens::int(0usize..=70).boxed()), (1, gens::int(65_530usize..=65_540).boxed())]).boxed();
    (gens::int(0u8..=3), n.clone(), gens::int(0usize..=5), gens::int(-3i8..=3))
}

/// Every constructor: "Refuses a block smaller than [`Self::bytes`]" with `Error::Storage { need }` and the block
/// handed back "untouched" (the same length); takes any block at least that long; a slab's index entry widens from 2
/// to 4 bytes above 65,535 records; an array refuses more places than a u16 numbers.
#[ephyra::test(gen = construction_cases(), tests = 4_000)]
fn constructors_take_exactly_the_blocks_they_need(case: (u8, usize, usize, i8)) {
    let (kind, n, size, d) = case;
    let need = match kind {
        0 => SortedSlab::bytes(n, size, 1),
        1 => Array::bytes(n, size),
        2 => Ring::bytes(n, size),
        _ => Pool::<()>::bytes(n, size),
    };
    let len = need.saturating_add_signed(isize::from(d));
    let mem = Storage::zeroed(len).expect("allocates");
    let got = match kind {
        0 => SortedSlab::new(mem, n, size, 1).map(|s| s.capacity()),
        1 => Array::new(mem, n, size).map(|a| a.places()),
        2 => Ring::new(mem, n, size).map(|r| r.capacity()),
        _ => Pool::<()>::new(mem, n, size).map(|p| p.capacity()),
    };
    if kind == 0 {
        let width = if n <= 65_535 { 2 } else { 4 };
        assert_eq!(need, n * (size + 1 + width), "the slab's size formula");
    }
    match got {
        Ok(cap) => {
            assert!(len >= need, "took a block of {len} bytes for a need of {need}");
            assert!(kind != 1 || n <= usize::from(u16::MAX), "an array of {n} places");
            assert_eq!(cap, n);
        },
        Err(r) => {
            assert_eq!(r.storage.len(), len, "the block was not handed back whole");
            if kind == 1 && n > usize::from(u16::MAX) {
                assert_eq!(r.error, Error::Capacity);
            } else {
                assert!(len < need, "refused a block of {len} bytes for a need of {need}: {:?}", r.error);
                assert_eq!(r.error, Error::Storage { need });
            }
        },
    }
}

fn empty_ring_cases() -> impl Gen<Value = (usize, Vec<RingOp>)> {
    let cap = gens::frequency(vec![
        (1, gens::int(usize::MAX - 2..=usize::MAX).boxed()),
        (1, gens::int((usize::MAX >> 1) - 1..=(usize::MAX >> 1) + 1).boxed()),
        (1, gens::int(0usize..=3).boxed()),
    ]);
    (cap, gens::vec(ephyra::any::<RingOp>()).len(0..=60))
}

/// A ring of 0-byte records needs no block at any capacity (`bytes` is 0), so the documented behaviour must hold at
/// capacities near `usize::MAX` too: no overflow, records pop in push order, `len <= capacity`.
#[ephyra::test(gen = empty_ring_cases(), tests = 5_000)]
fn ring_of_empty_records_at_any_capacity(case: (usize, Vec<RingOp>)) {
    let (cap, ops) = case;
    let mut r = Ring::new(Storage::zeroed(0).expect("allocates"), cap, 0).expect("needs no bytes");
    let mut len = 0usize;
    for (i, op) in ops.iter().enumerate() {
        match op {
            RingOp::Pop => {
                let got = r.pop().map(<[u8]>::len);
                assert_eq!(got, (len > 0).then_some(0), "step {i}: pop");
                len = len.saturating_sub(1);
            },
            RingOp::Push(_) => {
                let got = r.push(&[]);
                if len == cap {
                    assert_eq!(got, Err(Error::Full), "step {i}");
                } else {
                    assert_eq!(got, Ok(()), "step {i}");
                    len += 1;
                }
            },
            RingOp::PushBad(b) => assert_eq!(r.push(&[*b]), Err(Error::Length), "step {i}"),
            RingOp::Clear => {
                r.clear();
                len = 0;
            },
        }
        assert_eq!(r.len(), len, "step {i}: {op:?}");
        assert_eq!(r.is_full(), len == cap, "step {i}");
        assert_eq!(r.iter().count(), len, "step {i}");
        assert_eq!(r.get(len), None, "step {i}");
        assert_eq!(r.get(len.saturating_sub(1)).map(<[u8]>::len), (len > 0).then_some(0), "step {i}");
    }
}
