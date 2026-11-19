//! Trace generation for the sorted slab: seeded runs of a real `SortedSlab` (`pinc-table`, built with the `trace`
//! feature), recorded as ndjson (`table_slab.ndjson`) for the TLA+ trace check (`TraceTableSlab.tla`).
//!
//! A run makes a slab of capacity 0, 1, 3, 8, 64 (2-byte index entries) or 70,000 (4-byte entries) with 2-byte keys
//! and values (`u16`, big-endian) and drives it with inserts of new and held keys until full and past it, keys and
//! values of the wrong length, removals of the first, last, middle and absent keys, `retain` keeping none, all or
//! some of the records (changing the values or not), and clears. After every call the slab shows each position's
//! slot, key and value, its first and last entry, and `get`, `contains`, `first_at_or_after` and `next_after` of a
//! few probe keys.
//!
//! The test compares every call with a `BTreeMap` reference and checks the records stay packed in the first slots
//! and that a refused call, a removal of an absent key and a `retain` that changes nothing leave the slab as it was.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::needless_range_loop,
    clippy::too_many_arguments,
    unreachable_pub,
    clippy::panic
)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::ops::Bound::{Excluded, Unbounded};

use pinc_table::{Error, SortedSlab, Storage};
use pinc_tests::{SplitMix64, soaking};

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    full: u32,
    full_refused: u32,
    length_key: u32,
    length_val: u32,
    insert_held: u32,
    remove_last: u32,
    remove_hole: u32,
    retain_none: u32,
    retain_all: u32,
    retain_move: u32,
    big: u32,
}

/// A value below `n` (`n > 0`).
fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

fn be(bytes: &[u8]) -> u16 {
    u16::from_be_bytes(<[u8; 2]>::try_from(bytes).unwrap())
}

fn pair(e: Option<(&[u8], &[u8])>) -> Option<(u16, u16)> {
    e.map(|(k, v)| (be(k), be(v)))
}

/// `[]` or `[key,value]`.
fn pair_json(p: Option<(u16, u16)>) -> String {
    p.map_or_else(|| "[]".to_owned(), |(k, v)| format!("[{k},{v}]"))
}

/// A value in `1..=65535`.
fn value(rng: &mut SplitMix64) -> u16 {
    (below(rng, 65535) + 1) as u16
}

/// A slab beside its reference and its record.
struct Rig<'a> {
    s: SortedSlab,
    cap: usize,
    range: u64,
    map: BTreeMap<u16, u16>,
    out: &'a mut String,
    run: u32,
    last: String,
}

impl Rig<'_> {
    /// Checks the slab against the reference; returns the view without the probe keys and the whole view.
    fn view(&self, rng: &mut SplitMix64, extra: &[u16], seen: &mut Seen) -> (String, String) {
        let s = &self.s;
        let len = self.map.len();
        assert_eq!(s.capacity(), self.cap);
        assert_eq!(s.len(), len, "len");
        assert!(len <= self.cap, "the slab holds more than its capacity");
        assert_eq!(s.is_full(), len == self.cap);
        assert_eq!(s.is_empty(), len == 0);
        let want: Vec<(u16, u16)> = self.map.iter().map(|(&k, &v)| (k, v)).collect();
        let got: Vec<(u16, u16)> = s.iter().map(|(k, v)| (be(k), be(v))).collect();
        assert_eq!(got, want, "iter");
        for p in 0..=len {
            assert_eq!(pair(s.entry(p)), want.get(p).copied(), "entry({p})");
            assert_eq!(
                s.trace_slot(p).is_some(),
                p < len,
                "a slot is held exactly by a position below len"
            );
        }
        let mut used: Vec<usize> = (0..len).filter_map(|p| s.trace_slot(p)).collect();
        used.sort_unstable();
        assert_eq!(
            used,
            (0..len).collect::<Vec<_>>(),
            "the records are not packed in the first slots"
        );
        let (first, last) = (want.first().copied(), want.last().copied());
        assert_eq!(pair(s.first()), first);
        assert_eq!(pair(s.last()), last);
        seen.full += u32::from(self.cap >= 1 && len == self.cap);
        seen.big += u32::from(self.cap == 70_000 && len > 256);
        let slots: Vec<String> = want
            .iter()
            .enumerate()
            .map(|(p, (k, v))| format!("[{p},{k},{v}]"))
            .collect();
        let core = format!(
            r#"{{"len":{len},"slots":[{}],"first":{},"last":{}"#,
            slots.join(","),
            pair_json(first),
            pair_json(last)
        );
        let mut probes = vec![0u16, 65535];
        probes.extend((0..3).map(|_| below(rng, self.range) as u16));
        probes.extend_from_slice(extra);
        let mut qs = Vec::new();
        for &q in &probes {
            let kb = q.to_be_bytes();
            let get = self.map.get(&q).copied();
            assert_eq!(s.get(&kb).map(be), get, "get({q})");
            assert_eq!(s.contains(&kb), get.is_some(), "contains({q})");
            let aoa = self.map.range(q..).next().map(|(&k, &v)| (k, v));
            assert_eq!(pair(s.first_at_or_after(&kb)), aoa, "first_at_or_after({q})");
            let nxt = self.map.range((Excluded(q), Unbounded)).next().map(|(&k, &v)| (k, v));
            assert_eq!(pair(s.next_after(&kb)), nxt, "next_after({q})");
            qs.push(format!(
                r#"{{"key":{q},"get":[{}],"has":{},"aoa":{},"nxt":{}}}"#,
                get.map_or_else(String::new, |v| v.to_string()),
                get.is_some(),
                pair_json(aoa),
                pair_json(nxt)
            ));
        }
        let full = format!(r#"{core},"qs":[{}]}}"#, qs.join(","));
        (core, full)
    }

    /// Records the event, and checks a call that must change nothing left the slab as it was.
    fn emit(&mut self, head: &str, unchanged: bool, (core, full): (String, String)) {
        if unchanged {
            assert_eq!(core, self.last, "a call that changes nothing changed the slab");
        }
        let _ = writeln!(self.out, r#"{{"t":"tslab","run":{},{head},"v":{full}}}"#, self.run);
        self.last = core;
    }

    fn insert(&mut self, rng: &mut SplitMix64, seen: &mut Seen, kb: &[u8], vb: &[u8]) {
        let (kg, vg) = (kb.len() == 2, vb.len() == 2);
        // a 3-byte key or value is named by its first two bytes, a 1-byte one by 0 (the model ignores them)
        let named = |b: &[u8]| if b.len() >= 2 { be(&b[..2]) } else { 0 };
        let (key, val) = (named(kb), named(vb));
        let want = if !(kg && vg) {
            Err(Error::Length)
        } else if self.map.contains_key(&key) {
            Ok(true)
        } else if self.map.len() == self.cap {
            Err(Error::Full)
        } else {
            Ok(false)
        };
        let got = self.s.insert(kb, vb);
        assert_eq!(got, want, "insert({key})");
        let res = match got {
            Ok(true) => "true",
            Ok(false) => "false",
            Err(Error::Full) => "full",
            Err(Error::Length) => "length",
            Err(e) => panic!("insert refused with {e:?}"),
        };
        seen.insert_held += u32::from(got == Ok(true));
        seen.full_refused += u32::from(got == Err(Error::Full));
        seen.length_key += u32::from(!kg);
        seen.length_val += u32::from(kg && !vg);
        if got.is_ok() {
            self.map.insert(key, val);
        }
        let extra = if kg { vec![key] } else { vec![] };
        let v = self.view(rng, &extra, seen);
        self.emit(
            &format!(r#""op":"insert","kg":{kg},"vg":{vg},"key":{key},"val":{val},"res":"{res}""#),
            got.is_err(),
            v,
        );
    }

    fn insert_key(&mut self, rng: &mut SplitMix64, seen: &mut Seen, key: u16, val: u16) {
        self.insert(rng, seen, &key.to_be_bytes(), &val.to_be_bytes());
    }

    fn remove(&mut self, rng: &mut SplitMix64, seen: &mut Seen, key: u16) {
        let held = self.map.contains_key(&key);
        if held {
            let p = self.map.range(..key).count();
            let slot = self.s.trace_slot(p).unwrap();
            if slot + 1 == self.map.len() {
                seen.remove_last += 1;
            } else {
                seen.remove_hole += 1;
            }
        }
        let got = self.s.remove(&key.to_be_bytes());
        assert_eq!(got, held, "remove({key})");
        self.map.remove(&key);
        let v = self.view(rng, &[key], seen);
        self.emit(&format!(r#""op":"remove","key":{key},"res":"{got}""#), !got, v);
    }

    fn retain(&mut self, rng: &mut SplitMix64, seen: &mut Seen, keep: &BTreeSet<u16>, bump: bool) {
        let before: Vec<(u16, u16)> = self.map.iter().map(|(&k, &v)| (k, v)).collect();
        let new_len = before.iter().filter(|(k, _)| keep.contains(k)).count();
        // a kept record whose slot is at or above the new length moves into a hole
        let moves = before
            .iter()
            .enumerate()
            .any(|(p, (k, _))| keep.contains(k) && self.s.trace_slot(p).unwrap() >= new_len);
        let mut calls = Vec::new();
        let map = &self.map;
        let got = self.s.retain(|k, v| {
            let (key, cur) = (be(k), be(v));
            assert_eq!(
                map.get(&key),
                Some(&cur),
                "retain saw a value the reference does not hold"
            );
            calls.push(key);
            if !keep.contains(&key) {
                return false;
            }
            if bump {
                v.copy_from_slice(&(cur % 65535 + 1).to_be_bytes());
            }
            true
        });
        let removed = before.len() - new_len;
        assert_eq!(got, removed, "retain returned the wrong count");
        assert!(
            calls.iter().copied().eq(before.iter().map(|&(k, _)| k)),
            "retain called the closure out of order"
        );
        self.map.retain(|k, v| {
            let stays = keep.contains(k);
            if stays && bump {
                *v = *v % 65535 + 1;
            }
            stays
        });
        seen.retain_none += u32::from(removed == 0);
        seen.retain_all += u32::from(removed > 0 && self.map.is_empty());
        seen.retain_move += u32::from(moves);
        let v = self.view(rng, &[], seen);
        let list = |it: &mut dyn Iterator<Item = u16>| it.map(|k| k.to_string()).collect::<Vec<_>>().join(",");
        self.emit(
            &format!(
                r#""op":"retain","keep":[{}],"mut":{bump},"res":{removed},"calls":[{}]"#,
                list(&mut keep.iter().copied()),
                list(&mut calls.iter().copied())
            ),
            removed == 0 && !bump,
            v,
        );
    }

    fn clear(&mut self, rng: &mut SplitMix64, seen: &mut Seen) {
        self.s.clear();
        self.map.clear();
        let v = self.view(rng, &[], seen);
        self.emit(r#""op":"clear""#, false, v);
    }

    /// A key not held, if the draws find one.
    fn absent(&self, rng: &mut SplitMix64) -> u16 {
        let mut k = below(rng, self.range) as u16;
        for _ in 0..64 {
            if !self.map.contains_key(&k) {
                break;
            }
            k = below(rng, self.range) as u16;
        }
        k
    }

    /// A key held (the first, the last or a middle one, at random), or an absent key when empty.
    fn held(&self, rng: &mut SplitMix64) -> u16 {
        let keys: Vec<u16> = self.map.keys().copied().collect();
        match (keys.first(), keys.last()) {
            (Some(&f), Some(&l)) => match below(rng, 3) {
                0 => f,
                1 => l,
                _ => keys[below(rng, keys.len() as u64) as usize],
            },
            _ => self.absent(rng),
        }
    }
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, cap: usize, range: u64, calls: u32, seen: &mut Seen) {
    let big = cap == 70_000;
    let s = SortedSlab::new(Storage::zeroed(SortedSlab::bytes(cap, 2, 2)).unwrap(), cap, 2, 2).unwrap();
    let mut g = Rig {
        s,
        cap,
        range,
        map: BTreeMap::new(),
        out,
        run: id,
        last: String::new(),
    };
    let v = g.view(rng, &[], seen);
    g.emit(&format!(r#""op":"init","cap":{cap}"#), false, v);
    if big {
        for _ in 0..300 {
            let (k, x) = (g.absent(rng), value(rng));
            g.insert_key(rng, seen, k, x);
        }
    }
    for _ in 0..calls {
        match below(rng, 20) {
            0..=6 => {
                let (k, x) = (below(rng, range) as u16, value(rng));
                g.insert_key(rng, seen, k, x);
            }
            7 => {
                let (k, x) = (below(rng, range) as u16, value(rng));
                let n = if below(rng, 2) == 0 { 1 } else { 3 };
                let mut bad: Vec<u8> = (0..n).map(|_| rng.next_u64() as u8).collect();
                if n == 3 {
                    bad[..2].copy_from_slice(&k.to_be_bytes());
                }
                if below(rng, 2) == 0 {
                    g.insert(rng, seen, &bad, &x.to_be_bytes());
                } else {
                    g.insert(rng, seen, &k.to_be_bytes(), &bad);
                }
            }
            8 if !big => loop {
                let (k, x) = (g.absent(rng), value(rng));
                let was = g.map.len();
                g.insert_key(rng, seen, k, x);
                if g.map.len() == was {
                    break;
                }
            },
            8 | 18 if big => {
                let (k, x) = (below(rng, range) as u16, value(rng));
                g.insert_key(rng, seen, k, x);
            }
            9..=11 => {
                let k = g.held(rng);
                g.remove(rng, seen, k);
            }
            12 => {
                let k = g.absent(rng);
                g.remove(rng, seen, k);
            }
            13..=16 => {
                // vertexia: the 70,000 slab draws its subset from the held keys, not the 65,536-key range (the
                // keys named in a trace event stay few); every key outside the slab is kept or not with no effect
                let pool: Vec<u16> = if big {
                    g.map.keys().copied().collect()
                } else {
                    (0..range as u16).collect()
                };
                let keep: BTreeSet<u16> = pool.into_iter().filter(|_| below(rng, 2) == 0).collect();
                let bump = below(rng, 2) == 0;
                g.retain(rng, seen, &keep, bump);
            }
            17 => {
                let keep: BTreeSet<u16> = if below(rng, 2) == 0 {
                    BTreeSet::new()
                } else {
                    g.map.keys().copied().collect()
                };
                let bump = below(rng, 2) == 0;
                g.retain(rng, seen, &keep, bump);
            }
            18 => g.clear(rng, seen),
            _ => {
                let keep: BTreeSet<u16> = g.map.keys().copied().step_by(2).collect();
                g.retain(rng, seen, &keep, true);
            }
        }
    }
}

#[test]
fn the_slab_matches_the_model() {
    let mut rng = SplitMix64::traced(0x736c_6162);
    let mut out = String::new();
    let mut seen = Seen::default();
    let mut id = 1u32;
    for (cap, range, runs, calls) in [
        (0, 4, 2, 20),
        (1, 4, 6, 60),
        (3, 6, 10, 150),
        (8, 16, 10, 300),
        (64, 128, 4, 600),
        (70_000, 65_536, 1, 100),
    ] {
        for _ in 0..runs {
            run(&mut rng, &mut out, id, cap, range, calls, &mut seen);
            id += 1;
        }
    }
    if !soaking() {
        assert!(seen.full > 0, "no slab was full");
        assert!(seen.full_refused > 0, "no insert was refused as full");
        assert!(
            seen.length_key > 0 && seen.length_val > 0,
            "no key and no value of the wrong length"
        );
        assert!(seen.insert_held > 0, "no insert of a held key");
        assert!(seen.remove_last > 0, "no removal of the last slot");
        assert!(seen.remove_hole > 0, "no removal of a slot that is not the last");
        assert!(seen.retain_none > 0, "no retain removed nothing");
        assert!(seen.retain_all > 0, "no retain removed everything");
        assert!(seen.retain_move > 0, "no retain moved a kept record into a hole");
        assert!(seen.big > 0, "the 70,000 slab never held more than 256 records");
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("table_slab.ndjson"), &out).unwrap();
    }
}
