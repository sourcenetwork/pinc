//! Trace generation for the endpoint's connection-id table: seeded runs of a real `Table` (`pinc-core`, built with the
//! `trace` feature), recorded as ndjson (`core_table.ndjson`) for the TLA+ trace check (`TraceCoreTable.tla`) and the
//! Lean replay (`Pinc/TraceCoreTable.lean`).
//!
//! A run drives a table of 1, 2, 3, 4, 8 or 16 entries with a random seed (so a random bucket function: the
//! capacity-1 table sends every key to one chain, the others collide as the hash falls) through `insert`,
//! `insert_room`, `insert_dup` (a few hot keys, so a key gets many holders), `remove`, `remove_pair`, `touch`, `get`,
//! `matches::<M>` for M from 0 to 5, `at_index`/`index_of` and `clear`, on a small key space so the table fills, evicts
//! and refuses. After every call the event shows the result, the bucket of the key (read through the `trace` view
//! `trace_bucket`, which is what the models take as the bucket function), the array position `index_of` gives for the
//! key, and the table: the entry at every array position, the entries from the oldest to the newest, and `len`.
//!
//! The test compares every call with a naive table (the one of `core_props.rs`, a list in insertion order and a map,
//! extended with duplicates: each entry carries the number of the push that made it, the holders of a key are the
//! entries with that key by decreasing number): the result, the order, `get`, `contains`, every `matches::<M>` and
//! `len` must be the naive ones, and no array position of a live entry moves while the entry lives.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::type_complexity,
    clippy::needless_range_loop,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_core::Table;
use pinc_tests::SplitMix64;

/// The naive table: the entries in insertion order, each with the number of the push that made it.
#[derive(Default, Clone)]
struct Naive {
    order: Vec<(u8, u16, u64)>,
    pushes: u64,
}

impl Naive {
    fn newest(&self, k: u8) -> Option<usize> {
        (0..self.order.len())
            .filter(|i| self.order[*i].0 == k)
            .max_by_key(|i| self.order[*i].2)
    }
    fn push(&mut self, k: u8, v: u16) {
        self.order.push((k, v, self.pushes));
        self.pushes += 1;
    }
    fn insert(&mut self, cap: usize, k: u8, v: u16) -> Option<(u8, u16)> {
        if let Some(i) = self.newest(k) {
            self.order[i].1 = v;
            return None;
        }
        let ev = if self.order.len() == cap {
            let o = self.order.remove(0);
            Some((o.0, o.1))
        } else {
            None
        };
        self.push(k, v);
        ev
    }
    fn room(&mut self, cap: usize, k: u8, v: u16) -> bool {
        if let Some(i) = self.newest(k) {
            self.order[i].1 = v;
            true
        } else if self.order.len() < cap {
            self.push(k, v);
            true
        } else {
            false
        }
    }
    fn dup(&mut self, cap: usize, k: u8, v: u16) -> bool {
        if self.order.len() < cap {
            self.push(k, v);
            true
        } else {
            false
        }
    }
    fn remove(&mut self, k: u8) -> Option<u16> {
        let i = self.newest(k)?;
        Some(self.order.remove(i).1)
    }
    fn remove_pair(&mut self, k: u8, v: u16) -> bool {
        let i = (0..self.order.len())
            .filter(|i| self.order[*i].0 == k && self.order[*i].1 == v)
            .max_by_key(|i| self.order[*i].2);
        i.map(|i| self.order.remove(i)).is_some()
    }
    fn touch(&mut self, k: u8) {
        if let Some(i) = self.newest(k) {
            let e = self.order.remove(i);
            self.order.push(e);
        }
    }
    /// The values of the holders of `k`, newest push first.
    fn holders(&self, k: u8) -> Vec<u16> {
        let mut h: Vec<(u64, u16)> = self.order.iter().filter(|e| e.0 == k).map(|e| (e.2, e.1)).collect();
        h.sort_by_key(|a| std::cmp::Reverse(a.0));
        h.into_iter().map(|e| e.1).collect()
    }
}

fn matches_of<const CAP: usize>(t: &Table<u8, u16, CAP>, k: u8, m: usize) -> Vec<u16> {
    fn go<const CAP: usize, const M: usize>(t: &Table<u8, u16, CAP>, k: u8) -> Vec<u16> {
        let (out, n) = t.matches::<M>(&k);
        assert_eq!(
            out.iter().flatten().count(),
            n,
            "matches reports a count that is not what it stored"
        );
        out.iter().flatten().copied().collect()
    }
    match m {
        0 => go::<CAP, 0>(t, k),
        1 => go::<CAP, 1>(t, k),
        2 => go::<CAP, 2>(t, k),
        3 => go::<CAP, 3>(t, k),
        4 => go::<CAP, 4>(t, k),
        _ => go::<CAP, 5>(t, k),
    }
}

/// The table as the models see it: the entry at each array position, the entries oldest first, and `len`.
fn view<const CAP: usize>(t: &Table<u8, u16, CAP>) -> (String, Vec<(u8, u16)>) {
    let slots: Vec<String> = (0..CAP)
        .map(|i| t.at_index(i).map_or("[]".to_owned(), |(k, v)| format!("[{k},{v}]")))
        .collect();
    let order: Vec<(u8, u16)> = t.iter().map(|(k, v)| (*k, *v)).collect();
    let o: Vec<String> = order.iter().map(|(k, v)| format!("[{k},{v}]")).collect();
    (
        format!(
            r#"{{"slots":[{}],"order":[{}],"len":{}}}"#,
            slots.join(","),
            o.join(","),
            t.len()
        ),
        order,
    )
}

fn list(v: &[u16]) -> String {
    format!("[{}]", v.iter().map(ToString::to_string).collect::<Vec<_>>().join(","))
}

/// What a set of runs exercised.
#[derive(Default)]
struct Seen {
    evicted: u32,
    refused_room: u32,
    refused_dup: u32,
    cut: u32,
    most_holders: usize,
    removed_mid_chain: u32,
    shared_chain: u32,
    pair_removed: u32,
    touched_dup: u32,
    removed_dup: u32,
    cleared: u32,
}

fn run<const CAP: usize>(rng: &mut SplitMix64, out: &mut String, id: u32, steps: u32, seen: &mut Seen) {
    let seed = match rng.next_u64() % 8 {
        0 => 0,
        1 => u64::MAX,
        _ => rng.next_u64(),
    };
    let mut t: Table<u8, u16, CAP> = Table::new(seed);
    let mut naive = Naive::default();
    let space = (2 * CAP + 2).min(24) as u8;
    let hot = (CAP as u8).clamp(1, 3);
    let (v, _) = view(&t);
    let _ = writeln!(out, r#"{{"t":"cota","run":{id},"op":"init","n":{CAP},"v":{v}}}"#);
    let mut x = 0u16;
    for _ in 0..steps {
        let key = |rng: &mut SplitMix64| -> u8 {
            if rng.next_u64().is_multiple_of(2) {
                (rng.next_u64() % u64::from(hot)) as u8
            } else {
                (rng.next_u64() % u64::from(space)) as u8
            }
        };
        let k = key(rng);
        x = x.wrapping_add(1 + (rng.next_u64() % 3) as u16);
        let b = t.trace_bucket(&k);
        assert!(b < CAP);
        let before = view(&t).0;
        let slots_before: Vec<Option<(u8, u16)>> = (0..CAP).map(|i| t.at_index(i).map(|(a, b)| (*a, *b))).collect();
        let was_full = t.len() == CAP;
        let held = naive.newest(k).is_some();
        let mut head = format!(r#"{{"t":"cota","run":{id},"#);
        let res: String = match rng.next_u64() % 100 {
            0..=27 => {
                let ev = t.insert(k, x);
                let want = naive.insert(CAP, k, x);
                assert_eq!(ev, want, "insert: another entry evicted");
                if ev.is_some() {
                    assert!(was_full && !held);
                    seen.evicted += 1;
                }
                let o = ev.map_or("[]".to_owned(), |(a, b)| format!("[{a},{b}]"));
                format!(r#""op":"insert","k":{k},"x":{x},"b":{b},"out":{o}"#)
            }
            28..=39 => {
                let ok = t.insert_room(k, x);
                assert_eq!(ok, naive.room(CAP, k, x), "insert_room differs");
                if !ok {
                    seen.refused_room += 1;
                    assert!(was_full && !held);
                    assert_eq!(view(&t).0, before, "a refused insert_room changed the table");
                }
                format!(r#""op":"room","k":{k},"x":{x},"b":{b},"ok":{ok}"#)
            }
            40..=57 => {
                let ok = t.insert_dup(k, x);
                assert_eq!(ok, naive.dup(CAP, k, x), "insert_dup differs");
                if !ok {
                    seen.refused_dup += 1;
                    assert!(was_full);
                    assert_eq!(view(&t).0, before, "a refused insert_dup changed the table");
                }
                format!(r#""op":"dup","k":{k},"x":{x},"b":{b},"ok":{ok}"#)
            }
            58..=68 => {
                let shared = (0..CAP)
                    .filter(|i| {
                        t.at_index(*i)
                            .is_some_and(|(kk, _)| *kk != k && t.trace_bucket(kk) == b)
                    })
                    .count();
                let r = t.remove(&k);
                assert_eq!(r, naive.remove(k), "remove differs");
                if r.is_some() {
                    seen.removed_mid_chain += u32::from(shared > 0);
                    seen.removed_dup += u32::from(naive.holders(k).len() > 1);
                }
                let o = r.map_or("[]".to_owned(), |v| format!("[{v}]"));
                format!(r#""op":"remove","k":{k},"b":{b},"out":{o}"#)
            }
            69..=76 => {
                // a value the key holds, when it holds any
                let hs = naive.holders(k);
                let v = if hs.is_empty() || rng.next_u64().is_multiple_of(5) {
                    x
                } else {
                    hs[(rng.next_u64() % hs.len() as u64) as usize]
                };
                let ok = t.remove_pair(&k, &v);
                assert_eq!(ok, naive.remove_pair(k, v), "remove_pair differs");
                seen.pair_removed += u32::from(ok);
                format!(r#""op":"rempair","k":{k},"x":{v},"b":{b},"ok":{ok}"#)
            }
            77..=84 => {
                let n = naive.holders(k).len();
                t.touch(&k);
                naive.touch(k);
                seen.touched_dup += u32::from(n > 1);
                format!(r#""op":"touch","k":{k},"b":{b}"#)
            }
            85..=91 => {
                let g = t.get(&k).copied();
                assert_eq!(g, naive.holders(k).first().copied(), "get differs");
                assert_eq!(t.contains(&k), g.is_some());
                let o = g.map_or("[]".to_owned(), |v| format!("[{v}]"));
                format!(r#""op":"get","k":{k},"b":{b},"out":{o}"#)
            }
            92..=98 => {
                let m = (rng.next_u64() % 6) as usize;
                let got = matches_of(&t, k, m);
                let hs = naive.holders(k);
                assert_eq!(
                    got,
                    hs[..m.min(hs.len())],
                    "matches::<{m}> is not the first {m} holders, newest push first"
                );
                if hs.len() > m {
                    seen.cut += 1;
                }
                format!(r#""op":"matches","k":{k},"b":{b},"m":{m},"out":{}"#, list(&got))
            }
            _ => {
                t.clear();
                naive = Naive::default();
                seen.cleared += 1;
                r#""op":"clear""#.to_owned()
            }
        };
        // the table is the naive one, and no entry moved
        let (v, order) = view(&t);
        let want: Vec<(u8, u16)> = naive.order.iter().map(|e| (e.0, e.1)).collect();
        assert_eq!(order, want, "the order differs from the naive table");
        assert_eq!(t.len(), want.len());
        assert!(t.len() <= CAP, "the table holds more than its capacity");
        for kk in 0..space {
            let hs = naive.holders(kk);
            assert_eq!(t.get(&kk).copied(), hs.first().copied());
            assert_eq!(t.contains(&kk), !hs.is_empty());
            assert_eq!(matches_of(&t, kk, 5), hs[..hs.len().min(5)]);
            seen.most_holders = seen.most_holders.max(hs.len());
            assert_eq!(t.index_of(&kk).is_some(), !hs.is_empty());
            if let Some(i) = t.index_of(&kk) {
                assert_eq!(t.at_index(i).map(|(a, _)| *a), Some(kk));
            }
        }
        // an entry that stays keeps its array position: at most one position changes its key (the entry that left, or
        // the one an eviction replaced), none in a call that removes nothing, and a value changes only in place
        let mut left = 0;
        for i in 0..CAP {
            match (slots_before[i], t.at_index(i)) {
                (Some(s), Some(n)) if s.0 == *n.0 => {
                    assert!(
                        s.1 == *n.1 || res.contains(r#""op":"insert""#) || res.contains(r#""op":"room""#),
                        "{res}"
                    );
                }
                (Some(_), _) => left += 1,
                _ => {}
            }
        }
        assert!(
            left <= 1 || res.contains(r#""op":"clear""#),
            "{res}: {left} entries moved"
        );
        if left == 1 && !res.contains(r#""op":"clear""#) {
            assert!(
                ["insert", "remove", "rempair"]
                    .iter()
                    .any(|o| res.contains(&format!(r#""op":"{o}""#))),
                "{res}"
            );
        }
        for i in 0..CAP {
            if let Some((a, _)) = t.at_index(i) {
                let bb = t.trace_bucket(a);
                seen.shared_chain += u32::from(
                    (0..CAP).any(|j| j != i && t.at_index(j).is_some_and(|(c, _)| t.trace_bucket(c) == bb && c != a)),
                );
            }
        }
        let at = t.index_of(&k).map_or(-1, |i| i as i64);
        head.push_str(&res);
        let _ = writeln!(out, r#"{head},"at":{at},"v":{v}}}"#);
    }
}

#[test]
fn the_table_matches_the_models() {
    let mut rng = SplitMix64::new(0x7461_0001);
    let mut out = String::new();
    let mut seen = Seen::default();
    let mut id = 0;
    for round in 0..14 {
        id += 1;
        run::<1>(&mut rng, &mut out, id, 40, &mut seen);
        id += 1;
        run::<2>(&mut rng, &mut out, id, 60, &mut seen);
        id += 1;
        run::<3>(&mut rng, &mut out, id, 70, &mut seen);
        id += 1;
        run::<4>(&mut rng, &mut out, id, 80, &mut seen);
        id += 1;
        run::<8>(&mut rng, &mut out, id, 100, &mut seen);
        if round < 6 {
            id += 1;
            run::<16>(&mut rng, &mut out, id, 140, &mut seen);
        }
    }
    assert!(seen.evicted > 0, "the table never evicted");
    assert!(
        seen.refused_room > 0 && seen.refused_dup > 0,
        "no insert_room or insert_dup met a full table"
    );
    assert!(seen.cut > 0, "no matches call met more holders than it takes");
    assert!(
        seen.most_holders >= 5,
        "no key had five holders (most: {})",
        seen.most_holders
    );
    assert!(seen.removed_mid_chain > 0, "no removal left another key in its chain");
    assert!(seen.shared_chain > 0, "no two keys shared a chain");
    assert!(seen.pair_removed > 0 && seen.touched_dup > 0 && seen.removed_dup > 0 && seen.cleared > 0);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("core_table.ndjson"), &out).unwrap();
    }
}
