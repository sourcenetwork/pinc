//! Trace generation for the bounded tables: seeded random runs of the real `Table` and `Cache` through their public API,
//! recorded as ndjson (`connect_table.ndjson`) for the TLA+ trace check (`TraceConnectTable.tla`) and the Lean replay
//! (`Vinc/TraceConnectTable.lean`).
//!
//! A run is one table (or cache) of a small capacity `N` and `N + 2` keys. The bucket of every key is read with
//! `bucket_of` and recorded first, so the checkers use the hash of the real code: the node ids are searched so that the
//! buckets collide, wrap around the end of the array and fill it. Operations: insert (new key, known key, full table),
//! remove, and retain with the predicate "the value is odd" (the predicate's calls are counted, and every entry must be
//! visited). After every operation the table's entries in slot order (`iter`) are recorded. The test compares everything
//! with a plain map and checks the entries it holds.
//! The trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    unreachable_pub
)]

mod connect_common;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use connect_common::nid;
use vinc_connect::relay::table::{Cache, Table};
use vinc_tests::SplitMix64;

fn slots_json<'a>(it: impl Iterator<Item = (&'a vinc_crypto::NodeId, &'a u32)>) -> String {
    let parts: Vec<String> = it.map(|(k, v)| format!("[{},{v}]", k.bytes[0])).collect();
    format!("[{}]", parts.join(","))
}

fn run_table<const N: usize>(seed: u64, out: &mut Vec<String>) {
    let mut rng = SplitMix64::new(seed);
    let mut t: Table<u32, N> = Table::new(seed);
    let keys = N as u8 + 2;
    out.push(format!(r#"{{"t":"tbnew","n":{N}}}"#));
    for k in 1..=keys {
        out.push(format!(r#"{{"t":"tbk","k":{k},"b":{}}}"#, t.bucket_of(&nid(k))));
    }
    let mut m: BTreeMap<u8, u32> = BTreeMap::new();
    for _ in 0..120 {
        let k = (rng.next_u64() % u64::from(keys)) as u8 + 1;
        let line = match rng.next_u64() % 6 {
            0..=2 => {
                let v = (rng.next_u64() % 9) as u32 + 1;
                let r = t.insert(nid(k), v);
                if m.contains_key(&k) || m.len() < N {
                    assert_eq!(r, Ok(m.insert(k, v)));
                    format!(
                        r#"{{"t":"tins","k":{k},"v":{v},"res":"ok","old":{}}}"#,
                        r.unwrap().unwrap_or(0)
                    )
                } else {
                    assert_eq!(r, Err(v));
                    format!(r#"{{"t":"tins","k":{k},"v":{v},"res":"full","old":0}}"#)
                }
            }
            3 | 4 => {
                let want = m.remove(&k);
                let got = t.remove(&nid(k));
                assert_eq!(got, want);
                format!(
                    r#"{{"t":"trem","k":{k},"found":{},"v":{}}}"#,
                    got.is_some(),
                    got.unwrap_or(0)
                )
            }
            _ => {
                let mut seen = BTreeSet::new();
                t.retain(|key, v| {
                    seen.insert(key.bytes[0]);
                    *v % 2 == 1
                });
                for key in m.keys() {
                    assert!(seen.contains(key), "retain skipped an entry");
                }
                m.retain(|_, v| *v % 2 == 1);
                let vis: Vec<String> = seen.iter().map(ToString::to_string).collect();
                format!(r#"{{"t":"tret","vis":[{}]}}"#, vis.join(","))
            }
        };
        assert_eq!(t.len(), m.len());
        let held: BTreeMap<u8, u32> = t.iter().map(|(key, v)| (key.bytes[0], *v)).collect();
        assert_eq!(held, m);
        for key in 1..=keys {
            assert_eq!(t.get(&nid(key)).copied(), m.get(&key).copied());
        }
        out.push(line);
        out.push(format!(r#"{{"t":"tslots","s":{}}}"#, slots_json(t.iter())));
    }
}

fn run_cache<const N: usize>(seed: u64, out: &mut Vec<String>) {
    let mut rng = SplitMix64::new(seed);
    let mut c: Cache<u32, N> = Cache::new(seed);
    let keys = N as u8 + 2;
    out.push(format!(r#"{{"t":"knew","n":{N}}}"#));
    for k in 1..=keys {
        out.push(format!(r#"{{"t":"tbk","k":{k},"b":{}}}"#, c.bucket_of(&nid(k))));
    }
    let mut occupant: BTreeMap<usize, (u8, u32)> = BTreeMap::new();
    for _ in 0..120 {
        let k = (rng.next_u64() % u64::from(keys)) as u8 + 1;
        if rng.next_u64().is_multiple_of(2) {
            let v = (rng.next_u64() % 9) as u32 + 1;
            c.put(nid(k), v);
            occupant.insert(c.bucket_of(&nid(k)), (k, v));
            out.push(format!(r#"{{"t":"kput","k":{k},"v":{v}}}"#));
        } else {
            let want = occupant
                .get(&c.bucket_of(&nid(k)))
                .filter(|(o, _)| *o == k)
                .map(|(_, v)| *v);
            let got = c.get(&nid(k)).copied();
            assert_eq!(got, want);
            out.push(format!(
                r#"{{"t":"kget","k":{k},"hit":{},"v":{}}}"#,
                got.is_some(),
                got.unwrap_or(0)
            ));
        }
    }
}

#[test]
fn the_tables_match_a_map_and_record_their_trace() {
    let mut out = Vec::new();
    for seed in 0..60u64 {
        match seed % 6 {
            0 => run_table::<1>(seed, &mut out),
            1 => run_table::<2>(seed, &mut out),
            2 => run_table::<3>(seed, &mut out),
            3 => run_table::<4>(seed, &mut out),
            4 => run_table::<5>(seed, &mut out),
            _ => run_table::<8>(seed, &mut out),
        }
        match seed % 3 {
            0 => run_cache::<2>(seed, &mut out),
            1 => run_cache::<3>(seed, &mut out),
            _ => run_cache::<5>(seed, &mut out),
        }
    }
    let Some(dir) = std::env::var_os("VINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    let mut text = String::new();
    for l in &out {
        writeln!(text, "{l}").unwrap();
    }
    std::fs::write(dir.join("connect_table.ndjson"), text).unwrap();
}
