//! Trace generation for the values layer's tables and the roots a node serves: a real `Net` of `pinc-node` (built with
//! the `trace` feature) through the probe `values_net::probe`, and a real node over the scripted endpoint of
//! `node_script.rs`, recorded as ndjson (`node_values_net.ndjson`) for the TLA+ trace check
//! (`TraceNodeValuesNet.tla`).
//!
//! The probe fills all but a window of 2 slots of the provider table and all but 2 streams of the stream table with
//! fillers that are never given back, so what is left behaves as tables of 2; every number written is relative to the
//! first one past the fillers. A boundary script drives both tables to their limits (a fetch refused whole, a stream
//! refused by the full stream table and by the full provider table, a hole below a slot in use, the table trimming to
//! empty), and 40 seeded runs of 60 calls follow. `next_fetch_id` is recorded over `u32` ids as two 16-bit limbs around
//! 0 and the wrap, and over 200 seeded cases. The roots run drives `values_provide` and `values_unprovide` of a node
//! whose set of roots holds all but 2 places by fillers.
//!
//! The test checks without the model: after every call the window has at most 2 slots, the last slot is not free,
//! each slot's use count is the number of its holders (the streams of its number and the places in the running
//! fetches' lists), and at most 2 streams are held; a refused fetch changes nothing but the count, a refused stream
//! changes nothing, a fetch done as it starts changes nothing; `next_fetch_id` is never 0 or a running id; a provide
//! answers true exactly when the root is registered afterwards and an unprovide answers whether it was.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::cognitive_complexity,
    unreachable_pub,
    clippy::assert_is_empty,
    clippy::assertions_on_constants,
    clippy::match_same_arms,
    clippy::unused_self
)]

mod node_script;

use std::collections::BTreeSet;
use std::fmt::Write as _;

use node_script::{ScriptNode, node_with};
use pinc_node::values_net_probe::{NetProbe, NetView, TABLE_MAX_PROBE, next_fetch_id};
use pinc_node::{Enabled, PROVIDED_MAX};
use pinc_tests::{LayerApps, SplitMix64};

/// The window of the tables.
const W: usize = 2;

/// Peer `k`: byte 0 is 0x0A (the fillers' is 0xF0), the others `k`.
fn peer(k: u32) -> [u8; 32] {
    let mut id = [k as u8; 32];
    id[0] = 0x0A;
    id
}

/// The number of a peer made by [`peer`].
fn index(id: &[u8; 32]) -> u32 {
    u32::from(id[1])
}

fn peers(ks: &[u32]) -> Vec<[u8; 32]> {
    ks.iter().map(|k| peer(*k)).collect()
}

fn view_json(v: &NetView) -> String {
    let provs: Vec<String> = v
        .provs
        .iter()
        .map(|s| match s {
            Some((p, u)) => format!(r#"{{"peer":{},"uses":{u}}}"#, index(p)),
            None => r#"{"peer":0,"uses":0}"#.to_owned(),
        })
        .collect();
    let streams: Vec<String> = v
        .streams
        .iter()
        .map(|(l, p, o)| format!(r#"{{"lid":{l},"prov":{p},"owner":{o}}}"#))
        .collect();
    let held: Vec<String> = v
        .held
        .iter()
        .map(|(f, ps)| {
            let ps: Vec<String> = ps.iter().map(u32::to_string).collect();
            format!(r#"{{"f":{f},"ps":[{}]}}"#, ps.join(","))
        })
        .collect();
    format!(
        r#"{{"provs":[{}],"streams":[{}],"held":[{}],"refused":{},"next":{}}}"#,
        provs.join(","),
        streams.join(","),
        held.join(","),
        v.refused,
        v.next
    )
}

/// The tables apart from the count of refusals.
fn same_tables(a: &NetView, b: &NetView) -> bool {
    (&a.provs, &a.streams, &a.held, a.next) == (&b.provs, &b.streams, &b.held, b.next)
}

/// One run of the probe: every call, the checks and the record.
struct Run {
    p: NetProbe,
    out: String,
}

impl Run {
    fn new() -> Self {
        assert!(W < TABLE_MAX_PROBE);
        let p = NetProbe::new(W);
        let mut r = Self { p, out: String::new() };
        let v = r.p.view();
        r.check(&v);
        let _ = writeln!(r.out, r#"{{"t":"vnet","op":"init","w":{W},"v":{}}}"#, view_json(&v));
        r
    }

    /// The properties every state of the window has.
    fn check(&self, v: &NetView) {
        assert!(v.provs.len() <= W, "the provider table passed its window");
        assert!(v.provs.last().is_none_or(Option::is_some), "the last slot is free");
        assert!(v.streams.len() <= W, "the stream table passed its window");
        for (_, p, _) in &v.streams {
            assert!(
                v.provs.get(*p as usize).is_some_and(Option::is_some),
                "a stream names a free slot"
            );
        }
        for (k, s) in v.provs.iter().enumerate() {
            let uses = s.map_or(0, |s| s.1 as usize);
            let by_streams = v.streams.iter().filter(|x| x.1 as usize == k).count();
            let by_fetches = v.held.iter().flat_map(|h| &h.1).filter(|n| **n as usize == k).count();
            assert_eq!(uses, by_streams + by_fetches, "slot {k}: its uses are not its holders");
        }
    }

    fn emit(&mut self, op: &str, fields: &str, v: &NetView) {
        let _ = writeln!(self.out, r#"{{"t":"vnet","op":"{op}"{fields},"v":{}}}"#, view_json(v));
    }

    fn start(&mut self, f: u32, ps: &[u32]) -> bool {
        let before = self.p.view();
        let ok = self.p.start(f, &peers(ps));
        let after = self.p.view();
        self.check(&after);
        if ok {
            assert!(
                after.held.iter().any(|h| h.0 == f),
                "a fetch that started holds nothing"
            );
            assert_eq!(after.refused, before.refused);
        } else {
            assert!(same_tables(&before, &after), "a refused fetch changed the tables");
            assert_eq!(after.refused, before.refused + 1, "a refused fetch was not counted");
        }
        let list: Vec<String> = ps.iter().map(u32::to_string).collect();
        self.emit(
            "start",
            &format!(r#","f":{f},"peers":[{}],"ok":{ok}"#, list.join(",")),
            &after,
        );
        ok
    }

    fn start_done(&mut self, ps: &[u32]) -> bool {
        let before = self.p.view();
        let ok = self.p.start_done(&peers(ps));
        let after = self.p.view();
        self.check(&after);
        assert!(
            same_tables(&before, &after),
            "a fetch done as it starts changed the tables"
        );
        assert_eq!(after.refused, before.refused + u64::from(!ok));
        let list: Vec<String> = ps.iter().map(u32::to_string).collect();
        self.emit(
            "startdone",
            &format!(r#","peers":[{}],"ok":{ok}"#, list.join(",")),
            &after,
        );
        ok
    }

    fn end(&mut self, f: u32) {
        self.p.end(f);
        let after = self.p.view();
        self.check(&after);
        assert!(after.held.iter().all(|h| h.0 != f), "an ended fetch still holds");
        self.emit("end", &format!(r#","f":{f}"#), &after);
    }

    fn serve(&mut self, k: u32) -> u64 {
        let before = self.p.view();
        let lid = self.p.serve(&peer(k));
        let after = self.p.view();
        self.check(&after);
        if lid == 0 {
            assert!(same_tables(&before, &after), "a refused stream changed the tables");
        } else {
            assert!(after.streams.iter().any(|s| s.0 == lid && s.2 == 0));
        }
        self.emit("serve", &format!(r#","p":{k},"lid":{lid}"#), &after);
        lid
    }

    fn open(&mut self, f: u32, k: usize) -> u64 {
        let before = self.p.view();
        let lid = self.p.open(f, k);
        let after = self.p.view();
        self.check(&after);
        if lid == 0 {
            assert!(same_tables(&before, &after), "a refused stream changed the tables");
        } else {
            assert!(after.streams.iter().any(|s| s.0 == lid && s.2 == f));
        }
        self.emit("open", &format!(r#","f":{f},"k":{k},"lid":{lid}"#), &after);
        lid
    }

    fn drop_stream(&mut self, lid: u64) -> bool {
        let before = self.p.view();
        let ok = self.p.drop(lid);
        let after = self.p.view();
        self.check(&after);
        assert_eq!(ok, before.streams.iter().any(|s| s.0 == lid));
        if !ok {
            assert!(
                same_tables(&before, &after),
                "a drop of an unknown stream changed the tables"
            );
        }
        self.emit("drop", &format!(r#","lid":{lid},"ok":{ok}"#), &after);
        ok
    }
}

/// The boundary script: both tables at their limits, a hole, and the table trimmed to empty.
fn boundary() -> String {
    let mut r = Run::new();
    assert!(r.start(1, &[1]));
    assert!(r.start(2, &[2]));
    assert!(!r.start(3, &[3]), "a fetch to a full provider table was taken");
    assert!(!r.start(3, &[1, 3]), "a fetch the table cannot hold whole was taken");
    assert_eq!(r.p.view().refused, 2);
    assert!(r.start(3, &[1, 1]));
    r.end(3);
    let (a, b) = (r.open(1, 1), r.open(2, 1));
    assert!(a != 0 && b != 0);
    assert_eq!(r.open(1, 1), 0, "a stream was taken past the full stream table");
    assert_eq!(r.serve(1), 0, "a served stream was taken past the full stream table");
    assert_eq!(r.serve(3), 0, "a served stream was taken past the full provider table");
    assert!(r.drop_stream(a));
    r.end(1);
    let v = r.p.view();
    assert!(
        v.provs.first().is_some_and(Option::is_none) && v.provs.get(1).is_some_and(Option::is_some),
        "no hole below a slot in use"
    );
    let c = r.serve(3);
    assert!(c != 0);
    assert_eq!(
        r.p.view().provs.first().and_then(|s| s.map(|s| index(&s.0))),
        Some(3),
        "the first free slot was not taken"
    );
    assert!(r.drop_stream(b));
    assert!(r.drop_stream(c));
    r.end(2);
    assert!(r.p.view().provs.is_empty(), "the table did not trim to empty");
    assert!(r.start_done(&[1, 2]));
    assert!(r.p.view().provs.is_empty());
    assert!(!r.drop_stream(99));
    r.out
}

/// A seeded run of 60 calls.
fn random_run(seed: u64) -> String {
    let mut rng = SplitMix64::new(seed);
    let mut r = Run::new();
    for _ in 0..60 {
        let v = r.p.view();
        let running: Vec<u32> = v.held.iter().map(|h| h.0).collect();
        let free: Vec<u32> = (1..=3).filter(|f| !running.contains(f)).collect();
        let n = 1 + (rng.next_u64() % 2) as usize;
        let ps: Vec<u32> = (0..n).map(|_| 1 + (rng.next_u64() % 3) as u32).collect();
        match rng.next_u64() % 10 {
            0..=2 if !free.is_empty() => {
                let f = free[(rng.next_u64() % free.len() as u64) as usize];
                r.start(f, &ps);
            }
            3 => {
                r.start_done(&ps);
            }
            4 | 5 if !running.is_empty() => {
                r.end(running[(rng.next_u64() % running.len() as u64) as usize]);
            }
            6 => {
                r.serve(1 + (rng.next_u64() % 3) as u32);
            }
            7 if !running.is_empty() => {
                let (f, list) = &v.held[(rng.next_u64() % v.held.len() as u64) as usize];
                let k = 1 + (rng.next_u64() % list.len().max(1) as u64) as usize;
                r.open(*f, k);
            }
            8 | 9 if !v.streams.is_empty() => {
                let lid = if rng.next_u64().is_multiple_of(10) {
                    5000 + rng.next_u64() % 100
                } else {
                    v.streams[(rng.next_u64() % v.streams.len() as u64) as usize].0
                };
                r.drop_stream(lid);
            }
            _ => {
                r.serve(1 + (rng.next_u64() % 3) as u32);
            }
        }
    }
    r.out
}

/// A `u32` as two 16-bit limbs, high first.
fn limbs(v: u32) -> String {
    format!("[{},{}]", v >> 16, v & 0xFFFF)
}

/// `next_fetch_id` after `last` with `running` (id 0 dropped), recorded.
fn next_id_line(out: &mut String, last: u32, running: &[u32]) {
    let running: Vec<u32> = running.iter().copied().filter(|r| *r != 0).collect();
    let id = next_fetch_id(last, &running);
    assert!(id != 0 && !running.contains(&id), "a fetch id is 0 or running");
    let list: Vec<String> = running.iter().map(|r| limbs(*r)).collect();
    let _ = writeln!(
        out,
        r#"{{"t":"vnet","op":"nextid","last":{},"running":[{}],"id":{}}}"#,
        limbs(last),
        list.join(","),
        limbs(id)
    );
}

fn next_ids() -> String {
    let mut out = String::new();
    for last in [0u32, 1, 0xFFFF, 0x1_0000, 0xFFFF_FFFE, 0xFFFF_FFFF] {
        let n1 = last.wrapping_add(1);
        let n2 = last.wrapping_add(2);
        let sets: [&[u32]; 5] = [&[], &[1], &[1, 2], &[n1], &[n1, n2, 1]];
        for running in sets {
            next_id_line(&mut out, last, running);
        }
    }
    let mut rng = SplitMix64::new(0x6e65_7869);
    for _ in 0..200 {
        let last = rng.next_u64() as u32;
        let n = (rng.next_u64() % 5) as usize;
        let running: Vec<u32> = (0..n).map(|_| last.wrapping_add((rng.next_u64() % 6) as u32)).collect();
        next_id_line(&mut out, last, &running);
    }
    out
}

/// The root `[r; 32]` of the roots run.
fn root(r: u32) -> [u8; 32] {
    [r as u8; 32]
}

/// A filler root, which no `root` collides with.
fn filler_root(j: usize) -> [u8; 32] {
    let mut id = [0u8; 32];
    id[0] = 0xF0;
    id[1] = j as u8;
    id[2] = (j >> 8) as u8;
    id
}

type RootsNode = ScriptNode<LayerApps>;

/// `values_provide` of root `r`, checked against the registered window roots `reg` and recorded.
fn provide(node: &mut RootsNode, out: &mut String, reg: &mut BTreeSet<u32>, r: u32) -> bool {
    let ok = node.values_provide(&root(r));
    assert_eq!(
        ok,
        reg.contains(&r) || reg.len() < W,
        "a provide answered false with room, or true without"
    );
    if ok {
        reg.insert(r);
    }
    let _ = writeln!(out, r#"{{"t":"vnet","op":"provide","r":{r},"ok":{ok}}}"#);
    ok
}

/// `values_unprovide` of root `r`, checked and recorded.
fn unprovide(node: &mut RootsNode, out: &mut String, reg: &mut BTreeSet<u32>, r: u32) -> bool {
    let ok = node.values_unprovide(&root(r));
    assert_eq!(
        ok,
        reg.remove(&r),
        "an unprovide did not answer whether the root was registered"
    );
    let _ = writeln!(out, r#"{{"t":"vnet","op":"unprovide","r":{r},"ok":{ok}}}"#);
    ok
}

/// The roots a node serves, over a window of 2 past the fillers.
fn roots_run() -> String {
    let mut out = String::new();
    let enabled = Enabled {
        values: true,
        ..Enabled::NONE
    };
    let mut node = node_with(false, &[], b"t", LayerApps::new(1, enabled)).unwrap();
    for j in 0..PROVIDED_MAX - W {
        assert!(node.values_provide(&filler_root(j)), "a filler root was refused");
    }
    let _ = writeln!(out, r#"{{"t":"vnet","op":"pinit","w":{W}}}"#);
    let mut reg = BTreeSet::new();
    assert!(provide(&mut node, &mut out, &mut reg, 1));
    assert!(provide(&mut node, &mut out, &mut reg, 2));
    assert!(!provide(&mut node, &mut out, &mut reg, 3));
    assert!(provide(&mut node, &mut out, &mut reg, 1));
    assert!(!unprovide(&mut node, &mut out, &mut reg, 3));
    assert!(unprovide(&mut node, &mut out, &mut reg, 1));
    assert!(provide(&mut node, &mut out, &mut reg, 3));
    let mut rng = SplitMix64::new(0x726f_6f74);
    for _ in 0..100 {
        let r = 1 + (rng.next_u64() % 3) as u32;
        if rng.next_u64().is_multiple_of(2) {
            provide(&mut node, &mut out, &mut reg, r);
        } else {
            unprovide(&mut node, &mut out, &mut reg, r);
        }
    }
    out
}

/// A thread with the stack a node needs.
fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn the_values_tables_and_the_roots_match_the_models() {
    let mut out = boundary();
    for seed in 1..=40u64 {
        out.push_str(&random_run(seed));
    }
    out.push_str(&next_ids());
    out.push_str(&big(roots_run));
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("node_values_net.ndjson"), &out).unwrap();
    }
}
