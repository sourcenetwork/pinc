//! Trace generation for the held-address flag of a connection's paths (`pinc-transport`, built with the `trace`
//! feature): real connected and unconnected clients (4 path slots) driven through `add_path`, `remove_path` and
//! `set_path_held` with tracked and untracked ids and both flags, recorded as ndjson (`path_held.ndjson`) for the
//! TLA+ trace check (`TracePathHeld.tla`).
//!
//! After every call the client shows what `trace_held_paths` reads (the count `Paths::held` and every slot as its id
//! in four 16-bit limbs and its flag, or nothing) with `has_held_paths`. Each run is a boundary sequence (a flag for
//! an untracked path, a full table, a held path removed or replaced) and 60 seeded calls; the runs of even seeds are
//! connected first.
//!
//! The test asserts the rules itself (the count is the recount of the flags, `has_held_paths` is whether it is above
//! zero, no id is in two slots, `set_path_held` changes one flag or nothing, and the other calls only empty slots or
//! put a new path, flag clear, in one), so it is meaningful without the proof tools. The trace is written to
//! `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    unreachable_pub,
    clippy::manual_is_multiple_of,
    clippy::similar_names
)]

use std::fmt::Write as _;

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::{PathId, PathInfo};

/// The path ids the seeded calls draw from.
const IDS: [u64; 7] = [1, 2, 3, 4, 5, 6, 1 << 40];

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    fell: bool,
    untracked_set: bool,
}

/// The slots of a client: its count of held paths and each slot's `(id, held)`.
type Slots = (usize, Vec<Option<(u64, bool)>>);

/// The path id as four little-endian 16-bit limbs.
fn limbs4(id: u64) -> String {
    format!(
        "[{},{},{},{}]",
        id & 0xffff,
        (id >> 16) & 0xffff,
        (id >> 32) & 0xffff,
        id >> 48
    )
}

/// The client as the model sees it.
fn view(net: &Net<'_, '_>) -> String {
    let (held, slots) = net.a.conn.trace_held_paths();
    let s: Vec<String> = slots
        .iter()
        .map(|s| s.map_or_else(|| "[]".to_owned(), |(id, f)| format!("[{},{f}]", limbs4(id))))
        .collect();
    format!(
        r#"{{"held":{held},"has":{},"slots":[{}]}}"#,
        net.a.conn.has_held_paths(),
        s.join(",")
    )
}

/// The rules every state keeps.
fn consistent(net: &Net<'_, '_>) -> Slots {
    let (held, slots) = net.a.conn.trace_held_paths();
    assert_eq!(slots.len(), 4);
    assert_eq!(
        held,
        slots.iter().flatten().filter(|s| s.1).count(),
        "the count is not the recount"
    );
    assert_eq!(net.a.conn.has_held_paths(), held > 0);
    let mut ids: Vec<u64> = slots.iter().flatten().map(|s| s.0).collect();
    let listed: Vec<u64> = net.a.conn.path_list().map(|(id, _, _)| id.0).collect();
    let (mut a, mut b) = (ids.clone(), listed);
    a.sort_unstable();
    b.sort_unstable();
    assert_eq!(a, b, "path_list is not the occupied slots");
    ids.sort_unstable();
    ids.dedup();
    assert_eq!(ids.len(), slots.iter().flatten().count(), "an id is in two slots");
    (held, slots)
}

struct Run<'a, 'w, 'x> {
    net: Net<'w, 'x>,
    out: &'a mut String,
    seen: &'a mut Seen,
}

impl Run<'_, '_, '_> {
    fn log(&mut self, body: &str) {
        let v = view(&self.net);
        let _ = writeln!(self.out, r#"{{"t":"path_held",{body},"v":{v}}}"#);
    }

    fn add(&mut self, p: u64) {
        let before = consistent(&self.net);
        let now = self.net.now;
        let r = self
            .net
            .a
            .with_env(now, |c, env| c.add_path(env, PathId(p), PathInfo::default()));
        self.other(&before);
        self.log(&format!(
            r#""op":"add","id":{},"r":"{}""#,
            limbs4(p),
            if r.is_ok() { "ok" } else { "err" }
        ));
    }

    fn remove(&mut self, p: u64) {
        let before = consistent(&self.net);
        let r = self.net.a.conn.remove_path(PathId(p));
        self.other(&before);
        self.log(&format!(
            r#""op":"remove","id":{},"r":"{}""#,
            limbs4(p),
            if r.is_ok() { "ok" } else { "err" }
        ));
    }

    /// An `add` or `remove` only empties slots or puts a new path, flag clear, in one.
    fn other(&mut self, before: &Slots) {
        let after = consistent(&self.net);
        let tracked: Vec<u64> = before.1.iter().flatten().map(|s| s.0).collect();
        for (a, b) in after.1.iter().zip(&before.1) {
            assert!(
                a == b || a.is_none() || a.is_some_and(|(id, f)| !f && !tracked.contains(&id)),
                "a call changed a slot it should not have"
            );
        }
        self.seen.fell |= after.0 < before.0;
    }

    fn set(&mut self, p: u64, h: bool) {
        let before = consistent(&self.net);
        self.net.a.conn.set_path_held(PathId(p), h);
        let after = consistent(&self.net);
        match before.1.iter().position(|s| s.is_some_and(|s| s.0 == p)) {
            None => {
                assert_eq!(after, before, "a flag for an untracked path changed something");
                self.seen.untracked_set = true;
            }
            Some(k) => {
                let mut want = before.1.clone();
                want[k] = Some((p, h));
                assert_eq!(after.1, want, "a flag changed more than its slot");
            }
        }
        self.log(&format!(r#""op":"set","id":{},"h":{h}"#, limbs4(p)));
    }
}

fn run(out: &mut String, seen: &mut Seen, rng: &mut SplitMix64, seed: u64) {
    let mut w = World::new(IdentityAlg::Ed25519);
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, Params::new(10 * MS)));
    let mut r = Run { net, out, seen };
    r.log(r#""op":"init""#);
    if seed % 2 == 0 {
        let deadline = r.net.now + 10_000 * MS;
        assert!(r.net.connect(deadline), "the pair did not connect");
        r.log(r#""op":"drive""#);
    }
    // the boundary sequence
    r.set(1, true);
    r.set(1, true);
    r.set(9, true);
    r.set(1, false);
    r.set(1, true);
    r.add(2);
    r.add(3);
    r.add(4);
    r.set(2, true);
    r.set(3, true);
    r.add(5);
    r.add(6);
    r.remove(2);
    r.remove(1);
    r.set(5, true);
    r.remove(5);
    r.set(5, true);
    r.set(1 << 40, true);
    r.add(1 << 40);
    r.set(1 << 40, true);
    r.remove(1 << 40);
    // seeded calls
    let mut below = |n: usize| (rng.next_u64() % n as u64) as usize;
    for _ in 0..60 {
        let op = below(10);
        let p = IDS[below(7)];
        match op {
            0..=2 => r.add(p),
            3..=4 => r.remove(p),
            _ => r.set(p, below(2) == 1),
        }
    }
}

#[test]
fn the_held_flag_matches_the_model() {
    let (mut out, mut seen) = (String::new(), Seen::default());
    let mut rng = SplitMix64::traced(0x6865_6c64);
    for seed in 1..=30 {
        run(&mut out, &mut seen, &mut rng, seed);
    }
    assert!(seen.fell, "no held path left its slot");
    assert!(seen.untracked_set, "no flag was set for an untracked path");
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("path_held.ndjson"), &out).unwrap();
    }
}
