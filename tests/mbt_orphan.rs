//! Model-based tests of the endpoint's table of held first-flight fragments: a real table (`vinc-core`, built with
//! the `trace` feature) driven along every edge of the state graph of `proofs/tla/MbtOrphan.tla`.
//!
//! TLC enumerates every state the operators of `OrphanOps.tla` reach at the size of the real table within the bounds
//! of a config and writes the graph; `scripts/mbt.py` turns it into paths from the empty table that take every edge,
//! which `scripts/proofs.sh` writes to the directory `VINC_MBT_DIR`: `orphan.ndjson` from `MbtOrphan.cfg` and
//! `orphan_edge.ndjson` from `MbtOrphan_edge.cfg`. This test runs each path on a fresh `OrphanProbe`: after every call
//! the result must be the model's, and the whole table, every entry with its bytes, the order of arrival and the four
//! counters, must be the model's state. It stops at the first difference and names the file, the case, the step and
//! the calls that led there. Without `VINC_MBT_DIR` it checks nothing.
//!
//! The model's numbers stand for the code's as `MbtOrphan.tla` says: model time `t` is `origin + t * step` with
//! `step = ORPHAN_LIFE / LIFE`, so a datagram is older than the lifetime exactly when the model's is (the code
//! subtracts saturating at 0, the model's clock may step back); the origin is 0, an odd time, or the one that puts
//! the last model time on `u64::MAX`, by case. A length of at most `MAX` is one of at most `ORPHAN_MAX` bytes and
//! `MAX + 1` one of more, picked by the datagram's tag (its place in the order of arrival, which its bytes carry).
//! Key 1 is one message; key 2 differs from it in one of the destination id (its last byte), the message length (by
//! one) or the sender's port, by case. A datagram's local address carries the model time it arrived at.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    unreachable_pub
)]

use std::cmp::Ordering;
use std::fmt::Write as _;
use std::net::SocketAddr;

use vinc_core::{OrphanEntry, OrphanProbe};
use vinc_security::ConnId;
use vinc_tests::{Json, MbtCase, SplitMix64, mbt_cases};

const N: usize = OrphanProbe::SLOTS;
const MAX: usize = OrphanProbe::MAX;
const LIFE: u64 = OrphanProbe::LIFE;

/// How the model's numbers map onto the code's for one case.
struct Map {
    max: u64,
    step: u64,
    origin: u64,
    variant: u64,
}

impl Map {
    fn time(&self, t: u64) -> u64 {
        self.origin + t * self.step
    }

    /// The message `key`: the destination id, the message length and the sender.
    fn key(&self, key: u64) -> (ConnId, u64, SocketAddr) {
        let k = u8::try_from(key).unwrap();
        match self.variant {
            0 => (ConnId::new(&[1, 1, 1, k]).unwrap(), 2000, remote(1)),
            1 => (ConnId::new(&[1, 1, 1, 1]).unwrap(), 1999 + key, remote(1)),
            _ => (ConnId::new(&[1, 1, 1, 1]).unwrap(), 2000, remote(k)),
        }
    }

    /// The length of the datagram `tag` of the model length `len`.
    fn len(&self, len: u64, tag: u64) -> usize {
        match len.cmp(&self.max) {
            Ordering::Greater => MAX + 1 + (tag % 3) as usize * 250,
            Ordering::Equal => [MAX, MAX - 1, 600, 8][(tag % 4) as usize],
            Ordering::Less => 8 + len as usize,
        }
    }

    /// The entry the model's slot stands for, with its tag: `<<at, order, key, loc, len, tag>>`.
    fn entry(&self, s: &Json) -> Option<(OrphanEntry, u64)> {
        let v: Vec<u64> = s.arr().unwrap().iter().map(|x| x.u64().unwrap()).collect();
        let &[at, order, key, loc, len, tag] = v.as_slice() else {
            assert!(v.is_empty(), "a slot of the model is neither empty nor an entry: {s}");
            return None;
        };
        let (dcid, total, remote) = self.key(key);
        let e = OrphanEntry {
            at: self.time(at),
            order,
            dcid,
            total,
            local: local(loc),
            remote,
            len: self.len(len, tag),
        };
        Some((e, tag))
    }
}

fn remote(r: u8) -> SocketAddr {
    SocketAddr::from(([10, 0, 0, 1], 9000 + u16::from(r)))
}

fn local(loc: u64) -> SocketAddr {
    SocketAddr::from(([10, 1, 0, 1], 7000 + u16::try_from(loc).unwrap()))
}

/// The bytes of the datagram `tag`: the tag, then bytes that follow from it.
fn bytes_of(tag: u64, len: usize) -> Vec<u8> {
    let mut b = vec![0u8; len];
    SplitMix64::new(tag ^ 0x6f72_7068).fill(&mut b);
    b[..8].copy_from_slice(&tag.to_le_bytes());
    b
}

fn num(v: &Json) -> u64 {
    v.u64().unwrap()
}

/// The calls of `case` up to step `upto`, for a failure message.
fn calls(case: &MbtCase, upto: usize) -> String {
    let mut s = String::new();
    for (i, st) in case.steps.iter().take(upto + 1).enumerate() {
        let _ = write!(s, "\n  {i}: {st}");
    }
    s
}

/// The model's table `o` against the real one.
fn same_table(p: &OrphanProbe, o: &Json, map: &Map, at: &dyn Fn() -> String) {
    let slots = o.get("slots").and_then(Json::arr).unwrap();
    assert_eq!(
        slots.len(),
        N,
        "{}: the model's table has {} entries, the code's {N}",
        at(),
        slots.len()
    );
    for (k, s) in slots.iter().enumerate() {
        let want = map.entry(s);
        assert_eq!(
            p.slot(k),
            want.as_ref().map(|(e, _)| *e),
            "{}: entry {k} differs from the model's {s}",
            at()
        );
        let bytes = want.map_or_else(Vec::new, |(e, tag)| bytes_of(tag, e.len));
        assert!(
            p.bytes(k) == bytes.as_slice(),
            "{}: entry {k} holds other bytes than the datagram {s}",
            at()
        );
    }
    let field = |n: &str| num(o.get(n).unwrap());
    assert_eq!(
        (p.order(), p.counts()),
        (
            field("order"),
            [field("held"), field("replayed"), field("expired"), field("evicted")]
        ),
        "{}: the order or the counters (held, given out, expired, evicted) differ",
        at()
    );
    assert_eq!(
        p.waiting(),
        slots.iter().filter(|s| !s.arr().unwrap().is_empty()).count(),
        "{}: the count of datagrams held differs",
        at()
    );
}

/// Runs one case of `file` on a fresh table; returns the number of calls.
fn run(file: &str, case: &MbtCase, init: &Json, max: u64, step: u64, tmax: u64) -> usize {
    let map = Map {
        max,
        step,
        origin: [0, 5 * LIFE + 123_457, u64::MAX - tmax * step][(case.id % 3) as usize],
        variant: (case.id / 3) % 3,
    };
    let mut p = OrphanProbe::new();
    let mut before = init.get("o").unwrap();
    let who = format!("{file} case {}", case.id);
    same_table(&p, before, &map, &|| format!("{who}: the empty table"));
    let mut buf = [0u8; MAX];
    for (i, st) in case.steps.iter().enumerate() {
        let a = &st.args;
        match (st.call.as_str(), a.as_slice()) {
            ("CallHold", [t, key, len, ok]) => {
                // the datagram's tag is its place in the order of arrival: the model's order before the call
                let tag = num(before.get("order").unwrap());
                let (dcid, total, remote) = map.key(num(key));
                let n = map.len(num(len), tag);
                let got = p.hold(map.time(num(t)), dcid, total, local(num(t)), remote, &bytes_of(tag, n));
                assert_eq!(
                    Some(got),
                    ok.bool(),
                    "{who} step {i}: hold of {n} bytes returned {got}; calls:{}",
                    calls(case, i)
                );
            }
            ("CallTake", [t, key, out]) => {
                let (dcid, total, remote) = map.key(num(key));
                let got = p.take(map.time(num(t)), &dcid, total, &remote, &mut buf);
                let want = match out.arr().unwrap() {
                    [] => None,
                    [loc, len, tag] => Some((local(num(loc)), map.len(num(len), num(tag)), num(tag))),
                    _ => panic!("{who}: a take result of the model that is not <<>> or <<loc, len, tag>>"),
                };
                assert_eq!(
                    got,
                    want.map(|(l, n, _)| (l, n)),
                    "{who} step {i}: take gave out another datagram than the model's {out}; calls:{}",
                    calls(case, i)
                );
                if let (Some((_, n)), Some((_, _, tag))) = (got, want) {
                    assert!(
                        buf[..n] == bytes_of(tag, n)[..],
                        "{who} step {i}: take gave out other bytes than the datagram {tag}; calls:{}",
                        calls(case, i)
                    );
                }
            }
            ("CallExpire", [t]) => p.expire(map.time(num(t))),
            _ => panic!("{who}: a call the test does not know: {st}"),
        }
        let after = st.state.get("o").unwrap();
        same_table(&p, after, &map, &|| {
            format!("{who} after step {i}; calls:{}", calls(case, i))
        });
        before = after;
    }
    case.steps.len()
}

/// Walks every case of `file`; false when `VINC_MBT_DIR` is unset.
fn walk(file: &str) -> bool {
    let Some(cases) = mbt_cases(file) else {
        return false;
    };
    let mut cases = cases.unwrap();
    let head = cases.head.clone();
    let c = head.get("constants").unwrap();
    let k = |n: &str| num(c.get(n).unwrap());
    assert_eq!(
        k("N"),
        N as u64,
        "{file}: the model's table is not the size of the code's"
    );
    let (max, life) = (k("MAX"), k("LIFE"));
    assert!(
        life > 0 && LIFE.is_multiple_of(life),
        "{file}: the model's lifetime does not divide the code's"
    );
    let tmax = ["HT", "CT"]
        .iter()
        .flat_map(|n| c.get(n).unwrap().arr().unwrap().iter().map(num))
        .max()
        .unwrap();
    let init = head.get("init").unwrap();
    let (mut n, mut steps) = (0u64, 0usize);
    for case in &mut cases {
        steps += run(file, &case.unwrap(), init, max, LIFE / life, tmax);
        n += 1;
    }
    let count = |f: &str| num(head.get(f).unwrap());
    assert_eq!(
        (n, steps as u64),
        (count("cases"), count("steps")),
        "{file}: the file ends early"
    );
    eprintln!(
        "mbt_orphan: {file}: {n} cases, {steps} calls, every one of the {} edges between the {} states of the graph",
        count("edges"),
        count("states")
    );
    true
}

#[test]
fn the_held_fragments_follow_every_edge_of_the_model() {
    // MbtOrphan.cfg and MbtOrphan_edge.cfg
    let walked = ["orphan.ndjson", "orphan_edge.ndjson"].map(walk);
    if walked == [false; 2] {
        eprintln!("mbt_orphan: VINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)");
    }
}
