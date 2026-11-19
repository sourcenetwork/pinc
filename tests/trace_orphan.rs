//! Trace generation for the endpoint's table of held first-flight fragments: seeded runs of a real table
//! (`pinc-core`, built with the `trace` feature), recorded as ndjson (`orphan.ndjson`) for the TLA+ trace check
//! (`TraceOrphan.tla`) and the Lean replay (`Pinc/TraceOrphan.lean`).
//!
//! A run holds datagrams of random lengths (the largest one held, one byte more and longer ones included) for a
//! few messages from a few addresses, takes them for the same message, for another id, another message length and
//! another address, and expires them, at times that step forward, stand still, step back and land on the last
//! moment a held datagram is still fresh and on the first it is not. After every call the table shows its entries
//! and counters. A second file (`orphan_wide.ndjson`, read by the Lean replay only, whose numbers have no bound)
//! has the same calls with times up to `u64::MAX`.
//!
//! The test checks the bytes itself, and compares every call with a naive table (a list that drops what is old,
//! then the oldest arrival when it is full): a datagram given out is, byte for byte, one that was held for that
//! message from that address, not older than the lifetime, and given out for the first time.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    unreachable_pub
)]

use std::collections::HashSet;
use std::fmt::Write as _;
use std::net::SocketAddr;

use pinc_core::OrphanProbe;
use pinc_security::ConnId;
use pinc_tests::SplitMix64;

const N: usize = OrphanProbe::SLOTS;
const MAX: usize = OrphanProbe::MAX;
const LIFE: u64 = OrphanProbe::LIFE;
/// The last time of a narrow run: TLC's integers are 32 bits wide.
const TOP: u64 = 2_100_000_000;

/// The message a datagram is a part of, as three small numbers: the destination id, the length, the sender.
type Key = (u8, u64, u8);

fn cid(d: u8) -> ConnId {
    // ids of different lengths too: 1 + d % 3 bytes, each of them d
    ConnId::new(&[d; 4][..=usize::from(d % 3)]).unwrap()
}
fn remote(r: u8) -> SocketAddr {
    SocketAddr::from(([10, 0, 0, r], 9000 + u16::from(r)))
}
fn local(l: u8) -> SocketAddr {
    SocketAddr::from(([10, 1, 0, l], 7))
}
fn cid_no(c: &ConnId) -> u8 {
    c.as_bytes()[0]
}
fn addr_no(a: &SocketAddr) -> u8 {
    match a {
        SocketAddr::V4(v) => v.ip().octets()[3],
        SocketAddr::V6(_) => unreachable!(),
    }
}

/// The bytes of the datagram `tag`: the tag, then bytes that follow from it.
fn bytes_of(tag: u64, len: usize) -> Vec<u8> {
    let mut b = vec![0u8; len];
    SplitMix64::new(tag ^ 0x6f72_7068).fill(&mut b);
    b[..8].copy_from_slice(&tag.to_le_bytes());
    b
}
fn tag_of(b: &[u8]) -> u64 {
    u64::from_le_bytes(b[..8].try_into().unwrap())
}

/// One datagram of the naive table.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Entry {
    at: u64,
    order: u64,
    key: Key,
    loc: u8,
    tag: u64,
    len: usize,
}

/// The naive table: a list, and what it counted.
#[derive(Default)]
struct Naive {
    held: Vec<Entry>,
    order: u64,
    counts: [u64; 4],
}

impl Naive {
    fn expire(&mut self, now: u64) {
        let before = self.held.len();
        self.held.retain(|e| now.saturating_sub(e.at) <= LIFE);
        self.counts[2] += (before - self.held.len()) as u64;
    }
    fn hold(&mut self, now: u64, key: Key, loc: u8, tag: u64, len: usize) -> bool {
        if len > MAX {
            return false;
        }
        self.expire(now);
        if self.held.len() == N {
            let oldest = self.held.iter().map(|e| e.order).min().unwrap();
            self.held.retain(|e| e.order != oldest);
            self.counts[3] += 1;
        }
        self.held.push(Entry {
            at: now,
            order: self.order,
            key,
            loc,
            tag,
            len,
        });
        self.order += 1;
        self.counts[0] += 1;
        true
    }
    fn take(&mut self, now: u64, key: Key) -> Option<Entry> {
        self.expire(now);
        let oldest = self.held.iter().filter(|e| e.key == key).map(|e| e.order).min()?;
        let at = self.held.iter().position(|e| e.order == oldest)?;
        self.counts[1] += 1;
        Some(self.held.remove(at))
    }
}

/// The table as the models see it, and the same entries for the comparison with the naive table.
fn view(p: &OrphanProbe) -> (String, Vec<Entry>) {
    let mut slots = Vec::new();
    let mut entries = Vec::new();
    for k in 0..N {
        let Some(e) = p.slot(k) else {
            slots.push("[]".to_owned());
            continue;
        };
        let b = p.bytes(k);
        assert_eq!(b.len(), e.len);
        assert!(e.len <= MAX, "the table holds a datagram longer than the bound");
        let tag = tag_of(b);
        assert_eq!(b, &bytes_of(tag, e.len)[..], "an entry holds bytes that were not sent");
        let (d, r, l) = (cid_no(&e.dcid), addr_no(&e.remote), addr_no(&e.local));
        assert_eq!((e.dcid, e.remote, e.local), (cid(d), remote(r), local(l)));
        slots.push(format!(
            "[{},{},[{d},{},{r}],{l},{},{tag}]",
            e.at, e.order, e.total, e.len
        ));
        entries.push(Entry {
            at: e.at,
            order: e.order,
            key: (d, e.total, r),
            loc: l,
            tag,
            len: e.len,
        });
    }
    let c = p.counts();
    assert_eq!(
        c[0],
        c[1] + c[2] + c[3] + p.waiting() as u64,
        "the counters do not balance"
    );
    assert_eq!(p.waiting(), entries.len());
    let json = format!(
        r#"{{"slots":[{}],"order":{},"held":{},"replayed":{},"expired":{},"evicted":{}}}"#,
        slots.join(","),
        p.order(),
        c[0],
        c[1],
        c[2],
        c[3]
    );
    (json, entries)
}

/// What a set of runs exercised.
#[derive(Default)]
struct Seen {
    refused: u32,
    evicted: u64,
    expired: u64,
    given: u32,
    given_at_bound: u32,
    kept_from_other: u32,
    late: u32,
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, steps: u32, wide: bool, tags: &mut u64, seen: &mut Seen) {
    let mut p = OrphanProbe::new();
    let mut naive = Naive::default();
    let mut given: HashSet<u64> = HashSet::new();
    let (v, _) = view(&p);
    let _ = writeln!(
        out,
        r#"{{"t":"coor","run":{id},"op":"init","n":{N},"max":{MAX},"life":{LIFE},"v":{v}}}"#
    );
    let top = if wide { u64::MAX } else { TOP };
    let mut now = if wide {
        u64::MAX - (rng.next_u64() % (6 * LIFE))
    } else {
        rng.next_u64() % (LIFE / 2)
    };
    let mut buf = [0u8; MAX];
    for _ in 0..steps {
        // the clock: forward a little, not at all, back, or onto the edge of a held datagram's lifetime
        now = match rng.next_u64() % 12 {
            0 | 1 => now,
            2 => now.saturating_sub(rng.next_u64() % (LIFE / 2)),
            3 if wide => rng.next_u64(),
            4 | 5 if !naive.held.is_empty() => {
                let e = &naive.held[(rng.next_u64() % naive.held.len() as u64) as usize];
                e.at.saturating_add(LIFE + rng.next_u64() % 2)
            }
            6 => now.saturating_add(LIFE / 2 + rng.next_u64() % LIFE),
            _ => now.saturating_add(rng.next_u64() % (LIFE / 8)),
        }
        .min(top);
        let any_key = |rng: &mut SplitMix64| -> Key {
            (
                (rng.next_u64() % 4) as u8,
                [2000, 2001, 4000][(rng.next_u64() % 3) as usize],
                1 + (rng.next_u64() % 3) as u8,
            )
        };
        let mut looked = true;
        match rng.next_u64() % 10 {
            0..=4 => {
                let key = any_key(rng);
                let loc = 1 + (rng.next_u64() % 2) as u8;
                let len = match rng.next_u64() % 10 {
                    0 => MAX,
                    1 => MAX + 1,
                    2 => MAX + 2 + (rng.next_u64() % 600) as usize,
                    3 => 8,
                    _ => 8 + (rng.next_u64() % (MAX as u64 - 7)) as usize,
                };
                *tags += 1;
                let tag = *tags;
                let before = view(&p).1;
                let ok = p.hold(now, cid(key.0), key.1, local(loc), remote(key.2), &bytes_of(tag, len));
                assert_eq!(
                    ok,
                    naive.hold(now, key, loc, tag, len),
                    "hold differs from the naive table"
                );
                assert_eq!(ok, len <= MAX);
                let (v, after) = view(&p);
                if ok {
                    assert!(
                        after.iter().any(|e| e.tag == tag),
                        "a datagram within the bound was not held"
                    );
                } else {
                    looked = false;
                    seen.refused += 1;
                    assert_eq!(after, before, "a refused datagram changed the table");
                }
                let _ = writeln!(
                    out,
                    r#"{{"t":"coor","run":{id},"op":"hold","now":{now},"key":[{},{},{}],"loc":{loc},"len":{len},"tag":{tag},"ok":{ok},"v":{v}}}"#,
                    key.0, key.1, key.2
                );
            }
            5..=8 => {
                // the message of a datagram held (old ones too), that message with one part changed, or any
                let key = match (rng.next_u64() % 8, naive.held.is_empty()) {
                    (0, _) | (_, true) => any_key(rng),
                    (m, false) => {
                        let k = naive.held[(rng.next_u64() % naive.held.len() as u64) as usize].key;
                        match m {
                            1 => ((k.0 + 1) % 4, k.1, k.2),
                            2 => (k.0, k.1 ^ 1, k.2),
                            3 => (k.0, k.1, 1 + k.2 % 3),
                            _ => k,
                        }
                    }
                };
                let stale: Vec<Entry> = naive.held.iter().filter(|e| e.key == key).cloned().collect();
                let others = naive.held.iter().filter(|e| e.key != key).count();
                let r = p.take(now, &cid(key.0), key.1, &remote(key.2), &mut buf);
                let want = naive.take(now, key);
                let (v, after) = view(&p);
                assert_eq!(r.is_some(), want.is_some(), "take differs from the naive table");
                let o = if let (Some((l, n)), Some(e)) = (r, &want) {
                    let tag = tag_of(&buf[..n]);
                    assert_eq!(
                        (addr_no(&l), n, tag),
                        (e.loc, e.len, e.tag),
                        "another datagram was given out"
                    );
                    assert_eq!(l, local(e.loc));
                    assert_eq!(
                        &buf[..n],
                        &bytes_of(tag, n)[..],
                        "the bytes given out are not the bytes held"
                    );
                    assert!(now.saturating_sub(e.at) <= LIFE, "an old datagram was given out");
                    assert!(given.insert(tag), "a datagram was given out twice");
                    assert!(
                        !after.iter().any(|x| x.tag == tag),
                        "a datagram given out is still held"
                    );
                    seen.given += 1;
                    seen.given_at_bound += u32::from(now.saturating_sub(e.at) == LIFE);
                    seen.kept_from_other += u32::from(others > 0);
                    format!("[{},{n},{tag}]", e.loc)
                } else {
                    assert!(
                        stale.iter().all(|e| now.saturating_sub(e.at) > LIFE),
                        "a fresh datagram of the message was not given out"
                    );
                    seen.late += u32::from(!stale.is_empty());
                    "[]".to_owned()
                };
                let _ = writeln!(
                    out,
                    r#"{{"t":"coor","run":{id},"op":"take","now":{now},"key":[{},{},{}],"out":{o},"v":{v}}}"#,
                    key.0, key.1, key.2
                );
            }
            _ => {
                p.expire(now);
                naive.expire(now);
                let (v, _) = view(&p);
                let _ = writeln!(out, r#"{{"t":"coor","run":{id},"op":"expire","now":{now},"v":{v}}}"#);
            }
        }
        // the table is the naive one after every call, and never larger than its bound
        let (_, mut after) = view(&p);
        after.sort_by_key(|e| e.order);
        assert_eq!(after, naive.held, "the table differs from the naive table");
        assert!(after.len() <= N);
        assert_eq!((p.order(), p.counts()), (naive.order, naive.counts));
        for e in &after {
            // a datagram past the bound is refused before the table is looked at
            assert!(
                !looked || now.saturating_sub(e.at) <= LIFE,
                "an old datagram is still held"
            );
            assert!(!given.contains(&e.tag));
        }
    }
    seen.evicted += p.counts()[3];
    seen.expired += p.counts()[2];
}

#[test]
fn the_held_fragments_match_the_models() {
    let mut rng = SplitMix64::new(0x6f72_0001);
    let mut tags = 0u64;
    let (mut out, mut wide) = (String::new(), String::new());
    let (mut seen, mut seen_wide) = (Seen::default(), Seen::default());
    for id in 1..=120u32 {
        run(&mut rng, &mut out, id, 90, false, &mut tags, &mut seen);
    }
    for id in 900..940u32 {
        run(&mut rng, &mut wide, id, 90, true, &mut tags, &mut seen_wide);
    }
    for s in [&seen, &seen_wide] {
        assert!(s.refused > 0, "no datagram past the bound was offered");
        assert!(s.evicted > 0, "the table never filled");
        assert!(s.expired > 0, "no datagram grew old");
        assert!(
            s.given > 0 && s.kept_from_other > 0,
            "no datagram was given out beside another message's"
        );
        assert!(s.late > 0, "no take came too late for a held datagram");
    }
    assert!(
        seen.given_at_bound > 0,
        "no datagram was given out at the last moment it is fresh"
    );
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("orphan.ndjson"), &out).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("orphan_wide.ndjson"), &wide).unwrap();
    }
}
