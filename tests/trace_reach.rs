//! Trace generation for the ring of `REACH_OUT` bodies: seeded runs of a real ring (`vinc-core`, built with the
//! `trace` feature), recorded as ndjson (`reach.ndjson`) for the TLA+ trace check (`TraceReach.tla`) and the Lean
//! replay (`Vinc/TraceReach.lean`).
//!
//! A run puts bodies for a few sessions (more sessions than the ring has places, so it fills, refreshes bodies in
//! place, overwrites and wraps), with bodies of every length that matters (empty, short, exactly the limit of 153
//! bytes, one over it and well over it), and asks for the body of a session. A body is a run of one byte (its
//! `tag`), so the body read back is checked whole and the record carries its first byte. After every call the record
//! shows the four places.
//!
//! The test compares every call with a naive table written from the module's doc, and checks the rules itself: a
//! body over the limit changes nothing, at most one body per session, a get after a put returns the body put, and a
//! session that is not held takes a free place or else the place of the body put longest ago, while a held one keeps
//! its place, and every body lost is counted.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::single_match_else,
    unreachable_pub
)]

use std::fmt::Write as _;

use vinc_core::ReachProbe;
use vinc_tests::SplitMix64;

const SLOTS: usize = ReachProbe::SLOTS;
const MAX: usize = ReachProbe::BODY_MAX;

/// A place of the naive table: session, body.
type Cell = Option<(u64, Vec<u8>)>;

fn tag_of(body: &[u8]) -> u8 {
    body.first().copied().unwrap_or(0)
}

fn json_cell(c: Option<(u64, usize, u8)>) -> String {
    c.map_or("[]".to_owned(), |(s, l, g)| format!("[{s},{l},{g}]"))
}

struct Naive {
    cells: Vec<Cell>,
    /// When each place was last put.
    stamps: Vec<u64>,
    clock: u64,
}

impl Naive {
    /// What the module's doc says: the place of the session if held, else a free place, else the place of the body
    /// put longest ago.
    fn put(&mut self, session: u64, body: &[u8]) -> usize {
        self.clock += 1;
        let at = self
            .cells
            .iter()
            .position(|c| c.as_ref().is_some_and(|c| c.0 == session))
            .or_else(|| self.cells.iter().position(Option::is_none))
            .unwrap_or_else(|| (0..SLOTS).min_by_key(|k| self.stamps[*k]).unwrap());
        self.cells[at] = Some((session, body.to_vec()));
        self.stamps[at] = self.clock;
        at
    }
    fn get(&self, session: u64) -> Option<&[u8]> {
        self.cells.iter().flatten().find(|c| c.0 == session).map(|c| &c.1[..])
    }
}

fn view(p: &ReachProbe) -> String {
    let cells: Vec<String> = (0..SLOTS).map(|k| json_cell(p.cell(k))).collect();
    format!(r#"{{"cells":[{}]}}"#, cells.join(","))
}

#[derive(Default)]
struct Seen {
    refreshed: u32,
    overwritten: u32,
    refused: u32,
    at_limit: u32,
    got: u32,
    got_none: u32,
    zero_len: u32,
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, steps: u32, seen: &mut Seen) {
    let mut p = ReachProbe::new();
    let mut nv = Naive {
        cells: vec![None; SLOTS],
        stamps: vec![0; SLOTS],
        clock: 0,
    };
    let _ = writeln!(
        out,
        r#"{{"t":"cor","run":{id},"op":"init","n":{SLOTS},"mx":{MAX},"v":{}}}"#,
        view(&p)
    );
    // how many sessions share the ring, and how often a body is long
    let sessions = [2u64, 4, 6, 9][(rng.next_u64() % 4) as usize];
    let long_pct = [0u64, 6, 30][(rng.next_u64() % 3) as usize];
    for _ in 0..steps {
        let op = if rng.next_u64() % 100 < 75 {
            let session = rng.next_u64() % sessions;
            let len = if rng.next_u64() % 100 < long_pct {
                [MAX - 1, MAX, MAX + 1, MAX + 1, MAX + 50, 1200][(rng.next_u64() % 6) as usize]
            } else {
                [0usize, 1, 2, 19, 20, 100][(rng.next_u64() % 6) as usize]
            };
            let tag = (rng.next_u64() % 256) as u8;
            let body = vec![tag; len];
            let held = nv.cells.iter().position(|c| c.as_ref().is_some_and(|c| c.0 == session));
            let before: Vec<Cell> = nv.cells.clone();
            let stamps_before = nv.stamps.clone();
            let lost = p.put(session, &body);
            if len <= MAX {
                let at = nv.put(session, &body);
                seen.zero_len += u32::from(len == 0);
                seen.at_limit += u32::from(len == MAX);
                match held {
                    Some(h) => {
                        assert_eq!(at, h, "a held session did not keep its place");
                        seen.refreshed += 1;
                        assert_eq!(lost, 0, "a refresh lost a body");
                    }
                    None => {
                        let full = before.iter().all(Option::is_some);
                        if full {
                            let oldest = (0..SLOTS).min_by_key(|k| stamps_before[*k]).unwrap();
                            assert_eq!(at, oldest, "a full ring did not give up the body put longest ago");
                        } else {
                            assert!(before[at].is_none(), "a free place was passed over");
                        }
                        assert_eq!(lost, u64::from(full), "a lost body was not counted");
                        seen.overwritten += u32::from(before[at].is_some());
                    }
                }
                // no other place changed
                for (k, c) in before.iter().enumerate() {
                    if k != at {
                        assert_eq!(&nv.cells[k], c);
                    }
                }
                assert_eq!(
                    p.get(session),
                    Some(&body[..]),
                    "a get after a put does not return the body put"
                );
            } else {
                seen.refused += 1;
                assert_eq!(lost, 1, "a body over the limit was not counted");
                assert_eq!(nv.cells, before, "a body over the limit changed the table");
                assert_eq!(
                    p.get(session),
                    before.iter().flatten().find(|c| c.0 == session).map(|c| &c.1[..])
                );
            }
            format!(r#""op":"put","c":[{session},{len},{}]"#, if len == 0 { 0 } else { tag })
        } else {
            let session = rng.next_u64() % (sessions + 2);
            let got = p.get(session);
            assert_eq!(got, nv.get(session), "get differs from the naive table");
            let o = got.map_or("[]".to_owned(), |b| {
                seen.got += 1;
                format!("[{},{}]", b.len(), tag_of(b))
            });
            seen.got_none += u32::from(got.is_none());
            format!(r#""op":"get","s":{session},"out":{o}"#)
        };
        // at most one body per session, and the table is the naive one after every call
        for k in 0..SLOTS {
            let want = nv.cells[k].as_ref().map(|c| (c.0, c.1.len(), tag_of(&c.1)));
            assert_eq!(p.cell(k), want, "the ring differs from the naive table");
            if let Some((s, _, _)) = want {
                assert_eq!(
                    nv.cells.iter().flatten().filter(|c| c.0 == s).count(),
                    1,
                    "two bodies for one session"
                );
            }
        }
        let v = view(&p);
        let _ = writeln!(out, r#"{{"t":"cor","run":{id},{op},"v":{v}}}"#);
    }
}

#[test]
fn the_reach_ring_matches_the_models() {
    let mut rng = SplitMix64::new(0x7265_6163);
    let mut out = String::new();
    let mut seen = Seen::default();
    for id in 1..=80u32 {
        run(&mut rng, &mut out, id, 300, &mut seen);
    }
    assert!(seen.refreshed > 0, "no held session was refreshed");
    assert!(
        seen.overwritten > 0,
        "no body was overwritten by a session that was not held"
    );
    assert!(seen.refused > 0, "no body over the limit was refused");
    assert!(seen.at_limit > 0, "no body of exactly the limit was kept");
    assert!(seen.got > 0 && seen.got_none > 0, "get never found, or never missed");
    assert!(seen.zero_len > 0, "no empty body was kept");
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("reach.ndjson"), &out).unwrap();
    }
}
