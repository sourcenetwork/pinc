//! Trace generation for the held ring of a session: seeded runs of a real ring (`vinc-core`, built with the `trace`
//! feature), recorded as ndjson (`held.ndjson`) for the TLA+ trace check (`TraceHeld.tla`) and the Lean replay
//! (`Vinc/TraceHeld.lean`).
//!
//! A run pushes events of every kind (opened, readable, writable, reset, datagram, stopped, open ready) for a few
//! streams, in mixes that keep the ring short, fill it with events the application can recover or cannot, and push on
//! into the full ring (the oldest recoverable event goes, or, when the ring holds none, the new event is refused),
//! pops, and releases everything with `clear`. After every call the ring shows its head, length and drop count, the
//! stall flag, and its events (always when at most 16 are held, else on every 29th call and at the end of the run).
//!
//! The test compares every call with a naive queue (a list), and checks the rules itself: events leave in the order
//! they entered, a repeat of a recoverable event is merged and counted nowhere, the ring never holds more than its
//! places, nothing the application cannot recover is ever given up and a refusal happens only in a stalled ring,
//! every push is accounted for (popped, merged, dropped or held), and recoverable events held have distinct kind and
//! stream.
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

use std::fmt::Write as _;

use vinc_core::HeldProbe;
use vinc_tests::SplitMix64;

const CAP: usize = HeldProbe::SLOTS;

type Ev = (u8, u64, u64);

fn json_ev(e: Ev) -> String {
    format!("[{},{},{}]", e.0, e.1, e.2)
}

/// The naive ring: a list, and what it counted.
#[derive(Default)]
struct Naive {
    q: Vec<Ev>,
    dropped: u64,
    pushed: u64,
    popped: u64,
    merged: u64,
}

impl Naive {
    fn push(&mut self, e: Ev) -> &'static str {
        self.pushed += 1;
        if HeldProbe::lossy(e.0) && self.q.iter().any(|x| x.0 == e.0 && x.1 == e.1) {
            self.merged += 1;
            return "merged";
        }
        if self.q.len() == CAP {
            self.dropped += 1;
            match self.q.iter().position(|x| HeldProbe::lossy(x.0)) {
                Some(i) => {
                    self.q.remove(i);
                }
                None => return "refused",
            }
            self.q.push(e);
            return "evicted";
        }
        self.q.push(e);
        "held"
    }
    fn pop(&mut self) -> Option<Ev> {
        if self.q.is_empty() {
            return None;
        }
        self.popped += 1;
        Some(self.q.remove(0))
    }
    fn stalled(&self) -> bool {
        self.q.len() == CAP && !self.q.iter().any(|x| HeldProbe::lossy(x.0))
    }
}

fn view(p: &HeldProbe, nv: &Naive, full: bool) -> String {
    assert_eq!(p.len(), nv.q.len());
    assert!(p.len() <= CAP, "the ring holds more than its places");
    assert_eq!(p.stalled(), nv.stalled());
    assert_eq!(p.is_empty(), nv.q.is_empty());
    let q = if full {
        let v: Vec<String> = (0..p.len()).map(|i| json_ev(p.slot(i).unwrap())).collect();
        format!("[{}]", v.join(","))
    } else {
        "[]".to_owned()
    };
    format!(
        r#"{{"head":{},"len":{},"dropped":{},"stalled":{},"full":{full},"q":{q}}}"#,
        p.head(),
        p.len(),
        p.dropped(),
        p.stalled()
    )
}

#[derive(Default)]
struct Seen {
    merged: u32,
    refused: u32,
    evicted: u32,
    evict_deep: u32,
    stalled: u32,
    wrapped: u32,
    cleared: u32,
    popped_empty: u32,
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, steps: u32, seen: &mut Seen) {
    let mut p = HeldProbe::new();
    let mut nv = Naive::default();
    let _ = writeln!(
        out,
        r#"{{"t":"coh","run":{id},"op":"init","n":{CAP},"v":{}}}"#,
        view(&p, &nv, true)
    );
    // the share of pushes that can be recovered, and of calls that are pops
    let lossy_pct = [0u64, 3, 20, 60, 100][(rng.next_u64() % 5) as usize];
    let pop_pct = [2u64, 8, 30][(rng.next_u64() % 3) as usize];
    let streams = [2u64, 4, 40][(rng.next_u64() % 3) as usize];
    let mut last_head = 0usize;
    let mut tick = 0u32;
    for _ in 0..steps {
        tick += 1;
        let r = rng.next_u64() % 1000;
        let op = if r < 6 {
            // release everything: the events come out oldest first
            let before = nv.q.len();
            p.clear();
            while nv.pop().is_some() {}
            seen.cleared += u32::from(before > 0);
            r#""op":"clear""#.to_owned()
        } else if r < 6 + 10 * pop_pct {
            let got = p.pop();
            let want = nv.pop();
            assert_eq!(got, want, "pop differs from the naive ring");
            seen.popped_empty += u32::from(got.is_none());
            let o = got.map_or("[]".to_owned(), json_ev);
            format!(r#""op":"pop","out":{o}"#)
        } else {
            let lossy = rng.next_u64() % 100 < lossy_pct;
            let kind = if lossy {
                [1u8, 2, 6][(rng.next_u64() % 3) as usize]
            } else {
                [0u8, 3, 4, 5][(rng.next_u64() % 4) as usize]
            };
            let (stream, error) = match kind {
                4 | 6 => (0, 0),
                3 | 5 => (rng.next_u64() % streams, rng.next_u64() % 5),
                _ => (rng.next_u64() % streams, 0),
            };
            let e = (kind, stream, error);
            let was_len = nv.q.len();
            let first_lossy = nv.q.iter().position(|x| HeldProbe::lossy(x.0));
            let unrec_before = nv.q.iter().filter(|x| !HeldProbe::lossy(x.0)).count();
            let was_stalled = nv.stalled();
            p.push(kind, stream, error);
            let what = nv.push(e);
            match what {
                "merged" => seen.merged += 1,
                "refused" => {
                    seen.refused += 1;
                    assert!(was_stalled, "an event was refused by a ring that was not stalled");
                }
                "evicted" => {
                    seen.evicted += 1;
                    seen.evict_deep += u32::from(first_lossy.is_some_and(|i| i > 4));
                }
                _ => {}
            }
            // nothing the application cannot recover is given up
            assert!(
                nv.q.iter().filter(|x| !HeldProbe::lossy(x.0)).count()
                    >= unrec_before + usize::from(!HeldProbe::lossy(kind) && what != "refused"),
                "an event the application cannot recover was given up"
            );
            if was_len < CAP {
                assert!(what == "held" || what == "merged");
            }
            format!(r#""op":"push","ev":{}"#, json_ev(e))
        };
        seen.stalled += u32::from(nv.stalled());
        seen.wrapped += u32::from(p.head() < last_head);
        last_head = p.head();
        // the ring is the naive queue after every call
        assert_eq!(p.dropped(), nv.dropped);
        for (i, e) in nv.q.iter().enumerate() {
            assert_eq!(p.slot(i), Some(*e), "the ring differs from the naive queue");
        }
        assert_eq!(p.slot(nv.q.len()), None);
        // recoverable events held have distinct kind and stream
        for (i, a) in nv.q.iter().enumerate() {
            for b in &nv.q[i + 1..] {
                assert!(
                    !(HeldProbe::lossy(a.0) && HeldProbe::lossy(b.0) && a.0 == b.0 && a.1 == b.1),
                    "a recoverable event is held twice"
                );
            }
        }
        // every push is accounted for
        assert_eq!(
            nv.pushed,
            nv.popped + nv.merged + nv.dropped + nv.q.len() as u64,
            "a drop was not counted"
        );
        let full = nv.q.len() <= 16 || tick.is_multiple_of(29);
        let v = view(&p, &nv, full);
        let _ = writeln!(out, r#"{{"t":"coh","run":{id},{op},"v":{v}}}"#);
    }
    let v = view(&p, &nv, true);
    let _ = writeln!(out, r#"{{"t":"coh","run":{id},"op":"end","v":{v}}}"#);
}

#[test]
fn the_held_ring_matches_the_models() {
    let mut rng = SplitMix64::new(0x6865_6c64);
    let mut out = String::new();
    let mut seen = Seen::default();
    for id in 1..=80u32 {
        run(&mut rng, &mut out, id, 300, &mut seen);
    }
    assert!(seen.merged > 0, "no repeat of a recoverable event was merged");
    assert!(seen.refused > 0, "no event was refused by a stalled ring");
    assert!(seen.evicted > 0, "no recoverable event was given up");
    assert!(seen.evict_deep > 0, "every eviction took one of the first events");
    assert!(seen.stalled > 0, "the ring never stalled");
    assert!(seen.wrapped > 0, "the head never went round");
    assert!(seen.cleared > 0, "no clear released events");
    assert!(seen.popped_empty > 0, "no pop found the ring empty");
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("held.ndjson"), &out).unwrap();
    }
}
