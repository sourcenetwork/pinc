//! Trace generation for the endpoint's event queue: seeded runs of a real ring (`pinc-core`, built with the `trace`
//! feature), recorded as ndjson (`queue.ndjson`) for the TLA+ trace check (`TraceQueue.tla`) and the Lean replay
//! (`Pinc/TraceQueue.lean`).
//!
//! A run pushes events of the kinds the endpoint raises (recoverable stream notifications, unrecoverable ones that
//! name a session or none, a session's `Closed`), pops, and purges a session, in mixes that keep the ring short, fill
//! it, and push on into the full ring (an event the application can recover is dropped, any other evicts the oldest
//! recoverable one, or, when there is none, the oldest event), with the head going round the ring. After every call
//! the ring shows its head, length, recoverable count and counters, and its queued events (always when at most 24
//! are queued, else on every 307th call and at the end of the run). Some runs push bursts of at most the headroom of
//! unrecoverable events onto a ring that is not stalled, as the endpoint's steps do.
//!
//! The test compares every call with a naive queue (a list), and checks the rules itself: events leave in the
//! order they entered, the ring never holds more than its places, every drop is counted (pushes, pops, purged, queued
//! and dropped balance), an unrecoverable event is evicted only from a full queue that holds nothing recoverable, and
//! a burst within the headroom from a ring that is not stalled loses nothing. The `Closed` of a session and a few
//! other events carry no number of their own, so their place in the order of pushes is recorded as 0.
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

use pinc_core::{EndReason, Event, EventProbe, SessionId};
use pinc_crypto::{IdentityAlg, NodeId};
use pinc_security::Alpn;
use pinc_tests::{SplitMix64, trace_cases};

const CAP: usize = EventProbe::CAP;
const H: usize = EventProbe::HEADROOM;

/// An event as the models see it: its number (0 when it has none), whether it can be recovered, the session it
/// names (0 for none) and whether it is that session's `Closed`.
type Tup = (u64, bool, u64, bool);

fn tup(e: &Event) -> Tup {
    let id = match e {
        Event::StreamOpened { stream, .. }
        | Event::StreamReadable { stream, .. }
        | Event::StreamWritable { stream, .. }
        | Event::StreamReset { stream, .. } => *stream,
        Event::AcpCheck { check, .. } => *check,
        _ => 0,
    };
    (
        id,
        EventProbe::lossy(e),
        e.session().map_or(0, |s| s.0),
        matches!(e, Event::Closed { .. }),
    )
}

fn json_tup(t: Tup) -> String {
    format!("[{},{},{},{}]", t.0, t.1, t.2, t.3)
}

/// The kinds of event: 0 and 1 and 2 can be recovered, the rest cannot.
fn mk(kind: u64, session: u64, n: u64) -> Event {
    let s = SessionId(session);
    match kind {
        0 => Event::StreamReadable { session: s, stream: n },
        1 => Event::StreamWritable { session: s, stream: n },
        2 => Event::OpenReady { session: s },
        3 => Event::StreamOpened { session: s, stream: n },
        4 => Event::StreamReset {
            session: s,
            stream: n,
            error: 7,
        },
        5 => Event::Closed {
            session: s,
            reason: EndReason::Orphaned,
        },
        _ => Event::AcpCheck {
            check: n,
            node: NodeId {
                alg: IdentityAlg::Ed25519,
                bytes: [n as u8; 32],
            },
            alpn: Alpn::new(b"pinc/a").unwrap(),
        },
    }
}

/// The naive queue: a list, and what it counted.
#[derive(Default)]
struct Naive {
    q: Vec<Event>,
    dropped: u64,
    lost: u64,
    pushed: u64,
    popped: u64,
    purged: u64,
}

impl Naive {
    fn push(&mut self, ev: Event) {
        self.pushed += 1;
        if self.q.len() == CAP {
            self.dropped += 1;
            if EventProbe::lossy(&ev) {
                return;
            }
            if let Some(i) = self.q.iter().position(EventProbe::lossy) {
                self.q.remove(i);
            } else {
                self.lost += 1;
                self.q.remove(0);
            }
        }
        self.q.push(ev);
    }
    fn pop(&mut self) -> Option<Event> {
        if self.q.is_empty() {
            return None;
        }
        self.popped += 1;
        Some(self.q.remove(0))
    }
    fn purge(&mut self, s: SessionId) {
        let before = self.q.len();
        self.q
            .retain(|e| e.session() != Some(s) || matches!(e, Event::Closed { .. }));
        self.purged += (before - self.q.len()) as u64;
    }
    fn ll(&self) -> usize {
        self.q.iter().filter(|e| EventProbe::lossy(e)).count()
    }
    fn stalled(&self) -> bool {
        self.q.len() - self.ll() + H > CAP
    }
}

/// The ring as the models see it.
fn view(p: &EventProbe, nv: &Naive, full: bool) -> String {
    let c = p.counts();
    assert_eq!(p.len(), nv.q.len());
    assert!(p.len() <= CAP, "the ring holds more than its places");
    assert_eq!(p.lossy_len(), nv.ll());
    assert_eq!(p.stalled(), nv.stalled());
    assert_eq!(p.is_empty(), nv.q.is_empty());
    let q = if full {
        let v: Vec<String> = (0..p.len()).map(|i| json_tup(tup(&p.slot(i).unwrap()))).collect();
        format!("[{}]", v.join(","))
    } else {
        "[]".to_owned()
    };
    format!(
        r#"{{"head":{},"len":{},"ll":{},"dropped":{},"lost":{},"stalled":{},"full":{full},"q":{q}}}"#,
        p.head(),
        p.len(),
        p.lossy_len(),
        c[0],
        c[1],
        p.stalled()
    )
}

/// What a set of runs exercised.
#[derive(Default)]
struct Seen {
    full: u32,
    drop_new: u32,
    evict_old_lossy: u32,
    evict_deep: u32,
    lost: u32,
    wrapped: u32,
    purged: u32,
    stalled: u32,
    bursts: u32,
    popped_empty: u32,
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, steps: u32, heavy: bool, deep_at: u64, seen: &mut Seen) {
    let mut p = EventProbe::new();
    let mut nv = Naive::default();
    let _ = writeln!(
        out,
        r#"{{"t":"coq","run":{id},"op":"init","cap":{CAP},"h":{H},"v":{}}}"#,
        view(&p, &nv, true)
    );
    // how likely a push is recoverable, and how likely the next call is a pop
    let lossy_pct = if deep_at > 0 {
        0
    } else if heavy {
        [0u64, 10, 50, 100][(id % 4) as usize]
    } else {
        rng.next_u64() % 101
    };
    let pop_pct = if deep_at > 0 {
        0
    } else if heavy {
        2 + 3 * u64::from(id % 4)
    } else {
        20 + rng.next_u64() % 40
    };
    let purge_pm = if deep_at > 0 {
        0
    } else if heavy {
        rng.next_u64() % 4
    } else {
        20 + rng.next_u64() % 40
    };
    let mut n = 0u64;
    let mut last_head = 0usize;
    let mut tick = 0u32;
    let mut was_full = false;
    for _ in 0..steps {
        tick += 1;
        let r = rng.next_u64() % 1000;
        let op = if r < purge_pm {
            let s = 1 + rng.next_u64() % 4;
            let before = p.len();
            let before_nv = nv.q.len();
            p.purge(SessionId(s));
            nv.purge(SessionId(s));
            seen.purged += u32::from(p.len() < before);
            assert_eq!(before, before_nv);
            format!(r#""op":"purge","s":{s}"#)
        } else if r < purge_pm + 10 * pop_pct {
            let got = p.pop();
            let want = nv.pop();
            assert_eq!(got, want, "pop differs from the naive queue");
            seen.popped_empty += u32::from(got.is_none());
            let o = got.map_or("[]".to_owned(), |e| json_tup(tup(&e)));
            format!(r#""op":"pop","out":{o}"#)
        } else {
            // a push; sometimes a burst of the endpoint's size from a ring that is not stalled
            let burst = !heavy && p.len() < 200 && rng.next_u64().is_multiple_of(8) && !p.stalled();
            let count = if burst {
                1 + (rng.next_u64() % (3 * H as u64)) as usize
            } else {
                1
            };
            let lost0 = p.counts()[1];
            let mut unrec = 0usize;
            let mut text = String::new();
            for k in 0..count {
                n += 1;
                let lossy = if deep_at > 0 {
                    n == deep_at
                } else {
                    rng.next_u64() % 100 < lossy_pct
                };
                let mut kind = if lossy {
                    rng.next_u64() % 3
                } else {
                    3 + rng.next_u64() % 4
                };
                if burst && !lossy && unrec >= H {
                    // within the headroom
                    kind = rng.next_u64() % 3;
                }
                let ev = mk(kind, 1 + rng.next_u64() % 3, n);
                unrec += usize::from(!EventProbe::lossy(&ev));
                let was_len = nv.q.len();
                let ll_before = nv.ll();
                let first_lossy = nv.q.iter().position(EventProbe::lossy);
                p.push(ev);
                nv.push(ev);
                if was_len == CAP {
                    if EventProbe::lossy(&ev) {
                        seen.drop_new += 1;
                    } else if let Some(i) = first_lossy {
                        seen.evict_old_lossy += 1;
                        seen.evict_deep += u32::from(i > 8);
                    } else {
                        assert_eq!(ll_before, 0);
                        seen.lost += 1;
                    }
                }
                if burst {
                    let _ = write!(text, "{}{}", if k == 0 { "" } else { "," }, json_tup(tup(&ev)));
                } else {
                    text = json_tup(tup(&ev));
                }
            }
            if burst {
                seen.bursts += 1;
                assert_eq!(p.counts()[1], lost0, "a burst within the headroom lost an event");
                format!(r#""op":"burst","evs":[{text}]"#)
            } else {
                format!(r#""op":"push","ev":{text}"#)
            }
        };
        seen.full += u32::from(!was_full && nv.q.len() == CAP);
        was_full = nv.q.len() == CAP;
        seen.stalled += u32::from(nv.stalled());
        seen.wrapped += u32::from(p.head() < last_head);
        last_head = p.head();
        // the ring is the naive queue after every call
        assert_eq!(p.counts(), [nv.dropped, nv.lost]);
        for (i, e) in nv.q.iter().enumerate() {
            assert_eq!(p.slot(i), Some(*e), "the ring differs from the naive queue");
        }
        assert_eq!(p.slot(nv.q.len()), None);
        // every push is accounted for: popped, purged, dropped or queued; and every loss is counted
        assert_eq!(
            nv.pushed,
            nv.popped + nv.purged + nv.dropped + nv.q.len() as u64,
            "a drop was not counted"
        );
        let full = nv.q.len() <= 24 || tick.is_multiple_of(307);
        let v = view(&p, &nv, full);
        let _ = writeln!(out, r#"{{"t":"coq","run":{id},{op},"v":{v}}}"#);
    }
    let v = view(&p, &nv, true);
    let _ = writeln!(out, r#"{{"t":"coq","run":{id},"op":"end","v":{v}}}"#);
    // drain: the events leave in the order they entered
    let mut last = 0u64;
    while let Some(e) = p.pop() {
        let t = tup(&e);
        if t.0 != 0 {
            assert!(t.0 > last, "events left out of order");
            last = t.0;
        }
    }
}

#[test]
fn the_event_queue_matches_the_models() {
    let mut rng = SplitMix64::new(0x7175_6575);
    let mut out = String::new();
    let mut seen = Seen::default();
    for id in 1..=trace_cases(8, 60) as u32 {
        run(&mut rng, &mut out, id, 120, false, 0, &mut seen);
    }
    // the quick profile leaves out the ring-full runs but the last, which drops recoverable pushes: with no recoverable
    // push a full ring is scanned whole at every push, minutes of replay
    let deep = trace_cases(0, 1) == 1;
    for id in (100..104u32).filter(|id| deep || *id == 103) {
        // enough pushes to fill the ring, push on into it and take the head round
        run(&mut rng, &mut out, id, 2 * CAP as u32 + 300, true, 0, &mut seen);
    }
    if !deep {
        // the ring-full runs that take the head round are left out; a long run of short queues does it by pops
        run(&mut rng, &mut out, 61, 3000, false, 0, &mut seen);
    }
    for id in 110..110 + trace_cases(1, 4) as u32 {
        // a ring full of events that cannot be recovered but one, far from the head, which the next push evicts
        let deep_at = CAP as u64 / 2 + rng.next_u64() % (CAP as u64 / 2 - 8);
        run(&mut rng, &mut out, id, CAP as u32 + 40, true, deep_at, &mut seen);
    }
    assert!(seen.full > 0, "the ring never filled");
    assert!(seen.drop_new > 0, "no recoverable event was dropped from a full ring");
    assert!(seen.evict_old_lossy > 0, "no recoverable event was evicted");
    assert!(seen.evict_deep > 0, "every eviction took one of the first events");
    assert!(seen.lost > 0, "no unrecoverable event was lost");
    assert!(seen.wrapped > 0, "the head never went round");
    assert!(seen.purged > 0, "no purge dropped an event");
    assert!(seen.stalled > 0, "the ring never stalled");
    assert!(seen.bursts > 0, "no burst was pushed");
    assert!(seen.popped_empty > 0, "no pop found the ring empty");
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("queue.ndjson"), &out).unwrap();
    }
}
