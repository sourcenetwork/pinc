//! Trace generation for the node's queue of application events (`pinc-node`, built with the `trace` feature, through
//! `EventQueueProbe`), recorded as ndjson (`event_queue.ndjson`) for the TLA+ trace check (`TraceNodeEventQueue.tla`).
//!
//! The queue is the node's own (`EventQueue`, `io.rs`), pushed and read through the calls the node loop makes: `push`
//! and `extend` of endpoint events (recoverable by reading state, or not), `pop`, `can_take`, `resumable` and
//! `is_empty`. Runs: small queues, a queue filled to the point the node stops taking events and past the cap and
//! drained back to where it resumes, a full queue with nothing recoverable, a full queue with one recoverable event
//! in the middle, the edges of the stop and resume points, and long seeded runs over the whole range.
//!
//! The test compares every call with a naive queue written from the module docs of `io.rs` (a deque, a lost count and
//! a held flag): the result of each call, the length and the lost count. It also checks that the length never passes
//! the cap, that tags read back increase within a run, and that a queue filled only as the node loop does (batches
//! while `can_take`) loses nothing. After every call the record carries the length and the lost count.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::len_zero,
    clippy::cast_possible_truncation,
    unreachable_pub,
    clippy::manual_is_multiple_of,
    clippy::panic
)]

use std::collections::VecDeque;
use std::fmt::Write as _;

use pinc_node::{EventQueueProbe, Popped};
use pinc_tests::{SplitMix64, trace_cases};

const CAP: usize = EventQueueProbe::CAP;
const HIGH: usize = EventQueueProbe::HIGH;
const LOW: usize = EventQueueProbe::LOW;

/// The queue as the module docs say it behaves.
#[derive(Default)]
struct Naive {
    q: VecDeque<(u64, bool)>,
    lost: u32,
    held: bool,
}

impl Naive {
    fn push(&mut self, id: u64, lossy: bool) {
        if self.q.len() >= CAP {
            self.lost += 1;
            if lossy {
                return;
            }
            let victim = self.q.iter().position(|e| e.1).unwrap_or(0);
            self.q.remove(victim);
        }
        self.q.push_back((id, lossy));
    }

    fn pop(&mut self) -> Popped {
        if self.lost > 0 {
            return Popped::Lost(std::mem::take(&mut self.lost));
        }
        self.q
            .pop_front()
            .map_or(Popped::Empty, |(tag, lossy)| Popped::Event { tag, lossy })
    }

    fn can_take(&mut self) -> bool {
        self.held = if self.held {
            self.q.len() > LOW
        } else {
            self.q.len() >= HIGH
        };
        !self.held
    }
}

struct Run {
    p: EventQueueProbe,
    n: Naive,
    out: String,
    rng: SplitMix64,
    /// The lossy draw: a quarter count 0..=4, or 5 for alternating.
    quarters: u64,
    next: u64,
    last_read: u64,
}

impl Run {
    fn new(mut out: String, seed: u64, quarters: u64) -> Self {
        writeln!(
            out,
            "{{\"t\":\"evq\",\"op\":\"init\",\"cap\":{CAP},\"high\":{HIGH},\"low\":{LOW},\"len\":0,\"lost\":0}}"
        )
        .unwrap();
        Self {
            p: EventQueueProbe::new(),
            n: Naive::default(),
            out,
            rng: SplitMix64::new(seed),
            quarters,
            next: 1,
            last_read: 0,
        }
    }

    fn draw(&mut self) -> bool {
        match self.quarters {
            5 => self.next % 2 == 0,
            q => self.rng.next_u64() % 4 < q,
        }
    }

    /// The length and lost count of the probe, checked against the naive queue.
    fn tail(&mut self) -> String {
        let (len, lost) = (self.p.len(), self.p.lost());
        assert!(len <= CAP, "the queue passed its cap: {len}");
        assert_eq!(len, self.n.q.len(), "length");
        assert_eq!(lost, self.n.lost, "lost count");
        format!("\"len\":{len},\"lost\":{lost}")
    }

    fn push(&mut self, lossy: bool) {
        let id = self.next;
        self.next += 1;
        self.p.push(id, lossy);
        self.n.push(id, lossy);
        let t = self.tail();
        writeln!(
            self.out,
            "{{\"t\":\"evq\",\"op\":\"push\",\"id\":{id},\"lossy\":{lossy},{t}}}"
        )
        .unwrap();
    }

    fn push_drawn(&mut self) {
        let l = self.draw();
        self.push(l);
    }

    fn batch(&mut self, count: usize) -> Vec<(u64, bool)> {
        (0..count)
            .map(|_| {
                let id = self.next;
                self.next += 1;
                (id, self.draw())
            })
            .collect()
    }

    fn extend(&mut self, count: usize) {
        assert!(self.p.len() + count <= CAP, "a batch that crosses the cap");
        let events = self.batch(count);
        self.p.extend(&events);
        for &(id, l) in &events {
            self.n.push(id, l);
        }
        let t = self.tail();
        let ids = events.iter().map(|e| e.0.to_string()).collect::<Vec<_>>().join(",");
        let ls = events.iter().map(|e| e.1.to_string()).collect::<Vec<_>>().join(",");
        writeln!(
            self.out,
            "{{\"t\":\"evq\",\"op\":\"extend\",\"ids\":[{ids}],\"lossy\":[{ls}],{t}}}"
        )
        .unwrap();
    }

    /// Batches as the node loop fills the queue: each while the node takes events.
    fn fill(&mut self, to: usize) {
        assert!(to <= HIGH);
        while self.p.len() < to {
            assert!(self.take(), "the node would not take events at {}", self.p.len());
            let k = 512.min(to - self.p.len());
            self.extend(k);
        }
    }

    fn pop(&mut self) -> Popped {
        let r = self.p.pop();
        assert_eq!(r, self.n.pop(), "pop");
        let t = self.tail();
        let (name, count, id, lossy) = match r {
            Popped::Lost(c) => ("lost", c, 0, false),
            Popped::Event { tag, lossy } => {
                assert!(tag > self.last_read, "tag {tag} read after {}", self.last_read);
                self.last_read = tag;
                ("event", 0, tag, lossy)
            }
            Popped::Empty => ("none", 0, 0, false),
        };
        writeln!(
            self.out,
            "{{\"t\":\"evq\",\"op\":\"pop\",\"r\":\"{name}\",\"count\":{count},\"id\":{id},\"lossy\":{lossy},{t}}}"
        )
        .unwrap();
        r
    }

    /// `n` reads in one go, all of which return events.
    fn drain(&mut self, n: usize) -> Vec<u64> {
        assert!(self.p.lost() == 0 && self.p.len() >= n);
        let mut got = Vec::with_capacity(n);
        for _ in 0..n {
            let r = self.p.pop();
            assert_eq!(r, self.n.pop(), "drain");
            let Popped::Event { tag, lossy } = r else {
                panic!("a drain read {r:?}");
            };
            assert!(tag > self.last_read, "tag {tag} read after {}", self.last_read);
            self.last_read = tag;
            got.push((tag, lossy));
        }
        let t = self.tail();
        let ids = got.iter().map(|e| e.0.to_string()).collect::<Vec<_>>().join(",");
        let ls = got.iter().map(|e| e.1.to_string()).collect::<Vec<_>>().join(",");
        writeln!(
            self.out,
            "{{\"t\":\"evq\",\"op\":\"drain\",\"ids\":[{ids}],\"lossy\":[{ls}],{t}}}"
        )
        .unwrap();
        got.into_iter().map(|e| e.0).collect()
    }

    /// Everything queued, after the lost count: the tags read.
    fn drain_all(&mut self) -> Vec<u64> {
        if self.p.lost() > 0 {
            self.pop();
        }
        let mut all = Vec::new();
        while self.p.len() > 0 {
            let k = self.p.len().min(1000);
            all.extend(self.drain(k));
        }
        all
    }

    fn take(&mut self) -> bool {
        let r = self.p.can_take();
        assert_eq!(r, self.n.can_take(), "take");
        let t = self.tail();
        writeln!(self.out, "{{\"t\":\"evq\",\"op\":\"take\",\"ok\":{r},{t}}}").unwrap();
        r
    }

    fn resumable(&mut self) -> bool {
        let r = self.p.resumable();
        assert_eq!(r, self.n.held && self.n.q.len() <= LOW, "resumable");
        let t = self.tail();
        writeln!(self.out, "{{\"t\":\"evq\",\"op\":\"resumable\",\"r\":{r},{t}}}").unwrap();
        r
    }

    fn empty(&mut self) -> bool {
        let r = self.p.is_empty();
        assert_eq!(r, self.n.q.is_empty() && self.n.lost == 0, "empty");
        let t = self.tail();
        writeln!(self.out, "{{\"t\":\"evq\",\"op\":\"empty\",\"r\":{r},{t}}}").unwrap();
        r
    }

    fn finish(self) -> String {
        self.out
    }
}

/// Run 1: small queues, single calls.
fn small(r: u64, out: String) -> String {
    let mut run = Run::new(out, 0x6576_0000 + r, [0, 2, 4][(r % 3) as usize]);
    for _ in 0..400 {
        match run.rng.next_u64() % 6 {
            0 | 1 if run.p.len() < 64 => run.push_drawn(),
            2 | 3 => {
                run.pop();
            }
            4 => {
                run.take();
            }
            _ => {
                if run.rng.next_u64() & 1 == 0 {
                    run.resumable();
                } else {
                    run.empty();
                }
            }
        }
    }
    run.finish()
}

/// Run 2: fill past the stop point and the cap, drain to where the node resumes and to empty.
fn fill_drain(r: u64, out: String) -> String {
    let mut run = Run::new(out, 0x6576_0100 + r, r);
    assert!(run.take());
    run.fill(HIGH);
    assert!(!run.take(), "the node still takes events at the stop point");
    run.extend(CAP - HIGH);
    assert_eq!(run.p.lost(), 0, "a queue filled as the node loop does lost an event");
    for _ in 0..trace_cases(4, 20) {
        run.push_drawn();
    }
    assert!(run.p.lost() > 0);
    assert!(matches!(run.pop(), Popped::Lost(c) if c > 0));
    while run.p.len() > LOW {
        let k = 1000.min(run.p.len() - LOW);
        run.drain(k);
        run.resumable();
        if run.p.len() > LOW {
            assert!(!run.take());
        }
    }
    assert!(run.resumable(), "the queue at the resume point is not resumable");
    assert!(run.take(), "the node does not take events at the resume point");
    while run.p.len() > 0 {
        let k = run.p.len().min(1000);
        run.drain(k);
    }
    assert!(run.empty());
    run.finish()
}

/// A full queue of events nothing can recover, but the one at `recoverable_at`.
fn fill_full(run: &mut Run, recoverable_at: Option<usize>) {
    if trace_cases(1, 0) == 1 {
        // the quick profile fills in batches of 512, as the node loop does: the same queue in 17 lines, not 8192
        let fill = |run: &mut Run, to: usize| {
            while run.p.len() < to {
                run.extend(512.min(to - run.p.len()));
            }
        };
        if let Some(at) = recoverable_at {
            fill(run, at);
            run.push(true);
        }
        fill(run, CAP);
    } else {
        for i in 0..CAP {
            run.push(recoverable_at == Some(i));
        }
    }
    assert_eq!(run.p.len(), CAP);
}

/// Run 3: full with nothing recoverable.
fn nothing_recoverable(r: u64, out: String) -> String {
    let mut run = Run::new(out, 0x6576_0200 + r, 0);
    fill_full(&mut run, None);
    let first = run.n.q.front().map(|e| e.0).unwrap();
    let pushes = trace_cases(4, 10);
    for i in 0..pushes {
        let lossy = if r == 0 { i >= pushes / 2 } else { i % 2 == 1 };
        let (head, len) = (run.n.q.front().map(|e| e.0), run.p.len());
        run.push(lossy);
        assert_eq!(run.p.len(), len);
        if !lossy {
            assert_ne!(run.n.q.front().map(|e| e.0), head, "the oldest event was kept");
        }
    }
    assert_eq!(run.p.lost() as usize, pushes);
    let tags = run.drain_all();
    assert!(!tags.contains(&first), "the oldest unrecoverable event survived");
    assert!(run.empty());
    run.finish()
}

/// Run 4: full with one recoverable event in the middle.
fn one_recoverable(r: u64, out: String) -> String {
    let mut run = Run::new(out, 0x6576_0300 + r, 0);
    fill_full(&mut run, Some(4000));
    let kept = run.n.q.iter().find(|e| e.1).map(|e| e.0).unwrap();
    run.push(false);
    assert_eq!(run.p.lost(), 1);
    if r == 1 {
        run.push(false);
    }
    let tags = run.drain_all();
    assert!(!tags.contains(&kept), "the recoverable event survived a drop");
    if r == 0 {
        assert!(
            tags.contains(&1),
            "the oldest event was dropped instead of the recoverable one"
        );
    }
    assert!(run.empty());
    run.finish()
}

/// Run 5: the stop and resume points.
fn edges(r: u64, out: String) -> String {
    let mut run = Run::new(out, 0x6576_0400 + r, 0);
    match r {
        0 => {
            run.fill(HIGH - 2);
            for _ in 0..4 {
                run.push_drawn();
                run.take();
            }
        }
        1 => {
            run.fill(HIGH);
            assert!(!run.take());
            for _ in 0..2 {
                run.push_drawn();
                assert!(!run.take());
            }
            for _ in 0..3 {
                run.pop();
                run.take();
            }
        }
        2 => {
            run.fill(LOW + 1);
            for _ in 0..3 {
                assert!(run.take());
                run.resumable();
                run.pop();
            }
            run.take();
        }
        _ => {
            run.fill(HIGH);
            assert!(!run.take());
            run.drain(HIGH - LOW - 1);
            assert!(!run.take());
            assert!(!run.resumable());
            for _ in 0..3 {
                run.pop();
                run.resumable();
                run.take();
            }
        }
    }
    run.finish()
}

/// Run 6: long seeded runs that grow to the cap and past it and drain back.
fn random(r: u64, out: String) -> String {
    let mut run = Run::new(out, 0x6576_1000 + r, run_quarters(r));
    let mut growing = true;
    let mut at_cap = 0;
    for _ in 0..3000 {
        let len = run.p.len();
        if growing && at_cap >= 20 {
            growing = false;
            at_cap = 0;
        } else if !growing && len <= 3500 {
            growing = true;
        }
        at_cap += usize::from(len >= CAP);
        let x = run.rng.next_u64() % 100;
        let big = 1 + (run.rng.next_u64() % 600) as usize;
        let (extend, push, drain, pop) = if growing { (40, 70, 75, 80) } else { (5, 15, 55, 70) };
        if x < extend {
            if len + big <= CAP {
                run.extend(big);
            } else {
                run.push_drawn();
            }
        } else if x < push {
            run.push_drawn();
        } else if x < drain {
            let k = big.min(len);
            if run.p.lost() == 0 && k > 0 {
                run.drain(k);
            } else {
                run.pop();
            }
        } else if x < pop {
            run.pop();
        } else {
            match run.rng.next_u64() % 3 {
                0 => {
                    run.take();
                }
                1 => {
                    run.resumable();
                }
                _ => {
                    run.empty();
                }
            }
        }
    }
    run.finish()
}

fn run_quarters(r: u64) -> u64 {
    SplitMix64::new(0x6576_2000 + r).next_u64() % 6
}

#[test]
fn event_queue() {
    let mut out = String::new();
    for r in 0..trace_cases(3, 30) as u64 {
        out = small(r, out);
    }
    // the quick profile runs two of the six lossy mixes: with no recoverable event each overflow push scans the whole
    // queue
    for r in (0..6).filter(|r| trace_cases(0, 1) == 1 || r % 3 == 2) {
        out = fill_drain(r, out);
    }
    for r in 0..2 {
        out = nothing_recoverable(r, out);
    }
    for r in 0..2 {
        out = one_recoverable(r, out);
    }
    for r in 0..4 {
        out = edges(r, out);
    }
    for r in 0..trace_cases(0, 10) as u64 {
        out = random(r, out);
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("event_queue.ndjson"), &out).unwrap();
    }
}
