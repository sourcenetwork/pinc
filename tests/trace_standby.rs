//! Trace generation for the facade's standby slab (`crates/vinc/src/standby.rs`): seeded runs of a real slab (built
//! with the `trace` feature, `StandbyProbe`), recorded as ndjson (`standby.ndjson`) for the TLA+ trace check
//! (`TraceFacadeStandby.tla`) and the Lean replay (`Vinc/TraceFacadeStandby.lean`).
//!
//! A run allocates tickets for up to six futures, arms them with wakers numbered 1 to 5 (the same waker again, and
//! another), notifies them, passes the baton, wakes every armed ticket and releases them, with stale tickets (released
//! once, released again), forged ones (a slot past the slab, a generation the slot never had) and slots reused while
//! still queued. After every call the slab shows its slots, its free stack and its queue, and the call the wakers it
//! woke, in order.
//!
//! The test compares every call with a naive slab (the same rules over plain vectors, written from the module's
//! docs and the code's order: the queue is of slots, and a reused slot keeps its place) and checks the documented
//! invariants itself: the queue holds each slot at most once and exactly the queued ones, a waker only on a live
//! queued slot, the free stack exactly the slots not live, the slab as long as the most tickets held at once, a call
//! with a stale ticket changes nothing, a released ticket is dead.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    unreachable_pub
)]

use std::collections::HashSet;
use std::fmt::Write as _;

use vinc::{StandbyProbe, StandbySlot};
use vinc_tests::SplitMix64;

/// No waker woken.
const NONE: Vec<u32> = Vec::new();

/// The most tickets a run holds at once.
const HELD: usize = 6;

/// The naive slab.
#[derive(Default, Clone, PartialEq, Eq, Debug)]
struct Naive {
    slots: Vec<StandbySlot>,
    free: Vec<u32>,
    queue: Vec<u32>,
}

impl Naive {
    fn valid(&self, t: (u32, u32)) -> bool {
        self.slots
            .get(t.0 as usize)
            .is_some_and(|s| s.live && s.generation == t.1)
    }
    fn alloc(&mut self) -> (u32, u32) {
        if let Some(i) = self.free.pop() {
            let s = &mut self.slots[i as usize];
            s.live = true;
            return (i, s.generation);
        }
        self.slots.push(StandbySlot {
            generation: 0,
            waker: None,
            queued: false,
            live: true,
        });
        (self.slots.len() as u32 - 1, 0)
    }
    fn arm(&mut self, t: (u32, u32), w: u32) {
        if !self.valid(t) {
            return;
        }
        let s = &mut self.slots[t.0 as usize];
        s.waker = Some(w);
        if !s.queued {
            s.queued = true;
            self.queue.push(t.0);
        }
    }
    fn notify(&mut self, t: (u32, u32)) -> Vec<u32> {
        if !self.valid(t) {
            return Vec::new();
        }
        self.slots[t.0 as usize].waker.take().into_iter().collect()
    }
    fn baton(&mut self) -> Vec<u32> {
        while !self.queue.is_empty() {
            let i = self.queue.remove(0);
            let s = &mut self.slots[i as usize];
            s.queued = false;
            if s.live
                && let Some(w) = s.waker.take()
            {
                return vec![w];
            }
        }
        Vec::new()
    }
    fn notify_all(&mut self) -> Vec<u32> {
        let mut out = Vec::new();
        for s in &mut self.slots {
            if s.live
                && let Some(w) = s.waker.take()
            {
                out.push(w);
            }
        }
        out
    }
    fn release(&mut self, t: (u32, u32)) {
        if !self.valid(t) {
            return;
        }
        let s = &mut self.slots[t.0 as usize];
        s.live = false;
        s.generation = s.generation.wrapping_add(1);
        s.waker = None;
        self.free.push(t.0);
    }
}

fn view(p: &StandbyProbe) -> (String, Naive) {
    let slots = p.slots();
    let n = Naive {
        slots: slots.clone(),
        free: p.free(),
        queue: p.queue(),
    };
    let json = format!(
        r#"{{"slots":[{}],"free":{:?},"queue":{:?}}}"#,
        slots
            .iter()
            .map(|s| format!("[{},{},{},{}]", s.generation, s.waker.unwrap_or(0), s.queued, s.live))
            .collect::<Vec<_>>()
            .join(","),
        n.free,
        n.queue
    );
    (json, n)
}

/// The documented invariants of the slab.
fn check(n: &Naive, hw: usize) {
    let queued: Vec<u32> = (0..n.slots.len() as u32)
        .filter(|&i| n.slots[i as usize].queued)
        .collect();
    let mut q = n.queue.clone();
    q.sort_unstable();
    assert_eq!(q, queued, "the queue is not exactly the queued slots, once each");
    assert!(n.queue.len() <= n.slots.len());
    for s in &n.slots {
        assert!(
            s.waker.is_none() || (s.live && s.queued),
            "a waker on a slot not live and queued"
        );
    }
    let dead: Vec<u32> = (0..n.slots.len() as u32)
        .filter(|&i| !n.slots[i as usize].live)
        .collect();
    let mut f = n.free.clone();
    f.sort_unstable();
    assert_eq!(f, dead, "the free stack is not exactly the slots not live, once each");
    assert_eq!(
        n.slots.len(),
        hw,
        "the slab is not as long as the most tickets held at once"
    );
}

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    stale: u32,
    inherited: u32,
    skipped: u32,
    empty_baton: u32,
    woken_all: u32,
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, steps: u32, seen: &mut Seen) {
    let mut p = StandbyProbe::new();
    let mut naive = Naive::default();
    let mut held: Vec<(u32, u32)> = Vec::new();
    let mut gone: Vec<(u32, u32)> = Vec::new();
    let mut hw = 0usize;
    let (v, _) = view(&p);
    let _ = writeln!(out, r#"{{"t":"fsb","run":{id},"op":"init","v":{v}}}"#);
    // a ticket to call with: mostly one held, sometimes a released one, sometimes a forged one
    let pick = |rng: &mut SplitMix64, held: &[(u32, u32)], gone: &[(u32, u32)], n: &Naive| -> (u32, u32) {
        match rng.next_u64() % 10 {
            0 if !gone.is_empty() => gone[(rng.next_u64() % gone.len() as u64) as usize],
            1 => (n.slots.len() as u32 + (rng.next_u64() % 3) as u32, 0),
            2 if !held.is_empty() => {
                let t = held[(rng.next_u64() % held.len() as u64) as usize];
                (t.0, t.1.wrapping_add(1 + (rng.next_u64() % 3) as u32))
            }
            _ if !held.is_empty() => held[(rng.next_u64() % held.len() as u64) as usize],
            _ => (0, 0),
        }
    };
    for _ in 0..steps {
        let before = view(&p).1;
        let line = match rng.next_u64() % 16 {
            0..=3 if held.len() < HELD => {
                let t = p.alloc();
                assert_eq!(t, naive.alloc(), "alloc differs from the naive slab");
                assert!(!before.valid(t), "alloc handed out a live ticket");
                // a reused slot still queued keeps its place in the queue
                seen.inherited += u32::from(before.slots.get(t.0 as usize).is_some_and(|s| s.queued));
                held.push(t);
                gone.retain(|g| *g != t);
                format!(r#""op":"alloc","out":[{},{}]"#, t.0, t.1)
            }
            0..=6 => {
                let t = pick(rng, &held, &gone, &naive);
                let w = 1 + (rng.next_u64() % 5) as u32;
                let woke = p.arm(t.0, t.1, w);
                naive.arm(t, w);
                assert_eq!(woke, NONE);
                format!(r#""op":"arm","tk":[{},{}],"w":{w},"woke":[]"#, t.0, t.1)
            }
            7 | 8 => {
                let t = pick(rng, &held, &gone, &naive);
                let woke = p.notify(t.0, t.1);
                assert_eq!(woke, naive.notify(t), "notify differs from the naive slab");
                format!(r#""op":"notify","tk":[{},{}],"woke":{woke:?}"#, t.0, t.1)
            }
            9 | 10 => {
                // the waker of the first live armed slot in the queue, and the entries before it skipped
                let first = before.queue.iter().position(|&i| {
                    let s = before.slots[i as usize];
                    s.live && s.waker.is_some()
                });
                let woke = p.baton();
                assert_eq!(woke, naive.baton(), "the baton differs from the naive slab");
                if let Some(k) = first {
                    assert_eq!(woke, vec![before.slots[before.queue[k] as usize].waker.unwrap()]);
                    seen.skipped += k as u32;
                } else {
                    assert_eq!(woke, NONE);
                    seen.empty_baton += 1;
                }
                if before.slots.iter().any(|s| s.waker.is_some()) {
                    assert_eq!(woke.len(), 1, "a slot is armed and the baton woke no one");
                }
                format!(r#""op":"baton","woke":{woke:?}"#)
            }
            11 => {
                let woke = p.notify_all();
                assert_eq!(woke, naive.notify_all(), "notify_all differs from the naive slab");
                seen.woken_all += woke.len() as u32;
                format!(r#""op":"all","woke":{woke:?}"#)
            }
            _ => {
                let t = pick(rng, &held, &gone, &naive);
                let woke = p.release(t.0, t.1);
                naive.release(t);
                assert_eq!(woke, NONE);
                if before.valid(t) {
                    held.retain(|h| *h != t);
                    gone.push(t);
                }
                format!(r#""op":"release","tk":[{},{}],"woke":[]"#, t.0, t.1)
            }
        };
        let (v, after) = view(&p);
        assert_eq!(after, naive, "the slab differs from the naive slab");
        hw = hw.max(after.slots.iter().filter(|s| s.live).count());
        check(&after, hw);
        // a call with a stale ticket changed nothing
        if line.contains(r#""tk""#) {
            let t: Vec<u32> = line
                .split(r#""tk":["#)
                .nth(1)
                .unwrap()
                .split(']')
                .next()
                .unwrap()
                .split(',')
                .map(|x| x.parse().unwrap())
                .collect();
            if !before.valid((t[0], t[1])) {
                assert_eq!(after, before, "a call with a stale ticket changed the slab");
                seen.stale += 1;
            }
        }
        for g in &gone {
            assert!(!after.valid(*g), "a released ticket names a live slot");
        }
        let held_set: HashSet<_> = held.iter().copied().collect();
        assert_eq!(held_set.len(), held.len());
        let _ = writeln!(out, r#"{{"t":"fsb","run":{id},{line},"v":{v}}}"#);
    }
}

/// One slot reused many times: its generation counts the releases.
fn reuse(out: &mut String, id: u32, rounds: u32) {
    let mut p = StandbyProbe::new();
    let (v, _) = view(&p);
    let _ = writeln!(out, r#"{{"t":"fsb","run":{id},"op":"init","v":{v}}}"#);
    let mut last = None;
    for r in 0..rounds {
        let t = p.alloc();
        assert_eq!(t, (0, r));
        let (v, _) = view(&p);
        let _ = writeln!(
            out,
            r#"{{"t":"fsb","run":{id},"op":"alloc","out":[{},{}],"v":{v}}}"#,
            t.0, t.1
        );
        if let Some((a, b)) = last {
            // the ticket released before names the same slot, live again, and is dead
            let w = p.notify(a, b);
            assert_eq!(w, NONE);
            let (v, _) = view(&p);
            let _ = writeln!(
                out,
                r#"{{"t":"fsb","run":{id},"op":"notify","tk":[{a},{b}],"woke":[],"v":{v}}}"#
            );
        }
        assert_eq!(p.arm(t.0, t.1, 1), NONE);
        let (v, _) = view(&p);
        let _ = writeln!(
            out,
            r#"{{"t":"fsb","run":{id},"op":"arm","tk":[{},{}],"w":1,"woke":[],"v":{v}}}"#,
            t.0, t.1
        );
        assert_eq!(p.release(t.0, t.1), NONE);
        let (v, _) = view(&p);
        let _ = writeln!(
            out,
            r#"{{"t":"fsb","run":{id},"op":"release","tk":[{},{}],"woke":[],"v":{v}}}"#,
            t.0, t.1
        );
        last = Some(t);
    }
}

#[test]
fn the_standby_slab_matches_the_models() {
    let mut rng = SplitMix64::new(0x7374_6e64);
    let mut out = String::new();
    let mut seen = Seen::default();
    for id in 1..=60u32 {
        run(&mut rng, &mut out, id, 120, &mut seen);
    }
    reuse(&mut out, 900, 200);
    assert!(seen.stale > 0, "no stale or forged ticket was used");
    assert!(seen.inherited > 0, "no slot was reused while still queued");
    assert!(seen.skipped > 0, "the baton never skipped an entry");
    assert!(seen.empty_baton > 0, "the baton always found a slot");
    assert!(seen.woken_all > 0, "notify_all woke no one");
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("standby.ndjson"), &out).unwrap();
    }
}
