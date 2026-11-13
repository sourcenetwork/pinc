//! Trace generation for the endpoint's deadline heap: seeded runs of a real `DeadlineHeap` (`vinc-core`, built with
//! the `trace` feature), recorded as ndjson (`heap.ndjson`) for the TLA+ trace check (`TraceHeap.tla`) and the Lean
//! replay (`Vinc/TraceHeap.lean`).
//!
//! A run fills the heap, changes and removes deadlines at random, and then pops it empty (a peek and a removal of
//! the id it names, as the timer loop does). The deadlines are few, so that many are equal, and include the edges
//! (0, a large one, and in the wide file `u64::MAX`); the ids include ones outside `0..N`. The removals include the
//! root and a leaf, the updates move an element up, down and not at all. After every call the heap shows its
//! array, its position index and its stored deadlines. A second file (`heap_wide.ndjson`, read by the Lean replay
//! only, whose numbers have no bound) has the same calls with deadlines up to `u64::MAX` and ids up to
//! `usize::MAX`.
//!
//! The test compares every call with the naive reference of `core_props.rs` (an array of deadlines whose minimum
//! `(deadline, id)` is the earliest), and checks the invariants of the heap itself after every call: the position
//! index and the heap are inverse, each element is not earlier than its parent, nothing else changed, and the pops
//! come out in increasing order.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::needless_range_loop,
    unreachable_pub
)]

use std::fmt::Write as _;

use vinc_core::DeadlineHeap;
use vinc_tests::SplitMix64;

/// The last deadline of a narrow run: TLC's integers are 32 bits wide.
const TOP: u64 = 2_000_000_000;

/// What a set of runs exercised.
#[derive(Default)]
struct Seen {
    full: u32,
    root_removed: u32,
    leaf_removed: u32,
    moved_up: u32,
    moved_down: u32,
    same: u32,
    ties: u32,
    outside: u32,
    max_deadline: u32,
    popped: u32,
    on_full: u32,
}

/// The heap as the models see it.
fn view<const N: usize>(h: &DeadlineHeap<N>) -> String {
    let heap: Vec<String> = (0..h.len()).map(|i| h.heap_at(i).unwrap().to_string()).collect();
    assert_eq!(h.heap_at(h.len()), None, "an index at the length is an element");
    let pos: Vec<String> = (0..N)
        .map(|id| h.pos_of(id).map_or_else(|| "-1".to_owned(), |p| p.to_string()))
        .collect();
    let at: Vec<String> = (0..N).map(|id| h.stored(id).unwrap().to_string()).collect();
    format!(
        r#"{{"heap":[{}],"pos":[{}],"at":[{}],"len":{}}}"#,
        heap.join(","),
        pos.join(","),
        at.join(","),
        h.len()
    )
}

/// The invariants of the heap itself, and its agreement with the naive reference.
fn check<const N: usize>(h: &DeadlineHeap<N>, model: &[Option<u64>; N]) {
    assert!(h.len() <= N, "the heap holds more than N items");
    for i in 0..h.len() {
        let id = h.heap_at(i).unwrap();
        assert!(id < N);
        assert_eq!(
            h.pos_of(id),
            Some(i),
            "the position index is not the inverse of the heap"
        );
        if i > 0 {
            let parent = h.heap_at((i - 1) / 2).unwrap();
            let key = |x: usize| (h.stored(x).unwrap(), x);
            assert!(key(parent) <= key(id), "an element is earlier than its parent");
        }
    }
    for id in 0..N {
        match h.pos_of(id) {
            Some(p) => assert_eq!(h.heap_at(p), Some(id), "a position names another id"),
            None => assert!(model[id].is_none(), "an id with a deadline has no position"),
        }
        assert_eq!(h.deadline(id), model[id]);
    }
    let want = model.iter().enumerate().filter_map(|(i, t)| t.map(|t| (t, i))).min();
    assert_eq!(
        h.peek(),
        want,
        "peek is not the earliest deadline, the lowest id among equal ones"
    );
    assert_eq!(h.len(), model.iter().flatten().count());
}

fn run<const N: usize>(rng: &mut SplitMix64, out: &mut String, id: u32, steps: u32, wide: bool, seen: &mut Seen) {
    let mut h: DeadlineHeap<N> = DeadlineHeap::new();
    let mut model = [None::<u64>; N];
    let _ = writeln!(out, r#"{{"t":"cohp","run":{id},"op":"init","n":{N},"v":{}}}"#, view(&h));
    // few deadlines, so that many are equal, and the edges
    let deadline = |rng: &mut SplitMix64| -> u64 {
        match rng.next_u64() % 10 {
            0 => 0,
            1 if wide => u64::MAX,
            1 => TOP,
            2 if wide => u64::MAX - rng.next_u64() % 3,
            3..=7 => rng.next_u64() % 6,
            _ if wide => rng.next_u64(),
            _ => rng.next_u64() % TOP,
        }
    };
    let outside = |rng: &mut SplitMix64| -> usize {
        match rng.next_u64() % 3 {
            0 => N,
            1 => N + 1 + (rng.next_u64() % 40) as usize,
            _ if wide => usize::MAX - (rng.next_u64() % 3) as usize,
            _ => N + 100,
        }
    };
    // one call: the heap, the reference, the checks, the record
    let call = |h: &mut DeadlineHeap<N>,
                model: &mut [Option<u64>; N],
                out: &mut String,
                seen: &mut Seen,
                who: usize,
                t: Option<u64>| {
        let before = *model;
        let was_full = h.len() == N;
        let at_root = h.peek().map(|(_, r)| r);
        let len_before = h.len();
        let old_pos = h.pos_of(who);
        h.set(who, t);
        if let Some(m) = model.get_mut(who) {
            *m = t;
        } else {
            seen.outside += 1;
        }
        check(h, model);
        // nothing but the id named changed
        for (k, b) in before.iter().enumerate() {
            if k != who {
                assert_eq!(model[k], *b);
                assert_eq!(h.deadline(k), *b, "a call changed an id it did not name");
            }
        }
        let vals: Vec<u64> = model.iter().flatten().copied().collect();
        seen.ties += u32::from(vals.iter().enumerate().any(|(i, v)| vals[..i].contains(v)));
        seen.max_deadline += u32::from(vals.contains(&u64::MAX));
        seen.full += u32::from(h.len() == N);
        seen.on_full += u32::from(was_full && who < N);
        match (before.get(who).copied().flatten(), t) {
            _ if who >= N => assert_eq!(h.len(), len_before, "an id outside the heap changed it"),
            (None, None) => assert_eq!(h.len(), len_before),
            (None, Some(_)) => assert_eq!(h.len(), len_before + 1),
            (Some(_), None) => {
                assert_eq!(h.len(), len_before - 1);
                seen.root_removed += u32::from(at_root == Some(who));
                seen.leaf_removed += u32::from(old_pos == Some(len_before - 1));
            }
            (Some(o), Some(n)) => {
                assert_eq!(h.len(), len_before);
                seen.moved_up += u32::from(n < o);
                seen.moved_down += u32::from(n > o);
                seen.same += u32::from(n == o);
            }
        }
        let pk = h.peek().map_or_else(String::new, |(t, i)| format!("{t},{i}"));
        let dl = h.deadline(who).map_or_else(String::new, |t| t.to_string());
        let _ = writeln!(
            out,
            r#"{{"t":"cohp","run":{id},"op":"set","id":{who},"has":{},"at":{},"pk":[{pk}],"dl":[{dl}],"v":{}}}"#,
            t.is_some(),
            t.unwrap_or(0),
            view(h)
        );
    };
    // fill: every id once, in random order, with a deadline each
    let mut order: Vec<usize> = (0..N).collect();
    for i in (1..N).rev() {
        order.swap(i, (rng.next_u64() % (i as u64 + 1)) as usize);
    }
    for &who in &order {
        let t = deadline(rng);
        call(&mut h, &mut model, out, seen, who, Some(t));
    }
    for _ in 0..steps {
        let held: Vec<usize> = (0..N).filter(|&i| model[i].is_some()).collect();
        match rng.next_u64() % 12 {
            // no deadline for any id, held or not
            3..=5 => {
                let who = (rng.next_u64() % N as u64) as usize;
                call(&mut h, &mut model, out, seen, who, None);
            }
            // an id held moves up, down or stays
            6..=8 if !held.is_empty() => {
                let who = held[(rng.next_u64() % held.len() as u64) as usize];
                let o = model[who].unwrap();
                let t = match rng.next_u64() % 5 {
                    0 => o,
                    1 | 2 => o.saturating_sub(1 + rng.next_u64() % 4),
                    3 => o.saturating_add(1 + rng.next_u64() % 4),
                    _ => model.iter().flatten().copied().min().unwrap_or(0),
                };
                call(&mut h, &mut model, out, seen, who, Some(t));
            }
            // the root goes
            9 if !held.is_empty() => {
                let (_, root) = h.peek().unwrap();
                call(&mut h, &mut model, out, seen, root, None);
            }
            // a leaf goes
            10 if !held.is_empty() => {
                let leaf = h.heap_at(h.len() - 1).unwrap();
                call(&mut h, &mut model, out, seen, leaf, None);
            }
            // an id outside 0..N
            11 => {
                let who = outside(rng);
                let t = if rng.next_u64().is_multiple_of(2) {
                    Some(deadline(rng))
                } else {
                    None
                };
                call(&mut h, &mut model, out, seen, who, t);
            }
            // a deadline for any id, new or held (also when a case above has nothing to act on)
            _ => {
                let who = (rng.next_u64() % N as u64) as usize;
                let t = deadline(rng);
                call(&mut h, &mut model, out, seen, who, Some(t));
            }
        }
    }
    // pop it empty: a peek and the removal of the id it names
    let mut last: Option<(u64, usize)> = None;
    while let Some((t, who)) = h.peek() {
        assert!(last.is_none_or(|l| l < (t, who)), "a pop came out of order");
        last = Some((t, who));
        seen.popped += 1;
        call(&mut h, &mut model, out, seen, who, None);
    }
    assert!(h.is_empty() && model.iter().all(Option::is_none));
}

#[test]
fn the_deadline_heap_matches_the_models() {
    let mut rng = SplitMix64::new(0x6865_6170);
    let (mut out, mut wide) = (String::new(), String::new());
    let (mut seen, mut seen_wide) = (Seen::default(), Seen::default());
    let mut id = 1u32;
    for _ in 0..40 {
        run::<7>(&mut rng, &mut out, id, 120, false, &mut seen);
        id += 1;
    }
    for _ in 0..16 {
        run::<16>(&mut rng, &mut out, id, 200, false, &mut seen);
        id += 1;
    }
    for _ in 0..4 {
        run::<1>(&mut rng, &mut out, id, 20, false, &mut seen);
        id += 1;
    }
    for _ in 0..20 {
        run::<7>(&mut rng, &mut wide, id, 120, true, &mut seen_wide);
        id += 1;
    }
    for _ in 0..8 {
        run::<16>(&mut rng, &mut wide, id, 200, true, &mut seen_wide);
        id += 1;
    }
    for s in [&seen, &seen_wide] {
        assert!(s.full > 0, "the heap never filled");
        assert!(s.on_full > 0, "no call came when the heap was full");
        assert!(
            s.root_removed > 0 && s.leaf_removed > 0,
            "no root or no leaf was removed"
        );
        assert!(
            s.moved_up > 0 && s.moved_down > 0 && s.same > 0,
            "an update did not go up, down and stay"
        );
        assert!(s.ties > 0, "no two deadlines were equal");
        assert!(s.outside > 0, "no id outside the heap was named");
        assert!(s.popped > 0);
    }
    assert!(seen_wide.max_deadline > 0, "no deadline was u64::MAX");
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("heap.ndjson"), &out).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("heap_wide.ndjson"), &wide).unwrap();
    }
}
