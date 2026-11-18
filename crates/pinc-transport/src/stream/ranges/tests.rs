//! Unit tests of the range set: spilling into an arena slot and moving back, against a plain model.

use alloc::vec::Vec;

use super::*;

/// Four intervals inline, so a spill needs a fifth and the move back needs two or fewer.
type Set = RangeSet<4>;

fn contents(s: &Set, pool: &BufferPool<'_>) -> Vec<Range<u64>> {
    s.overlaps(pool, 0..u64::MAX).collect()
}

/// A pool lent an arena of eight slots, as the endpoint lends it for a call.
fn spilling() -> BufferPool<'static> {
    let mut pool = BufferPool::new_boxed(4);
    pool.lend_spill(crate::stream::spill::SpillArena::new_boxed(8));
    pool
}

/// `n` disjoint, non-adjacent intervals of 5 offsets, 10 apart.
fn run_of(n: u64) -> Vec<Range<u64>> {
    (0..n).map(|k| 10 * k..10 * k + 5).collect()
}

fn filled(pool: &mut BufferPool<'_>, n: u64) -> Set {
    let mut s = Set::EMPTY;
    for r in run_of(n) {
        s.insert(pool, r).unwrap();
    }
    s
}

/// The slot takes and returns the arena saw across `edit`, from the slots the session holds after each step.
struct Moves {
    takes: u32,
    returns: u32,
    used: usize,
}

impl Moves {
    fn new(pool: &BufferPool<'_>) -> Self {
        Self {
            takes: 0,
            returns: 0,
            used: pool.spill_held(),
        }
    }

    fn after(&mut self, pool: &BufferPool<'_>) {
        let now = pool.spill_held();
        self.takes += u32::from(now > self.used);
        self.returns += u32::from(now < self.used);
        self.used = now;
    }
}

fn ins(s: &mut Set, pool: &mut BufferPool<'_>, m: &mut Moves, r: Range<u64>) {
    s.insert(pool, r).unwrap();
    m.after(pool);
}

fn rem(s: &mut Set, pool: &mut BufferPool<'_>, m: &mut Moves, r: Range<u64>) {
    s.remove(pool, &r).unwrap();
    m.after(pool);
}

/// A set that crosses the spill boundary (5 intervals) and the half boundary (2) back and forth moves once per
/// crossing, and a set that sits between the two does not move on any edit.
#[test]
fn a_set_moves_once_per_crossing_and_not_at_all_between_the_boundaries() {
    let mut pool = spilling();
    let mut s = filled(&mut pool, 4);
    let mut m = Moves::new(&pool);
    assert!(!s.is_spilled(), "four intervals fit inline");
    for cycle in 0..3 {
        // 4 -> 5 spills.
        ins(&mut s, &mut pool, &mut m, 40..45);
        assert!(s.is_spilled());
        // Between 3 and 5 intervals the slot stays, edit by edit.
        for _ in 0..10 {
            rem(&mut s, &mut pool, &mut m, 40..45);
            ins(&mut s, &mut pool, &mut m, 40..45);
        }
        rem(&mut s, &mut pool, &mut m, 30..35);
        ins(&mut s, &mut pool, &mut m, 30..35);
        assert!(s.is_spilled(), "cycle {cycle}: 5 intervals stay spilled");
        // 5 -> 2 returns the slot on the edit that reaches 2, and not before.
        rem(&mut s, &mut pool, &mut m, 40..45);
        rem(&mut s, &mut pool, &mut m, 30..35);
        assert!(s.is_spilled(), "cycle {cycle}: 3 intervals stay spilled");
        rem(&mut s, &mut pool, &mut m, 20..25);
        assert!(!s.is_spilled(), "cycle {cycle}: 2 intervals are inline again");
        // 2 <-> 3 inline: no move either way.
        for _ in 0..10 {
            ins(&mut s, &mut pool, &mut m, 20..25);
            rem(&mut s, &mut pool, &mut m, 20..25);
        }
        ins(&mut s, &mut pool, &mut m, 20..25);
        ins(&mut s, &mut pool, &mut m, 30..35);
        assert_eq!(contents(&s, &pool), run_of(4));
    }
    assert_eq!((m.takes, m.returns), (3, 3), "one take and one return per crossing");
    assert_eq!(s.take_spills(), 3);
    assert_eq!(s.take_spills(), 0, "the count is read once");
}

/// The move back keeps every interval, in order, and the lowest one is what `first` answers.
#[test]
fn moving_back_inline_keeps_every_range() {
    let mut pool = spilling();
    let mut s = filled(&mut pool, 9);
    assert!(s.is_spilled());
    assert_eq!(contents(&s, &pool), run_of(9));
    // Cut the set down from the top: it stays spilled down to 3 intervals and moves inline at 2.
    for (k, r) in run_of(9).into_iter().enumerate().skip(2).rev() {
        s.remove(&mut pool, &r).unwrap();
        assert_eq!(contents(&s, &pool), run_of(k as u64), "after cutting interval {k}");
        assert_eq!(s.is_spilled(), k > 2);
    }
    assert_eq!(pool.spill_held(), 0, "the slot is back in the arena");
    assert_eq!(s.first(), Some(0..5));
    s.take_front(&mut pool, 100).unwrap();
    assert_eq!(s.first(), Some(10..15));
}

/// An emptied set holds no slot, whichever edit emptied it.
#[test]
fn an_empty_set_holds_no_slot() {
    let mut pool = spilling();
    let mut s = filled(&mut pool, 6);
    assert_eq!(pool.spill_held(), 1);
    while s.take_front(&mut pool, u64::MAX).is_some() {}
    assert!(s.is_empty());
    assert!(!s.is_spilled());
    assert_eq!(pool.spill_held(), 0);
    let mut s = filled(&mut pool, 6);
    s.remove(&mut pool, &(0..100)).unwrap();
    assert!(!s.is_spilled());
    assert_eq!(pool.spill_held(), 0);
}

/// An insertion between spilled intervals shifts the ones above it right, a merge joins its neighbours and a cut in
/// the middle of an interval splits it.
#[test]
fn edits_in_the_middle_of_a_spilled_set_shift_the_intervals_around_them() {
    let mut pool = spilling();
    let mut s = filled(&mut pool, 8);
    assert!(s.is_spilled());
    // New interval between the 4th (30..35) and 5th (40..45).
    s.insert(&mut pool, 36..38).unwrap();
    let mut want = run_of(8);
    want.insert(4, 36..38);
    assert_eq!(contents(&s, &pool), want);
    // A bridge from 5 to 41 merges the first interval, 10..15, 20..25, 30..35, 36..38 and 40..45 into one.
    s.insert(&mut pool, 5..41).unwrap();
    assert_eq!(contents(&s, &pool), [0..45, 50..55, 60..65, 70..75]);
    // A cut inside the merged interval splits it in two.
    s.remove(&mut pool, &(20..22)).unwrap();
    assert_eq!(contents(&s, &pool), [0..20, 22..45, 50..55, 60..65, 70..75]);
}

/// A tiny generator for the property test.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: u64) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        (z ^ (z >> 31)) % n
    }
}

/// The offsets of a model set, as maximal runs.
fn runs(model: &[bool]) -> Vec<Range<u64>> {
    let mut out: Vec<Range<u64>> = Vec::new();
    for (i, on) in model.iter().enumerate() {
        let i = i as u64;
        if !*on {
            continue;
        }
        match out.last_mut() {
            Some(l) if l.end == i => l.end = i + 1,
            _ => out.push(i..i + 1),
        }
    }
    out
}

/// Any sequence of inserts, removes and front takes, applied to a set that spills and moves back, gives the contents
/// of the same sequence on a plain model of the offsets (a bit per offset), after every step.
#[test]
fn any_edit_sequence_gives_the_contents_of_a_plain_model_while_the_set_spills_and_moves_back() {
    const SPAN: usize = 400;
    let (mut takes, mut returns) = (0, 0);
    for seed in 0..64u64 {
        let mut rng = Rng(seed);
        let mut pool = spilling();
        let mut s = Set::EMPTY;
        let mut model = [false; SPAN];
        let mut m = Moves::new(&pool);
        for step in 0..400 {
            let a = rng.below(SPAN as u64 - 8);
            // Short inserts scatter intervals (spill); wide removes and front takes sweep them away (move back).
            let remove = |s: &mut Set, pool: &mut BufferPool<'_>, model: &mut [bool; SPAN], r: Range<u64>| {
                s.remove(pool, &r).unwrap();
                model[r.start as usize..r.end as usize].fill(false);
            };
            match rng.below(20) {
                0..=8 => {
                    let r = a..a + 1 + rng.below(3);
                    s.insert(&mut pool, r.clone()).unwrap();
                    model[r.start as usize..r.end as usize].fill(true);
                }
                9..=13 => remove(&mut s, &mut pool, &mut model, a..a + 1 + rng.below(3)),
                14..=17 => {
                    let max = 1 + rng.below(6);
                    let got = s.take_front(&mut pool, max);
                    let want = runs(&model).first().map(|f| f.start..f.end.min(f.start + max));
                    assert_eq!(got, want, "seed {seed} step {step}: the front taken");
                    if let Some(r) = got {
                        model[r.start as usize..r.end as usize].fill(false);
                    }
                }
                18 => remove(
                    &mut s,
                    &mut pool,
                    &mut model,
                    a..(a + 1 + rng.below(150)).min(SPAN as u64),
                ),
                _ if rng.below(3) == 0 => remove(&mut s, &mut pool, &mut model, 0..SPAN as u64),
                _ => remove(&mut s, &mut pool, &mut model, a..a + 1 + rng.below(3)),
            }
            m.after(&pool);
            let want = runs(&model);
            assert_eq!(contents(&s, &pool), want, "seed {seed} step {step}");
            assert_eq!(s.first(), want.first().cloned(), "seed {seed} step {step}: first");
            assert!(
                s.len <= 4 || s.is_spilled(),
                "seed {seed} step {step}: past the inline size, spilled"
            );
            assert!(
                !s.is_spilled() || s.len > 2,
                "seed {seed} step {step}: spilled only above half the inline size"
            );
            assert_eq!(
                (pool.used_chunks(), pool.spill_held()),
                (0, usize::from(s.is_spilled()))
            );
        }
        takes += m.takes;
        returns += m.returns;
    }
    assert!(
        takes > 20 && returns > 20,
        "the sequences spill and move back: {takes} {returns}"
    );
}
