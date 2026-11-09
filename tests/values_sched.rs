//! The work lists of the fetch scheduler against a plain byte-set model: `RangeList` `push`, `push_front`, `pop_front`,
//! `push_new`, `holes`, `align` and `split`, over seeded random inputs, plus the fetches that pinned two defects of the
//! scheduler (a wanted range listed twice, an empty range that fetched a group).
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    reason = "tests assert freely"
)]

mod values_support;

use std::collections::BTreeSet;

use values_support::*;
use vinc_tests::SplitMix64;
use vinc_values::knobs::GROUP;
use vinc_values::span::{RangeList, Span, align, holes};
use vinc_values::trace::Trace;

fn bytes(l: &[Span]) -> BTreeSet<u64> {
    l.iter().flat_map(|s| s.off..s.end()).collect()
}

fn below(r: &mut SplitMix64, n: u64) -> u64 {
    r.next_u64() % n
}

#[test]
fn push_never_loses_coverage_and_never_outgrows_its_capacity() {
    let mut r = SplitMix64::new(11);
    for round in 0..4000 {
        let mut l: RangeList<4> = RangeList::new();
        let mut model: BTreeSet<u64> = BTreeSet::new();
        for _ in 0..=below(&mut r, 7) {
            let s = Span {
                off: below(&mut r, 40),
                len: below(&mut r, 9),
            };
            let was_full = l.len() == 4;
            let before = l.as_slice().to_vec();
            if below(&mut r, 5) == 0 {
                l.push_front(s);
            } else {
                l.push(s);
            }
            let want: BTreeSet<u64> = model.union(&(s.off..s.end()).collect()).copied().collect();
            let got = bytes(l.as_slice());
            assert!(l.len() <= 4, "round {round}: grew past capacity");
            assert!(
                want.is_subset(&got),
                "round {round}: lost coverage pushing {s:?} onto {before:?}"
            );
            if !was_full {
                assert!(
                    l.len() < 4 || got.len() >= want.len(),
                    "round {round}: coverage must not shrink"
                );
            }
            if !was_full && l.len() <= 4 && before.len() < 4 {
                // below capacity the union is exact unless the push merged over a gap (a push that touches the last
                // span only adds bytes from the last offset to s.end(), still within the union of the two)
                assert_eq!(got, want, "round {round}: exact below capacity");
            }
            model = got;
        }
    }
}

#[test]
fn pop_front_returns_the_first_span_and_keeps_the_rest() {
    let mut l: RangeList<4> = RangeList::new();
    for i in 0..4 {
        l.push(Span { off: i * 100, len: 10 });
    }
    assert_eq!(l.pop_front(), Some(Span { off: 0, len: 10 }));
    assert_eq!(l.len(), 3);
    assert_eq!(l.as_slice()[0], Span { off: 100, len: 10 });
    while l.pop_front().is_some() {}
    assert_eq!(l.pop_front(), None);
}

#[test]
fn push_new_adds_exactly_the_uncovered_bytes_in_order() {
    let mut r = SplitMix64::new(12);
    for round in 0..4000 {
        let mut l: RangeList<32> = RangeList::new();
        let mut model: BTreeSet<u64> = BTreeSet::new();
        for _ in 0..=below(&mut r, 5) {
            let s = Span {
                off: below(&mut r, 60),
                len: below(&mut r, 20),
            };
            let total_before = l.total();
            l.push_new(s);
            let add: BTreeSet<u64> = (s.off..s.end()).filter(|x| !model.contains(x)).collect();
            assert_eq!(
                l.total() - total_before,
                add.len() as u64,
                "round {round}: {s:?} added bytes twice"
            );
            model.extend(add);
            assert_eq!(bytes(l.as_slice()), model, "round {round}");
        }
    }
}

fn store_with(ranges: &[(u64, u64)]) -> ClientStore {
    let mut st = ClientStore::new();
    for &(a, b) in ranges {
        st.verified.insert(a..b).unwrap();
    }
    st
}

#[test]
fn holes_are_exactly_the_unverified_bytes_in_order() {
    let mut r = SplitMix64::new(13);
    for round in 0..3000 {
        let mut ranges = Vec::new();
        for _ in 0..below(&mut r, 6) {
            let a = below(&mut r, 50);
            ranges.push((a, a + 1 + below(&mut r, 12)));
        }
        let st = store_with(&ranges);
        let verified: BTreeSet<u64> = ranges.iter().flat_map(|&(a, b)| a..b).collect();
        let span = Span {
            off: below(&mut r, 60),
            len: below(&mut r, 30),
        };
        let mut out = Vec::new();
        holes(&st, &[0; 32], span, |h| out.push(h));
        let want: BTreeSet<u64> = (span.off..span.end()).filter(|x| !verified.contains(x)).collect();
        assert_eq!(bytes(&out), want, "round {round}: {span:?} over {ranges:?}");
        assert_eq!(
            out.iter().map(|s| s.len).sum::<u64>(),
            want.len() as u64,
            "round {round}: pieces overlap"
        );
        assert!(
            out.iter().all(|s| s.len > 0) && out.windows(2).all(|w| w[0].end() < w[1].off),
            "round {round}: pieces not ordered and separated: {out:?}"
        );
    }
}

#[test]
fn align_rounds_out_to_whole_groups_clamped_to_the_value() {
    let mut r = SplitMix64::new(14);
    for _ in 0..20_000 {
        let total = below(&mut r, 40 * GROUP);
        let s = Span {
            off: below(&mut r, 41 * GROUP),
            len: below(&mut r, 5 * GROUP),
        };
        if s.len == 0 {
            assert_eq!(align(s, total), None, "an empty span asks for no group: {s:?}");
        }
        match align(s, total) {
            None => assert!(s.len == 0 || s.off >= total, "{s:?} {total}"),
            Some(a) => {
                assert_eq!(a.off % GROUP, 0);
                assert!(a.off <= s.off && a.end() >= s.end().min(total) && a.end() <= total);
                assert!(a.end() % GROUP == 0 || a.end() == total);
                assert!(a.len > 0 && a.off + GROUP > s.off);
            }
        }
    }
    for off in [0, 1, 5, GROUP - 1, GROUP, GROUP + 3, 20_000] {
        assert_eq!(
            align(Span { off, len: 0 }, 20_000),
            None,
            "an empty span asks for no group (offset {off})"
        );
    }
    assert_eq!(
        align(
            Span {
                off: u64::MAX - 3,
                len: 100
            },
            u64::MAX
        ),
        Some(Span {
            off: u64::MAX / GROUP * GROUP,
            len: u64::MAX - u64::MAX / GROUP * GROUP
        })
    );
}

fn groups(l: &[Span]) -> Vec<u64> {
    l.iter()
        .flat_map(|s| (s.off..s.end()).step_by(GROUP as usize))
        .collect()
}

#[test]
fn split_gives_contiguous_shares_of_whole_groups_that_cover_the_input_exactly() {
    let mut r = SplitMix64::new(15);
    for round in 0..4000 {
        let mut l: RangeList<32> = RangeList::new();
        let mut at = 0;
        for _ in 0..=below(&mut r, 4) {
            at += below(&mut r, 3) * GROUP;
            let len = (1 + below(&mut r, 9)) * GROUP;
            l.push(Span { off: at, len });
            at += len;
        }
        let k = 1 + below(&mut r, 6) as usize;
        let shares = l.split::<4>(k);
        let used = k.clamp(1, 4);
        let all: Vec<Span> = shares.iter().flat_map(|s| s.as_slice().iter().copied()).collect();
        // every group of the input is in exactly one share, and the shares come in the order of the input
        assert_eq!(
            groups(&all),
            groups(l.as_slice()),
            "round {round}: cover, overlap or order"
        );
        for (i, s) in shares.iter().enumerate() {
            assert!(i < used || s.is_empty(), "round {round}: share {i} beyond k");
            assert!(
                s.as_slice().iter().all(|x| x.off % GROUP == 0 && x.len % GROUP == 0),
                "round {round}: cut inside a group"
            );
        }
    }
}

/// Providers asked for ranges that overlap in the same groups: each group is wanted, requested and verified once.
#[test]
fn wanted_ranges_that_overlap_are_fetched_once() {
    let g = GROUP;
    for providers in [1usize, 3] {
        let mut sim = Sim::uniform(providers, (10 * g) as usize, 4000);
        let ranges = [
            Span { off: 0, len: 1 },
            Span { off: 3 * g, len: g },
            Span { off: 2 * g, len: g + 1 },
        ];
        let provs = sim.all_providers();
        sim.start_with(&ranges, &provs, None);
        sim.run(60);
        assert!(sim.rec.complete(), "{:?}", sim.rec.failed());
        let wanted = sim.rec.traces_of(|t| {
            if let Trace::FetchStart { wanted, .. } = t {
                Some(*wanted)
            } else {
                None
            }
        });
        assert_eq!(
            wanted[0].1,
            3 * g,
            "the groups 0, 2 and 3 are 3 groups, not {}",
            wanted[0].1 / g
        );
        let mut seen = BTreeSet::new();
        for (_, off) in sim.rec.traces_of(|t| {
            if let Trace::Verified { off, .. } = t {
                Some(*off)
            } else {
                None
            }
        }) {
            assert!(
                seen.insert(off),
                "group at {off} verified twice with {providers} providers"
            );
        }
        assert_eq!(seen, BTreeSet::from([0, 2 * g, 3 * g]));
    }
}
