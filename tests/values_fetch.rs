//! The fetcher end to end over the in-memory multi-provider harness: sizes, providers, faults, resume.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::assert_is_empty,
    clippy::doc_markdown,
    clippy::similar_names,
    clippy::single_range_in_vec_init,
    clippy::unreadable_literal,
    reason = "tests assert freely and name protocol rules in capitals"
)]

mod values_support;

use values_support::*;
use vinc_values::session::Provider;
use vinc_values::span::Span;
use vinc_values::trace::{FailReason, LiarWhy, Trace};

/// Run a whole-value fetch to its end and check the store holds exactly the truth.
fn fetch_all(mut sim: Sim, limit_s: u64) -> Sim {
    sim.start();
    sim.run(limit_s);
    assert!(sim.rec.complete(), "fetch failed: {:?}", sim.rec.failed());
    let content = sim.provs[0].cfg.store.content().clone();
    assert!(
        sim.store.verified.contains_range(0..sim.length),
        "not all bytes verified"
    );
    sim.store.assert_verified_is_true(&content);
    let read = sim.store.read(0, sim.length);
    assert_eq!(read.as_slice(), content.bytes(0, sim.length).as_slice());
    sim
}

#[test]
fn values_of_every_size_arrive_whole() {
    let g = GROUP as usize;
    // 1 byte, one group less/exact/more, multiples and non-multiples around power-of-two group counts.
    for len in [
        1,
        2,
        1023,
        1024,
        1025,
        g - 1,
        g,
        g + 1,
        2 * g,
        3 * g - 1,
        3 * g,
        4 * g,
        5 * g + 7,
        8 * g,
        8 * g + 1,
        16 * g,
        33 * g + 99,
    ] {
        for providers in [1, 3] {
            let sim = fetch_all(Sim::uniform(providers, len, 4000), 120);
            assert_eq!(sim.store.covered(), len as u64, "len {len} providers {providers}");
        }
    }
}

#[test]
fn zero_byte_value_completes_with_no_request_and_a_wrong_root_fails() {
    let empty = PStore::bytes(Vec::new());
    let mut sim = Sim::new(vec![ProvCfg::new(empty.clone(), 100)], ClientStore::new());
    sim.start();
    sim.run(5);
    assert!(sim.rec.complete());
    assert!(
        sim.rec
            .traces
            .iter()
            .all(|(_, t)| !matches!(t, Trace::Requested { .. })),
        "a request went out for 0 bytes"
    );

    let mut sim = Sim::new(vec![ProvCfg::new(empty, 100)], ClientStore::new());
    sim.root = [9; 32];
    sim.start();
    sim.run(5);
    assert_eq!(sim.rec.failed(), Some(FailReason::BadRoot));
    assert!(sim.store.pieces.is_empty());
}

#[test]
fn no_provider_fails_at_once() {
    let mut sim = Sim::uniform(1, 5000, 100);
    sim.start_with(&[], &[], None);
    assert_eq!(sim.rec.failed(), Some(FailReason::NoProvider));
}

#[test]
fn ranges_fetch_only_what_is_asked_rounded_to_groups() {
    let mut sim = Sim::uniform(2, 40 * GROUP as usize, 4000);
    let ps = sim.all_providers();
    let ranges = [
        Span {
            off: 3 * GROUP + 5,
            len: 10,
        },
        Span {
            off: 20 * GROUP,
            len: 2 * GROUP + 1,
        },
    ];
    sim.start_with(&ranges, &ps, None);
    sim.run(60);
    assert!(sim.rec.complete());
    let want = [3 * GROUP..4 * GROUP, 20 * GROUP..23 * GROUP];
    for r in &want {
        assert!(sim.store.verified.contains_range(r.clone()));
    }
    assert_eq!(sim.store.covered(), 4 * GROUP);
    sim.store.assert_matches(sim.provs[0].cfg.store.content());
}

#[test]
fn many_providers_split_the_work_and_all_help() {
    let sim = fetch_all(Sim::uniform(4, 6 << 20, 3000), 120);
    let mut by_provider = [0u64; 4];
    for (_, t) in &sim.rec.traces {
        if let Trace::Verified { provider, len, .. } = t {
            by_provider[provider.0 as usize] += len;
        }
    }
    assert!(
        by_provider.iter().all(|&b| b > 0),
        "a provider delivered nothing: {by_provider:?}"
    );
    assert_eq!(by_provider.iter().sum::<u64>(), 6 << 20);
}

#[test]
fn more_than_four_providers_use_the_first_four() {
    let store = PStore::random(3, 300_000);
    let cfgs: Vec<_> = (0..6).map(|_| ProvCfg::new(store.clone(), 4000)).collect();
    let mut sim = Sim::new(cfgs, ClientStore::new());
    sim.start();
    sim.run(60);
    assert!(sim.rec.complete());
    assert!(
        sim.rec
            .traces
            .iter()
            .all(|(_, t)| !matches!(t, Trace::Dial(p) if p.0 >= 4))
    );
}

#[test]
fn request_streams_of_one_provider_are_bounded_only_by_the_table_on_a_long_fat_link() {
    let store = PStore::random(5, 48 << 20);
    let cfgs: Vec<_> = (0..4)
        .map(|_| ProvCfg::new(store.clone(), 40_000).latency(100 * MS))
        .collect();
    let mut sim = Sim::new(cfgs, ClientStore::new());
    sim.start();
    sim.run(300);
    assert!(sim.rec.complete(), "fetch failed: {:?}", sim.rec.failed());
    sim.store.assert_matches(sim.provs[0].cfg.store.content());
    eprintln!("peak request streams of one provider: {}", sim.sess.peak);
    assert!(sim.sess.peak <= vinc_values::fetch::MAX_STREAMS);
}

#[test]
fn loss_and_reordering_are_repaired_and_write_through_verifies_ahead() {
    let store = PStore::random(5, 8 << 20);
    let cfg = ProvCfg::new(store, 6000).loss(30).reorder(4);
    let sim = fetch_all(Sim::new(vec![cfg], ClientStore::new()), 300);
    let ahead = sim
        .rec
        .traces
        .iter()
        .filter(|(_, t)| matches!(t, Trace::Verified { ahead: true, .. }))
        .count();
    assert!(ahead > 0, "no group was verified out of order against a range proof");
    assert!(
        sim.provs[0]
            .rec
            .traces
            .iter()
            .any(|(_, t)| matches!(t, Trace::ProofSent { .. }))
    );
}

#[test]
fn a_liar_is_evicted_nothing_bad_is_released_and_the_value_completes() {
    let honest = PStore::random(11, 4 << 20);
    let liar = honest.lying(Lie::EveryGroup);
    let mut sim = Sim::new(
        vec![ProvCfg::new(honest.clone(), 3000), ProvCfg::new(liar, 6000)],
        ClientStore::new(),
    );
    sim.start();
    sim.run(120);
    assert!(sim.rec.complete(), "{:?}", sim.rec.failed());
    let evicted: Vec<_> = sim.rec.traces_of(|t| {
        if let Trace::Liar { provider, why } = t {
            Some((*provider, *why))
        } else {
            None
        }
    });
    assert_eq!(evicted.len(), 1);
    assert_eq!(evicted[0].1, (Provider(1), LiarWhy::Hash));
    sim.store.assert_verified_is_true(honest.content());
    assert_eq!(sim.store.covered(), 4 << 20);
    // After the eviction the liar is never asked again.
    let t_liar = evicted[0].0;
    assert!(
        sim.rec
            .traces
            .iter()
            .filter(|(t, _)| *t > t_liar)
            .all(|(_, x)| !matches!(x, Trace::Requested { provider, .. } if provider.0 == 1))
    );
}

#[test]
fn a_corrupt_proof_is_a_liar_too() {
    let honest = PStore::random(12, 2 << 20);
    let liar = honest.lying(Lie::BadPair(0));
    let mut sim = Sim::new(
        vec![ProvCfg::new(honest.clone(), 3000), ProvCfg::new(liar, 6000)],
        ClientStore::new(),
    );
    sim.start();
    sim.run(120);
    assert!(sim.rec.complete());
    assert!(
        sim.rec
            .traces
            .iter()
            .any(|(_, t)| matches!(t, Trace::Liar { provider, .. } if provider.0 == 1))
    );
    sim.store.assert_verified_is_true(honest.content());
}

#[test]
fn every_provider_lying_fails_and_stores_nothing_bad() {
    let honest = PStore::random(13, 1 << 20);
    let a = honest.lying(Lie::EveryGroup);
    let b = honest.lying(Lie::FlipByte(5));
    let mut sim = Sim::new(vec![ProvCfg::new(a, 3000), ProvCfg::new(b, 3000)], ClientStore::new());
    sim.start();
    sim.run(60);
    assert_eq!(sim.rec.failed(), Some(FailReason::EveryProviderLied));
    assert!(sim.rec.readable().is_empty() || sim.store.covered() > 0);
    sim.store.assert_verified_is_true(honest.content());
    // Bytes announced are bytes verified.
    for (_, off, len) in sim.rec.readable() {
        assert!(sim.store.verified.contains_range(off..off + len));
    }
}

#[test]
fn a_single_lying_provider_fails_the_fetch() {
    let honest = PStore::random(14, 100_000);
    let mut sim = Sim::new(
        vec![ProvCfg::new(honest.lying(Lie::FlipByte(77)), 1000)],
        ClientStore::new(),
    );
    sim.start();
    sim.run(30);
    assert_eq!(sim.rec.failed(), Some(FailReason::EveryProviderLied));
    assert_eq!(sim.store.covered(), 0);
}

#[test]
fn resume_after_a_restart_asks_only_for_what_is_missing() {
    let store = PStore::random(21, 10 << 20);
    let mut sim = Sim::new(
        vec![ProvCfg::new(store.clone(), 2500), ProvCfg::new(store.clone(), 2500)],
        ClientStore::new(),
    );
    sim.start();
    // Run until about half is in, then "restart": drop the fetch, the session and the providers' streams.
    let half = 5 << 20;
    assert!(sim.run_until(300 * SEC, |s| s.store.covered() >= half));
    let kept = std::mem::take(&mut sim.store);
    let have = kept.covered();
    assert!(have >= half && have < 10 << 20);

    let mut again = Sim::new(
        vec![ProvCfg::new(store.clone(), 2500), ProvCfg::new(store.clone(), 2500)],
        kept,
    );
    again.start();
    again.run(300);
    assert!(again.rec.complete());
    let requested: u64 = again
        .rec
        .traces_of(|t| {
            if let Trace::Requested { bytes, .. } = t {
                Some(*bytes)
            } else {
                None
            }
        })
        .iter()
        .map(|x| x.1)
        .sum();
    assert!(
        requested <= (10 << 20) - have + 2 * GROUP,
        "re-requested verified bytes: {requested} for {} missing",
        (10 << 20) - have
    );
    again.store.assert_verified_is_true(store.content());
    assert_eq!(again.store.covered(), 10 << 20);
}

#[test]
fn resume_with_everything_present_completes_without_a_request() {
    let store = PStore::random(22, 100_000);
    let seeded = ClientStore::seeded(store.content(), &[0..100_000]);
    let mut sim = Sim::new(vec![ProvCfg::new(store, 100)], seeded);
    sim.start();
    assert!(sim.rec.complete());
    assert!(
        sim.rec
            .traces
            .iter()
            .all(|(_, t)| !matches!(t, Trace::Requested { .. }))
    );
}

#[test]
fn resume_with_holes_requests_exactly_the_holes() {
    let store = PStore::random(23, 20 * GROUP as usize);
    let g = GROUP;
    let seeded = ClientStore::seeded(store.content(), &[0..2 * g, 5 * g..9 * g, 15 * g..20 * g]);
    let mut sim = Sim::new(vec![ProvCfg::new(store.clone(), 4000)], seeded);
    sim.start();
    sim.run(60);
    assert!(sim.rec.complete());
    let requested: u64 = sim
        .rec
        .traces_of(|t| {
            if let Trace::Requested { bytes, .. } = t {
                Some(*bytes)
            } else {
                None
            }
        })
        .iter()
        .map(|x| x.1)
        .sum();
    assert_eq!(requested, 3 * g + 6 * g, "holes are [2,5) and [9,15) groups");
    sim.store.assert_verified_is_true(store.content());
}

#[test]
fn a_provider_dropping_mid_transfer_is_replaced_by_the_others() {
    let store = PStore::random(31, 6 << 20);
    let mut sim = Sim::new(
        vec![
            ProvCfg::new(store.clone(), 2000),
            ProvCfg::new(store.clone(), 2000),
            ProvCfg::new(store.clone(), 2000),
        ],
        ClientStore::new(),
    );
    sim.start();
    assert!(sim.run_until(60 * SEC, |s| s.store.covered() >= 1 << 20));
    sim.cut(1);
    sim.provs[1].up = false;
    sim.run(300);
    assert!(sim.rec.complete(), "{:?}", sim.rec.failed());
    sim.store.assert_verified_is_true(store.content());
    assert!(
        sim.rec
            .traces
            .iter()
            .any(|(_, t)| matches!(t, Trace::Steal { from, .. } if from.0 == 1)),
        "the dropped provider's work was not taken over"
    );
}

#[test]
fn a_single_provider_that_drops_and_returns_resumes() {
    let store = PStore::random(32, 3 << 20);
    let mut sim = Sim::new(vec![ProvCfg::new(store.clone(), 1500)], ClientStore::new());
    sim.start();
    assert!(sim.run_until(60 * SEC, |s| s.store.covered() >= 1 << 20));
    let at_cut = sim.store.covered();
    sim.cut(0);
    let down_until = sim.now + 3 * SEC;
    sim.run_until(down_until, |_| false);
    sim.revive(0);
    sim.run(300);
    assert!(sim.rec.complete());
    sim.store.assert_verified_is_true(store.content());
    let after: u64 = sim
        .rec
        .traces_of(|t| {
            if let Trace::Requested { bytes, .. } = t {
                Some(*bytes)
            } else {
                None
            }
        })
        .iter()
        .map(|x| x.1)
        .sum();
    assert!(after >= (3 << 20) - at_cut, "the rest was requested");
}

#[test]
fn the_deadline_fails_a_fetch_that_cannot_finish() {
    let store = PStore::random(33, 4 << 20);
    let mut sim = Sim::new(vec![ProvCfg::new(store, 10)], ClientStore::new());
    let ps = sim.all_providers();
    sim.start_with(&[], &ps, Some(3 * SEC));
    sim.run(30);
    assert_eq!(sim.rec.failed(), Some(FailReason::Deadline));
}

#[test]
fn a_store_that_refuses_writes_fails_the_fetch() {
    let store = PStore::random(34, 100_000);
    let mut cs = ClientStore::new();
    cs.fail_writes = true;
    let mut sim = Sim::new(vec![ProvCfg::new(store, 1000)], cs);
    sim.start();
    sim.run(30);
    assert_eq!(sim.rec.failed(), Some(FailReason::Store));
    assert_eq!(sim.store.covered(), 0);
}

#[test]
fn the_machine_can_run_a_second_fetch_after_the_first() {
    let store = PStore::random(35, 70_000);
    let mut sim = Sim::new(vec![ProvCfg::new(store.clone(), 2000)], ClientStore::new());
    sim.start();
    sim.run(30);
    assert!(sim.rec.complete());
    let ranges = [Span { off: 0, len: 10 }];
    sim.store = ClientStore::new();
    let ps = sim.all_providers();
    sim.start_with(&ranges, &ps, None);
    sim.run(30);
    assert_eq!(
        sim.rec
            .events
            .iter()
            .filter(|(_, e)| matches!(e, vinc_values::trace::Event::Complete))
            .count(),
        2
    );
}

#[test]
fn ranges_in_any_order_and_overlapping_are_all_fetched() {
    let mut sim = Sim::uniform(2, 60 * GROUP as usize, 4000);
    let ps = sim.all_providers();
    let ranges = [
        Span {
            off: 40 * GROUP,
            len: GROUP,
        },
        Span {
            off: 3 * GROUP,
            len: 2 * GROUP,
        },
        Span {
            off: 4 * GROUP,
            len: 3 * GROUP,
        },
        Span { off: 0, len: 5 },
    ];
    sim.start_with(&ranges, &ps, None);
    sim.run(60);
    assert!(sim.rec.complete());
    for r in [0..GROUP, 3 * GROUP..7 * GROUP, 40 * GROUP..41 * GROUP] {
        assert!(sim.store.verified.contains_range(r));
    }
    assert_eq!(sim.store.covered(), 6 * GROUP);
}

#[test]
fn bad_specs_are_refused_and_change_nothing() {
    let mut sim = Sim::uniform(1, 10_000, 100);
    let ps = sim.all_providers();
    let too_many = vec![Span { off: 0, len: 1 }; vinc_values::knobs::MAX_REQ_RANGES + 1];
    let spec = sim.spec(&too_many, &ps);
    {
        let mut io = vinc_values::fetch::Io {
            session: &mut sim.sess,
            store: &mut sim.store,
            out: &mut sim.rec,
        };
        assert_eq!(
            sim.fetch.start(&mut io, 0, &spec),
            Err(vinc_values::fetch::StartError::TooManyRanges)
        );
        let past = [Span { off: 9_999, len: 2 }];
        let spec = FetchSpecOf::new(&past, &ps, sim.root, sim.length);
        assert_eq!(
            sim.fetch.start(&mut io, 0, &spec.0),
            Err(vinc_values::fetch::StartError::OutOfBounds)
        );
    }
    assert!(!sim.fetch.is_running() && !sim.fetch.is_done());
    sim.start();
    let mut io = vinc_values::fetch::Io {
        session: &mut sim.sess,
        store: &mut sim.store,
        out: &mut sim.rec,
    };
    let spec = FetchSpecOf::new(&[], &ps, sim.root, sim.length);
    assert_eq!(
        sim.fetch.start(&mut io, 0, &spec.0),
        Err(vinc_values::fetch::StartError::Busy)
    );
}

struct FetchSpecOf<'a>(vinc_values::fetch::FetchSpec<'a>);

impl<'a> FetchSpecOf<'a> {
    fn new(ranges: &'a [Span], providers: &'a [Provider], root: [u8; 32], length: u64) -> Self {
        Self(vinc_values::fetch::FetchSpec {
            root,
            length,
            ranges,
            providers,
            deadline: None,
        })
    }
}

#[test]
fn a_run_is_deterministic_and_its_trace_repeats_exactly() {
    let run = || {
        let store = PStore::random(61, 3 << 20);
        let cfgs = vec![
            ProvCfg::new(store.clone(), 2500).loss(20).reorder(3),
            ProvCfg::new(store.clone(), 1800).loss(10),
            ProvCfg::new(store, 900),
        ];
        let mut sim = Sim::new(cfgs, ClientStore::new());
        sim.start();
        sim.run(300);
        assert!(sim.rec.complete());
        (
            sim.rec.events,
            sim.rec.traces,
            sim.provs.iter().map(|p| p.rec.traces.clone()).collect::<Vec<_>>(),
        )
    };
    let (e1, t1, s1) = run();
    let (e2, t2, s2) = run();
    assert_eq!(e1, e2);
    assert_eq!(t1, t2);
    assert_eq!(s1, s2);
    assert!(t1.len() > 100);
}
