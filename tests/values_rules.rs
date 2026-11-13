//! The ported rules with their numbers: ARRIVAL_CURVE, TAIL_SHRINK, STEAL, HEAD_HOLD and STALL_REDIAL.
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
use vinc_values::knobs;
use vinc_values::plan::Plan;
use vinc_values::session::Provider;
use vinc_values::span::Span;
use vinc_values::trace::{Event, Release, Trace};

const G: u64 = GROUP;

fn topups(sim: &Sim) -> Vec<(u64, Provider, u64, u64)> {
    sim.rec
        .traces_of(|t| {
            if let Trace::TopUp {
                provider,
                bytes,
                target,
            } = t
            {
                Some((*provider, *bytes, *target))
            } else {
                None
            }
        })
        .into_iter()
        .map(|(t, (p, b, g))| (t, p, b, g))
        .collect()
}

fn releases(sim: &Sim) -> Vec<(u64, u64, Release)> {
    sim.rec
        .traces_of(|t| {
            if let Trace::Released { off, why } = t {
                Some((*off, *why))
            } else {
                None
            }
        })
        .into_iter()
        .map(|(t, (o, w))| (t, o, w))
        .collect()
}

fn redials(sim: &Sim) -> Vec<(u64, u64, u64)> {
    sim.rec
        .traces_of(|t| {
            if let Trace::StallRedial { wait, next } = t {
                Some((*wait, *next))
            } else {
                None
            }
        })
        .into_iter()
        .map(|(t, (w, n))| (t, w, n))
        .collect()
}

#[test]
fn the_numbers_are_the_tuned_ones() {
    assert_eq!(knobs::GROUP, 16384);
    assert_eq!(knobs::MAX_PROVIDERS, 4);
    assert_eq!(knobs::SERVE_BATCH, 16);
    assert_eq!(knobs::TGT0, 786_432);
    assert_eq!(knobs::TGT_MAX, 1_572_864);
    assert_eq!(knobs::RATE_HORIZON, 1000);
    assert_eq!(knobs::STRIPE_CHUNK, 1_048_576);
    assert_eq!(knobs::STEAL_MIN, 262_144);
    assert_eq!(knobs::STEAL_IDLE, 2 * SEC);
    assert_eq!(knobs::STEAL_ETA_MS, 800);
    assert_eq!(knobs::HOLD_B, 98_304);
    assert_eq!(knobs::HOLD_NV, 40);
    assert_eq!(knobs::HOLD_MAX, 2 * SEC);
    assert_eq!(knobs::STALL_WAIT, 4 * SEC);
    assert_eq!(knobs::STALL_CAP, 16 * SEC);
    assert_eq!(knobs::ARK_PACE_CAP, 40 * SEC);
    assert_eq!(knobs::BYTE_GAP_CAP, 60 * SEC);
    assert_eq!(knobs::STALL_RTT, 4);
    // The most the one-byte count of a request holds, and the size of the largest request it allows.
    assert_eq!(knobs::MAX_REQ_RANGES, 255);
    assert_eq!(vinc_values::wire::REQ_MAX, 34 + 16 * 255);
}

#[test]
fn arrival_curve_target_is_the_verified_rate_times_one_second_within_the_bounds() {
    let store = PStore::random(41, 24 << 20);
    let slow = ProvCfg::new(store.clone(), 20);
    let fast = ProvCfg::new(store.clone(), 3000);
    let mut sim = Sim::new(vec![slow, fast], ClientStore::new());
    sim.start();
    sim.run_until(40 * SEC, |s| s.fetch.is_done());
    let tops = topups(&sim);
    // The first top-up of each provider is before 500 ms of samples: the starting target.
    for p in [0u32, 1] {
        let first = tops.iter().find(|t| t.1.0 == p).unwrap();
        assert_eq!(first.3, 786_432, "provider {p}");
    }
    // After the warm-up the fast provider is at the ceiling and the slow one at the floor (20 B/ms is below 64 KiB/s).
    let late_fast: Vec<_> = tops.iter().filter(|t| t.1.0 == 1 && t.0 > 2 * SEC).collect();
    let late_slow: Vec<_> = tops.iter().filter(|t| t.1.0 == 0 && t.0 > 2 * SEC).collect();
    assert!(
        !late_fast.is_empty() && late_fast.iter().all(|t| t.3 == 1_572_864),
        "{late_fast:?}"
    );
    assert!(late_slow.iter().all(|t| t.3 == 65_536), "{late_slow:?}");
    // A middle rate lands between the bounds at rate x 1 s.
    let mid = ProvCfg::new(store.clone(), 300);
    let other = ProvCfg::new(store, 3000);
    let mut sim = Sim::new(vec![mid, other], ClientStore::new());
    sim.start();
    sim.run_until(40 * SEC, |s| s.fetch.is_done());
    let late: Vec<u64> = topups(&sim)
        .iter()
        .filter(|t| t.1.0 == 0 && t.0 > 3 * SEC)
        .map(|t| t.3)
        .collect();
    assert!(!late.is_empty());
    assert!(
        late.iter().take(6).all(|&t| (280_000..=330_000).contains(&t)),
        "300 B/ms x 1 s is about 300 kB: {late:?}"
    );
}

/// A provider that verifies twice the starting target before the warm-up is over gets its rate's target at once: at
/// 20 kB/ms the starting target is less than what one round trip holds in flight, and the provider would idle
/// between top-ups for the rest of the half second.
#[test]
fn a_fast_provider_leaves_the_starting_target_before_the_warm_up_ends() {
    let store = PStore::random(43, 24 << 20);
    let mut sim = Sim::new(
        vec![ProvCfg::new(store.clone(), 20_000), ProvCfg::new(store, 20_000)],
        ClientStore::new(),
    );
    sim.start();
    sim.run_until(40 * SEC, |s| s.fetch.is_done());
    let tops = topups(&sim);
    let first = tops.iter().map(|t| t.0).min().unwrap();
    let early: Vec<u64> = tops
        .iter()
        .filter(|t| t.0 > first + 200 * MS && t.0 < first + 450 * MS)
        .map(|t| t.3)
        .collect();
    assert!(
        !early.is_empty() && early.iter().all(|&t| t == knobs::TGT_MAX),
        "{early:?}"
    );
}

#[test]
fn tail_shrink_cuts_each_top_up_to_a_share_of_what_is_left() {
    let len = 12 << 20;
    let store = PStore::random(42, len);
    let cfgs = (0..4).map(|_| ProvCfg::new(store.clone(), 2000)).collect();
    let mut sim = Sim::new(cfgs, ClientStore::new());
    sim.start();
    sim.run(120);
    assert!(sim.rec.complete());
    let k = 4u64;
    let mut left = len as u64;
    let mut shrunk = 0;
    let mut prev_steal = false;
    let mut minimum = u64::MAX;
    for (_, x) in &sim.rec.traces {
        match x {
            Trace::Steal { .. } => prev_steal = true,
            Trace::TopUp { bytes, .. } => {
                if !prev_steal {
                    let cap = (4 * G).max(left / (2 * k)).max(G);
                    assert!(*bytes <= cap + G, "top-up of {bytes} with {left} left (cap {cap})");
                    if left / (2 * k) < knobs::TGT0 {
                        shrunk += 1;
                    }
                    minimum = minimum.min(*bytes);
                    left = left.saturating_sub(*bytes);
                }
                prev_steal = false;
            }
            _ => prev_steal = false,
        }
    }
    assert!(shrunk > 3, "the tail never shrank");
    assert!(minimum <= 4 * G + G, "the smallest top-up was {minimum}");
}

#[test]
fn an_idle_provider_takes_the_tail_of_the_one_that_would_finish_last() {
    let store = PStore::random(43, 8 << 20);
    let mut sim = Sim::new(
        vec![ProvCfg::new(store.clone(), 3000), ProvCfg::new(store.clone(), 150)],
        ClientStore::new(),
    );
    sim.start();
    sim.run(120);
    assert!(sim.rec.complete());
    let steals = sim.rec.traces_of(|t| {
        if let Trace::Steal { from, to, bytes } = t {
            Some((*from, *to, *bytes))
        } else {
            None
        }
    });
    assert!(!steals.is_empty(), "no steal");
    assert!(
        steals
            .iter()
            .all(|(_, (from, to, bytes))| from.0 == 1 && to.0 == 0 && *bytes >= G)
    );
    let done = sim
        .rec
        .events
        .iter()
        .find(|(_, e)| matches!(e, Event::Complete))
        .unwrap()
        .0;
    assert!(
        done < 8 * SEC,
        "stealing should finish near the sum of the rates, took {} ms",
        done / MS
    );
    sim.store.assert_verified_is_true(store.content());
}

#[test]
fn a_provider_idle_for_two_seconds_is_robbed_even_of_a_small_remainder() {
    let store = PStore::random(44, 3 << 20);
    // Provider 1 sends 1.4 MiB then goes silent with the session up.
    let mut sim = Sim::new(
        vec![
            ProvCfg::new(store.clone(), 3000),
            ProvCfg::new(store.clone(), 3000).stall_after(1_400_000),
        ],
        ClientStore::new(),
    );
    sim.start();
    sim.run(120);
    assert!(sim.rec.complete());
    let steals = sim.rec.traces_of(|t| {
        if let Trace::Steal { from, .. } = t {
            Some(*from)
        } else {
            None
        }
    });
    let (t_steal, from) = steals.first().copied().unwrap();
    assert_eq!(from.0, 1);
    let last_ok = sim
        .rec
        .traces_of(|t| {
            if let Trace::Verified { provider, .. } = t {
                Some(provider.0)
            } else {
                None
            }
        })
        .iter()
        .filter(|(_, p)| *p == 1)
        .map(|(t, _)| *t)
        .max()
        .unwrap();
    assert!(
        t_steal - last_ok >= 2 * SEC,
        "robbed {} ms after its last granule",
        (t_steal - last_ok) / MS
    );
    sim.store.assert_verified_is_true(store.content());
}

#[test]
fn head_hold_releases_the_first_granule_once_96_kib_stand_behind_it() {
    let mut sim = Sim::uniform(1, 1 << 20, 2000);
    sim.start();
    sim.run(60);
    let ev = sim.rec.readable();
    // Groups 1..=6 are announced as they verify; at the sixth, 96 KiB stand behind group 0, which follows at once.
    let offs: Vec<u64> = ev.iter().map(|e| e.1).collect();
    assert_eq!(&offs[..8], &[G, 2 * G, 3 * G, 4 * G, 5 * G, 6 * G, 0, 7 * G]);
    let rel = releases(&sim);
    assert_eq!(rel.len(), 1);
    assert_eq!(rel[0].2, Release::Buffered);
    assert_eq!(
        rel[0].0, ev[5].0,
        "released in the call that verified the sixth later granule"
    );
    let held = sim
        .rec
        .traces_of(|t| if let Trace::Held { off } = t { Some(*off) } else { None });
    assert_eq!(held[0].1, 0);
    assert!(held[0].0 < rel[0].0);
}

#[test]
fn head_hold_with_the_value_ending_in_the_buffer_releases_at_the_tail() {
    let mut sim = Sim::uniform(1, 3 * G as usize, 2000);
    sim.start();
    sim.run(30);
    let rel = releases(&sim);
    assert_eq!(rel.len(), 1);
    assert_eq!(rel[0].2, Release::Tail);
    let offs: Vec<u64> = sim.rec.readable().iter().map(|e| e.1).collect();
    assert_eq!(offs, vec![G, 2 * G, 0]);
}

#[test]
fn head_hold_releases_after_forty_later_granules_when_no_buffer_stands_behind() {
    let store = PStore::random(45, 300 * G as usize);
    let mut sim = Sim::new(vec![ProvCfg::new(store, 4000)], ClientStore::new());
    let ps = sim.all_providers();
    // The first granule, then a far range: nothing contiguous stands behind the first granule.
    sim.start_with(
        &[
            Span { off: 0, len: G },
            Span {
                off: 100 * G,
                len: 60 * G,
            },
        ],
        &ps,
        None,
    );
    sim.run(60);
    let rel = releases(&sim);
    assert_eq!(rel.len(), 1);
    assert_eq!(rel[0].2, Release::Granules);
    let before: usize = sim.rec.readable().iter().take_while(|e| e.1 != 0).count();
    assert_eq!(before, 40, "the first granule follows the 40th later one");
}

#[test]
fn head_hold_gives_up_after_two_seconds() {
    let len = 300 * G as usize;
    let store = PStore::random(46, len);
    let head_frame = Plan::new(len as u64, &[Span { off: 0, len: G }]).unwrap().total();
    // Provider 0 delivers the first granule and goes silent; provider 1 is too slow to fill a buffer in two seconds.
    let cfgs = vec![
        ProvCfg::new(store.clone(), 3000).stall_after(head_frame),
        ProvCfg::new(store, 100),
    ];
    let mut sim = Sim::new(cfgs, ClientStore::new());
    let ps = sim.all_providers();
    sim.start_with(
        &[
            Span { off: 0, len: G },
            Span {
                off: 100 * G,
                len: 120 * G,
            },
        ],
        &ps,
        None,
    );
    assert!(sim.run_until(30 * SEC, |s| !releases(s).is_empty()));
    let rel = releases(&sim);
    assert_eq!(rel[0].2, Release::Timeout);
    let held = sim
        .rec
        .traces_of(|t| if let Trace::Held { off } = t { Some(*off) } else { None });
    assert_eq!(rel[0].0, held[0].0 + 2 * SEC, "held at {} ms", held[0].0 / MS);
    assert!(sim.rec.readable().iter().all(|e| e.1 != 0 || e.0 == rel[0].0));
}

fn silent_sim(rate: u64, latency: u64, after: u64) -> Sim {
    let store = PStore::random(47, 2 << 20);
    Sim::new(
        vec![ProvCfg::new(store, rate).latency(latency).stall_after(after)],
        ClientStore::new(),
    )
}

#[test]
fn stall_redial_waits_four_seconds_then_doubles_to_sixteen() {
    let mut sim = silent_sim(1000, 10 * MS, 400_000);
    sim.start();
    sim.run_until(120 * SEC, |s| redials(s).len() >= 4);
    let r = redials(&sim);
    assert_eq!((r[0].1, r[0].2), (4 * SEC, 8 * SEC));
    assert_eq!((r[1].1, r[1].2), (8 * SEC, 16 * SEC));
    assert_eq!((r[2].1, r[2].2), (16 * SEC, 16 * SEC));
    assert_eq!((r[3].1, r[3].2), (16 * SEC, 16 * SEC));
    // The first fires four seconds after the last byte; each later one a full wait after the previous.
    assert_eq!(r[0].0, sim.sess.last_rx[0].min(r[0].0 - 4 * SEC) + 4 * SEC);
    assert_eq!(r[1].0 - r[0].0, 8 * SEC);
    assert_eq!(r[2].0 - r[1].0, 16 * SEC);
    assert_eq!(r[3].0 - r[2].0, 16 * SEC);
    // Every redial hangs up and dials again.
    assert!(
        sim.rec
            .traces
            .iter()
            .filter(|(_, t)| matches!(t, Trace::Dial(_)))
            .count()
            >= 4
    );
}

#[test]
fn ark_pace_stretches_the_wait_to_three_times_the_granule_pace() {
    // One granule per two seconds, then silence: the wait is three granule gaps, not four seconds.
    let mut sim = silent_sim(8, 10 * MS, 8 * 2048 * 6);
    sim.start();
    sim.run_until(300 * SEC, |s| !redials(s).is_empty());
    let (_, wait, _) = redials(&sim)[0];
    assert!((6 * SEC..6_400_000_000).contains(&wait), "wait {} ms", wait / MS);
}

#[test]
fn stall_rtt_waits_four_round_trips_on_a_slow_session() {
    // 1.5 s each way: rtt 3 s, so the wait is at least 12 s.
    let mut sim = silent_sim(1000, 1500 * MS, 300_000);
    sim.start();
    sim.run_until(200 * SEC, |s| !redials(s).is_empty());
    let (t, wait, _) = redials(&sim)[0];
    assert_eq!(wait, 12 * SEC);
    assert!(t >= sim.sess.last_rx[0].min(t) + 4 * SEC);
}

#[test]
fn stall_live_keeps_a_slow_session_that_is_still_receiving() {
    let mut sim = silent_sim(1000, 200 * MS, 300_000);
    sim.sess.live = true;
    sim.start();
    sim.run_until(60 * SEC, |_| false);
    assert!(redials(&sim).is_empty(), "a live slow session was redialled");
    // A probe timeout makes the session not live: the redial follows.
    sim.sess.pto = true;
    let end = sim.now + 60 * SEC;
    sim.run_until(end, |s| !redials(s).is_empty());
    assert_eq!(redials(&sim).len(), 1);
}
