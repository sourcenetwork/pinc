//! Terms on hand-built recordings, the fair rule and the delivery check.

use std::rc::Rc;

use pinc_sim::suite::grade::fixture::blank_world;
use pinc_sim::suite::grade::{
    RunFacts, TERMS, Terms, compute_fair_terms, compute_terms, delivery_share, delivery_shares, with_fair,
};
use pinc_sim::suite::rec::{IntentMeta, MemberEvent, MustArg, Rec};
use pinc_sim::suite::world::model::{Change, ChangeKind, IntentKind, World};

use crate::common::*;

// ----------------------------------------------------------------------------------------------- terms

struct Terms21 {
    world: Rc<World>,
    rec: Rec,
    facts: RunFacts,
}

/// The hand-built recording behind the term tests; every expected value below is worked out in the comments.
fn term_run() -> Terms21 {
    let mut w = blank_world("S3", 4, sec(100));
    w.score_c3 = true;
    w.changes.push(Change {
        t: sec(50),
        kind: ChangeKind::Crash,
        node: 3,
        version: None,
    });
    let world = Rc::new(w);
    let mut rec = Rec::new(world.clone());
    let mut facts = RunFacts::new(&world);
    for i in 0..4 {
        rec.node_started(i, 0);
    }
    let meta = IntentMeta::default;
    // publish by node 0 to 1, 2, 3; must is {1, 2}: node 1 in 0.2 s, node 2 late (12 s), node 3 never
    let a = rec.intent(
        IntentKind::Publish,
        0,
        sec(1),
        sec(11),
        &[1, 2, 3],
        50,
        MustArg::Set(vec![1, 2]),
        meta(),
    );
    rec.delivered(a, 1, ms(1200), 50);
    rec.delivered(a, 2, sec(13), 50);
    // a push under bulk in 0.5 s and five manage requests under bulk in 1 to 5 s
    let b = rec.intent(
        IntentKind::Push,
        0,
        sec(2),
        sec(12),
        &[1],
        20,
        MustArg::Flag(true),
        meta(),
    );
    rec.set_under_bulk(b, true);
    rec.delivered(b, 1, ms(2500), 20);
    for k in 1..=5 {
        let m = rec.intent(
            IntentKind::Manage,
            0,
            sec(3),
            sec(20),
            &[1],
            0,
            MustArg::Flag(true),
            IntentMeta { to: Some(1), ..meta() },
        );
        rec.set_under_bulk(m, true);
        rec.delivered(m, 1, sec(3 + k), 10);
    }
    // two must echoes: the first connects at 10.1 s and returns at 10.4 s, the second never connects; one
    // non-must echo that counts nowhere
    let e1 = rec.intent(
        IntentKind::Echo,
        0,
        sec(10),
        sec(40),
        &[],
        32,
        MustArg::Flag(true),
        meta(),
    );
    rec.echo_connected(e1, sec(10) + ms(100));
    rec.delivered(e1, 0, sec(10) + ms(400), 32);
    rec.intent(
        IntentKind::Echo,
        0,
        sec(20),
        sec(50),
        &[],
        32,
        MustArg::Flag(true),
        meta(),
    );
    rec.intent(
        IntentKind::Echo,
        0,
        sec(21),
        sec(50),
        &[],
        32,
        MustArg::Flag(false),
        meta(),
    );
    // fetches: A (2000 B, two providers, stream, done in 10 s, first byte after 1 s, stall 0.25), B (3000 B, never),
    // C (not must), D (1000 B, stream, never, no first byte)
    let stream = |first, stall| IntentMeta {
        providers: vec![0, 2],
        stream_rate: Some(8000),
        first_byte: first,
        stall_frac: stall,
        ..meta()
    };
    let fa = rec.intent(
        IntentKind::Fetch,
        1,
        sec(5),
        sec(65),
        &[1],
        2000,
        MustArg::Flag(true),
        stream(Some(sec(6)), Some(0.25)),
    );
    rec.intent(
        IntentKind::Fetch,
        2,
        sec(6),
        sec(36),
        &[2],
        3000,
        MustArg::Flag(true),
        IntentMeta {
            providers: vec![0],
            ..meta()
        },
    );
    rec.intent(
        IntentKind::Fetch,
        3,
        sec(6),
        sec(36),
        &[3],
        500,
        MustArg::Flag(false),
        IntentMeta {
            providers: vec![0],
            ..meta()
        },
    );
    rec.intent(
        IntentKind::Fetch,
        1,
        sec(7),
        sec(37),
        &[1],
        1000,
        MustArg::Flag(true),
        IntentMeta {
            providers: vec![0],
            stream_rate: Some(8000),
            ..meta()
        },
    );
    // resumes: node 1 at 12 s (closed by the first store write at 15 s), node 2 at 20 s (never closed)
    rec.resumed(1, sec(12), true);
    rec.wire(1, sec(13), 60, false, false, false, 0, None);
    rec.wire(1, sec(14), 40, false, false, false, 0, None);
    rec.value_bytes_written(sec(15), 1, 1, 0, 2000, 2000);
    rec.delivered(fa, 1, sec(15), 0);
    rec.link_returned(2, sec(20), true);
    rec.wire(2, sec(21), 25, false, false, false, 0, None);
    rec.udp_received(0, sec(50), addr(1), 28, 50);
    // wire: 21 020 B outside the idle window (1101 of them third party), 1000 B and five calls inside it
    rec.wire(0, sec(30), 1101, true, false, false, 0, None);
    rec.wire(0, sec(40), 21_020 - 125 - 1101, false, false, false, 0, None);
    for _ in 0..5 {
        rec.transmit_call(0, sec(95));
    }
    rec.wire(0, sec(95), 1000, false, false, false, 0, None);
    // awareness of the crash of node 3: node 0 confirms after 8 s, node 1 only suspects after 2 s, node 2 never
    rec.node_stopped(3, sec(50), false);
    rec.core_event(sec(58), 0, 0, &MemberEvent::ConfirmedDown(Some(3)));
    rec.core_event(sec(52), 1, 0, &MemberEvent::Suspected(Some(3)));
    rec.reconcile_done(500, 0);
    rec.reconcile_done(300, 4);
    for (i, p) in [1000, 2000, 3000].into_iter().enumerate() {
        rec.state_sample(sec(10), i, p);
    }
    for (i, e) in [100, 100, 100, 0].into_iter().enumerate() {
        facts.nodes[i].export_max = e;
    }
    rec.finish(sec(100), 16_515.0, 0);
    Terms21 { world, rec, facts }
}

fn want(t: &Terms, k: &str, v: f64) {
    let got = t.get(k).unwrap_or_else(|| panic!("{k} is absent"));
    assert!(close(got, v), "{k}: got {got}, want {v}");
}

#[test]
fn every_term_on_a_hand_built_recording() {
    let r = term_run();
    assert_eq!(r.rec.app_bytes, 2202);
    assert_eq!(r.rec.wire_bytes, 22_020);
    let t = compute_terms(&r.world, &r.rec, &r.facts);
    // L1: samples 0.2 12 0.5 1 2 3 4 5 s -> p50 3 s, tail (largest 1 of 8) 12 s; the never-delivered non-must is skipped
    want(&t, "L1", 3e9);
    want(&t, "L2", 12e9);
    // L3: echoes 0.4 s and (never done) 30 s to the deadline 50 s: tail 30 s
    want(&t, "L3", 30e9);
    // L4: under bulk 0.5 1 2 3 4 5 s: six samples, tail 5 s
    want(&t, "L4", 5e9);
    // L5: crash of node 3 at 50 s: node 0 8 s, node 1 2 s (a suspicion counts here), node 2 none: end - t0 = 50 s
    want(&t, "L5", 50e9);
    // T1: (10 + 30 + 30) s over (2000 + 3000 + 1000) B; T2: fetch A only; T3: p50 of 1 s and 30 s; T4: 0.25
    want(&t, "T1", 70e9 / 6000.0);
    want(&t, "T2", 5e6);
    want(&t, "T3", 30e9);
    want(&t, "T4", 0.25);
    // C1: (50 redundant + 100 + 25 resume bytes) / 2; C2: (3 s + 80 s) / 2; C3: 4 of 12 must deliveries missing or
    // late; C4: one of two must echoes did not connect
    want(&t, "C1", 87.5);
    want(&t, "C2", 41.5e9);
    want(&t, "C3", 1.0 / 3.0);
    want(&t, "C4", 0.5);
    // B1: 22020 / 2202; B2: 800 B over 5 items; B3, B4: 3 nodes alive through the 10 s idle window
    want(&t, "B1", 10.0);
    want(&t, "B2", 160.0);
    want(&t, "B3", 1000.0 * 120.0);
    want(&t, "B4", 5.0 * 120.0);
    want(&t, "B5", 0.5);
    // R1: 16515 ns / 2202 B; R2: mean of 1000 2000 3000; R3: mean of 100 100 100 0
    want(&t, "R1", 7.5);
    want(&t, "R2", 2000.0);
    want(&t, "R3", 75.0);
    assert_eq!(TERMS.iter().filter(|k| t.get(k).is_none()).count(), 0);
}

#[test]
fn fair_rule_differs_from_the_current_rule_exactly_where_stated() {
    let r = term_run();
    let cur = compute_terms(&r.world, &r.rec, &r.facts);
    let (fair, n) = compute_fair_terms(&r.world, &r.rec, &r.facts);
    // every intended receiver counts, bounded by its deadline: 0.2 10 10 0.5 1 2 3 4 5 s
    want(&fair, "L1", 3e9);
    want(&fair, "L2", 10e9);
    want(&fair, "L4", 5e9);
    // the unfinished stream fetch is fully stalled: (0.25 + 1) / 2
    want(&fair, "T4", 0.625);
    assert_eq!(fair.get("L3"), None, "the fair set holds only the four replaced terms");
    assert_eq!(
        (
            n.small,
            n.small_current,
            n.under_bulk,
            n.under_bulk_current,
            n.stream,
            n.stream_current
        ),
        (9, 8, 6, 6, 2, 1)
    );
    let both = with_fair(&cur, &fair);
    want(&both, "L2", 10e9);
    want(&both, "T4", 0.625);
    want(&both, "L3", 30e9);
    want(&both, "B1", 10.0);
}

#[test]
fn terms_without_samples_are_absent_not_zero() {
    let world = Rc::new(blank_world("S2", 2, sec(100)));
    let mut rec = Rec::new(world.clone());
    rec.node_started(0, 0);
    rec.finish(sec(100), 0.0, 0);
    let t = compute_terms(&world, &rec, &RunFacts::new(&world));
    for k in [
        "L1", "L2", "L3", "L4", "L5", "T1", "T2", "T3", "T4", "C1", "C2", "C3", "C4", "B1", "B2", "B5", "R1", "R2",
    ] {
        assert_eq!(t.get(k), None, "{k}");
    }
    // the idle terms exist whenever there is an idle window: no bytes -> 0, which is a measurement here
    assert_eq!(t.get("B3"), Some(0.0));
    assert_eq!(t.get("B4"), Some(0.0));
    assert_eq!(t.get("R3"), Some(0.0));
}

#[test]
fn small_samples_use_p50_upper_middle_and_ceil_five_percent_tail() {
    // 20 small samples of 1..=20 s: p50 is index 10 (11 s), the tail is the largest 1 (20 s)
    let mk = |n: u64| {
        let world = Rc::new(blank_world("S2", 2, sec(1000)));
        let mut rec = Rec::new(world.clone());
        for k in 1..=n {
            let i = rec.intent(
                IntentKind::Push,
                0,
                0,
                sec(900),
                &[1],
                1,
                MustArg::Flag(true),
                IntentMeta::default(),
            );
            rec.delivered(i, 1, sec(k), 1);
        }
        rec.finish(sec(1000), 0.0, 0);
        compute_terms(&world, &rec, &RunFacts::new(&world))
    };
    let t20 = mk(20);
    want(&t20, "L1", 11e9);
    want(&t20, "L2", 20e9);
    // 21 samples: ceil(1.05) = 2 -> mean of 20 s and 21 s
    let t21 = mk(21);
    want(&t21, "L1", 11e9);
    want(&t21, "L2", 20.5e9);
    let t1 = mk(1);
    want(&t1, "L1", 1e9);
    want(&t1, "L2", 1e9);
}

#[test]
fn delivery_check_counts_receivers_outside_the_must_set() {
    let r = term_run();
    assert_eq!(delivery_share(&r.world, &r.rec), (0, 1));
    let s = delivery_shares(&r.rec);
    assert_eq!(s.must, (8, 8));
    assert_eq!(s.outside, (0, 1));
}
