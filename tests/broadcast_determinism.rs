//! The same inputs give the same outputs: two runs of a scenario that touches every rule leave identical traces,
//! identical frames on the wire and identical deliveries, and the trace carries the transitions the proofs replay.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::expect_used,
    clippy::assert_is_empty,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::type_complexity,
    clippy::cast_possible_truncation
)]

#[path = "broadcast_common.rs"]
mod common;

use common::{Net, SEC, ty};
use pinc_broadcast::Trace;
use pinc_crypto::IdentityAlg;

const T: &[u8] = b"det";

/// Two hubs, a publisher and two subscribers; a partition and its heal, a restart of the publisher, a fallback, a hold and a restore.
fn scenario(alg: IdentityAlg) -> (Vec<Vec<Trace>>, Vec<(u64, usize, usize, u8, bool)>, Vec<Vec<[u8; 8]>>) {
    let mut net = Net::new(alg, 2, 3, SEC);
    net.subscribe(3, T);
    net.subscribe(4, T);
    net.publish(2, T, b"one");
    net.run_until(5 * SEC);
    net.link(3, 0, false);
    net.publish(2, T, b"two");
    net.run_until(12 * SEC);
    net.link(3, 0, true);
    net.run_until(30 * SEC);
    let m = net.id(4);
    let n = &mut net.nodes[0];
    n.t.hold(&mut n.h, &m);
    net.publish(2, T, b"three");
    let n = &mut net.nodes[0];
    n.t.restore(&mut n.h, &m);
    net.pump();
    for i in 2..5 {
        net.cut_from_hubs(i, false);
    }
    net.publish(2, T, b"four");
    for i in 2..5 {
        net.cut_from_hubs(i, true);
    }
    net.run_until(60 * SEC);
    // A restart replaces the machine, and its trace with it: keep what the first life recorded.
    let mut early = Vec::new();
    while let Some(t) = net.nodes[2].t.poll_trace() {
        early.push(t);
    }
    net.restart(2, 61 * SEC);
    net.set_primary(2, 0);
    net.attach(2);
    net.run_until(120 * SEC);
    let traces = (0..net.nodes.len())
        .map(|i| {
            let mut v = if i == 2 { early.clone() } else { Vec::new() };
            while let Some(t) = net.nodes[i].t.poll_trace() {
                v.push(t);
            }
            v
        })
        .collect();
    let delivered = (0..net.nodes.len()).map(|i| net.delivered(i)).collect();
    (traces, net.log.clone(), delivered)
}

#[test]
fn two_runs_of_the_same_inputs_leave_the_same_trace_for_every_algorithm() {
    for alg in [IdentityAlg::Ed25519, IdentityAlg::EcdsaP256] {
        let (t1, w1, d1) = scenario(alg);
        let (t2, w2, d2) = scenario(alg);
        assert_eq!(t1, t2, "{alg:?}");
        assert_eq!(w1, w2, "{alg:?}");
        assert_eq!(d1, d2, "{alg:?}");
    }
}

#[test]
fn the_trace_records_every_kind_of_transition_the_scenario_exercises() {
    let (traces, wire, delivered) = scenario(IdentityAlg::Ed25519);
    let all: Vec<&Trace> = traces.iter().flatten().collect();
    let has = |f: &dyn Fn(&Trace) -> bool| all.iter().any(|t| f(t));
    assert!(has(&|t| matches!(t, Trace::Published { .. })));
    assert!(has(&|t| matches!(t, Trace::Stored { .. })));
    assert!(has(&|t| matches!(t, Trace::Delivered { .. })));
    assert!(has(&|t| matches!(t, Trace::PubAcked { .. })));
    assert!(has(&|t| matches!(t, Trace::SubSent { .. })));
    assert!(has(&|t| matches!(t, Trace::HaveSent { .. })));
    assert!(has(&|t| matches!(t, Trace::GetSent { .. })));
    assert!(has(&|t| matches!(t, Trace::Repaired { .. })));
    assert!(has(&|t| matches!(t, Trace::FallbackSent { .. })));
    assert!(has(&|t| matches!(t, Trace::SubsHeld { .. })));
    assert!(has(&|t| matches!(t, Trace::SubsRestored { .. })));
    assert!(has(&|t| matches!(t, Trace::RestoredSeen { .. })));
    assert!(has(&|t| matches!(t, Trace::FloorReported { .. })));
    assert!(has(&|t| matches!(t, Trace::FloorDone { .. })));
    assert!(has(&|t| matches!(t, Trace::Primary { .. })));
    assert!(wire.iter().any(|l| l.3 == ty::MEMBER_PUSH));
    assert!(delivered[3].len() >= 3);
}

#[test]
fn a_full_trace_queue_reports_how_many_records_it_dropped() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, T);
    for i in 0..10_000u32 {
        net.publish(1, T, &i.to_be_bytes());
    }
    let mut lost = 0u64;
    let mut kept = 0usize;
    while let Some(t) = net.nodes[0].t.poll_trace() {
        match t {
            Trace::Lost { count } => lost += u64::from(count),
            _ => kept += 1,
        }
    }
    assert!(lost > 0, "the hub traced more than the queue holds");
    assert!(kept <= pinc_broadcast::consts::QUEUE_CAP + 1);
}
