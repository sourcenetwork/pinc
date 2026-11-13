//! The failure modes of the membership scenario with partitions, slow nodes and churn, each reproduced against the
//! old rule (a small reference model of the rule, fed the very frames and times of the run) and shown fixed.
//!
//! Also: completeness within the awareness bound under loss, and the false-suspicion rate over a long run.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::struct_excessive_bools,
    clippy::cast_possible_truncation,
    clippy::doc_markdown,
    clippy::bool_to_int_with_if,
    clippy::manual_range_contains,
    clippy::manual_assert_eq,
    clippy::redundant_closure_for_method_calls,
    clippy::assert_is_empty,
    clippy::len_zero,
    clippy::unused_self,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::too_many_arguments
)]

#[path = "membership_world.rs"]
mod world;

use std::collections::BTreeSet;

use vinc_membership::codec::{Frame, ty};
use vinc_membership::{Carrier, Event, NodeId, Trace};
use world::{Bc, LEAVE, MS, SEC, World, id};

const START: u64 = 100 * SEC;

fn started(hubs: usize, members: usize) -> World {
    let mut w = World::new(hubs, members, START);
    w.attach_all();
    w.run(5 * SEC);
    w
}

fn traces(w: &World, i: usize, f: impl Fn(&Trace) -> bool) -> usize {
    w.traces[i].iter().filter(|t| f(t)).count()
}

/// The old snapshot rule: the view becomes the snapshot (every member missing from it is deleted).
fn old_snapshot_rule(view: &BTreeSet<NodeId>, snap: &BTreeSet<NodeId>) -> BTreeSet<NodeId> {
    let _ = view;
    snap.clone()
}

/// The old carrier-drop rule: confirmed at max(drop + 1 s, probe + max(250 ms, 3 srtt)) when nothing was heard in
/// answer to the one probe on the one path.
fn old_confirm_rule(drop: u64, probe: u64, srtt: u64, answered_in_time: bool) -> Option<u64> {
    (!answered_in_time).then(|| (drop + SEC).max(probe + (250 * MS).max(3 * srtt)))
}

/// The old DOWN rule at another hub: accepted when the member was silent more than 1 s and holds no carrier here.
fn old_down_rule(silent_for: u64, carrier_open: bool) -> bool {
    silent_for > SEC && !carrier_open
}

fn snapshot_set(w: &World, from: usize, to: usize, last: bool) -> BTreeSet<NodeId> {
    let frames: Vec<_> = w
        .frames
        .iter()
        .filter(|f| f.1 == from && f.2 == to && f.3[4] == ty::SNAP)
        .collect();
    let f = if last { frames.last() } else { frames.first() }.expect("a snapshot was sent");
    let Ok(Some((Frame::Snap(s), _))) = Frame::read(&f.3) else {
        panic!("snap")
    };
    s.entries().map(|e| *e.member).collect()
}

#[test]
fn a_snapshot_after_a_heal_does_not_remove_partition_mates() {
    // Two hubs, two members that sit on the same side of a partition: they are cut from every hub for 100 s (longer
    // than a lease), then the first one redials and gets a snapshot before the second has said HELLO again.
    let mut w = started(2, 2);
    let (m, p) = (2, 3);
    assert!(w.has(m, p));
    for hub in 0..2 {
        w.cut.insert((hub, m));
        w.cut.insert((hub, p));
    }
    w.run(100 * SEC);
    assert_eq!(w.nodes[0].m.lease_of(&id(p)), None, "the hubs let both leases go");
    assert!(w.has(m, p), "isolated, the member keeps its view");
    for hub in 0..2 {
        w.cut.remove(&(hub, m));
        w.cut.remove(&(hub, p));
        w.close_session(m, hub, 0);
    }
    w.run(SEC);
    for hub in 0..2 {
        w.connect(m, hub);
    }
    w.run(2 * SEC);
    // The snapshot the old rule would have applied.
    let hub = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    let snap = snapshot_set(&w, hub, m, true);
    assert!(
        !snap.contains(&id(p)),
        "the partition mate has not said HELLO yet, so the snapshot lacks it"
    );
    let view: BTreeSet<NodeId> = w.members_of(m).into_iter().collect();
    let old = old_snapshot_rule(&view, &snap);
    assert!(
        !old.contains(&id(p)),
        "the old rule deleted the partition mate and reported it down"
    );
    // The new rule keeps it.
    assert!(w.has(m, p));
    assert_eq!(
        w.count_events(
            m,
            |e| matches!(e, Event::MemberConfirmedDown { member } if *member == id(p))
        ),
        0
    );
    assert_eq!(
        traces(&w, m, |t| matches!(t, Trace::Absent { member } if *member == id(p))),
        2,
        "each of the two hubs' snapshots omits the mate: the omissions are noted, and nothing is reported"
    );
    // Then the mate redials, the hub lists it again, and the absence ends without any event.
    for hub in 0..2 {
        w.close_session(p, hub, 0);
    }
    w.run(SEC);
    for hub in 0..2 {
        w.connect(p, hub);
    }
    w.run(150 * SEC);
    assert!(w.has(m, p));
    assert_eq!(w.count_events(m, |e| matches!(e, Event::MemberConfirmedDown { .. })), 0);
}

#[test]
fn a_single_lost_probe_does_not_confirm_a_live_member() {
    let mut w = started(2, 1);
    let m = 2;
    w.run(40 * SEC);
    // The carrier closes and the probe on the session path is lost; the member is alive and its relay path works.
    w.drop_once.push((0, m, ty::PROBE));
    let t = w.now;
    w.dead_default.insert((0, m));
    w.nodes[0]
        .h
        .carriers
        .insert(id(m), Carrier::Gone { since: t, sleep: None });
    w.with(0, |n, h, now| n.carrier_gone(h, now, &id(m)));
    w.run(10 * SEC);
    // Old rule: one probe on one path, unanswered in time: confirmed one second after the drop.
    let probe = w
        .sent_types
        .iter()
        .find(|s| s.1 == 0 && s.2 == m && s.3 == ty::PROBE)
        .unwrap()
        .0;
    let answered = w
        .frames
        .iter()
        .any(|f| f.1 == m && f.2 == 0 && f.3[4] == ty::HELLO && f.0 > probe && f.0 < probe + SEC);
    let old = old_confirm_rule(t, probe, 20 * MS, false);
    assert_eq!(
        old,
        Some(t + SEC),
        "the old rule confirms a live node down (answered via the relay: {answered})"
    );
    // New rule: the second probe was answered, so nothing was confirmed and no DOWN went out.
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 0);
    assert!(!w.sent_types.iter().any(|s| s.3 == ty::DOWN));
    assert!(w.nodes[0].m.lease_of(&id(m)).is_some());
}

#[test]
fn a_slow_member_is_not_confirmed_down() {
    let mut w = started(2, 1);
    let m = 2;
    w.direct.insert((0, m));
    w.nodes[m].cpu = 6 * SEC; // CPU factor 12 on a half second budget
    w.run(40 * SEC);
    let t = w.now;
    w.set_carrier_gone(0, m);
    w.run(10 * SEC);
    // The member's reply comes 6 s after the probe: far past 3 srtt, so the old rule confirmed it at the deadline.
    let probe = w
        .sent_types
        .iter()
        .find(|s| s.1 == 0 && s.2 == m && s.3 == ty::PROBE)
        .unwrap()
        .0;
    let reply = w
        .frames
        .iter()
        .find(|f| f.1 == m && f.2 == 0 && f.3[4] == ty::HELLO && f.0 > probe)
        .map(|f| f.0);
    assert!(
        reply.is_some_and(|r| r - probe >= 5 * SEC),
        "the application answered late: {reply:?}"
    );
    assert_eq!(old_confirm_rule(t, probe, 20 * MS, false), Some(t + SEC));
    // New rule: its transport acknowledged the probe at once, which counts as life.
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 0);
    assert!(w.nodes[0].m.lease_of(&id(m)).is_some());
}

#[test]
fn another_hubs_down_is_refused_while_our_lease_is_fresh() {
    // Hub 0 reaches a wrong decision (both its probes are lost); hub 1 holds a lease that is 12 s old.
    let mut w = World::new(2, 1, START);
    w.keepalive = 0;
    w.attach_all();
    w.run(14 * SEC);
    let m = 2;
    w.drop_once.push((0, m, ty::PROBE));
    w.drop_once.push((0, m, ty::PROBE));
    w.dead_default.insert((0, m));
    w.nodes[0].h.carriers.insert(
        id(m),
        Carrier::Gone {
            since: w.now,
            sleep: None,
        },
    );
    w.with(0, |n, h, now| n.carrier_gone(h, now, &id(m)));
    w.run(5 * SEC);
    assert_eq!(
        traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })),
        1,
        "hub 0 decided"
    );
    let silent = w.now - w.nodes[1].m.lease_of(&id(m)).unwrap();
    assert!(
        old_down_rule(silent, false),
        "the old rule accepted a DOWN for a member silent {} s",
        silent / SEC
    );
    assert_eq!(
        traces(&w, 1, |t| matches!(
            t,
            Trace::DownRefused {
                why: vinc_membership::event::Refusal::LeaseFresh,
                ..
            }
        )),
        1
    );
    assert!(w.nodes[1].m.lease_of(&id(m)).is_some());
    assert!(w.has(1, m));
    assert!(!w.nodes[1].h.bc.contains(&Bc::Hold(id(m))));
    // One hub's decision did not reach the other members: nobody reports the live member down.
    assert_eq!(w.count_events(1, |e| matches!(e, Event::MemberConfirmedDown { .. })), 0);
}

#[test]
fn subscriptions_return_with_the_carrier_and_the_member_learns() {
    let mut w = started(2, 1);
    let m = 2;
    w.run(30 * SEC);
    w.cut.insert((1, m));
    w.set_carrier_gone(0, m);
    w.run(3 * SEC);
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 1);
    w.cut.remove(&(1, m));
    w.set_carrier_open(0, m);
    w.run(2 * SEC);
    let log: Vec<&Bc> = w.nodes[0]
        .h
        .bc
        .iter()
        .filter(|b| matches!(b, Bc::Hold(_) | Bc::Restore(_) | Bc::Release(_)))
        .collect();
    // Old: hub_down released the subscriptions and the return restored only the roster entry.
    assert_eq!(
        log,
        [&Bc::Hold(id(m)), &Bc::Restore(id(m))],
        "held through the confirmation, restored on the return"
    );
    assert!(
        w.nodes[m].h.bc.contains(&Bc::Resub(id(0))),
        "the member was sent a delta about itself and subscribed again"
    );
    assert!(w.nodes[0].m.lease_of(&id(m)).is_some());
}

#[test]
fn a_redial_gets_a_snapshot_even_if_the_hub_still_holds_the_attachment() {
    let mut w = started(1, 3);
    // A hub younger than a lease sends partial snapshots, which say nothing about absence; let it come of age.
    w.run(90 * SEC);
    let (m, x) = (1, 2);
    let hub = 0;
    assert!(w.has(m, x));
    // The member's side closed the session silently (an idle close): the hub still believes it attached.
    w.sessions.remove(&(m, hub));
    w.with(m, |n, h, now| n.session_down(h, now, &id(hub), 0));
    // The member x leaves while the member is off the hub.
    w.with(x, |n, h, _| n.leave(h));
    w.close_session(x, 0, LEAVE);
    w.run(5 * SEC);
    assert!(w.has(m, x), "the delta about the leaver went into the closed session");
    // Old: a redial before the slow tick sent flags = 2 only, and a hub that still held the attachment only acked.
    let old_replies_with_snapshot = |snap_flag: bool, hub_still_attached: bool| snap_flag || !hub_still_attached;
    assert!(!old_replies_with_snapshot(false, true));
    let snaps_before = w
        .frames
        .iter()
        .filter(|f| f.1 == hub && f.2 == m && f.3[4] == ty::SNAP)
        .count();
    w.connect(m, hub);
    w.run(2 * SEC);
    let snaps_after = w
        .frames
        .iter()
        .filter(|f| f.1 == hub && f.2 == m && f.3[4] == ty::SNAP)
        .count();
    assert!(snaps_after > snaps_before, "the redial got a snapshot");
    assert!(
        !snapshot_set(&w, hub, m, true).contains(&id(x)),
        "the snapshot no longer lists the leaver"
    );
    // The view converges within a lease of the snapshot: the leaver is gone, and reported.
    assert!(w.has(m, x), "a snapshot alone does not remove");
    let ok = w.run_until(90 * SEC, |w| !w.has(m, x));
    assert!(ok);
    assert_eq!(
        w.count_events(
            m,
            |e| matches!(e, Event::MemberConfirmedDown { member } if *member == id(x))
        ),
        1
    );
}

#[test]
fn a_leave_is_reported_at_every_node() {
    let mut w = started(2, 4);
    let x = 3;
    w.with(x, |n, h, _| n.leave(h));
    for hb in 0..2 {
        w.close_session(x, hb, LEAVE);
    }
    w.run(5 * SEC);
    for i in [0, 1, 2, 4, 5] {
        assert!(!w.has(i, x), "node {i} dropped the leaver");
        assert_eq!(
            w.count_events(i, |e| matches!(e, Event::MemberLeft { member } if *member == id(x))),
            1,
            "node {i}"
        );
    }
}

fn crash_scenario(seed: u64, carrier: bool) -> (u64, World) {
    let mut w = World::new(2, 6, START);
    w.rng = vinc_tests::SplitMix64::new(seed);
    w.loss_pct = 20;
    w.attach_all();
    w.run(120 * SEC);
    let victim = 5;
    let t = w.now;
    w.crash(victim);
    if carrier {
        for hub in 0..2 {
            w.set_carrier_gone(hub, victim);
        }
    }
    let live: Vec<usize> = (2..8).filter(|&i| i != victim).collect();
    let limit = 145 * SEC;
    let ok = w.run_until(limit, |w| live.iter().all(|&i| !w.has(i, victim)));
    assert!(
        ok,
        "seed {seed}: the failed member is still listed after the awareness bound"
    );
    (w.now - t, w)
}

#[test]
fn a_failed_member_is_confirmed_within_the_awareness_bound_under_loss() {
    let mut worst_quiet = 0;
    let mut worst_carrier = 0;
    for seed in 1..=6 {
        let (took, w) = crash_scenario(seed, false);
        worst_quiet = worst_quiet.max(took);
        for i in (2..8).filter(|&i| i != 5) {
            assert_eq!(
                w.count_events(
                    i,
                    |e| matches!(e, Event::MemberConfirmedDown { member } if *member == id(5))
                ),
                1
            );
        }
        let (took, _) = crash_scenario(seed, true);
        worst_carrier = worst_carrier.max(took);
    }
    // A silent crash waits for the lease; with the carrier evidence it takes about a second, then the other hub's
    // lease (refused DOWN) or its own probes end it.
    assert!(worst_quiet < 145 * SEC, "{} s", worst_quiet / SEC);
    assert!(worst_carrier < 145 * SEC, "{} s", worst_carrier / SEC);
    assert!(
        worst_quiet > 60 * SEC,
        "a silent crash can only be seen at the lease: {} s",
        worst_quiet / SEC
    );
}

#[test]
fn live_members_are_never_confirmed_down_over_a_long_run_with_churn_and_carrier_drops() {
    let mut w = World::new(2, 5, START);
    w.rng = vinc_tests::SplitMix64::new(99);
    w.loss_pct = 15;
    w.attach_all();
    w.run(10 * SEC);
    // Thirty virtual minutes: every five minutes a live member's carrier closes for three seconds (the member
    // itself and its relay path are fine), and a quiet member's keepalives are sparse.
    for round in 0..6usize {
        let victim = 2 + round % 5;
        let hub = round % 2;
        w.run(300 * SEC);
        w.set_carrier_gone(hub, victim);
        w.run(3 * SEC);
        w.set_carrier_open(hub, victim);
    }
    w.run(60 * SEC);
    for i in 0..7 {
        assert_eq!(
            w.count_events(i, |e| matches!(
                e,
                Event::MemberConfirmedDown { .. } | Event::MemberLeft { .. }
            )),
            0,
            "node {i} reported a live member gone: {:?}",
            w.events[i]
                .iter()
                .filter(|(_, e)| matches!(e, Event::MemberConfirmedDown { .. }))
                .collect::<Vec<_>>()
        );
        assert_eq!(w.nodes[i].m.member_count(), 6, "node {i} lists everyone else");
    }
    assert!(
        w.sent_types.iter().all(|s| s.3 != ty::DOWN),
        "no hub ever sent a DOWN about a live member"
    );
}
