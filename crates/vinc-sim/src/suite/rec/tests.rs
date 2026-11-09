//! Recorder tests: hashes against the reference text, accounting, intents, resumes and the oracle.

#![allow(clippy::unwrap_used)]

use std::net::SocketAddr;
use std::rc::Rc;

use super::*;
use crate::suite::grade::fixture::blank_world;
use crate::suite::world::model::{Change, ChangeKind, IntentKind};

fn rec(nodes: usize) -> Rec {
    Rec::new(Rc::new(blank_world("S2", nodes, 100 * NS)))
}

fn addr(n: u8) -> SocketAddr {
    SocketAddr::from(([10, 0, 0, n], 4000))
}

fn publish(r: &mut Rec, node: usize, t: u64, deadline: u64, receivers: &[usize], must: MustArg) -> u32 {
    r.intent(
        IntentKind::Publish,
        node,
        t,
        deadline,
        receivers,
        50,
        must,
        IntentMeta::default(),
    )
}

#[test]
fn trace_hash_matches_the_reference_text() {
    let mut r = rec(2);
    r.node_started(0, 0);
    r.node_started(1, 5);
    let iid = publish(&mut r, 0, 10, 100, &[1], MustArg::Flag(true));
    r.wire(0, 12, 100, false, false, false, 0, None);
    r.delivered(iid, 1, 20, 50);
    r.violation(20, "G-INT", 1, "it's bad");
    r.node_stopped(1, 30, false);
    r.nat_rebind(1, 31);
    r.value_bytes_written(35, 1, 7, 0, 64, 64);
    r.core_event(40, 0, 0, &MemberEvent::Connected);
    r.finish(100, 1234.5, 0);
    // recorded from the reference recorder's hash calls for the same sequence
    assert_eq!(r.trace_hash(), "3b46d8171d4ee51593ade1fef8541651");
    assert_eq!(r.wire_bytes, 100);
    assert_eq!(r.app_bytes, 114);
}

#[test]
fn trace_hash_is_repeatable_and_input_sensitive() {
    let run = |size| {
        let mut r = rec(1);
        r.wire(0, 1, size, false, false, false, 0, None);
        r.finish(10, 0.0, 0);
        r.trace_hash()
    };
    assert_eq!(run(10), run(10));
    assert_ne!(run(10), run(11));
}

#[test]
fn violations_keep_three_per_message_but_count_all() {
    let mut r = rec(1);
    for i in 0..5 {
        r.violation(i, "G-INT", 0, "same");
    }
    r.violation(9, "G-INT", 0, "other");
    assert_eq!(r.violations.len(), 4);
    assert_eq!(r.vcount[&("G-INT".to_owned(), "same".to_owned())], 5);
    r.crash(10, 0, "poll_event", "KeyError");
    assert_eq!(r.crashes, 1);
    let v = r.violations.last().unwrap();
    assert_eq!(v.gate, "G-SPEC");
    assert_eq!(
        v.msg,
        "protocol raised KeyError in poll_event (never raise on peer input)"
    );
}

#[test]
fn wire_accounting() {
    let mut r = rec(2);
    r.idle = Some((10, 20));
    r.amp_probe(0, addr(9));
    r.transmit_call(0, 5);
    r.transmit_call(0, 15);
    r.wire(0, 5, 100, true, false, false, 0, None);
    r.wire(0, 15, 40, false, true, true, 0, Some(addr(9)));
    r.wire(1, 20, 0, true, false, false, 77, None);
    r.udp_received(0, 16, addr(9), 28, 5);
    r.carrier_received(0, 17, 6);
    assert_eq!((r.tx_count, r.idle_tx), (2, 1));
    assert_eq!((r.wire_bytes, r.idle_bytes, r.tcp_bytes), (140, 40, 40));
    assert_eq!(r.third_bytes, 100 + 77);
    assert_eq!(r.node_tx_bytes[&0], 140);
    assert_eq!(r.plaintext_payload, vec![(0, 15)]);
    assert_eq!(r.amp[&addr(9)], [28, 40]);
    assert_eq!(r.redundant, 11);
    r.adversary_injected(0, 30, 10, addr(9));
    assert_eq!(r.amp[&addr(9)][0], 28 + 38);
    assert_eq!(r.adv["inject"], 1);
    r.adversary_action("replay");
    assert_eq!(r.adv["replay"], 1);
    r.carrier_opened();
    assert_eq!(r.carriers, 1);
}

#[test]
fn plaintext_payload_keeps_the_first_four() {
    let mut r = rec(1);
    for t in 0..9 {
        r.wire(0, t, 1, false, true, false, 0, None);
    }
    assert_eq!(r.plaintext_payload.len(), 4);
}

#[test]
fn intent_must_rules_follow_the_reference() {
    let mut r = rec(4);
    let flag = publish(&mut r, 0, 0, 10, &[1, 2], MustArg::Flag(true));
    let none = publish(&mut r, 0, 0, 10, &[1, 2], MustArg::Flag(false));
    let set = publish(&mut r, 0, 0, 10, &[1, 2, 3], MustArg::Set(vec![2]));
    let empty_set = publish(&mut r, 0, 0, 10, &[1], MustArg::Set(vec![]));
    let echo_flag = r.intent(
        IntentKind::Echo,
        0,
        0,
        10,
        &[],
        32,
        MustArg::Flag(true),
        IntentMeta::default(),
    );
    let echo_set = r.intent("echo", 0, 0, 10, &[], 32, MustArg::Set(vec![]), IntentMeta::default());
    let get = |i: u32| &r.intents[&i];
    assert!(get(flag).must && get(flag).must_set.len() == 2);
    assert!(!get(none).must && get(none).must_set.is_empty());
    assert!(get(set).must && get(set).must_set.len() == 1);
    assert!(!get(empty_set).must);
    assert!(get(echo_flag).must && get(echo_flag).must_set.is_empty());
    assert!(!get(echo_set).must);
    assert!(get(flag).small && !get(echo_flag).small);
    assert_eq!(r.next_iid, 7);
}

#[test]
fn unknown_intent_kind_is_a_spec_violation_not_a_panic() {
    let mut r = rec(1);
    assert_eq!(
        r.intent("persist", 0, 0, 1, &[], 0, MustArg::Flag(false), IntentMeta::default()),
        0
    );
    assert_eq!(r.violations.len(), 1);
    assert!(r.intents.is_empty());
}

#[test]
fn delivery_counts_bytes_once_and_flags_a_duplicate_broadcast() {
    let mut r = rec(3);
    let iid = publish(&mut r, 0, 0, 50, &[1], MustArg::Flag(true));
    r.delivered(iid, 1, 5, 50);
    r.delivered(iid, 1, 6, 50);
    assert_eq!(r.app_bytes, 50);
    assert_eq!(r.intents[&iid].delivered[&1], 5);
    assert_eq!(r.violations.len(), 1);
    assert_eq!(r.violations[0].gate, "G-INT");
    let push = r.intent(
        IntentKind::Push,
        0,
        0,
        50,
        &[2],
        10,
        MustArg::Flag(true),
        IntentMeta::default(),
    );
    r.delivered(push, 2, 7, 10);
    r.delivered(push, 2, 8, 10);
    assert_eq!(r.violations.len(), 1, "a repeated push is ignored silently");
    r.delivered(999, 0, 1, 1);
    assert_eq!(r.app_bytes, 60);
    assert!(r.message_first_delivery(9, 1, 3));
    assert!(!r.message_first_delivery(9, 1, 3));
    assert_eq!(r.violations.len(), 2);
}

#[test]
fn echo_timeline_keeps_first_connect_and_serve_and_last_write() {
    let mut r = rec(2);
    let iid = r.intent(
        IntentKind::Echo,
        0,
        0,
        50,
        &[],
        32,
        MustArg::Flag(true),
        IntentMeta::default(),
    );
    r.echo_connected(iid, 3);
    r.echo_connected(iid, 9);
    r.echo_written(iid, 4);
    r.echo_written(iid, 6);
    r.echo_served(iid, 8);
    r.echo_served(iid, 12);
    r.delivered(iid, 0, 14, 32);
    let e = r.echo[&iid];
    assert_eq!(
        (e.connected, e.written, e.served, e.done),
        (Some(3), Some(6), Some(8), Some(14))
    );
}

#[test]
fn alive_and_suspended_intervals() {
    let mut r = rec(2);
    r.node_started(0, 10);
    r.node_stopped(0, 20, true);
    r.node_started(0, 30);
    r.suspended(0, 40, 5);
    assert!(!r.alive_at(0, 9) && r.alive_at(0, 10) && r.alive_at(0, 19) && !r.alive_at(0, 20));
    assert!(r.alive_at(0, 1000));
    assert!(r.alive_through(0, 10, 19) && !r.alive_through(0, 10, 21) && r.alive_through(0, 30, 99));
    assert!(r.suspended_at(0, 40) && r.suspended_at(0, 44) && !r.suspended_at(0, 45));
    assert!(!r.alive_at(1, 5));
    r.node_stopped(1, 3, false);
    assert!(!r.alive_iv.contains_key(&1));
}

#[test]
fn resume_records_collect_wire_bytes_until_the_first_app_byte() {
    let mut r = rec(2);
    r.resumed(0, 100, false);
    assert!(r.resumes.is_empty(), "no open intents, no record");
    r.resumed(0, 100, true);
    r.link_returned(1, 100, true);
    r.restarted_with_state(0, 105, true);
    r.wire(0, 101, 10, false, false, false, 0, None);
    r.wire(1, 101, 7, false, false, false, 0, None);
    let early = publish(&mut r, 1, 90, 400, &[0], MustArg::Flag(true));
    r.delivered(early, 0, 99, 1);
    assert!(
        r.resumes.iter().all(|x| x.first.is_none()),
        "a delivery before the event does not close it"
    );
    let late = publish(&mut r, 1, 90, 400, &[0], MustArg::Flag(true));
    r.delivered(late, 0, 120, 1);
    r.wire(0, 130, 1000, false, false, false, 0, None);
    let (a, b, c) = (&r.resumes[0], &r.resumes[1], &r.resumes[2]);
    assert_eq!((a.kind, a.first, a.bytes), (ResumeKind::Resume, Some(120), 10));
    assert_eq!((c.kind, c.first, c.bytes), (ResumeKind::Restart, Some(120), 10));
    // node 1 is the sender of the intent, so its own record closes at the same delivery
    assert_eq!((b.kind, b.first, b.bytes), (ResumeKind::Link, Some(120), 7));
}

#[test]
fn store_writes_close_a_resume_and_count_new_bytes_only() {
    let mut r = rec(1);
    r.restarted_with_state(0, 10, true);
    r.value_bytes_written(11, 0, 1, 0, 100, 0);
    assert_eq!(r.app_bytes, 0);
    assert_eq!(r.resumes[0].first, None);
    r.value_bytes_written(12, 0, 1, 0, 100, 64);
    assert_eq!(r.app_bytes, 64);
    assert_eq!(r.resumes[0].first, Some(12));
    assert_eq!(r.value_events.len(), 2);
}

#[test]
fn view_epochs_must_strictly_increase_per_incarnation() {
    let mut r = rec(1);
    r.core_event(1, 0, 1, &MemberEvent::ViewChanged { epoch: 5 });
    r.core_event(2, 0, 1, &MemberEvent::ViewChanged { epoch: 6 });
    assert_eq!(r.violations.len(), 0);
    r.core_event(3, 0, 1, &MemberEvent::ViewChanged { epoch: 6 });
    assert_eq!(r.violations.len(), 1);
    assert_eq!(r.violations[0].gate, "G-AWARE");
    r.core_event(4, 0, 2, &MemberEvent::ViewChanged { epoch: 1 });
    assert_eq!(r.violations.len(), 1, "a new incarnation starts over");
}

#[test]
fn membership_events_are_recorded_with_their_member_and_version() {
    let mut r = rec(3);
    r.core_event(5, 0, 0, &MemberEvent::Joined(Some(1)));
    r.core_event(
        6,
        0,
        0,
        &MemberEvent::StackChanged {
            member: Some(1),
            version: 2,
        },
    );
    r.core_event(7, 0, 0, &MemberEvent::Suspected(None));
    r.core_event(8, 0, 0, &MemberEvent::Incoming);
    assert_eq!(r.membership.len(), 3);
    assert_eq!(r.membership[1].kind, MemberKind::StackChanged);
    assert_eq!(r.membership[1].extra, Some(2));
    assert_eq!(r.membership[2].member, None);
}

#[test]
fn acp_oracle_decides_and_logs() {
    let mut w = blank_world("S12", 4, 100 * NS);
    w.denied = vec![3];
    let mut r = Rec::new(Rc::new(w));
    r.revoke(2, 50);
    assert_eq!(r.acp_decide(10, 0, Some(1)), (true, 10 + 60 * NS));
    assert!(!r.acp_decide(10, 0, Some(3)).0, "denied principal");
    assert!(!r.acp_decide(10, 3, Some(1)).0, "denied asker");
    assert!(r.acp_decide(49, 0, Some(2)).0);
    assert!(!r.acp_decide(50, 0, Some(2)).0, "revoked at that time");
    assert!(!r.acp_decide(10, 0, None).0, "unknown principal");
    assert_eq!(r.acp_allowed(0, 1, 10), Some(true));
    assert_eq!(r.acp_allowed(0, 1, 10 + 60 * NS), Some(true));
    assert_eq!(r.acp_allowed(0, 1, 11 + 60 * NS), None);
    assert_eq!(r.acp_allowed(0, 2, 60), Some(false), "the latest covering answer wins");
    assert_eq!(r.acp_allowed(0, 9, 10), None);
}

#[test]
fn acp_delivery_check_cases() {
    let mut w = blank_world("S12", 4, 100 * NS);
    w.denied = vec![3];
    let mut r = Rec::new(Rc::new(w));
    r.acp_decide(NS, 0, Some(1));
    assert!(
        r.check_acp_delivery(2 * NS, 0, 1),
        "an allow answer covers the delivery"
    );
    assert!(r.check_acp_delivery(2 * NS, 0, 0), "a node's own data needs no answer");
    assert_eq!(r.acp_violations, 0);
    assert!(!r.check_acp_delivery(2 * NS, 0, 2), "no answer: fail closed");
    assert!(!r.check_acp_delivery(2 * NS, 0, None), "unknown origin");
    assert!(!r.check_acp_delivery(2 * NS, 0, 3), "denied origin");
    assert!(!r.check_acp_delivery(2 * NS, 3, 1), "denied receiver");
    assert_eq!(r.acp_violations, 4);
    r.revoke(1, 10 * NS);
    assert!(
        r.check_acp_delivery(15 * NS, 0, 1),
        "inside the revocation bound the earlier answer still counts"
    );
    assert!(
        !r.check_acp_delivery(15 * NS + 1, 0, 1),
        "after the bound the delivery is a violation"
    );
    assert_eq!(r.acp_violations, 5);
    assert_eq!(r.violations.iter().filter(|v| v.gate == "G-ACP").count(), 5);
    assert!(r.violations.last().unwrap().msg.contains("revocation bound"));
}

#[test]
fn state_samples_keep_peaks_and_soak_thirds() {
    let mut w = blank_world("S15", 1, 90 * NS);
    w.soak = true;
    let mut r = Rec::new(Rc::new(w));
    r.state_sample(10 * NS, 0, 5);
    r.state_sample(40 * NS, 0, 9);
    r.state_sample(41 * NS, 0, 7);
    r.state_sample(89 * NS, 0, 3);
    r.state_sample(90 * NS, 0, 4);
    assert_eq!(r.state_peaks[&0], 9);
    assert_eq!(r.state_thirds[&0], [5, 9, 4]);
}

#[test]
fn changes_start_from_the_world_and_grow_with_address_changes() {
    let mut w = blank_world("S3", 2, 100 * NS);
    w.changes.push(Change {
        t: 5,
        kind: ChangeKind::Join,
        node: 1,
        version: None,
    });
    let mut r = Rec::new(Rc::new(w));
    assert_eq!(r.changes.len(), 1);
    r.address_change(0, 9);
    assert_eq!(r.changes.len(), 2);
    assert_eq!(r.changes[1].node, 0);
    assert_eq!(r.changes[1].kind, ChangeKind::Addr);
}

#[test]
fn reconcile_cost_and_pushlog_order_are_stored() {
    let mut r = rec(2);
    r.reconcile_done(500, 0);
    r.reconcile_done(300, 4);
    assert_eq!(r.reconcile_cost, vec![(500, 1), (300, 4)]);
    r.pushlog_delivered(0, 1, 1);
    r.pushlog_delivered(0, 1, 2);
    assert_eq!(r.pushlog_order[&(0, 1)], vec![1, 2]);
}
