//! The subscriber list a hub replicates to its members (SUBS): what a join costs each member, and that every member
//! ends with the hub's list whatever happened to the frames on the way: a change is never applied on the wrong base.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::assert_is_empty
)]

#[path = "broadcast_common.rs"]
mod common;

use std::cell::RefCell;
use std::rc::Rc;

use common::{Net, SEC, ty};
use vinc_broadcast::{SubsDrop, Trace};
use vinc_crypto::IdentityAlg;
use vinc_membership::NodeId;

const T: &[u8] = b"roster";

/// Count the SUBS bytes each node receives.
fn tally(net: &mut Net) -> Rc<RefCell<Vec<usize>>> {
    let got = Rc::new(RefCell::new(vec![0usize; net.nodes.len()]));
    let g = Rc::clone(&got);
    net.filter = Some(Box::new(move |_, to, bytes| {
        if bytes.get(4) == Some(&ty::SUBS) {
            g.borrow_mut()[to] += bytes.len();
        }
        true
    }));
    got
}

/// The live subscribers in id order, cut at `max`: the list every subscriber must hold.
fn expected(net: &Net, subs: &[usize], max: usize) -> Vec<NodeId> {
    let mut ids: Vec<NodeId> = subs.iter().map(|i| net.id(*i)).collect();
    ids.sort_unstable();
    ids.truncate(max);
    ids
}

fn assert_all_hold(net: &Net, subs: &[usize], max: usize) {
    let want = expected(net, subs, max);
    for i in subs {
        assert_eq!(net.nodes[*i].t.known_subscribers(T), want.as_slice(), "subscriber {i}");
    }
}

fn unsubscribe(net: &mut Net, i: usize) {
    let n = &mut net.nodes[i];
    n.t.unsubscribe(&mut n.h, T);
    net.pump();
}

/// A join of `n` subscribers costs each of them the list once and a small change per later join: bytes linear in
/// `n`. Sending the whole list on every change cost the first joiner `n` lists, `16 * n * (n + 1)` bytes.
#[test]
fn a_join_costs_each_subscriber_bytes_linear_in_the_subscribers() {
    let n = 48;
    let mut net = Net::new(IdentityAlg::Ed25519, 1, n, SEC);
    let got = tally(&mut net);
    for i in 1..=n {
        net.subscribe(i, T);
    }
    net.advance(SEC);
    assert_all_hold(&net, &(1..=n).collect::<Vec<_>>(), 256);
    let worst = got.borrow()[1..].iter().copied().max().unwrap();
    assert!(
        worst <= 100 * n,
        "a subscriber received {worst} bytes of lists for {n} joins"
    );
}

/// Subscribes, unsubscribes, a stream that refuses the changes for a while, and a hold and restore: every subscriber
/// ends with the hub's list.
#[test]
fn every_subscriber_ends_with_the_hubs_list() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 12, SEC);
    let mut live: Vec<usize> = (1..=8).collect();
    for i in &live {
        net.subscribe(*i, T);
    }
    assert_all_hold(&net, &live, 256);

    unsubscribe(&mut net, 2);
    unsubscribe(&mut net, 5);
    live.retain(|i| ![2, 5].contains(i));
    assert_all_hold(&net, &live, 256);

    // Subscriber 3's stream refuses frames while two more join: it missed changes, and is sent the whole list once
    // its stream has room.
    let three = net.id(3);
    net.nodes[0].h.full.insert(three);
    for i in [9, 10] {
        net.subscribe(i, T);
        live.push(i);
    }
    net.nodes[0].h.full.remove(&three);
    let now = net.now;
    let hub = &mut net.nodes[0];
    hub.t.peer_writable(&mut hub.h, now, &three);
    net.pump();
    assert_all_hold(&net, &live, 256);

    // Subscriber 4 is held while 11 joins and 6 leaves, then restored: it is sent the whole list.
    let four = net.id(4);
    let hub = &mut net.nodes[0];
    hub.t.hold(&mut hub.h, &four);
    net.pump();
    net.subscribe(11, T);
    unsubscribe(&mut net, 6);
    live.retain(|i| *i != 6);
    live.push(11);
    let hub = &mut net.nodes[0];
    hub.t.restore(&mut hub.h, &four);
    net.pump();
    assert_all_hold(&net, &live, 256);

    // Subscriber 7 loses a change its stream took (the session ended under it), then subscribes again on its new
    // session: it is sent the whole list though its subscription did not change.
    net.filter = Some(Box::new(|_, to, bytes| !(to == 7 && bytes.get(4) == Some(&ty::SUBS))));
    net.subscribe(12, T);
    live.push(12);
    net.filter = None;
    let (now, hub) = (net.now, net.id(0));
    let seven = &mut net.nodes[7];
    seven.t.resubscribe(&mut seven.h, now, &hub);
    net.pump();
    assert_all_hold(&net, &live, 256);
}

/// With more subscribers than `max_subscribers`, a member holds the lowest `max` ids, and a removal from that list
/// brings in the next one.
#[test]
fn a_capped_list_takes_in_the_next_subscriber_when_one_leaves() {
    let limits = vinc_broadcast::Limits {
        max_subscribers: 4,
        ..vinc_broadcast::Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 9], 1, SEC, limits);
    for i in 1..=8 {
        net.attach(i);
    }
    let mut live: Vec<usize> = (1..=7).collect();
    for i in &live {
        net.subscribe(*i, T);
    }
    assert_all_hold(&net, &live, 4);
    for _ in 0..2 {
        let first = expected(&net, &live, 4)[0];
        let i = live.iter().copied().find(|i| net.id(*i) == first).unwrap();
        unsubscribe(&mut net, i);
        live.retain(|x| *x != i);
        assert_all_hold(&net, &live, 4);
    }
    net.subscribe(8, T);
    live.push(8);
    assert_all_hold(&net, &live, 4);
}

fn resubscribe(net: &mut Net, i: usize) {
    let (now, hub) = (net.now, net.id(0));
    let n = &mut net.nodes[i];
    n.t.resubscribe(&mut n.h, now, &hub);
    net.pump();
}

/// Drop every SUBS frame to node `to` while `f` runs: a change lost on a stream that stays up (a relay drop).
fn losing_subs_to(net: &mut Net, to: usize, f: impl FnOnce(&mut Net)) {
    net.filter = Some(Box::new(move |_, t, bytes| {
        !(t == to && bytes.get(4) == Some(&ty::SUBS))
    }));
    f(net);
    net.filter = None;
}

/// A member that missed a change applies no later change on the wrong base: the next change does not start from the
/// version it holds, so it asks the hub and is sent the whole list.
#[test]
fn a_change_on_a_base_the_member_does_not_hold_is_not_applied_and_the_member_asks_for_the_list() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 5, SEC);
    for i in 1..=3 {
        net.subscribe(i, T);
    }
    losing_subs_to(&mut net, 1, |net| net.subscribe(4, T));
    assert_eq!(
        net.nodes[1].t.known_subscribers(T),
        expected(&net, &[1, 2, 3], 256).as_slice()
    );
    net.subscribe(5, T);
    assert_all_hold(&net, &[1, 2, 3, 4, 5], 256);
}

/// A member that missed the last change is sent the whole list on its next periodic gap check: its SUB carries the
/// version it holds, which is not the hub's.
#[test]
fn a_member_that_missed_the_last_change_is_repaired_by_its_next_gap_check() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 4, SEC);
    for i in 1..=3 {
        net.subscribe(i, T);
    }
    losing_subs_to(&mut net, 1, |net| net.subscribe(4, T));
    // A message keeps the topic live, so the members check it.
    net.publish(4, T, b"live");
    net.advance(vinc_broadcast::consts::GAP_EVERY + SEC);
    assert_all_hold(&net, &[1, 2, 3, 4], 256);
}

/// After a hub restarts, its lists count from zero again under a new incarnation: a member that held a list of the
/// old life is sent the whole list when it subscribes again, and never applies a change of the new life to it.
#[test]
fn after_a_hub_restart_the_lists_of_its_old_life_are_replaced_whole() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 4, SEC);
    for i in 1..=3 {
        net.subscribe(i, T);
    }
    let at = net.now + SEC;
    net.restart(0, at);
    for i in [2, 1, 3] {
        resubscribe(&mut net, i);
    }
    net.subscribe(4, T);
    unsubscribe(&mut net, 2);
    assert_all_hold(&net, &[1, 3, 4], 256);
}

/// Once every member holds the hub's list, the periodic gap checks (which carry the member's version) are answered
/// with no list at all: no whole list goes out while nothing changes.
#[test]
fn a_member_that_holds_the_current_list_is_sent_no_list_by_its_gap_checks() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 4, SEC);
    for i in 1..=4 {
        net.subscribe(i, T);
    }
    net.publish(4, T, b"live");
    net.advance(SEC);
    let got = tally(&mut net);
    for _ in 0..6 {
        net.publish(4, T, b"live");
        net.advance(10 * SEC);
    }
    assert_eq!(
        got.borrow().iter().sum::<usize>(),
        0,
        "lists sent while nothing changed"
    );
}

/// A join hint taken once the member holds a hub's list leaves the list alone: it is the hub's list at its version,
/// and the hub's next change applies to it. A hinted node pushed onto it stayed there, out of id order.
#[test]
fn a_hint_leaves_a_hubs_list_alone() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 5, SEC);
    for i in 1..=3 {
        net.subscribe(i, T);
    }
    let four = net.id(4);
    let one = &mut net.nodes[1];
    assert!(one.t.hint(T, &four));
    net.subscribe(5, T);
    assert_all_hold(&net, &[1, 2, 3, 5], 256);
}

/// Hand node `to` the SUBS payload `rest` as if `from` sent it, and return the drop reasons it traced.
fn inject(net: &mut Net, from: usize, to: usize, rest: &[u8]) -> Vec<SubsDrop> {
    let (now, fid) = (net.now, net.id(from));
    let n = &mut net.nodes[to];
    while n.t.poll_trace().is_some() {}
    n.t.frame(&mut n.h, now, &fid, ty::SUBS, T, rest);
    let mut why = Vec::new();
    while let Some(t) = n.t.poll_trace() {
        if let Trace::SubsDropped { why: w, .. } = t {
            why.push(w);
        }
    }
    why
}

/// A SUBS piece payload: kind 0, the version, the rank of the first id, the length of the whole list, the ids.
fn piece(ver: (u64, u32), first: u16, total: u16, ids: &[NodeId]) -> Vec<u8> {
    let mut b = vec![0u8];
    b.extend_from_slice(&ver.0.to_be_bytes());
    b.extend_from_slice(&ver.1.to_be_bytes());
    b.extend_from_slice(&first.to_be_bytes());
    b.extend_from_slice(&total.to_be_bytes());
    b.extend_from_slice(&(ids.len() as u16).to_be_bytes());
    b.extend_from_slice(ids.as_flattened());
    b
}

/// A SUBS change payload: kind 1, the version, the added ids, the removed ids.
fn change(ver: (u64, u32), add: &[NodeId]) -> Vec<u8> {
    let mut b = vec![1u8];
    b.extend_from_slice(&ver.0.to_be_bytes());
    b.extend_from_slice(&ver.1.to_be_bytes());
    b.extend_from_slice(&(add.len() as u16).to_be_bytes());
    b.extend_from_slice(add.as_flattened());
    b.extend_from_slice(&0u16.to_be_bytes());
    b
}

/// Every field of a SUBS frame is the sender's to choose. A change from a hub other than the one the member's list
/// came from, a list from a member, an ASK from a node the hub does not tell, a short frame and a change on a base
/// the member does not hold change no list and are traced; the last one asks the hub, which repairs the list.
#[test]
fn stray_and_spoofed_subs_frames_change_no_list_and_are_traced() {
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 4, SEC);
    for i in 2..=4 {
        net.set_primary(i, 0);
        net.subscribe(i, T);
    }
    let want = expected(&net, &[2, 3, 4], 256);
    let five = net.id(5);
    assert_eq!(net.nodes[2].t.known_subscribers(T), want.as_slice());

    assert_eq!(inject(&mut net, 1, 2, &change((0, 1), &[five])), [SubsDrop::OtherHub]);
    assert_eq!(inject(&mut net, 3, 2, &change((0, 1), &[five])), [SubsDrop::NotHub]);
    assert_eq!(inject(&mut net, 0, 2, &[1, 0, 0]), [SubsDrop::Malformed]);
    assert_eq!(net.nodes[2].t.known_subscribers(T), want.as_slice());

    assert_eq!(inject(&mut net, 5, 0, &[2]), [SubsDrop::NotRecipient]);
    assert!(
        net.nodes[0].h.out.iter().all(|o| o.bytes.get(4) != Some(&ty::SUBS)),
        "a node the hub does not tell was sent a list"
    );

    assert_eq!(inject(&mut net, 0, 2, &change((0, 999), &[five])), [SubsDrop::OffBase]);
    assert!(!net.nodes[2].t.known_subscribers(T).contains(&five));
    net.pump();
    assert_all_hold(&net, &[2, 3, 4], 256);
}

/// A hub owes the whole list only to the recipients whose stream refused one, at most every recipient, and settles
/// it once that stream has room. Another peer's stream draining finds nothing owed.
#[test]
fn a_hub_owes_the_list_only_to_streams_that_refused_one() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 5, SEC);
    for i in 1..=2 {
        net.subscribe(i, T);
    }
    let (one, two) = (net.id(1), net.id(2));
    net.nodes[0].h.full.insert(one);
    net.subscribe(3, T);
    assert_eq!(net.nodes[0].t.subs_owed(), 1);
    let now = net.now;
    let hub = &mut net.nodes[0];
    hub.t.peer_writable(&mut hub.h, now, &two);
    assert_eq!(net.nodes[0].t.subs_owed(), 1);

    // Every stream refuses while two more join: what is owed stays within the recipients.
    let all: Vec<NodeId> = (1..=5).map(|i| net.id(i)).collect();
    net.nodes[0].h.full.extend(all.iter().copied());
    net.subscribe(4, T);
    net.subscribe(5, T);
    assert!(net.nodes[0].t.subs_owed() <= 5);

    net.nodes[0].h.full.clear();
    let now = net.now;
    for p in &all {
        let hub = &mut net.nodes[0];
        hub.t.peer_writable(&mut hub.h, now, p);
    }
    net.pump();
    assert_eq!(net.nodes[0].t.subs_owed(), 0);
    assert_all_hold(&net, &[1, 2, 3, 4, 5], 256);
}

/// A member whose subscriber limit is under its hub's holds the first of the hub's list; a change that removes from
/// the list it holds is not applied (the id after the cut would never come back): it asks for the whole list.
#[test]
fn a_member_whose_subscriber_limit_is_under_its_hubs_asks_for_the_list_when_a_change_removes_from_a_cut_list() {
    let small = vinc_broadcast::Limits {
        max_subscribers: 2,
        ..vinc_broadcast::Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 4], 1, SEC, small);
    for i in 1..=3 {
        net.attach(i);
    }
    // The hub keeps the default limit; the members keep two.
    net.limits = vinc_broadcast::Limits::default();
    let at = net.now;
    net.restart(0, at);
    let mut order: Vec<usize> = (1..=3).collect();
    order.sort_by_key(|i| net.id(*i));
    let (first, member) = (order[0], order[2]);
    for i in 1..=3 {
        net.subscribe(i, T);
    }
    assert_eq!(
        net.nodes[member].t.known_subscribers(T),
        expected(&net, &[1, 2, 3], 2).as_slice()
    );
    unsubscribe(&mut net, first);
    let live: Vec<usize> = (1..=3).filter(|i| *i != first).collect();
    assert_eq!(
        net.nodes[member].t.known_subscribers(T),
        expected(&net, &live, 2).as_slice()
    );
}

/// A hint is kept beside the hub's list: dropped once a hub's list names the hinted node, and when the topic is left.
#[test]
fn a_hint_is_dropped_once_a_hubs_list_names_it_and_when_the_topic_is_left() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 5, SEC);
    for i in 1..=3 {
        net.subscribe(i, T);
    }
    let (two, four, five) = (net.id(2), net.id(4), net.id(5));
    assert!(net.nodes[1].t.hint(T, &two));
    assert!(net.nodes[1].t.hint(T, &four));
    assert_eq!(net.nodes[1].t.hinted_subscribers(T), [four].as_slice());
    net.subscribe(4, T);
    assert!(net.nodes[1].t.hinted_subscribers(T).is_empty());
    assert!(net.nodes[1].t.hint(T, &five));
    unsubscribe(&mut net, 1);
    assert!(net.nodes[1].t.hinted_subscribers(T).is_empty());
}

/// A late whole list from the hub a member left must not pin the member to it: when the next change comes from the
/// primary, the member takes the primary as its source and asks it for the whole list.
#[test]
fn a_change_from_the_primary_after_a_late_list_from_the_old_hub_makes_the_member_ask_the_primary() {
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 3, SEC);
    net.set_primary(2, 0);
    net.set_primary(3, 1);
    net.subscribe(2, T);
    // The member moves to hub 1, which sends it the whole list; then a late whole list of hub 0 arrives.
    net.set_primary(2, 1);
    net.pump();
    let late = piece((0, 1), 0, 1, &[net.id(2)]);
    assert!(inject(&mut net, 0, 2, &late).is_empty());
    // Hub 0 no longer tells the member anything; a change at hub 1 reaches it.
    net.filter = Some(Box::new(|from, to, bytes| {
        !(from == 0 && to == 2 && bytes.get(4) == Some(&ty::SUBS))
    }));
    net.subscribe(3, T);
    net.pump();
    let held = net.nodes[2].t.known_subscribers(T).to_vec();
    assert!(
        held.contains(&net.id(3)),
        "the member never learned of the change at its primary"
    );
    assert_eq!(held.as_slice(), net.nodes[3].t.known_subscribers(T));
}

/// A subscriber the hub holds and that also published recently is told nothing: not the changes, and not the list an
/// ASK or a stale flush would send.
#[test]
fn a_held_subscriber_that_also_published_is_not_a_recipient_of_the_list() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    net.publish(1, T, b"first");
    net.subscribe(1, T);
    let one = net.id(1);
    let hub = &mut net.nodes[0];
    hub.t.hold(&mut hub.h, &one);
    net.pump();
    let lists_to_one = |net: &Net| {
        net.log
            .iter()
            .filter(|(_, _, to, t, _)| *to == 1 && *t == ty::SUBS)
            .count()
    };
    net.subscribe(2, T);
    let before = lists_to_one(&net);
    assert_eq!(inject(&mut net, 1, 0, &[2]), [SubsDrop::NotRecipient]);
    // Neither the ask nor the flush of a stale recipient brings the held node a list.
    net.pump();
    assert_eq!(lists_to_one(&net), before, "a held subscriber was sent a list");
}

/// A change older than the version the member holds (from an old session, after a newer whole list) is ignored: the
/// member keeps its version and does not ask for the list.
#[test]
fn a_change_older_than_the_version_held_is_ignored_and_the_member_does_not_ask() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    let seen = Rc::new(RefCell::new((0u64, 0u32)));
    let s = Rc::clone(&seen);
    net.filter = Some(Box::new(move |_, to, bytes| {
        if to == 2 && bytes.get(4) == Some(&ty::SUBS) {
            let rest = &bytes[6 + usize::from(bytes[5])..];
            *s.borrow_mut() = (
                u64::from_be_bytes(rest[1..9].try_into().unwrap()),
                u32::from_be_bytes(rest[9..13].try_into().unwrap()),
            );
        }
        true
    }));
    for i in 1..=3 {
        net.subscribe(i, T);
    }
    net.filter = None;
    let asks = |net: &Net| {
        net.log
            .iter()
            .filter(|(_, from, to, t, _)| (*from, *to, *t) == (2, 0, ty::SUBS))
            .count()
    };
    let before = asks(&net);
    let held = net.nodes[2].t.known_subscribers(T).to_vec();
    let (inc, seq) = *seen.borrow();
    assert!(seq > 1);
    let five = net.id(0);
    inject(&mut net, 0, 2, &change((inc, seq - 1), &[five]));
    net.pump();
    assert_eq!(asks(&net), before, "the member asked for the list");
    assert_eq!(net.nodes[2].t.known_subscribers(T), held.as_slice());
}

/// A SUB from a member whose stream is behind and is owed the list gets the list once, not once for the stream's
/// room and again for the version its SUB carries.
#[test]
fn a_lagging_member_that_subscribes_again_is_sent_the_list_once() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    net.subscribe(1, T);
    let one = net.id(1);
    net.nodes[0].h.full.insert(one);
    net.publish(2, T, b"while full");
    net.subscribe(3, T);
    net.nodes[0].h.full.remove(&one);
    let sent = |net: &Net| {
        net.log
            .iter()
            .filter(|(_, _, to, t, _)| *to == 1 && *t == ty::SUBS)
            .count()
    };
    let before = sent(&net);
    resubscribe(&mut net, 1);
    let lists = sent(&net) - before;
    assert_eq!(lists, 1, "the member was sent the list {lists} times");
}

/// A change that is the version the member holds, again (a copy from an old session), is ignored without an ask, and
/// so is a whole list older than the one held: today the member takes any whole list from its hub as the newest, so the
/// older list replaces the newer and the next gap check repairs it (the SUB carries the version, which is then not the
/// hub's). The second half pins that: the member holds the older list, and the repair brings the current one.
#[test]
fn an_exact_duplicate_of_a_change_is_ignored_and_a_late_older_list_is_repaired_by_the_next_check() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    let seen = Rc::new(RefCell::new((0u64, 0u32)));
    let s = Rc::clone(&seen);
    net.filter = Some(Box::new(move |_, to, bytes| {
        if to == 2 && bytes.get(4) == Some(&ty::SUBS) {
            let rest = &bytes[6 + usize::from(bytes[5])..];
            *s.borrow_mut() = (
                u64::from_be_bytes(rest[1..9].try_into().unwrap()),
                u32::from_be_bytes(rest[9..13].try_into().unwrap()),
            );
        }
        true
    }));
    for i in 1..=3 {
        net.subscribe(i, T);
    }
    net.filter = None;
    let asks = |net: &Net| {
        net.log
            .iter()
            .filter(|(_, from, to, t, _)| (*from, *to, *t) == (2, 0, ty::SUBS))
            .count()
    };
    let (inc, seq) = *seen.borrow();
    let held = net.nodes[2].t.known_subscribers(T).to_vec();
    let before = asks(&net);
    let stranger = net.id(0);
    inject(&mut net, 0, 2, &change((inc, seq), &[stranger]));
    net.pump();
    assert_eq!(asks(&net), before, "a duplicate made the member ask");
    assert_eq!(net.nodes[2].t.known_subscribers(T), held.as_slice());

    // A whole list of an earlier version of the same life: the member takes it.
    let old = piece((inc, 1), 0, 1, &[net.id(1)]);
    assert!(inject(&mut net, 0, 2, &old).is_empty());
    assert_eq!(net.nodes[2].t.known_subscribers(T), [net.id(1)].as_slice());
    net.publish(2, T, b"live");
    net.advance(vinc_broadcast::consts::GAP_EVERY + SEC);
    assert_eq!(
        net.nodes[2].t.known_subscribers(T),
        expected(&net, &[1, 2, 3], 256).as_slice()
    );
}

/// A removal of an id the member never held (past its cut) changes nothing and asks for nothing.
#[test]
fn a_removal_past_the_cut_of_a_member_with_a_lower_limit_asks_for_nothing() {
    let small = vinc_broadcast::Limits {
        max_subscribers: 2,
        ..vinc_broadcast::Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 5], 1, SEC, small);
    for i in 1..=4 {
        net.attach(i);
    }
    net.limits = vinc_broadcast::Limits::default();
    let at = net.now;
    net.restart(0, at);
    let mut order: Vec<usize> = (1..=4).collect();
    order.sort_by_key(|i| net.id(*i));
    let (member, past) = (order[3], order[2]);
    for i in 1..=4 {
        net.subscribe(i, T);
    }
    let asks = |net: &Net| {
        net.log
            .iter()
            .filter(|(_, from, to, t, _)| (*from, *to, *t) == (member, 0, ty::SUBS))
            .count()
    };
    let before = asks(&net);
    let held = net.nodes[member].t.known_subscribers(T).to_vec();
    unsubscribe(&mut net, past);
    assert_eq!(
        asks(&net),
        before,
        "the member asked for a list over a removal past its cut"
    );
    assert_eq!(net.nodes[member].t.known_subscribers(T), held.as_slice());
}
