//! Gap repair: SUB(since), then HAVE, then GET, then MSG, across a partition and its heal; the periodic check (every
//! 20 s, the last 25 s, only while the topic had traffic in the last 60 s); the failover to another hub; and the
//! repair between hubs.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::expect_used,
    clippy::assert_is_empty,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation
)]

#[path = "broadcast_common.rs"]
mod common;

use common::{Ev, Net, SEC, WALL0, ty};
use vinc_crypto::IdentityAlg;

const T: &[u8] = b"gap";

/// Publisher 2 and subscriber 3, both on hub 0 of two hubs.
fn world() -> Net {
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 2, SEC);
    net.subscribe(3, T);
    net
}

fn sub_times(net: &Net, from: usize) -> Vec<u64> {
    net.log
        .iter()
        .filter(|l| l.1 == from && l.3 == ty::SUB)
        .map(|l| l.0)
        .collect()
}

#[test]
fn messages_published_during_a_partition_arrive_after_the_heal_in_order_sub_have_get_msg() {
    let mut net = world();
    let m0 = net.publish(2, T, b"before");
    net.run_until(5 * SEC);
    net.link(3, 0, false);
    let m1 = net.publish(2, T, b"during 1");
    let m2 = net.publish(2, T, b"during 2");
    net.run_until(10 * SEC);
    assert_eq!(net.delivered(3), vec![m0], "nothing crosses the cut");
    net.link(3, 0, true);
    let healed = net.log.len();
    net.run_until(30 * SEC);
    assert_eq!(net.delivered(3), vec![m0, m1, m2]);
    // The repair ran SUB, HAVE, GET, MSG in that order, and the subscriber reports each repaired message.
    let seq: Vec<u8> = net.log[healed..]
        .iter()
        .filter(|l| (l.1 == 3 || l.2 == 3) && matches!(l.3, ty::SUB | ty::HAVE | ty::GET | ty::MSG))
        .map(|l| l.3)
        .collect();
    assert_eq!(seq, vec![ty::SUB, ty::HAVE, ty::GET, ty::MSG, ty::MSG]);
    let repaired: Vec<[u8; 8]> = net
        .events(3)
        .iter()
        .filter_map(|e| {
            if let Ev::Repaired { mid, .. } = e {
                Some(*mid)
            } else {
                None
            }
        })
        .collect();
    assert_eq!(repaired, vec![m1, m2]);
}

#[test]
fn a_repair_never_redelivers_a_message_the_subscriber_has() {
    let mut net = world();
    let m0 = net.publish(2, T, b"a");
    net.run_until(100 * SEC);
    assert_eq!(net.delivered(3), vec![m0]);
    assert_eq!(net.count(ty::GET), 0, "every id in the HAVE was already seen");
}

#[test]
fn the_periodic_check_runs_every_20s_while_the_topic_had_traffic_in_the_last_60s() {
    let mut net = world();
    net.publish(2, T, b"x");
    net.run_until(130 * SEC);
    let times = sub_times(&net, 3);
    // The initial SUB at 1 s, then the check on its 20 s grid from the start (21 s, 41 s). At 61 s the last traffic is
    // exactly 60 s old, which is no longer live, and nothing follows.
    assert_eq!(times, vec![SEC, 21 * SEC, 41 * SEC]);
    // New traffic makes the topic live again at the next tick (81 s).
    net.publish(2, T, b"y");
    net.run_until(200 * SEC);
    let times = sub_times(&net, 3);
    assert_eq!(&times[3..], &[141 * SEC, 161 * SEC, 181 * SEC]);
}

#[test]
fn the_periodic_check_asks_for_the_last_25s() {
    let mut net = world();
    net.publish(2, T, b"x");
    let seen = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    let s2 = seen.clone();
    net.filter = Some(Box::new(move |from, _, b| {
        if from == 3 && b[4] == ty::SUB {
            let tl = usize::from(b[5]);
            let since = u64::from_be_bytes(b[6 + tl..14 + tl].try_into().unwrap());
            s2.borrow_mut().push(since);
        }
        true
    }));
    net.run_until(50 * SEC);
    // At the 41 s check the wall clock reads WALL0 + 41 000 ms: ask from 25 s earlier.
    assert_eq!(seen.borrow().last().copied(), Some(WALL0 + 41_000 - 25_000));
}

#[test]
fn a_topic_without_traffic_is_not_asked_about() {
    let mut net = world();
    net.run_until(100 * SEC);
    assert_eq!(sub_times(&net, 3), vec![SEC], "only the subscription itself");
}

#[test]
fn a_resubscribe_from_membership_asks_the_primary_again_for_every_topic() {
    let mut net = world();
    net.subscribe(3, b"other");
    net.publish(2, T, b"x");
    let before = sub_times(&net, 3).len();
    let hub = net.id(0);
    let now = net.now;
    let n = &mut net.nodes[3];
    n.t.resubscribe(&mut n.h, now, &hub);
    net.pump();
    assert_eq!(sub_times(&net, 3).len(), before + 2);
    // A hub that is not our primary is ignored.
    let other = net.id(1);
    let before = sub_times(&net, 3).len();
    let n = &mut net.nodes[3];
    n.t.resubscribe(&mut n.h, now, &other);
    net.pump();
    assert_eq!(sub_times(&net, 3).len(), before);
}

#[test]
fn a_failover_leaves_the_old_hub_and_subscribes_at_the_new_one_with_repair() {
    let mut net = world();
    let m0 = net.publish(2, T, b"a");
    net.run_until(5 * SEC);
    // Hub 1 holds the mirror of m0 and everything after; the subscriber moves there.
    net.set_primary(3, 1);
    assert_eq!(net.count_between(3, 0, ty::UNSUB), 1);
    assert!(net.count_between(3, 1, ty::SUB) >= 1);
    net.link(2, 1, false);
    net.link(2, 0, true);
    let m1 = net.publish(2, T, b"b");
    net.run_until(10 * SEC);
    assert_eq!(
        net.delivered(3),
        vec![m0, m1],
        "pushed by the new primary, mirrored from hub 0"
    );
    assert_eq!(net.nodes[0].t.sub_state(T, &net.id(3)), None);
    assert_eq!(net.nodes[1].t.sub_state(T, &net.id(3)), Some(true));
}

#[test]
fn hubs_repair_each_other_after_a_partition() {
    let mut net = world();
    net.set_primary(3, 1);
    // The publisher reaches only hub 0, and hubs 0 and 1 are cut from each other: hub 1 misses the message.
    net.link(2, 1, false);
    net.link(0, 1, false);
    let m = net.publish(2, T, b"x");
    net.run_until(10 * SEC);
    assert!(net.delivered(3).is_empty());
    net.link(0, 1, true);
    net.run_until(20 * SEC);
    assert_eq!(net.delivered(3), vec![m]);
    assert!(net.count_between(0, 1, ty::HAVE) >= 1);
    assert!(net.count_between(1, 0, ty::GET) >= 1);
    assert_eq!(net.nodes[1].t.log_len(T), 1);
}

#[test]
fn a_have_is_capped_at_512_ids_newest_first_kept() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    for i in 0..600u32 {
        net.publish(1, T, &i.to_be_bytes());
    }
    // A subscriber asking from the beginning of time gets the newest 512 ids.
    let asker = net.id(2);
    let now = net.now;
    let n = &mut net.nodes[0];
    n.h.out.clear();
    n.t.frame(&mut n.h, now, &asker, ty::SUB, T, &0u64.to_be_bytes());
    let have = n.h.out.iter().find(|o| o.bytes[4] == ty::HAVE).unwrap();
    let rest = &have.bytes[6 + T.len()..];
    assert_eq!(rest.len(), 512 * 8);
}
