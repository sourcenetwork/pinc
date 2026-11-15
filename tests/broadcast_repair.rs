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

/// A GET for more than the subscriber's stream takes is not answered in part (vinc#504): the messages the stream has
/// no room for are owed from the hub's log, the hub keeping one place for them, and arrive in order when the stream
/// has room, without waiting for the next periodic check.
#[test]
fn a_repair_larger_than_the_stream_takes_is_finished_when_the_stream_has_room() {
    let mut net = world();
    let m0 = net.publish(2, T, b"before");
    net.run_until(5 * SEC);
    net.link(3, 0, false);
    let missed: Vec<[u8; 8]> = (0..40)
        .map(|k| {
            let m = net.publish(2, T, format!("during {k:02}").as_bytes());
            net.advance(SEC / 1000);
            m
        })
        .collect();
    net.run_until(10 * SEC);
    assert_eq!(net.delivered(3), vec![m0], "nothing crosses the cut");
    // After the heal the subscriber's stream at the hub takes the HAVE and ten messages, then it is full. The
    // subscriber asks at its next periodic check, 20 s after it started.
    let sub = net.id(3);
    net.nodes[0].h.room.insert(sub, 11);
    net.link(3, 0, true);
    net.run_until(25 * SEC);
    let mut want = vec![m0];
    want.extend(&missed[..10]);
    assert_eq!(net.delivered(3), want, "the stream took ten of the forty");
    assert_eq!(
        net.nodes[0].t.behind_count(T),
        1,
        "the hub keeps the subscriber's place for the thirty it asked for and was not sent"
    );
    // Room again: the rest arrives now, in order, each once.
    net.nodes[0].h.room.remove(&sub);
    let now = net.now;
    let n = &mut net.nodes[0];
    n.t.peer_writable(&mut n.h, now, &sub);
    net.pump();
    let mut all = vec![m0];
    all.extend(&missed);
    assert_eq!(net.delivered(3), all);
    assert_eq!(net.nodes[0].t.behind_count(T), 0);
    // And the subscriber is pushed live again.
    let after = net.publish(2, T, b"after");
    net.advance(SEC / 10);
    assert_eq!(net.delivered(3).last(), Some(&after));
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

/// One HAVE carries at most 512 ids, and an offer of more goes on in further frames, oldest first: the asker learns of
/// every id the log holds, not only of the newest.
#[test]
fn a_have_carries_at_most_512_ids_and_the_offer_goes_on_in_further_frames() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    let sent: Vec<[u8; 8]> = (0..600u32).map(|i| net.publish(1, T, &i.to_be_bytes())).collect();
    // A subscriber asking from the beginning of time is offered all 600 ids.
    let asker = net.id(2);
    let now = net.now;
    let n = &mut net.nodes[0];
    n.h.out.clear();
    n.t.frame(&mut n.h, now, &asker, ty::SUB, T, &0u64.to_be_bytes());
    let haves: Vec<&[u8]> =
        n.h.out
            .iter()
            .filter(|o| o.bytes[4] == ty::HAVE)
            .map(|o| &o.bytes[6 + T.len()..])
            .collect();
    assert_eq!(
        haves.iter().map(|r| r.len() / 8).collect::<Vec<_>>(),
        vec![512, 88],
        "the ids of each frame"
    );
    let offered: Vec<[u8; 8]> = haves.concat().as_chunks::<8>().0.to_vec();
    assert_eq!(offered, sent, "every id, in the order it was logged");
}

/// A replay (a SUB with the replay flag) is answered with every message the log holds since the time asked, oldest
/// first, not only the newest 256 (vinc#510).
#[test]
fn a_replay_is_answered_with_every_message_the_log_holds_oldest_first() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    for i in 0..600u32 {
        net.publish(1, T, &i.to_be_bytes());
    }
    let asker = net.id(2);
    let now = net.now;
    let n = &mut net.nodes[0];
    n.h.out.clear();
    let mut rest = 0u64.to_be_bytes().to_vec();
    rest.push(1);
    n.t.frame(&mut n.h, now, &asker, ty::SUB, T, &rest);
    // Each message's body is its number, the last four bytes of its frame.
    let pushed: Vec<u32> =
        n.h.out
            .iter()
            .filter(|o| o.to == asker && o.bytes[4] == ty::MSG)
            .map(|o| u32::from_be_bytes(o.bytes[o.bytes.len() - 4..].try_into().unwrap()))
            .collect();
    assert_eq!(pushed.len(), 600, "the replay left messages the log holds unsent");
    assert_eq!(pushed, (0..600).collect::<Vec<u32>>(), "oldest first");
}

/// A site is cut off for fifteen seconds while fifty messages a second are published elsewhere: 750 messages, more
/// than one HAVE carries. After the heal its hub learns of every one of them from the other hub, not only of the
/// newest, and its subscriber misses none.
#[test]
fn a_hub_cut_off_through_750_messages_gets_every_one_after_the_heal() {
    // Hubs 0 and 1, publisher 2 on hub 0, subscriber 3 on hub 1.
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 2, SEC);
    net.set_primary(3, 1);
    net.subscribe(3, T);
    let before = net.publish(2, T, b"before");
    net.run_until(5 * SEC);
    assert_eq!(net.delivered(3), vec![before]);

    let cut = |net: &mut Net, up: bool| {
        net.link(0, 1, up);
        net.link(2, 1, up);
        net.link(3, 0, up);
    };
    cut(&mut net, false);
    let mut sent = vec![before];
    for k in 0..750u32 {
        sent.push(net.publish(2, T, format!("during {k}").as_bytes()));
        net.advance(SEC / 50);
    }
    assert_eq!(net.delivered(3), vec![before], "nothing crosses the cut");

    cut(&mut net, true);
    net.advance(12 * SEC);
    let mut got = net.delivered(3);
    assert_eq!(got.len(), sent.len(), "the subscriber behind the cut misses messages");
    got.sort_unstable();
    sent.sort_unstable();
    assert_eq!(got, sent);
}
