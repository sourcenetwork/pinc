//! A hub and a subscriber whose stream has no room: the hub keeps the subscriber's place in the topic's log, drops
//! nothing, and sends everything in order once the stream has room again. And a publisher whose hub's stream has no
//! room: it keeps its publishes, sends them in order when there is room, and refuses one it cannot track.
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

use common::{Net, SEC};
use vinc_crypto::IdentityAlg;

const T: &[u8] = b"burst";

/// Hub 0, publisher 1, subscribers 2 and 3, all subscribed and attached.
fn net() -> Net {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    net.subscribe(2, T);
    net.subscribe(3, T);
    net.advance(SEC);
    net
}

/// Say whether subscriber `i`'s stream at the hub is full; when it gets room, the host tells the hub.
fn set_full(net: &mut Net, i: usize, full: bool) {
    let id = net.id(i);
    if full {
        net.nodes[0].h.full.insert(id);
    } else {
        net.nodes[0].h.full.remove(&id);
        let now = net.now;
        let n = &mut net.nodes[0];
        n.t.peer_writable(&mut n.h, now, &id);
        net.pump();
    }
}

fn body(k: usize) -> Vec<u8> {
    format!("message {k:04}").into_bytes()
}

#[test]
fn a_subscriber_whose_stream_is_full_gets_every_message_in_order_once_it_has_room() {
    let mut net = net();
    let first = net.publish(1, T, &body(0));
    net.advance(SEC / 10);
    assert_eq!(net.delivered(2), vec![first]);

    // The stream of subscriber 2 fills; 300 messages are published meanwhile. Subscriber 3 is not affected.
    set_full(&mut net, 2, true);
    let mut sent = vec![first];
    for k in 1..=300 {
        sent.push(net.publish(1, T, &body(k)));
        net.advance(SEC / 1000);
    }
    assert_eq!(
        net.delivered(3),
        sent,
        "the other subscriber got each message as it came"
    );
    assert_eq!(net.delivered(2), vec![first], "nothing reaches a full stream");
    assert_eq!(
        net.nodes[0].t.behind_count(T),
        1,
        "the hub keeps one place, not 300 copies"
    );

    // Room again: everything arrives, in the order it was published, once.
    set_full(&mut net, 2, false);
    assert_eq!(net.delivered(2), sent);
    assert_eq!(net.bodies(2), (0..=300).map(body).collect::<Vec<_>>());
    assert_eq!(net.nodes[0].t.behind_count(T), 0);

    // And the subscriber is pushed live again.
    let after = net.publish(1, T, b"after");
    net.advance(SEC / 10);
    assert_eq!(net.delivered(2).last(), Some(&after));
    assert_eq!(net.delivered(2).len(), 302);
}

#[test]
fn a_stream_that_fills_again_midway_keeps_its_place() {
    let mut net = net();
    set_full(&mut net, 2, true);
    let sent: Vec<[u8; 8]> = (0..50)
        .map(|k| {
            let m = net.publish(1, T, &body(k));
            net.advance(SEC / 1000);
            m
        })
        .collect();
    // Room for a moment with nothing new to say, then full again while more arrives: no message is sent twice and
    // none is skipped.
    set_full(&mut net, 2, false);
    assert_eq!(net.delivered(2), sent);
    set_full(&mut net, 2, true);
    let more: Vec<[u8; 8]> = (50..80)
        .map(|k| {
            let m = net.publish(1, T, &body(k));
            net.advance(SEC / 1000);
            m
        })
        .collect();
    set_full(&mut net, 2, false);
    let all: Vec<[u8; 8]> = sent.iter().chain(&more).copied().collect();
    assert_eq!(net.delivered(2), all);
}

#[test]
fn a_subscriber_that_published_a_message_is_not_sent_it_back_from_the_log() {
    let mut net = net();
    set_full(&mut net, 2, true);
    let own = net.publish(2, T, b"mine");
    let other = net.publish(1, T, b"theirs");
    net.advance(SEC / 10);
    set_full(&mut net, 2, false);
    assert_eq!(net.delivered(2), vec![other], "its own message is not echoed");
    assert!(net.delivered(3).contains(&own) && net.delivered(3).contains(&other));
}

/// Hub 0, publisher 1 and subscriber 2, over a log of 64 KiB, so about sixty messages of 1 KiB fit.
fn small_log_net() -> Net {
    let limits = vinc_broadcast::Limits {
        max_body: 2048,
        log_bytes: 64 << 10,
        ..vinc_broadcast::Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 3], 1, SEC, limits);
    net.attach(1);
    net.attach(2);
    net.subscribe(2, T);
    net.advance(SEC);
    net
}

/// Publish `n` bodies of 1 KiB from member 1, 1 ms apart.
fn publish_kib(net: &mut Net, from: u64, n: u64) -> Vec<[u8; 8]> {
    (from..from + n)
        .map(|k| {
            let mut b = vec![0u8; 1024];
            b[..8].copy_from_slice(&k.to_be_bytes());
            let m = net.publish(1, T, &b);
            net.advance(SEC / 1000);
            m
        })
        .collect()
}

#[test]
fn a_log_full_of_owed_messages_takes_no_more_until_they_are_sent() {
    let mut net = small_log_net();
    set_full(&mut net, 2, true);
    let sent = publish_kib(&mut net, 0, 200);
    // The log stops at what it holds: evicting the oldest would lose a message the subscriber is owed, so the rest
    // are refused, not acknowledged, and wait at the publisher.
    let kept = net.nodes[0].t.log_len(T);
    assert!(kept > 40 && kept < 70, "the log holds {kept} messages");
    set_full(&mut net, 2, false);
    assert_eq!(net.delivered(2), sent[..kept].to_vec(), "the oldest `kept`, in order");
    // The publisher retries the others every 3 s and the hub takes them now.
    net.advance(5 * SEC);
    let mut got = net.delivered(2);
    let mut want = sent.clone();
    got.sort_unstable();
    want.sort_unstable();
    assert_eq!(got, want, "every message, once");
}

#[test]
fn a_stalled_subscriber_is_let_go_continues_from_the_oldest_message_left_and_is_told() {
    let mut net = small_log_net();
    set_full(&mut net, 2, true);
    publish_kib(&mut net, 0, 1);
    // Past PUSH_STALL_MS with nothing taken: the next store that needs room lets it go and evicts.
    net.advance(3 * SEC);
    let sent = publish_kib(&mut net, 1, 200);
    let kept = net.nodes[0].t.log_len(T);
    assert!(kept > 40 && kept < 70, "the log holds {kept} messages");
    set_full(&mut net, 2, false);
    // Exactly the messages the log still had, in order: the newest `kept` of the 200.
    assert_eq!(net.delivered(2), sent[200 - kept..].to_vec());
    assert!(
        net.events(2).iter().any(|e| matches!(e, common::Ev::Restored { .. })),
        "the subscriber is told it lost messages"
    );
}

#[test]
fn a_refusal_that_is_not_a_full_stream_keeps_no_place() {
    // The subscriber's session is gone (the hub cannot reach it): as before, nothing is kept for it here, and its
    // next subscribe repairs what it missed.
    let mut net = net();
    net.link(0, 2, false);
    net.publish(1, T, b"while away");
    net.advance(SEC / 10);
    assert_eq!(net.nodes[0].t.behind_count(T), 0);
}

/// Say whether the hub's stream at publisher 1 is full; when it gets room, the host tells the publisher.
fn set_hub_full(net: &mut Net, full: bool) {
    let hub = net.id(0);
    if full {
        net.nodes[1].h.full.insert(hub);
    } else {
        net.nodes[1].h.full.remove(&hub);
        let now = net.now;
        let n = &mut net.nodes[1];
        n.t.peer_writable(&mut n.h, now, &hub);
        net.pump();
    }
}

/// A burst faster than the path to the hub: the publisher sends nothing its hub's stream has no room for and drops
/// nothing. When the stream has room, every publish goes out in the order it was made, and each is acknowledged.
#[test]
fn a_publisher_whose_hub_stream_is_full_sends_every_publish_in_order_once_it_has_room() {
    let mut net = net();
    let first = net.publish(1, T, &body(0));
    net.advance(SEC / 10);
    assert_eq!(net.delivered(2), vec![first]);
    assert_eq!(net.nodes[1].t.pending_len(), 0, "the first publish was acknowledged");

    set_hub_full(&mut net, true);
    let mut sent = vec![first];
    for k in 1..=300 {
        sent.push(net.publish(1, T, &body(k)));
        net.advance(SEC / 1000);
    }
    assert_eq!(net.delivered(2), vec![first], "nothing left for a full stream");
    assert_eq!(net.nodes[1].t.unsent_len(), 300, "every publish is kept, none was sent");
    // The retry time passes with the stream still full: the publishes are still kept.
    net.advance(4 * SEC);
    assert_eq!(net.nodes[1].t.unsent_len(), 300);
    assert_eq!(net.delivered(2), vec![first]);

    set_hub_full(&mut net, false);
    assert_eq!(net.nodes[1].t.unsent_len(), 0);
    assert_eq!(
        net.delivered(2),
        sent,
        "every publish arrived once, in the order it was made"
    );
    assert_eq!(net.delivered(3), sent);
    net.advance(SEC / 10);
    assert_eq!(net.nodes[1].t.pending_len(), 0, "the hub acknowledged every one");
}

/// While older publishes wait for room, a new one waits behind them even if the stream would take it now, so the hub
/// gets them in order; and past the publishes the node tracks, a publish is refused to its caller.
#[test]
fn a_publish_waits_behind_the_unsent_ones_and_one_past_the_tracked_ones_is_refused() {
    let mut net = net();
    set_hub_full(&mut net, true);
    let a = net.publish(1, T, &body(0));
    // The stream has room again, but the host has not said so yet: the next publish must not overtake.
    let hub = net.id(0);
    net.nodes[1].h.full.remove(&hub);
    let b = net.publish(1, T, &body(1));
    net.advance(SEC / 1000);
    assert!(net.delivered(2).is_empty());
    assert_eq!(net.nodes[1].t.unsent_len(), 2);
    set_hub_full(&mut net, false);
    assert_eq!(net.delivered(2), vec![a, b]);

    set_hub_full(&mut net, true);
    let now = net.now;
    let n = &mut net.nodes[1];
    let mut taken = 0;
    let refused = loop {
        match n.t.publish(&mut n.h, now, T, &body(taken)) {
            Ok(_) => taken += 1,
            Err(e) => break e,
        }
        assert!(taken <= 4096, "no publish was ever refused");
    };
    assert_eq!(refused, vinc_broadcast::Refused::Backlog);
    assert_eq!(taken, n.t.pending_len(), "every publish that was taken is tracked");
    assert_eq!(n.t.unsent_len(), taken);
}

/// A hub publishes 1 KiB bodies of its own until one is refused; how many it took.
fn hub_publishes_until_refused(net: &mut Net) -> usize {
    let now = net.now;
    let n = &mut net.nodes[0];
    n.h.tick(now);
    let mut taken = 0;
    let refused = loop {
        match n.t.publish(&mut n.h, now, T, &[7u8; 1024]) {
            Ok(_) => taken += 1,
            Err(e) => break e,
        }
        assert!(taken <= 4096, "no publish of the hub was ever refused");
    };
    assert_eq!(refused, vinc_broadcast::Refused::Backlog);
    net.pump();
    taken
}

fn rooms(net: &Net) -> usize {
    net.events(0).iter().filter(|e| matches!(e, common::Ev::Room)).count()
}

/// A hub that publishes itself has no acknowledgement to wait for. When its log is full of messages a subscriber is
/// still owed its publish is refused, and it is told when to publish again: as soon as the subscriber moved on, or
/// once a subscriber that stalls can be let go.
#[test]
fn a_hub_whose_own_publish_found_no_room_is_told_when_to_publish_again() {
    let mut net = small_log_net();
    set_full(&mut net, 2, true);
    let taken = hub_publishes_until_refused(&mut net);
    assert!(taken > 40 && taken < 70, "the log took {taken} messages");
    assert_eq!(rooms(&net), 0, "nothing changed yet");

    // The subscriber's stream has room: it is sent what it was owed, and the hub is told, once.
    set_full(&mut net, 2, false);
    assert_eq!(net.delivered(2).len(), taken);
    assert_eq!(rooms(&net), 1);
    net.publish(0, T, &[8u8; 1024]);

    // The subscriber stalls: the hub is refused again, and told once the stall time has passed. Its next publish
    // lets the subscriber go and is taken.
    set_full(&mut net, 2, true);
    hub_publishes_until_refused(&mut net);
    assert_eq!(rooms(&net), 1);
    net.advance(SEC);
    assert_eq!(rooms(&net), 1, "not before the stall time");
    net.advance(2 * SEC);
    assert_eq!(rooms(&net), 2);
    net.publish(0, T, &[9u8; 1024]);
}
