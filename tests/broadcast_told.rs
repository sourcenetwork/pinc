//! A hub that cannot give a subscriber every message it asks for says so (vinc#505): a subscriber that comes back
//! to a log that moved past it, one whose session ended while the hub still owed it messages, and one that asks
//! for a message the log dropped meanwhile are each told once (RESTORED, `Event::Restored`); a subscriber that
//! subscribes for the first time is not; and the notice waits for room in the subscriber's stream as a message does.
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

use common::{Ev, Net, NodeHost, SEC, ty};
use vinc_broadcast::Topics;
use vinc_crypto::IdentityAlg;

const T: &[u8] = b"told";

/// Hub 0, publisher 1, subscriber 2 and member 3 (not subscribed), over a log of 64 KiB, so about sixty messages of
/// 1 KiB fit.
fn world() -> Net {
    let limits = vinc_broadcast::Limits {
        max_body: 2048,
        log_bytes: 64 << 10,
        ..vinc_broadcast::Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 4], 1, SEC, limits);
    for i in 1..4 {
        net.attach(i);
    }
    net.subscribe(2, T);
    net
}

fn at_hub(net: &mut Net, f: impl FnOnce(&mut Topics, &mut NodeHost, u64)) {
    let now = net.now;
    let n = &mut net.nodes[0];
    n.h.tick(now);
    f(&mut n.t, &mut n.h, now);
    net.pump();
}

/// Member `i`'s session ends at the hub, which was not told the member is down: membership releases it there.
fn end_session(net: &mut Net, i: usize) {
    let id = net.id(i);
    net.link(i, 0, false);
    at_hub(net, |t, h, _| t.release(h, &id));
}

/// Member `i` has a session with the hub again, and membership asks it to subscribe again.
fn come_back(net: &mut Net, i: usize) {
    net.link(i, 0, true);
    let (hub, now) = (net.id(0), net.now);
    let n = &mut net.nodes[i];
    n.h.tick(now);
    n.t.resubscribe(&mut n.h, now, &hub);
    net.pump();
}

/// Say whether subscriber `i`'s stream at the hub is full; when it gets room, the host tells the hub.
fn set_full(net: &mut Net, i: usize, full: bool) {
    let id = net.id(i);
    if full {
        net.nodes[0].h.full.insert(id);
    } else {
        net.nodes[0].h.full.remove(&id);
        at_hub(net, |t, h, now| t.peer_writable(h, now, &id));
    }
}

/// Subscriber `i`'s stream at the hub takes `frames` more frames and is full again; the host tells the hub.
fn give_room(net: &mut Net, i: usize, frames: usize) {
    let id = net.id(i);
    net.nodes[0].h.full.remove(&id);
    net.nodes[0].h.room.insert(id, frames);
    at_hub(net, |t, h, now| t.peer_writable(h, now, &id));
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

/// How many times member `i` was told that messages of the topic may be missing.
fn told(net: &Net, i: usize) -> usize {
    net.events(i)
        .iter()
        .filter(|e| matches!(e, Ev::Restored { topic, .. } if topic == T))
        .count()
}

#[test]
fn a_subscriber_that_comes_back_to_a_log_that_moved_past_it_is_told_once_and_a_new_one_is_not() {
    let mut net = world();
    let m0 = net.publish(1, T, b"before");
    net.run_until(5 * SEC);
    assert_eq!(net.delivered(2), vec![m0]);
    // Away while a burst longer than the log goes by.
    end_session(&mut net, 2);
    let sent = publish_kib(&mut net, 0, 200);
    let kept = net.nodes[0].t.log_len(T);
    assert!(kept > 40 && kept < 70, "the log holds {kept} messages");
    come_back(&mut net, 2);
    let mut want = vec![m0];
    want.extend(&sent[200 - kept..]);
    assert_eq!(net.delivered(2), want, "what the log still holds, in order");
    assert_eq!(told(&net, 2), 1, "and one notice for what it no longer holds");
    // Its periodic checks (21 s, 41 s, 61 s) ask the hub again and are not told again.
    let live = net.publish(1, T, b"live");
    net.run_until(50 * SEC);
    let later = net.publish(1, T, b"later");
    net.run_until(70 * SEC);
    assert_eq!(&net.delivered(2)[want.len()..], &[live, later]);
    assert_eq!(told(&net, 2), 1);
    // Another session end, with nothing dropped since the time it now asks from.
    end_session(&mut net, 2);
    come_back(&mut net, 2);
    assert_eq!(told(&net, 2), 1);
    // A member that subscribes for the first time asks from now: it is owed nothing older.
    net.subscribe(3, T);
    net.advance(SEC);
    assert_eq!(told(&net, 3), 0);
    assert_eq!(net.nodes[0].t.sub_state(T, &net.id(3)), Some(true));
}

#[test]
fn a_subscriber_whose_session_ends_while_it_is_behind_and_asks_from_before_what_it_was_owed_gets_it_and_is_not_told() {
    let mut net = world();
    let m0 = net.publish(1, T, b"before");
    net.run_until(5 * SEC);
    set_full(&mut net, 2, true);
    let owed: Vec<[u8; 8]> = (0..5)
        .map(|k| net.publish(1, T, format!("owed {k}").as_bytes()))
        .collect();
    net.advance(SEC);
    assert_eq!(net.nodes[0].t.behind_count(T), 1);
    end_session(&mut net, 2);
    assert_eq!(net.nodes[0].t.behind_count(T), 0, "the place went with the session");
    net.nodes[0].h.full.clear();
    // It asks from 15 s before its last receipt: the answer reaches back to everything it was owed.
    come_back(&mut net, 2);
    let mut want = vec![m0];
    want.extend(&owed);
    assert_eq!(net.delivered(2), want);
    assert_eq!(told(&net, 2), 0, "nothing is missing");
}

/// The subscriber is behind, is sent one of the five messages it is owed 23 s after they were logged, and its session
/// ends. It asks from 15 s before that receipt, which is after the other four were logged, so the hub's answer does
/// not offer them, and the hub no longer has its place.
fn behind_then_gone(net: &mut Net, release: bool) -> Vec<[u8; 8]> {
    let m0 = net.publish(1, T, b"before");
    net.run_until(22 * SEC);
    set_full(net, 2, true);
    let owed: Vec<[u8; 8]> = (0..5)
        .map(|k| net.publish(1, T, format!("owed {k}").as_bytes()))
        .collect();
    // The periodic check of 41 s passes while it is behind.
    net.run_until(45 * SEC);
    give_room(net, 2, 1);
    assert_eq!(net.delivered(2), vec![m0, owed[0]]);
    assert_eq!(net.nodes[0].t.behind_count(T), 1);
    net.run_until(46 * SEC);
    let id = net.id(2);
    if release {
        end_session(net, 2);
    } else {
        // The hub finds the session gone when it next serves the place; membership's release follows.
        net.link(2, 0, false);
        at_hub(net, |t, h, now| t.peer_writable(h, now, &id));
        assert_eq!(net.nodes[0].t.behind_count(T), 0);
        at_hub(net, |t, h, _| t.release(h, &id));
    }
    net.nodes[0].h.full.clear();
    net.nodes[0].h.room.clear();
    net.run_until(47 * SEC);
    come_back(net, 2);
    vec![m0, owed[0]]
}

#[test]
fn a_subscriber_whose_session_ends_while_it_is_behind_is_told_when_its_answer_does_not_reach_what_it_was_owed() {
    let mut net = world();
    let got = behind_then_gone(&mut net, true);
    assert_eq!(
        net.delivered(2),
        got,
        "the four it was owed were logged before the time it asks from"
    );
    assert_eq!(told(&net, 2), 1);
    // A member that subscribes for the first time, after the hub forgot the place, is not told.
    net.subscribe(3, T);
    net.advance(SEC);
    assert_eq!(told(&net, 3), 0);
}

#[test]
fn a_place_the_hub_finds_gone_with_its_session_is_told_about_as_one_that_was_released() {
    let mut net = world();
    let got = behind_then_gone(&mut net, false);
    assert_eq!(net.delivered(2), got);
    assert_eq!(told(&net, 2), 1);
}

#[test]
fn a_get_for_a_message_the_log_dropped_is_answered_with_the_notice() {
    let mut net = world();
    net.run_until(2 * SEC);
    // The subscriber is live through a burst longer than the log: it receives every message, and the log keeps the
    // newest sixty or so.
    let sent = publish_kib(&mut net, 0, 200);
    assert_eq!(net.delivered(2), sent);
    assert_eq!(told(&net, 2), 0);
    let (sub, other) = (net.id(2), net.id(3));
    let frames = |net: &mut Net, from: &[u8; 32], mid: &[u8; 8]| -> Vec<u8> {
        let now = net.now;
        let n = &mut net.nodes[0];
        n.h.tick(now);
        n.h.out.clear();
        n.t.frame(&mut n.h, now, from, ty::GET, T, mid);
        let out: Vec<u8> = n.h.out.iter().filter(|o| o.to == *from).map(|o| o.bytes[4]).collect();
        net.pump();
        out
    };
    // An id the hub offered and no longer holds: the notice, once for the request.
    assert_eq!(frames(&mut net, &sub, &sent[0]), vec![ty::RESTORED]);
    assert_eq!(told(&net, 2), 1);
    // An id it still holds: the message, and no notice.
    assert_eq!(frames(&mut net, &sub, &sent[199]), vec![ty::MSG]);
    assert_eq!(told(&net, 2), 1);
    // A node that is not a live subscriber of the topic is told nothing.
    assert_eq!(frames(&mut net, &other, &sent[0]), Vec::<u8>::new());
}

#[test]
fn a_notice_the_stream_has_no_room_for_is_sent_when_it_has() {
    let mut net = world();
    let m0 = net.publish(1, T, b"before");
    net.run_until(5 * SEC);
    end_session(&mut net, 2);
    let sent = publish_kib(&mut net, 0, 200);
    let kept = net.nodes[0].t.log_len(T);
    // The subscriber's new stream takes the hub's offer and is full: no room for the notice, nor for what it asks.
    let sub = net.id(2);
    net.nodes[0].h.room.insert(sub, 1);
    come_back(&mut net, 2);
    assert_eq!(net.delivered(2), vec![m0]);
    assert_eq!(told(&net, 2), 0);
    assert_eq!(
        net.nodes[0].t.behind_count(T),
        1,
        "the hub owes it the notice and the messages"
    );
    // Room: the messages in order, then the notice.
    net.nodes[0].h.room.remove(&sub);
    at_hub(&mut net, |t, h, now| t.peer_writable(h, now, &sub));
    let mut want = vec![m0];
    want.extend(&sent[200 - kept..]);
    assert_eq!(net.delivered(2), want);
    assert_eq!(told(&net, 2), 1);
    assert_eq!(net.nodes[0].t.behind_count(T), 0);
}

#[test]
fn a_subscriber_let_go_that_catches_up_into_a_stream_with_no_room_for_the_notice_is_told_when_it_has() {
    let mut net = world();
    net.run_until(2 * SEC);
    set_full(&mut net, 2, true);
    publish_kib(&mut net, 0, 1);
    // Past the stall time with nothing taken: the next store that needs room lets it go and evicts.
    net.advance(3 * SEC);
    let sent = publish_kib(&mut net, 1, 200);
    let kept = net.nodes[0].t.log_len(T);
    // Room for exactly the messages the log still has.
    give_room(&mut net, 2, kept);
    assert_eq!(net.delivered(2), sent[200 - kept..].to_vec());
    assert_eq!(told(&net, 2), 0, "no room for the notice yet");
    assert_eq!(net.nodes[0].t.behind_count(T), 1, "so the hub still owes it");
    let sub = net.id(2);
    net.nodes[0].h.room.remove(&sub);
    at_hub(&mut net, |t, h, now| t.peer_writable(h, now, &sub));
    assert_eq!(told(&net, 2), 1);
    assert_eq!(net.nodes[0].t.behind_count(T), 0);
    // And it is pushed live again.
    let after = net.publish(1, T, b"after");
    net.advance(SEC / 10);
    assert_eq!(net.delivered(2).last(), Some(&after));
}

/// A new life of subscriber 2: the hubs forget the old one's subscriptions, it subscribes, the hub reports its floor
/// and it asks for the replay from there.
fn restart(net: &mut Net, at: u64) {
    net.cut_from_hubs(2, false);
    net.restart(2, at);
    net.cut_from_hubs(2, true);
    net.set_primary(2, 0);
    net.subscribe(2, T);
    net.attach(2);
}

#[test]
fn a_restarted_subscriber_that_replays_from_its_floor_is_told_when_the_log_dropped_messages_since() {
    let mut net = world();
    net.publish(1, T, b"before");
    net.run_until(5 * SEC);
    // It is off while a burst longer than the log goes by, and comes back as a new life.
    net.cut_from_hubs(2, false);
    let sent = publish_kib(&mut net, 0, 200);
    restart(&mut net, 10 * SEC);
    net.run_until(12 * SEC);
    assert_eq!(net.delivered(2).last(), sent.last());
    assert_eq!(
        told(&net, 2),
        1,
        "the replay from its floor cannot reach what the log dropped"
    );
    // A restart with nothing dropped since its floor is not told.
    let live = net.publish(1, T, b"live");
    net.run_until(40 * SEC);
    assert_eq!(net.delivered(2).last(), Some(&live));
    restart(&mut net, 45 * SEC);
    net.run_until(50 * SEC);
    assert_eq!(told(&net, 2), 0);
}
