//! The subscriber list of a hub in pieces: a list of any length reaches every member whole, a piece that does not follow
//! the ones before it is never taken, a recipient in the middle of a list keeps its place, and every field of a piece
//! is checked before it changes a list.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::assert_is_empty
)]

#[path = "broadcast_common.rs"]
mod common;
#[path = "broadcast_subs_support.rs"]
mod support;

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use common::{Net, SEC, ty};
use support::{
    HOLDS, T, count_pieces, fake, gaps, hand, holds, inject, piece, resubscribe, sorted, subs_kind, subscribed, synth,
    wide_net, wire_bytes, writable,
};
use vinc_broadcast::consts::{GAP_EVERY, SUBS_PIECE};
use vinc_broadcast::{Limits, SubsDrop};
use vinc_crypto::IdentityAlg;
use vinc_membership::NodeId;

/// A hub that cannot write to `synth_n` subscribers is joined by three members: each ends with all the ids, the
/// widest SUBS frame is a piece, and the hub still owes the list to the ones it cannot reach.
fn the_members_of_a_big_list_hold_it_whole(limits: Limits, synth_n: u32) {
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 4], 1, SEC, limits);
    for i in 1..=3 {
        net.attach(i);
    }
    let widest = Rc::new(Cell::new(0usize));
    let w = Rc::clone(&widest);
    net.filter = Some(Box::new(move |_, _, bytes| {
        if bytes.get(4) == Some(&ty::SUBS) {
            w.set(w.get().max(bytes.len()));
        }
        true
    }));
    let mut want = synth(&mut net, synth_n);
    for i in 1..=3 {
        net.subscribe(i, T);
        want.push(net.id(i));
    }
    let want = sorted(want);
    for i in 1..=3 {
        assert!(
            holds(&net, i, &want),
            "member {i} holds {} ids",
            net.nodes[i].t.known_subscribers(T).len()
        );
        assert!(subscribed(&net, i), "member {i} was never told");
    }
    println!("widest SUBS frame: {} bytes", widest.get());
    assert!(
        widest.get() <= 25 + T.len() + 32 * SUBS_PIECE,
        "a SUBS frame of {} bytes",
        widest.get()
    );
    assert_eq!(net.nodes[0].t.subs_owed(), synth_n as usize);
}

/// With the default limits a hub with 4,096 subscribers gives every member the whole list, in pieces: the list used to
/// be one frame, which the hub could not build past 2,216 ids, so it sent none.
#[test]
fn a_hub_with_the_default_limits_and_4096_subscribers_gives_every_member_the_complete_list() {
    let limits = Limits {
        max_subscribers: 4096,
        ..Limits::default()
    };
    the_members_of_a_big_list_hold_it_whole(limits, 4093);
}

/// A 1 KiB body limit leaves a frame of 6,700 bytes, and the default 256 subscribers made a list of 8,219.
#[test]
fn at_a_1_kib_body_limit_the_default_256_subscribers_reach_every_member() {
    let limits = Limits {
        max_body: 1024,
        ..Limits::default()
    };
    the_members_of_a_big_list_hold_it_whole(limits, 253);
}

/// A piece lost in the middle of a list is never taken as the list: the member holds no list and no event, traces the
/// gap for the piece after it and for the one after that, and asks the hub once; the whole list comes on its next
/// subscribe.
#[test]
fn a_lost_middle_piece_is_never_taken_and_the_member_asks_once() {
    let limits = Limits {
        max_subscribers: 512,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 4], 1, SEC, limits);
    for i in 1..=3 {
        net.attach(i);
    }
    let mut want = synth(&mut net, 397);
    for i in [1, 2] {
        net.subscribe(i, T);
    }
    let asks = Rc::new(Cell::new(0usize));
    let a = Rc::clone(&asks);
    net.filter = Some(Box::new(move |from, to, bytes| match subs_kind(bytes) {
        Some((2, _)) if (from, to) == (3, 0) => {
            a.set(a.get() + 1);
            false
        }
        Some((0, 128)) => to != 3,
        _ => true,
    }));
    net.subscribe(3, T);
    assert!(net.nodes[3].t.known_subscribers(T).is_empty());
    assert!(!subscribed(&net, 3));
    assert_eq!(gaps(&mut net, 3), 2);
    assert_eq!(asks.get(), 1);

    net.filter = None;
    resubscribe(&mut net, 3);
    want.extend((1..=3).map(|i| net.id(i)));
    assert!(holds(&net, 3, &sorted(want)));
    assert!(subscribed(&net, 3));
}

/// A piece lost at the end of a list leaves no gap to see: the member holds no list and no event. Nothing but a change
/// of the list repairs it on a topic with no traffic (the periodic check runs on live topics only): the change comes
/// from the member's primary, which is not the hub of a list the member holds (it holds none), so the member takes the
/// primary as its source and asks it for the whole list (the `OtherHub` arm of the change handler).
#[test]
fn a_lost_last_piece_is_repaired() {
    let limits = Limits {
        max_subscribers: 512,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 5], 1, SEC, limits);
    for i in 1..=4 {
        net.attach(i);
    }
    let mut want = synth(&mut net, 397);
    for i in [1, 2] {
        net.subscribe(i, T);
    }
    net.filter = Some(Box::new(|_, to, bytes| {
        !(to == 3 && subs_kind(bytes) == Some((0, 384)))
    }));
    net.subscribe(3, T);
    net.filter = None;
    assert!(net.nodes[3].t.known_subscribers(T).is_empty());
    assert!(!subscribed(&net, 3));
    net.advance(3 * GAP_EVERY);
    assert!(
        net.nodes[3].t.known_subscribers(T).is_empty(),
        "a quiet topic repaired itself"
    );
    assert!(!subscribed(&net, 3));

    net.subscribe(4, T);
    want.extend((1..=4).map(|i| net.id(i)));
    assert!(holds(&net, 3, &sorted(want)));
    assert!(subscribed(&net, 3));
}

/// A stream with room for one frame at a time: a member's stream takes the first piece and refuses the second. The
/// list then changes (a subscriber joins) and every place goes back to the first piece; the member ends with the new
/// list, whole, without a gap or an ask.
#[test]
fn a_list_that_changes_while_it_is_sent_ends_whole_at_the_new_version() {
    let mut net = wide_net(4);
    let mut want = synth(&mut net, 297);
    for i in [1, 2] {
        net.subscribe(i, T);
    }
    let (three, now) = (net.id(3), net.now);
    let asks = Rc::new(Cell::new(0usize));
    let a = Rc::clone(&asks);
    net.filter = Some(Box::new(move |from, to, bytes| {
        a.set(a.get() + usize::from((from, to) == (3, 0) && subs_kind(bytes) == Some((2, 0))));
        true
    }));
    net.nodes[0].h.room.insert(three, 1);
    net.subscribe(3, T);
    assert_eq!(net.count_between(0, 3, ty::SUBS), 1);
    net.subscribe(4, T);
    want.extend((1..=4).map(|i| net.id(i)));
    let want = sorted(want);
    let mut writes = 0;
    while !holds(&net, 3, &want) && writes < 10 {
        net.nodes[0].h.room.insert(three, 1);
        let hub = &mut net.nodes[0];
        hub.t.peer_writable(&mut hub.h, now, &three);
        net.pump();
        writes += 1;
    }
    assert!(
        holds(&net, 3, &want),
        "member 3 holds {} ids",
        net.nodes[3].t.known_subscribers(T).len()
    );
    assert_eq!(want.len(), 301);
    assert_eq!(gaps(&mut net, 3), 0);
    assert_eq!(asks.get(), 0);
}

/// A stream that takes one piece at a time resumes the list from the piece it refused, not from the first: three
/// pieces cross for a list of three.
#[test]
fn a_full_stream_resumes_the_list_from_its_place() {
    let mut net = wide_net(3);
    let mut want = synth(&mut net, 297);
    for i in [1, 2] {
        net.subscribe(i, T);
    }
    let (three, now) = (net.id(3), net.now);
    net.nodes[0].h.room.insert(three, 1);
    net.subscribe(3, T);
    want.extend((1..=3).map(|i| net.id(i)));
    let want = sorted(want);
    let mut writes = 0;
    while !holds(&net, 3, &want) && writes < 10 {
        net.nodes[0].h.room.insert(three, 1);
        let hub = &mut net.nodes[0];
        hub.t.peer_writable(&mut hub.h, now, &three);
        net.pump();
        writes += 1;
    }
    assert!(
        holds(&net, 3, &want),
        "member 3 holds {} ids",
        net.nodes[3].t.known_subscribers(T).len()
    );
    assert_eq!(want.len(), 300);
    assert_eq!(net.count_between(0, 3, ty::SUBS), 3);
}

/// A list that fits the stream ends whole at a member whose stream never has room for all of it while the list
/// changes: nothing is handed over meanwhile, and one call hands it all once the room is there.
#[test]
fn a_list_that_changes_before_every_writable() {
    let mut net = wide_net(3);
    net.nodes[0].h.holds = HOLDS;
    let mut want = synth(&mut net, 297);
    for i in [1, 2] {
        net.subscribe(i, T);
    }
    let three = net.id(3);
    let pieces = count_pieces(&mut net, 3);
    net.nodes[0].h.bytes.insert(three, 0);
    net.subscribe(3, T);
    for k in 0..6 {
        let id = fake(1000 + k);
        // Room for two pieces, never for all three.
        net.nodes[0].h.bytes.insert(three, 2 * (25 + T.len() + 32 * SUBS_PIECE));
        hand(&mut net, &[id]);
        want.push(id);
        writable(&mut net, &three);
    }
    want.extend((1..=3).map(|i| net.id(i)));
    let want = sorted(want);
    assert_eq!(pieces.get(), 0, "pieces were handed over while the room was short");
    net.nodes[0].h.bytes.insert(three, wire_bytes(want.len()));
    writable(&mut net, &three);
    assert!(
        holds(&net, 3, &want),
        "member 3 holds {} ids",
        net.nodes[3].t.known_subscribers(T).len()
    );
    assert_eq!(pieces.get(), want.len().div_ceil(SUBS_PIECE), "each piece once");
    assert_eq!(gaps(&mut net, 3), 0);
}

/// The ids of `n` fake subscribers, in id order.
fn fakes(n: u32) -> Vec<NodeId> {
    sorted((0..n).map(fake).collect())
}

/// A member in the middle of a list whose stream refused a piece sends its periodic SUB, which carries a version that
/// is not the hub's current one. The SUB changes nothing in the list, so the member goes on from the piece it was owed
/// and ends with the whole list: the hub hands it each piece once (the SUB comes every 20 s, which a stream that drains
/// slowly needs longer than).
#[test]
fn a_members_periodic_sub_does_not_restart_a_list_in_flight() {
    let mut net = wide_net(3);
    // Member 3 holds an earlier version of the list when the stream stops taking frames.
    net.subscribe(3, T);
    let mut want = synth(&mut net, 297);
    for i in [1, 2] {
        net.subscribe(i, T);
    }
    let (three, now) = (net.id(3), net.now);
    let pieces = Rc::new(Cell::new(0usize));
    let p = Rc::clone(&pieces);
    let asks = Rc::new(Cell::new(0usize));
    let a = Rc::clone(&asks);
    net.filter = Some(Box::new(move |from, to, bytes| {
        p.set(p.get() + usize::from(to == 3 && matches!(subs_kind(bytes), Some((0, _)))));
        a.set(a.get() + usize::from((from, to) == (3, 0) && subs_kind(bytes) == Some((2, 0))));
        true
    }));
    // A change the stream refuses leaves member 3 owed the list (301 ids: three pieces).
    net.nodes[0].h.full.insert(three);
    let late = fake(5000);
    hand(&mut net, &[late]);
    want.push(late);
    want.extend((1..=3).map(|i| net.id(i)));
    let want = sorted(want);
    assert_eq!(want.len(), 301);
    net.nodes[0].h.full.remove(&three);
    // The stream takes the first piece and refuses the second.
    net.nodes[0].h.room.insert(three, 1);
    let hub = &mut net.nodes[0];
    hub.t.peer_writable(&mut hub.h, now, &three);
    net.pump();
    assert_eq!(pieces.get(), 1);
    // Its periodic SUB arrives while the stream has no room, and again once it has.
    resubscribe(&mut net, 3);
    let mut writes = 0;
    while !holds(&net, 3, &want) && writes < 10 {
        net.nodes[0].h.room.insert(three, 1);
        let hub = &mut net.nodes[0];
        hub.t.peer_writable(&mut hub.h, now, &three);
        net.pump();
        writes += 1;
    }
    assert!(
        holds(&net, 3, &want),
        "member 3 holds {} ids",
        net.nodes[3].t.known_subscribers(T).len()
    );
    assert_eq!(
        pieces.get(),
        3,
        "the hub handed member 3 {} pieces of a list of three",
        pieces.get()
    );
    assert_eq!(gaps(&mut net, 3), 0);
    assert_eq!(asks.get(), 0);
}

/// A piece that names ranks past the end of its list is refused: a gathering that overshot its total would complete
/// with ids the list does not have.
#[test]
fn a_piece_whose_ranks_pass_the_end_of_its_list_is_refused() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    let all = fakes(6);
    let ver = (7, 3);
    assert_eq!(
        inject(&mut net, 0, 1, &piece(ver, 5, 6, &all[..3])),
        [SubsDrop::Malformed]
    );
    assert_eq!(
        inject(&mut net, 0, 1, &piece(ver, 0, 2, &all[..3])),
        [SubsDrop::Malformed]
    );
    assert!(net.nodes[1].t.known_subscribers(T).is_empty());
    // The same piece within its list is taken.
    assert!(inject(&mut net, 0, 1, &piece(ver, 0, 3, &all[..3])).is_empty());
    assert_eq!(net.nodes[1].t.known_subscribers(T), &all[..3]);
}

/// A piece with no ids of a list that has some is refused (it would never complete the list); an empty list is one
/// empty piece, and is taken.
#[test]
fn an_empty_piece_of_a_list_that_has_ids_is_refused() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    let all = fakes(4);
    let ver = (7, 3);
    assert!(inject(&mut net, 0, 1, &piece(ver, 0, 4, &all)).is_empty());
    assert_eq!(inject(&mut net, 0, 1, &piece((7, 4), 0, 5, &[])), [SubsDrop::Malformed]);
    assert_eq!(net.nodes[1].t.known_subscribers(T), all.as_slice());
    assert!(inject(&mut net, 0, 1, &piece((7, 5), 0, 0, &[])).is_empty());
    assert!(net.nodes[1].t.known_subscribers(T).is_empty());
}

/// A piece of the same version whose total differs from its gathering's marks the gathering broken: the member traces
/// the gap and asks the hub once, and the rest of that version asks nothing more.
#[test]
fn a_piece_whose_total_differs_from_its_gathering_breaks_it_and_the_member_asks_once() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    let all = fakes(12);
    let ver = (7, 3);
    let asks = |net: &Net| {
        net.log
            .iter()
            .filter(|(_, from, to, t, _)| (*from, *to, *t) == (1, 0, ty::SUBS))
            .count()
    };
    assert!(inject(&mut net, 0, 1, &piece(ver, 0, 10, &all[..3])).is_empty());
    assert_eq!(inject(&mut net, 0, 1, &piece(ver, 3, 12, &all[3..6])), [SubsDrop::Gap]);
    net.pump();
    assert_eq!(asks(&net), 1);
    assert_eq!(inject(&mut net, 0, 1, &piece(ver, 6, 12, &all[6..9])), [SubsDrop::Gap]);
    net.pump();
    assert_eq!(asks(&net), 1, "the member asked again for the same version");
    assert!(net.nodes[1].t.known_subscribers(T).is_empty());
}

/// A change of more than 128 ids (another hub's set arriving) reaches the members as the whole list in pieces, never as
/// one change.
#[test]
fn a_change_of_more_than_128_ids_reaches_members_as_the_whole_list() {
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 2, SEC);
    for i in [2, 3] {
        net.subscribe(i, T);
    }
    let kinds = Rc::new(RefCell::new(Vec::new()));
    let k = Rc::clone(&kinds);
    net.filter = Some(Box::new(move |_, to, bytes| {
        if to == 2 {
            k.borrow_mut().extend(subs_kind(bytes));
        }
        true
    }));
    // Hub 1 reports 200 subscribers, in two pieces.
    let set = fakes(200);
    let ver = (9, 1);
    assert!(inject(&mut net, 1, 0, &piece(ver, 0, 200, &set[..128])).is_empty());
    assert!(inject(&mut net, 1, 0, &piece(ver, 128, 200, &set[128..])).is_empty());
    net.pump();
    assert_eq!(*kinds.borrow(), [(0, 0), (0, 128)], "what member 2 was sent");
    let mut want = set;
    want.extend((2..=3).map(|i| net.id(i)));
    assert!(holds(&net, 2, &sorted(want)));
}
