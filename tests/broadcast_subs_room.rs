//! A subscriber list that fits the recipient's stream is queued whole or not at all: a hub whose host says how much a
//! stream holds sends nothing while the stream lacks room for all of it, and the list as it then is when it has. A list
//! larger than the stream holds, or a host that cannot tell, goes piece by piece from the place a refusal kept.
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

use common::{Net, SEC};
use support::{
    HOLDS, T, count_pieces, fake, hand, holds, inject, piece, sorted, synth, wide_net, wire_bytes, writable,
};
use vinc_broadcast::Limits;
use vinc_broadcast::consts::SUBS_PIECE;
use vinc_crypto::IdentityAlg;

/// The largest list a stream of `HOLDS` bytes takes whole.
fn largest() -> usize {
    (1..=usize::from(u16::MAX)).rfind(|n| wire_bytes(*n) <= HOLDS).unwrap()
}

/// Hub 1 reports a set to hub 0, whose member 2 has a stream with no room: the list of `n` ids (the set, the member and
/// three more subscribers that join) is owed. The stream then has room for all of it but a byte, and the list changes
/// before each of the three times the host offers the stream: nothing is handed to the member while the room is short.
/// When the stream has room for the list as it then is, the member gets all of it, in one call.
fn whole_or_nothing(n: usize) {
    let limits = Limits {
        max_subscribers: 40_000,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 3], 2, SEC, limits);
    net.attach(2);
    net.nodes[0].h.holds = HOLDS;
    let member = net.id(2);
    let pieces = count_pieces(&mut net, 2);
    net.nodes[0].h.bytes.insert(member, 0);
    net.subscribe(2, T);
    let set = sorted((0..n - 4).map(|i| fake(i as u32)).collect());
    let ver = (9, 1);
    for (i, chunk) in set.chunks(SUBS_PIECE).enumerate() {
        let first = (i * SUBS_PIECE) as u16;
        assert!(inject(&mut net, 1, 0, &piece(ver, first, set.len() as u16, chunk)).is_empty());
    }
    net.pump();
    assert_eq!(pieces.get(), 0);
    let mut want = set;
    want.push(member);
    for k in 0..3u32 {
        let late = fake(100_000 + k);
        // The room is short of the list as it will be after this change by one byte.
        net.nodes[0].h.bytes.insert(member, wire_bytes(want.len() + 1) - 1);
        hand(&mut net, &[late]);
        want.push(late);
        writable(&mut net, &member);
        assert_eq!(
            pieces.get(),
            0,
            "a piece was handed to a stream that lacked room for the list"
        );
    }
    assert_eq!(want.len(), n);
    net.nodes[0].h.bytes.insert(member, wire_bytes(n));
    writable(&mut net, &member);
    assert_eq!(
        pieces.get(),
        n.div_ceil(SUBS_PIECE),
        "the list as it then was, in one call"
    );
    assert!(
        holds(&net, 2, &sorted(want)),
        "member 2 holds {} ids",
        net.nodes[2].t.known_subscribers(T).len()
    );
}

#[test]
fn a_list_of_129_ids_is_sent_whole_or_not_at_all() {
    whole_or_nothing(129);
}

#[test]
fn a_list_of_2000_ids_is_sent_whole_or_not_at_all() {
    whole_or_nothing(2000);
}

#[test]
fn the_largest_list_the_default_stream_holds_is_sent_whole_or_not_at_all() {
    whole_or_nothing(largest());
}

/// A list larger than what the stream holds goes piece by piece, whatever room there is, and resumes from the piece a
/// refusal kept: three pieces cross for a list of three.
#[test]
fn a_list_larger_than_the_stream_holds_resumes_from_its_place() {
    let mut net = wide_net(3);
    let mut want = synth(&mut net, 297);
    for i in [1, 2] {
        net.subscribe(i, T);
    }
    let three = net.id(3);
    let pieces = count_pieces(&mut net, 3);
    net.nodes[0].h.bytes.insert(three, 0);
    net.subscribe(3, T);
    want.extend((1..=3).map(|i| net.id(i)));
    let want = sorted(want);
    // The stream holds less than the list, and takes one piece per offer.
    net.nodes[0].h.holds = wire_bytes(want.len()) - 1;
    let mut writes = 0;
    while !holds(&net, 3, &want) && writes < 10 {
        net.nodes[0].h.bytes.insert(three, 25 + T.len() + 32 * SUBS_PIECE);
        writable(&mut net, &three);
        writes += 1;
    }
    assert!(
        holds(&net, 3, &want),
        "member 3 holds {} ids",
        net.nodes[3].t.known_subscribers(T).len()
    );
    assert_eq!(pieces.get(), 3);
    assert_eq!(writes, 3);
}

/// A host that cannot tell what a stream holds (it answers 0) gets the list piece by piece: the pieces that fit are
/// handed over while the room for the whole list is short.
#[test]
fn a_host_that_cannot_tell_gets_the_list_piece_by_piece() {
    let mut net = wide_net(3);
    let mut want = synth(&mut net, 297);
    for i in [1, 2] {
        net.subscribe(i, T);
    }
    let three = net.id(3);
    let pieces = count_pieces(&mut net, 3);
    net.nodes[0].h.bytes.insert(three, 0);
    net.subscribe(3, T);
    want.extend((1..=3).map(|i| net.id(i)));
    let want = sorted(want);
    net.nodes[0].h.bytes.insert(three, wire_bytes(want.len()) - 1);
    writable(&mut net, &three);
    assert!(pieces.get() >= 1 && pieces.get() < want.len().div_ceil(SUBS_PIECE));
    net.nodes[0].h.bytes.insert(three, wire_bytes(want.len()));
    writable(&mut net, &three);
    assert!(holds(&net, 3, &want));
    assert_eq!(pieces.get(), want.len().div_ceil(SUBS_PIECE), "resumed from its place");
}
