//! The drain's bound: a pass reads every held byte once and moves it at most once.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    reason = "tests assert"
)]

extern crate std;

use std::println;

use super::*;
use pinc_crypto::IdentityAlg;

/// The most a body can be and still go down a datagram.
const FIT: usize = 1389;
const BYTES: usize = 16 * 1024;
type M = Mailbox<2, BYTES>;

fn node(tag: u8) -> NodeId {
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: [tag; 32],
    }
}

/// Offer everything that fits and take it all.
fn take_all(m: &mut M, to: &NodeId) {
    let mut buf = [0u8; MAX_PACKET_LEN];
    Mailbox::drain(
        m,
        |m| m,
        0,
        to,
        FIT,
        &mut buf,
        |_, _, _| Offer {
            taken: true,
            go_on: true,
        },
    );
}

/// Six messages too long in front, then as many one-byte messages as the quota holds: the layout the earlier
/// scan-per-hand-over way moved the most bytes for. The long ones stay in front, so nothing moves at all.
#[test]
fn the_worst_layout_of_long_ones_in_front_moves_nothing() {
    let (mut m, to, from) = (M::new(1_000_000_000, 1), node(1), node(2));
    let mut held = 0;
    for _ in 0..6 {
        m.push(0, &to, &from, 0, &[1u8; FIT + 1]);
        held += ENTRY_HEAD + FIT + 1;
    }
    while held + ENTRY_HEAD < BYTES {
        assert!(matches!(m.push(0, &to, &from, 0, &[2u8; 1]), Push::Stored { .. }));
        held += ENTRY_HEAD + 1;
    }
    assert_eq!(m.pending(&to).1, held);
    take_all(&mut m, &to);
    println!("DRAINMOVED worst layout: held {held} bytes, moved {}", m.moved(&to));
    assert!(m.moved(&to) <= held);
    assert_eq!(m.moved(&to), 0);
    assert_eq!(m.pending(&to), (6, 6 * (ENTRY_HEAD + FIT + 1)));
}

/// Long ones between short ones: each long one behind a taken message is moved once, no byte more than once.
#[test]
fn a_long_one_behind_a_taken_message_is_moved_once_and_no_byte_twice() {
    let (mut m, to, from) = (M::new(1_000_000_000, 1), node(1), node(2));
    let mut held = 0;
    for i in 0..5u8 {
        m.push(0, &to, &from, i, &[i; 3]);
        m.push(0, &to, &from, 100 + i, &[i; FIT + 1]);
        held += 2 * ENTRY_HEAD + 3 + FIT + 1;
    }
    assert_eq!(m.pending(&to).1, held);
    take_all(&mut m, &to);
    println!("DRAINMOVED interleaved: held {held} bytes, moved {}", m.moved(&to));
    // the first long one stays where the walk left it; the four after it are moved down once each
    assert_eq!(m.moved(&to), 4 * (ENTRY_HEAD + FIT + 1));
    assert!(m.moved(&to) <= held);
    let mut buf = [0u8; MAX_PACKET_LEN];
    for i in 0..5usize {
        let (d, _) = m.peek(&to, i, &mut buf).unwrap();
        assert_eq!((d.flag, d.len), (100 + i as u8, FIT + 1));
        assert!(buf[..d.len].iter().all(|b| *b == i as u8));
    }
}
