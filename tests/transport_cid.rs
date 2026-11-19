//! Connection ids: the lookahead survives a peer that skips indices.
//!
//! A path whose packets never arrive leaves its derived id unused. The table forgets used ids first; when unused ids
//! older than the highest used index filled the table, no slot was left for the next ids and the lookahead (the ids
//! just above the highest used index) was lost, so a packet on a fresh path could not be routed.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::many_single_char_names,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::too_many_lines,
    unreachable_pub
)]

use pinc_transport::conn::CidTable;

const SECRET: [u8; 32] = [7; 32];

fn table() -> CidTable {
    let mut t = CidTable::new(true, &[1, 2, 3, 4]).unwrap();
    t.set_first_remote(&[5, 6, 7, 8]);
    t.install(&SECRET);
    t
}

#[test]
fn a_peer_that_skips_every_other_index_keeps_the_lookahead() {
    let mut t = table();
    for index in (2..=40).step_by(2) {
        assert!(t.is_local(index), "the id of index {index} is not routable");
        t.on_authenticated(index);
        let hi = t.view().highest;
        assert_eq!(hi, index);
        assert!(
            t.is_local(hi + 1) && t.is_local(hi + 2),
            "the lookahead is lost after index {hi}"
        );
    }
}

#[test]
fn a_retired_id_is_never_accepted_again() {
    let mut t = table();
    let mut retired = Vec::new();
    let mut held: Vec<u64> = (1..=2).collect();
    for index in 1..=30u64 {
        t.on_authenticated(index);
        let now: Vec<u64> = (1..=index + 2).filter(|i| t.is_local(*i)).collect();
        retired.extend(held.iter().copied().filter(|h| !now.contains(h)));
        held = now;
        for r in &retired {
            assert!(!t.is_local(*r), "the retired id {r} is accepted again");
            assert!(*r <= t.view().highest);
        }
    }
    assert_ne!(retired.len(), 0, "no id was ever retired");
}

#[test]
fn the_sender_takes_fresh_indices_in_order_and_none_before_the_peers_first_id() {
    let mut t = CidTable::new(false, &[9, 9, 9, 9]).unwrap();
    assert_eq!(t.claim_remote(), None);
    t.set_first_remote(&[1, 1, 1, 1]);
    assert_eq!(t.claim_remote(), Some((0, true)));
    assert_eq!(t.claim_remote(), None, "an index past 0 needs the session secret");
    t.install(&SECRET);
    assert_eq!(
        t.claim_remote(),
        Some((1, true)),
        "the id claimed is the one derived for its index"
    );
    assert_eq!(t.claim_remote(), Some((2, true)));
}

#[test]
fn every_id_a_sender_takes_with_nothing_confirmed_is_one_the_receiver_accepts() {
    let recv = table();
    let mut send = CidTable::new(false, &[9, 9, 9, 9]).unwrap();
    send.set_first_remote(&[1, 1, 1, 1]);
    send.install(&SECRET);
    for path in 0..6 {
        let (index, derived) = send.claim_remote().unwrap();
        assert!(derived);
        assert!(
            recv.is_local(index),
            "path {path} was given index {index}, which the receiver does not accept"
        );
    }
}

#[test]
fn a_confirmed_index_moves_the_window_and_retires_the_ids_below_it() {
    let mut send = CidTable::new(false, &[9, 9, 9, 9]).unwrap();
    send.set_first_remote(&[1, 1, 1, 1]);
    send.install(&SECRET);
    assert_eq!(send.claim_remote().map(|c| c.0), Some(0));
    assert_eq!(send.claim_remote().map(|c| c.0), Some(1));
    assert_eq!(send.claim_remote().map(|c| c.0), Some(2));
    assert_eq!(
        send.claim_remote().map(|c| c.0),
        Some(1),
        "past the window the ids of the window come again"
    );
    assert_eq!(send.claim_remote().map(|c| c.0), Some(2));
    assert!(send.remote_usable(1));
    send.confirm_remote(2);
    assert_eq!(send.claim_remote().map(|c| c.0), Some(3));
    assert!(!send.remote_usable(1));
    assert!(!send.remote_usable(2));
    assert!(send.remote_usable(0));
    assert!(send.remote_usable(3));
}

#[test]
fn the_unused_id_below_the_highest_seen_stays_held_when_the_table_is_full_of_used_ones() {
    let mut t = table();
    for index in 1..=7 {
        t.on_authenticated(index);
    }
    // The used ids are the most recently used; the id of index 8 was never used.
    for index in 2..=7 {
        t.on_authenticated(index);
    }
    t.on_authenticated(9);
    assert!(t.is_local(8), "the id just below the highest seen was evicted");
    assert!(t.is_local(10) && t.is_local(11));
}
