//! Connection ids: the lookahead survives a peer that skips indices.
//!
//! A path whose packets never arrive leaves its derived id unused. The table forgets used ids first; when unused ids
//! older than the highest used index filled the table, no slot was left for the next ids and the lookahead (the ids
//! just above the highest used index) was lost, so a packet on a fresh path could not be routed.
#![allow(clippy::unwrap_used, unreachable_pub)]

use vinc_transport::conn::CidTable;

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
    assert!(!retired.is_empty());
}

#[test]
fn the_sender_takes_each_index_once_and_none_before_the_peers_first_id() {
    let mut t = CidTable::new(false, &[9, 9, 9, 9]).unwrap();
    assert_eq!(t.claim_remote(), None);
    t.set_first_remote(&[1, 1, 1, 1]);
    assert_eq!(t.claim_remote(), Some((0, true)));
    assert_eq!(t.claim_remote(), None, "an index past 0 needs the session secret");
    t.install(&SECRET);
    assert_eq!(t.claim_remote(), Some((1, true)), "the id claimed is the one derived for its index");
    assert_eq!(t.claim_remote(), Some((2, true)));
}
