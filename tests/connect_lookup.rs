//! The lookup client: query timing, CARRIER_DNS, DIAL_PRUNE and the verification of a returned record.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::many_single_char_names
)]

mod connect_common;

use connect_common::{ed, id, nid};
use vinc_connect::carrier::frame::DnsAnswer;
use vinc_connect::client::dial::Pending;
use vinc_connect::client::lookup::{Ask, CARRIER_WAIT_NS, LookupError, Lookups, RETRY_NS, verify};
use vinc_connect::record::{self, Reach, RecordFields};

const MS: u64 = 1_000_000;

#[test]
fn a_query_repeats_after_300ms_and_the_repeat_goes_to_every_relay() {
    let mut l = Lookups::<4>::new();
    let p = nid(7);
    assert_eq!(l.ask(0, &p, true, false), Ask::Udp { others: false });
    assert_eq!(l.ask(RETRY_NS - 1, &p, true, false), Ask::Skip);
    assert_eq!(l.ask(RETRY_NS, &p, true, false), Ask::Udp { others: true });
    assert_eq!(l.ask(RETRY_NS + 1, &p, true, false), Ask::Skip);
    // due is strictly after the wait
    assert_eq!(l.due(2 * RETRY_NS).count(), 0);
    assert_eq!(l.due(2 * RETRY_NS + 1).collect::<Vec<_>>(), vec![p]);
    assert_eq!(l.next_deadline(), Some(2 * RETRY_NS + 1));
    l.answered(&p);
    assert!(l.is_empty());
}

#[test]
fn a_dark_node_asks_over_the_carrier_and_waits_two_seconds() {
    let mut l = Lookups::<4>::new();
    let p = nid(7);
    assert_eq!(l.ask(0, &p, false, true), Ask::Carrier);
    assert_eq!(l.ask(CARRIER_WAIT_NS - 1, &p, false, true), Ask::Skip);
    assert_eq!(
        l.ask(CARRIER_WAIT_NS, &p, false, true),
        Ask::Carrier,
        "repeated after at least 2 s"
    );
    // never to every relay, and with no carrier nothing is sent after the first try
    let q = nid(8);
    assert_eq!(
        l.ask(0, &q, false, false),
        Ask::Udp { others: false },
        "the first query goes out over UDP"
    );
    assert_eq!(l.ask(CARRIER_WAIT_NS - RETRY_NS, &q, false, false), Ask::Later);
    assert_eq!(l.ask(CARRIER_WAIT_NS - RETRY_NS + 1, &q, false, false), Ask::Skip);
}

#[test]
fn a_too_large_answer_is_asked_again_over_the_carrier() {
    let mut l = Lookups::<4>::new();
    let p = nid(7);
    assert_eq!(l.ask(0, &p, true, true), Ask::Udp { others: false });
    l.too_large(&p);
    assert_eq!(l.ask(1, &p, true, true), Ask::Carrier);
}

#[test]
fn the_table_is_bounded_and_clear_forgets_everything() {
    let mut l = Lookups::<2>::new();
    assert_eq!(l.ask(0, &nid(1), true, false), Ask::Udp { others: false });
    assert_eq!(l.ask(0, &nid(2), true, false), Ask::Udp { others: false });
    assert_eq!(l.ask(0, &nid(3), true, false), Ask::Skip);
    assert_eq!(l.len(), 2);
    l.clear();
    assert!(l.is_empty());
    assert_eq!(l.ask(0, &nid(3), true, false), Ask::Udp { others: false });
}

#[test]
fn dial_prune_keeps_only_sessions_in_handshake() {
    let mut p = Pending::<u32, 4, 3>::new();
    let (a, b) = (nid(1), nid(2));
    assert!(p.add(a, 10));
    assert!(p.add(a, 11));
    assert!(p.add(b, 20));
    assert!(p.add(a, 11), "adding the same session twice is fine");
    let mut dropped = vec![];
    p.prune(|s| s == 11, |peer| dropped.push(*peer));
    assert_eq!(
        dropped,
        vec![b],
        "b has no session left in handshake: its lookup is dropped"
    );
    assert!(p.contains(&a));
    assert!(!p.contains(&b));
    let taken = p.take(&a);
    assert_eq!(taken.iter().flatten().copied().collect::<Vec<_>>(), vec![11]);
    assert!(!p.contains(&a));
    // a full list refuses
    let c = nid(3);
    assert!(p.add(c, 1) && p.add(c, 2) && p.add(c, 3));
    assert!(!p.add(c, 4));
}

fn signed(tag: u8, seq: u64) -> (vinc_crypto::Keypair, Vec<u8>) {
    let kp = ed(tag);
    let mut buf = vec![0u8; record::MAX_RECORD_LEN];
    let addrs = ["203.0.113.9:6000".parse().unwrap()];
    let f = RecordFields {
        home: nid(99),
        seq,
        reach: Reach::Nat,
        addrs: &addrs,
        hints: &[],
    };
    let n = record::sign(&kp, &f, &mut buf).unwrap();
    buf.truncate(n);
    (kp, buf)
}

#[test]
fn the_asker_verifies_the_returned_record() {
    let (kp, bytes) = signed(5, 4);
    let peer = id(&kp);
    let f = verify(&peer, &DnsAnswer::Record(&bytes)).unwrap().unwrap();
    assert_eq!(f.home, nid(99));
    assert_eq!(f.seq, 4);
    assert_eq!(f.addrs().collect::<Vec<_>>(), vec!["203.0.113.9:6000".parse().unwrap()]);
    assert_eq!(verify(&peer, &DnsAnswer::Absent), Ok(None));
    assert_eq!(verify(&peer, &DnsAnswer::TooLarge), Err(LookupError::TooLarge));
    // a record of another node, a flipped bit and a truncation are all refused
    assert_eq!(verify(&nid(6), &DnsAnswer::Record(&bytes)), Err(LookupError::WrongNode));
    for i in [10usize, 60, bytes.len() - 1] {
        let mut bad = bytes.clone();
        bad[i] ^= 1;
        assert!(
            matches!(
                verify(&peer, &DnsAnswer::Record(&bad)),
                Err(LookupError::Record(_)) | Err(LookupError::WrongNode)
            ),
            "byte {i}"
        );
    }
    assert!(matches!(
        verify(&peer, &DnsAnswer::Record(&bytes[..bytes.len() - 1])),
        Err(LookupError::Record(_))
    ));
    let _ = MS;
}
