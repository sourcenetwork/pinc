//! Records and lookup: signed, replicated, republished and bounded; address discovery.
#![allow(
    clippy::many_single_char_names,
    clippy::assert_is_empty,
    clippy::decimal_bitwise_operands,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::cast_lossless,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements
)]

mod connect_common;

use core::net::SocketAddr;

use connect_common::*;
use vinc_connect::carrier::{DnsAnswer, Frame};
use vinc_connect::record::{Record, RecordError};
use vinc_connect::relay::datagram::{Datagram, MAX_TUNNEL_DATAGRAM};
use vinc_connect::relay::{Config, RecordOrigin, Reject, Relay, Trace, UdpTarget, rule};
use vinc_crypto::IdentityAlg;

#[test]
fn published_records_are_verified_stored_replicated_and_served() {
    let mut fx = Fx::new();
    let (p1, p2) = (nid(0x91), nid(0x92));
    fx.r.add_peer(p1);
    fx.r.add_peer(p2);
    let a_kp = ed(0x61);
    let a = id(&a_kp);
    let sa = fx.open(T0, a);
    let rec = record_bytes(&a_kp, fx.me, 7);
    fx.fx();
    fx.send(T0, a, sa, &Frame::Publish { record: &rec }).unwrap();
    // replicated byte for byte to every peer relay
    let out = fx.fx();
    assert_eq!(
        out,
        [
            Rec::Peer(p1, enc(&Frame::Sync { record: &rec })),
            Rec::Peer(p2, enc(&Frame::Sync { record: &rec })),
        ]
    );
    assert!(traces_of(&fx).contains(&Trace::RecordStored {
        node: a,
        seq: 7,
        origin: RecordOrigin::Publish
    }));
    assert_eq!(fx.r.record_count(), 1);
    // served over the carrier; the asker verifies the signature itself
    let q = nid(0x42);
    let sq = fx.open(T0, q);
    fx.fx();
    fx.send(T0, q, sq, &Frame::DnsQuery { peer: a }).unwrap();
    let out = fx.fx();
    assert_eq!(
        out,
        [Rec::Carrier(
            q,
            enc(&Frame::DnsReply {
                peer: a,
                answer: DnsAnswer::Record(&rec)
            })
        )]
    );
    let parsed = Record::parse_verified(&rec).unwrap();
    assert_eq!((parsed.node, parsed.seq, parsed.home), (a, 7, fx.me));
    // served over UDP
    fx.r.datagram(T0, addr(), None, &dg(&Datagram::DnsQuery { peer: a }), &mut fx.s)
        .unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Udp(
            UdpTarget::Reply(addr()),
            dg(&Datagram::DnsReply {
                peer: a,
                answer: DnsAnswer::Record(&rec)
            })
        )]
    );
    // a node nobody published
    fx.send(T0, q, sq, &Frame::DnsQuery { peer: nid(0x43) }).unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Carrier(
            q,
            enc(&Frame::DnsReply {
                peer: nid(0x43),
                answer: DnsAnswer::Absent
            })
        )]
    );
    assert_eq!(fx.r.stats().lookups, 3);
}

#[test]
fn a_replicated_record_equals_the_published_one_and_is_not_replicated_again() {
    let mut a_side = Fx::new();
    let mut b_side = Fx::with(|c| c.me = id(&ed(0x11)));
    let (rel_a, rel_b) = (a_side.me, b_side.me);
    a_side.r.add_peer(rel_b);
    b_side.r.add_peer(rel_a);
    b_side.r.add_peer(nid(0x93));
    let kp = ed(0x61);
    let n = id(&kp);
    let s = a_side.open(T0, n);
    let rec = record_bytes(&kp, rel_a, 3);
    a_side.send(T0, n, s, &Frame::Publish { record: &rec }).unwrap();
    let a_out = a_side.fx();
    let Rec::Peer(to, bytes) = &a_out[0] else { panic!() };
    assert_eq!(*to, rel_b);
    let Frame::Sync { record } = Frame::decode(bytes).unwrap() else {
        panic!()
    };
    assert_eq!(record, &rec[..]);
    b_side.peer(T0, rel_a, &Frame::Sync { record }).unwrap();
    assert!(b_side.fx().is_empty(), "a replica is not sent on");
    assert_eq!(b_side.r.lookup(T0, &n), Some(&rec[..]));
    assert!(b_side.traces_has_replica(n));
}

#[test]
fn records_with_bad_signatures_are_rejected_everywhere() {
    let mut fx = Fx::new();
    let p1 = nid(0x91);
    fx.r.add_peer(p1);
    let kp = ed(0x61);
    let a = id(&kp);
    let sa = fx.open(T0, a);
    let good = record_bytes(&kp, fx.me, 1);
    fx.fx();
    // every byte flipped: published or replicated, never stored, never replicated onward
    for i in 0..good.len() {
        let mut bad = good.clone();
        bad[i] ^= 0x01;
        let by_node = fx.send(T0, a, sa, &Frame::Publish { record: &bad });
        let by_peer = fx.peer(T0, p1, &Frame::Sync { record: &bad });
        assert!(by_node.is_err(), "published flip at {i}");
        assert!(by_peer.is_err(), "replicated flip at {i}");
    }
    assert_eq!(fx.r.record_count(), 0);
    assert!(
        fx.fx().iter().all(|r| !matches!(r, Rec::Peer(..))),
        "nothing was replicated"
    );
    let rejected = traces_of(&fx)
        .iter()
        .filter(|t| {
            matches!(
                t,
                Trace::Rejected {
                    reason: Reject::BadRecord(_) | Reject::WrongOwner,
                    ..
                }
            )
        })
        .count();
    assert_eq!(rejected, 2 * good.len());
    // a record signed by someone else, on a's carrier
    let other_kp = ed(0x62);
    let theirs = record_bytes(&other_kp, fx.me, 1);
    assert_eq!(
        fx.send(T0, a, sa, &Frame::Publish { record: &theirs }),
        Err(Reject::WrongOwner)
    );
    // a forged record: b's node id with a's key and signature
    let mut forged = good.clone();
    forged[8..41].copy_from_slice(&connect_common::node_bytes(&id(&other_kp)));
    let r = fx.peer(T0, p1, &Frame::Sync { record: &forged });
    assert!(matches!(r, Err(Reject::BadRecord(RecordError::Signature(_)))));
    assert_eq!(fx.r.record_count(), 0);
    // while the good one goes in
    fx.send(T0, a, sa, &Frame::Publish { record: &good }).unwrap();
    assert_eq!(fx.r.record_count(), 1);
}

#[test]
fn a_higher_sequence_replaces_and_a_lower_or_conflicting_one_is_refused() {
    let mut fx = Fx::new();
    let kp = ed(0x61);
    let a = id(&kp);
    let sa = fx.open(T0, a);
    let r5 = record_bytes(&kp, fx.me, 5);
    let r6 = record_bytes(&kp, nid(0x93), 6);
    let r4 = record_bytes(&kp, fx.me, 4);
    let r5b = record_bytes(&kp, nid(0x94), 5);
    fx.send(T0, a, sa, &Frame::Publish { record: &r5 }).unwrap();
    fx.send(T0, a, sa, &Frame::Publish { record: &r5 }).unwrap();
    assert_eq!(
        fx.send(T0, a, sa, &Frame::Publish { record: &r4 }),
        Err(Reject::StaleRecord)
    );
    assert_eq!(
        fx.send(T0, a, sa, &Frame::Publish { record: &r5b }),
        Err(Reject::StaleRecord)
    );
    assert_eq!(fx.r.lookup(T0, &a), Some(&r5[..]));
    fx.send(T0, a, sa, &Frame::Publish { record: &r6 }).unwrap();
    assert_eq!(fx.r.lookup(T0, &a), Some(&r6[..]));
    assert_eq!(fx.r.record_count(), 1);
}

#[test]
fn the_own_record_is_republished_every_1800_seconds() {
    assert_eq!(rule::RECORD_REPUBLISH_NS, 1800 * SEC);
    let mut fx = Fx::new();
    let p1 = nid(0x91);
    fx.r.add_peer(p1);
    let rec = record_bytes(&fx.kp, fx.me, 1);
    let other = record_bytes(&ed(0x61), fx.me, 1);
    assert_eq!(fx.r.set_own_record(T0, &other, &mut fx.s), Err(Reject::WrongOwner));
    fx.r.set_own_record(T0, &rec, &mut fx.s).unwrap();
    assert_eq!(fx.fx(), [Rec::Peer(p1, enc(&Frame::Sync { record: &rec }))]);
    fx.r.handle_timeout(T0, &mut fx.s);
    assert_eq!(fx.r.next_deadline(), Some(T0 + SEC));
    assert!(fx.fx().is_empty());
    fx.r.handle_timeout(T0 + 1799 * SEC, &mut fx.s);
    assert!(fx.fx().is_empty(), "not yet at 1799 s");
    fx.r.handle_timeout(T0 + 1800 * SEC, &mut fx.s);
    assert_eq!(fx.fx(), [Rec::Peer(p1, enc(&Frame::Sync { record: &rec }))]);
    assert!(traces_of(&fx).contains(&Trace::Republished { peers: 1 }));
    fx.r.handle_timeout(T0 + 3599 * SEC, &mut fx.s);
    assert!(fx.fx().is_empty());
    fx.r.handle_timeout(T0 + 3600 * SEC, &mut fx.s);
    assert_eq!(fx.fx().len(), 1);
    // the own record is served and never expires while it is republished
    assert_eq!(fx.r.lookup(T0 + 3600 * SEC, &fx.me), Some(&rec[..]));
}

#[test]
fn a_record_that_is_not_refreshed_expires() {
    let mut fx = Fx::new();
    let kp = ed(0x61);
    let a = id(&kp);
    let sa = fx.open(T0, a);
    let rec = record_bytes(&kp, fx.me, 1);
    fx.send(T0, a, sa, &Frame::Publish { record: &rec }).unwrap();
    assert_eq!(rule::RECORD_TTL_NS, 5400 * SEC);
    assert!(fx.r.lookup(T0 + 5399 * SEC, &a).is_some());
    assert!(fx.r.lookup(T0 + 5400 * SEC, &a).is_none());
    fx.r.handle_timeout(T0 + 5400 * SEC, &mut fx.s);
    assert_eq!(fx.r.record_count(), 0);
}

#[test]
fn the_record_store_is_bounded() {
    let mut r: Box<Relay<64, 4, 2, 256>> = Box::new(Relay::new(Config::new(id(&ed(0x10)), 1)));
    let mut s = Collect::default();
    for i in 0..4u8 {
        let kp = ed(0x80 + i);
        let rec = record_bytes(&kp, nid(1), 1);
        r.replica_for_test(T0, &rec, &mut s).unwrap();
    }
    assert_eq!(r.record_count(), 4);
    let kp = ed(0x90);
    let rec = record_bytes(&kp, nid(1), 1);
    assert_eq!(r.replica_for_test(T0, &rec, &mut s), Err(Reject::StoreFull));
    // an update of a stored node still fits
    let kp0 = ed(0x80);
    let upd = record_bytes(&kp0, nid(1), 2);
    assert_eq!(r.replica_for_test(T0, &upd, &mut s), Ok(()));
    assert_eq!(r.record_count(), 4);
}

#[test]
fn address_discovery_answers_the_observed_address() {
    let mut fx = Fx::new();
    for (i, a) in ["198.51.100.9:40000", "[2001:db8::7]:5555"].iter().enumerate() {
        let src: SocketAddr = a.parse().unwrap();
        let nonce = [i as u8 + 1; 8];
        fx.r.datagram(T0, src, None, &dg(&Datagram::Qad { nonce }), &mut fx.s)
            .unwrap();
        assert_eq!(
            fx.fx(),
            [Rec::Udp(
                UdpTarget::Reply(src),
                dg(&Datagram::Qadr { nonce, addr: src })
            )]
        );
    }
    assert_eq!(fx.r.stats().qad, 2);
    assert!(traces_of(&fx).contains(&Trace::QadAnswered));
    // an answer, or garbage, is not a query
    let bad = dg(&Datagram::Qadr {
        nonce: [0; 8],
        addr: addr(),
    });
    assert_eq!(
        fx.r.datagram(T0, addr(), None, &bad, &mut fx.s),
        Err(Reject::UnexpectedFrame)
    );
    assert!(matches!(
        fx.r.datagram(T0, addr(), None, &[0xee], &mut fx.s),
        Err(Reject::BadDatagram(_))
    ));
    assert!(fx.fx().is_empty());
}

#[test]
fn a_record_too_large_for_a_datagram_is_answered_over_the_carrier_only() {
    big_stack(|| {
        let mut fx = Fx::new();
        let kp = keypair(IdentityAlg::Hybrid, 0x61);
        let a = id(&kp);
        let sa = fx.open(T0, a);
        let rec = record_bytes(&kp, fx.me, 1);
        assert!(rec.len() > MAX_TUNNEL_DATAGRAM);
        fx.send(T0, a, sa, &Frame::Publish { record: &rec }).unwrap();
        fx.fx();
        fx.r.datagram(T0, addr(), None, &dg(&Datagram::DnsQuery { peer: a }), &mut fx.s)
            .unwrap();
        assert_eq!(
            fx.fx(),
            [Rec::Udp(
                UdpTarget::Reply(addr()),
                dg(&Datagram::DnsReply {
                    peer: a,
                    answer: DnsAnswer::TooLarge
                })
            )]
        );
        fx.send(T0, a, sa, &Frame::DnsQuery { peer: a }).unwrap();
        assert_eq!(
            fx.fx(),
            [Rec::Carrier(
                a,
                enc(&Frame::DnsReply {
                    peer: a,
                    answer: DnsAnswer::Record(&rec)
                })
            )]
        );
    });
}
