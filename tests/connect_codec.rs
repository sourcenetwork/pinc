//! The carrier frame codec, the control datagrams, aliases, signed records and sleep notices.
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

use connect_common::{big_stack, ed, enc, id, keypair, nid};
use proptest::prelude::*;
use vinc_connect::carrier::frame::{MAX_NOTICE_LEN, kind};
use vinc_connect::carrier::{
    ALIAS_MAX, AliasTable, Assigned, BATCH_MAX_BYTES, BATCH_MAX_FRAMES, BatchBuilder, DnsAnswer, Frame, FrameError,
    MAX_FRAME_LEN, MAX_PACKET_LEN, Offer,
};
use vinc_connect::record::{MAX_ADDRS, MAX_HINT_LEN, MAX_RECORD_LEN, Reach, Record, RecordError, RecordFields, sign};
use vinc_connect::relay::datagram::{Datagram, DatagramError, MAX_TUNNEL_DATAGRAM};
use vinc_connect::relay::sleep::{self, Notice, SleepError};
use vinc_crypto::{IdentityAlg, NodeId};

fn round_trip(f: &Frame<'_>) {
    let bytes = enc(f);
    let back = Frame::decode(&bytes).unwrap();
    assert_eq!(&back, f);
    assert_eq!(enc(&back), bytes);
}

#[test]
fn every_frame_round_trips() {
    let a = nid(1);
    let b = nid(2);
    let pkt = [0x40u8; 100];
    let rec = [7u8; 300];
    let frames = [
        Frame::Send {
            dst: a,
            flag: 9,
            packet: &pkt,
        },
        Frame::Recv {
            src: a,
            flag: 0,
            packet: &pkt,
        },
        Frame::SendNew {
            dst: a,
            alias: 31,
            flag: 1,
            packet: &pkt,
        },
        Frame::SendAlias {
            alias: 0,
            flag: 1,
            packet: &pkt,
        },
        Frame::RecvNew {
            src: b,
            alias: 5,
            flag: 2,
            packet: &pkt,
        },
        Frame::RecvAlias {
            alias: 5,
            flag: 2,
            packet: &pkt,
        },
        Frame::Publish { record: &rec },
        Frame::Ping,
        Frame::Pong,
        Frame::SelfSend { packet: &pkt },
        Frame::SelfRecv { packet: &pkt },
        Frame::DnsQuery { peer: a },
        Frame::DnsReply {
            peer: a,
            answer: DnsAnswer::Absent,
        },
        Frame::DnsReply {
            peer: a,
            answer: DnsAnswer::Record(&rec),
        },
        Frame::DnsReply {
            peer: a,
            answer: DnsAnswer::TooLarge,
        },
        Frame::Forward {
            src: a,
            dst: b,
            flag: 3,
            packet: &pkt,
        },
        Frame::Sync { record: &rec },
        Frame::Sleep { notice: &rec },
    ];
    for f in &frames {
        round_trip(f);
    }
    // every identity algorithm tag is a valid node id
    for alg in [
        IdentityAlg::Ed25519,
        IdentityAlg::EcdsaP256,
        IdentityAlg::MlDsa65,
        IdentityAlg::Hybrid,
    ] {
        let n = NodeId { alg, bytes: [9; 32] };
        round_trip(&Frame::DnsQuery { peer: n });
    }
}

#[test]
fn the_wire_layout_is_the_documented_one() {
    let a = nid(1);
    let bytes = enc(&Frame::Send {
        dst: a,
        flag: 7,
        packet: &[0xaa, 0xbb],
    });
    assert_eq!(bytes[0], kind::SEND);
    assert_eq!(bytes[1], 1, "algorithm tag");
    assert_eq!(&bytes[2..34], &[1u8; 32]);
    assert_eq!(bytes[34], 7);
    assert_eq!(&bytes[35..], &[0xaa, 0xbb]);
    assert_eq!(enc(&Frame::Ping), [kind::PING]);
    assert_eq!(
        enc(&Frame::SendAlias {
            alias: 4,
            flag: 2,
            packet: &[1]
        }),
        [kind::SEND_ALIAS, 4, 2, 1]
    );
}

#[test]
fn strict_decoding_refuses_what_it_should() {
    let a = nid(1);
    // unknown and removed types
    assert_eq!(
        Frame::decode(&[]).unwrap_err(),
        FrameError::Wire(vinc_wire::WireError::Truncated { needed: 1 })
    );
    assert_eq!(Frame::decode(&[1]).unwrap_err(), FrameError::UnknownType(1));
    assert_eq!(Frame::decode(&[19]).unwrap_err(), FrameError::UnknownType(19));
    assert_eq!(Frame::decode(&[0xff]).unwrap_err(), FrameError::UnknownType(0xff));
    // trailing bytes after fixed-size frames
    assert_eq!(Frame::decode(&[kind::PING, 0]).unwrap_err(), FrameError::Trailing);
    assert_eq!(Frame::decode(&[kind::PONG, 0]).unwrap_err(), FrameError::Trailing);
    let mut q = enc(&Frame::DnsQuery { peer: a });
    q.push(0);
    assert_eq!(Frame::decode(&q).unwrap_err(), FrameError::Trailing);
    // empty and over-long packets
    let mut s = enc(&Frame::Send {
        dst: a,
        flag: 0,
        packet: &[1],
    });
    s.pop();
    assert_eq!(Frame::decode(&s).unwrap_err(), FrameError::PacketSize);
    let mut long = enc(&Frame::Send {
        dst: a,
        flag: 0,
        packet: &[1],
    });
    long.extend(vec![0u8; MAX_PACKET_LEN]);
    assert_eq!(Frame::decode(&long).unwrap_err(), FrameError::PacketSize);
    assert_eq!(Frame::decode(&[kind::SELF]).unwrap_err(), FrameError::PacketSize);
    // an alias of 32 or more
    assert_eq!(
        Frame::decode(&[kind::SEND_ALIAS, 32, 0, 1]).unwrap_err(),
        FrameError::Alias(32)
    );
    let mut sn = enc(&Frame::SendNew {
        dst: a,
        alias: 0,
        flag: 0,
        packet: &[1],
    });
    sn[34] = 200;
    assert_eq!(Frame::decode(&sn).unwrap_err(), FrameError::Alias(200));
    // an unknown identity tag
    let mut bad = enc(&Frame::DnsQuery { peer: a });
    bad[1] = 0;
    assert!(matches!(Frame::decode(&bad), Err(FrameError::Wire(_))));
    bad[1] = 5;
    assert!(matches!(Frame::decode(&bad), Err(FrameError::Wire(_))));
    // lookup answer statuses
    let mut r = enc(&Frame::DnsReply {
        peer: a,
        answer: DnsAnswer::Absent,
    });
    *r.last_mut().unwrap() = 3;
    assert_eq!(Frame::decode(&r).unwrap_err(), FrameError::Status(3));
    // a record frame with no record, or an over-long one
    assert_eq!(Frame::decode(&[kind::PUB]).unwrap_err(), FrameError::BodySize);
    let mut big = vec![kind::SYNC];
    big.extend(vec![0u8; MAX_RECORD_LEN + 1]);
    assert_eq!(Frame::decode(&big).unwrap_err(), FrameError::BodySize);
    let mut notice = vec![kind::SLEEP];
    notice.extend(vec![0u8; MAX_NOTICE_LEN + 1]);
    assert_eq!(Frame::decode(&notice).unwrap_err(), FrameError::BodySize);
}

#[test]
fn encode_refuses_what_decode_would() {
    let a = nid(1);
    let mut out = vec![0u8; 4096];
    assert_eq!(
        Frame::Send {
            dst: a,
            flag: 0,
            packet: &[]
        }
        .encode(&mut out)
        .unwrap_err(),
        FrameError::PacketSize
    );
    let big = vec![0u8; MAX_PACKET_LEN + 1];
    assert_eq!(
        Frame::Send {
            dst: a,
            flag: 0,
            packet: &big
        }
        .encode(&mut out)
        .unwrap_err(),
        FrameError::PacketSize
    );
    assert_eq!(
        Frame::SendAlias {
            alias: 32,
            flag: 0,
            packet: &[1]
        }
        .encode(&mut out)
        .unwrap_err(),
        FrameError::Alias(32)
    );
    assert!(matches!(Frame::Ping.encode(&mut []), Err(FrameError::Wire(_))));
    assert!(matches!(
        Frame::Send {
            dst: a,
            flag: 0,
            packet: &[1]
        }
        .encode(&mut out[..10]),
        Err(FrameError::Wire(_))
    ));
}

fn build_batch(frames: &[Frame<'_>]) -> (Vec<u8>, usize) {
    let mut buf = vec![0u8; MAX_FRAME_LEN + 64];
    let mut b = BatchBuilder::new(&mut buf);
    let mut added = 0;
    for f in frames {
        if b.offer(f).unwrap() == Offer::Added {
            added += 1;
        }
    }
    (b.finish().unwrap().unwrap().to_vec(), added)
}

#[test]
fn a_batch_round_trips_and_a_single_frame_is_not_wrapped() {
    let a = nid(1);
    let frames = [
        Frame::SendAlias {
            alias: 1,
            flag: 0,
            packet: &[0x41; 50],
        },
        Frame::Ping,
        Frame::Send {
            dst: a,
            flag: 1,
            packet: &[0x42; 700],
        },
    ];
    let (bytes, added) = build_batch(&frames);
    assert_eq!(added, 3);
    assert_eq!(bytes[0], kind::BATCH);
    assert_eq!(bytes[1], 3);
    let Frame::Batch(b) = Frame::decode(&bytes).unwrap() else {
        panic!("not a batch")
    };
    assert_eq!(b.len(), 3);
    assert_eq!(b.frames().collect::<Vec<_>>(), frames);
    round_trip(&Frame::decode(&bytes).unwrap());
    // one frame alone is the frame itself
    let (single, added) = build_batch(&frames[2..]);
    assert_eq!(added, 1);
    assert_eq!(single, enc(&frames[2]));
}

#[test]
fn a_batch_holds_at_most_64_frames_and_16_kib() {
    assert_eq!((BATCH_MAX_FRAMES, BATCH_MAX_BYTES), (64, 16 * 1024));
    let pings: Vec<Frame<'_>> = (0..70).map(|_| Frame::Ping).collect();
    let (bytes, added) = build_batch(&pings);
    assert_eq!(added, 64);
    let Frame::Batch(b) = Frame::decode(&bytes).unwrap() else {
        panic!()
    };
    assert_eq!(b.len(), 64);
    // the byte limit: 1452-byte packets in 1488-byte frames; the 12th would pass 16384 bytes
    let pkt = vec![0x41u8; MAX_PACKET_LEN];
    let big: Vec<Frame<'_>> = (0..14).map(|_| Frame::SelfSend { packet: &pkt }).collect();
    let (bytes, added) = build_batch(&big);
    assert_eq!(added, BATCH_MAX_BYTES / (1 + MAX_PACKET_LEN));
    let Frame::Batch(b) = Frame::decode(&bytes).unwrap() else {
        panic!()
    };
    assert_eq!(b.len(), added);
    // exactly 16384 bytes of frames is allowed, one byte more is not
    let exact: Vec<Vec<u8>> = vec![vec![0x41u8; 1023]; 16];
    let frames: Vec<Frame<'_>> = exact.iter().map(|p| Frame::SelfSend { packet: p }).collect();
    let (bytes, added) = build_batch(&frames);
    assert_eq!(added, 16);
    assert_eq!(bytes.len(), 2 + 16 * 2 + BATCH_MAX_BYTES);
    let mut buf = vec![0u8; MAX_FRAME_LEN + 64];
    let mut b = BatchBuilder::new(&mut buf);
    for f in &frames {
        assert_eq!(b.offer(f).unwrap(), Offer::Added);
    }
    assert_eq!(b.offer(&Frame::Ping).unwrap(), Offer::Refused);
}

#[test]
fn long_header_packets_are_never_batched() {
    let a = nid(1);
    let long = Frame::Send {
        dst: a,
        flag: 0,
        packet: &[0xc3, 1, 2],
    };
    let short = Frame::Send {
        dst: a,
        flag: 0,
        packet: &[0x43, 1, 2],
    };
    assert!(long.is_long_header() && !short.is_long_header());
    let mut buf = vec![0u8; MAX_FRAME_LEN + 64];
    // a long-header packet cannot start a batch
    let mut b = BatchBuilder::new(&mut buf);
    assert_eq!(b.offer(&long).unwrap(), Offer::Refused);
    assert!(b.is_empty());
    assert!(b.finish().unwrap().is_none());
    // nor join one
    let mut b = BatchBuilder::new(&mut buf);
    assert_eq!(b.offer(&short).unwrap(), Offer::Added);
    assert_eq!(b.offer(&long).unwrap(), Offer::Refused);
    assert_eq!(b.offer(&short).unwrap(), Offer::Added);
    assert_eq!(b.len(), 2);
    // a batch inside a batch is refused too
    let (inner, _) = build_batch(&[Frame::Ping, Frame::Pong]);
    let nested = Frame::decode(&inner).unwrap();
    assert_eq!(b.offer(&nested).unwrap(), Offer::Refused);
}

#[test]
fn malformed_batches_are_refused_whole() {
    let (good, _) = build_batch(&[Frame::Ping, Frame::Pong]);
    assert!(Frame::decode(&good).is_ok());
    // count of one, zero and 65
    let mut b = good.clone();
    b[1] = 1;
    assert!(matches!(Frame::decode(&b), Err(FrameError::Batch(_))));
    b[1] = 0;
    assert!(matches!(Frame::decode(&b), Err(FrameError::Batch(_))));
    b[1] = 65;
    assert!(matches!(Frame::decode(&b), Err(FrameError::Batch(_))));
    // a length that does not match the body
    let mut b = good.clone();
    b[2] = 2;
    assert!(matches!(Frame::decode(&b), Err(FrameError::Batch(_))));
    // a zero length
    let b = [kind::BATCH, 2, 0, 1, kind::PING];
    assert!(matches!(Frame::decode(&b), Err(FrameError::Batch(_))));
    // a bad frame inside
    let b = [kind::BATCH, 2, 1, 1, kind::PING, 0xee];
    assert!(Frame::decode(&b).is_err());
    // a nested batch
    let b = [kind::BATCH, 2, 4, 1, kind::BATCH, 2, 1, 1, kind::PING, kind::PING];
    let _ = b;
    let nested = [kind::BATCH, 2, 5, 1, kind::BATCH, 2, 1, 1];
    assert!(Frame::decode(&nested).is_err());
    // a non-minimal length varint
    let b = [kind::BATCH, 2, 0x81, 0x00, 1, kind::PING, kind::PING];
    assert!(Frame::decode(&b).is_err());
    // over 16 KiB of frames
    let mut over = vec![kind::BATCH, 2, 0x81, 0x80, 0x01, 1];
    over.push(kind::SELF);
    over.extend(vec![0x41u8; 16384 - 1]);
    over.push(kind::PING);
    assert!(Frame::decode(&over).is_err(), "16385 bytes of frames");
    // truncated
    for cut in 0..good.len() {
        assert!(Frame::decode(&good[..cut]).is_err(), "cut at {cut}");
    }
}

#[test]
fn aliases_follow_first_use_order_and_reset_after_32() {
    let mut tx = AliasTable::new();
    let mut rx = AliasTable::new();
    for i in 0..ALIAS_MAX as u8 {
        assert_eq!(tx.assign(&nid(i)), Assigned::New(i));
    }
    for i in 0..ALIAS_MAX as u8 {
        assert_eq!(tx.assign(&nid(i)), Assigned::Known(i));
    }
    // the 33rd node clears the table and takes alias 0 again
    assert_eq!(tx.assign(&nid(100)), Assigned::New(0));
    assert_eq!(tx.assign(&nid(100)), Assigned::Known(0));
    assert_eq!(tx.assign(&nid(0)), Assigned::New(1), "an earlier node starts again");
    // the frames: the first use carries the node, the next only the alias
    let first = tx.send_frame(&nid(77), 5, &[1, 2, 3]);
    assert!(matches!(first, Frame::SendNew { alias: 2, .. }));
    let second = tx.send_frame(&nid(77), 5, &[1, 2, 3]);
    assert_eq!(
        second,
        Frame::SendAlias {
            alias: 2,
            flag: 5,
            packet: &[1, 2, 3]
        }
    );
    if let Frame::SendNew { dst, alias, .. } = first {
        rx.learn(alias, dst);
    }
    assert_eq!(rx.resolve(2), Some(nid(77)));
    assert_eq!(rx.resolve(3), None);
    rx.learn(200, nid(1));
    assert_eq!(rx.resolve(200), None, "an out-of-range alias is ignored");
    let r1 = tx.recv_frame(&nid(9), 0, &[1]);
    assert!(matches!(r1, Frame::RecvNew { .. }));
}

proptest! {
    #[test]
    fn garbage_never_panics_and_valid_garbage_is_canonical(bytes in proptest::collection::vec(any::<u8>(), 0..300)) {
        if let Ok(f) = Frame::decode(&bytes) {
            prop_assert_eq!(enc(&f), bytes);
        }
    }

    #[test]
    fn garbage_behind_a_valid_type_never_panics(ty in 2u8..=18, rest in proptest::collection::vec(any::<u8>(), 0..400)) {
        let mut bytes = vec![ty];
        bytes.extend(rest);
        if let Ok(f) = Frame::decode(&bytes) {
            prop_assert_eq!(enc(&f), bytes);
        }
    }

    #[test]
    fn datagram_garbage_never_panics(bytes in proptest::collection::vec(any::<u8>(), 0..300)) {
        if let Ok(d) = Datagram::decode(&bytes) {
            prop_assert_eq!(connect_common::dg(&d), bytes);
        }
    }

    #[test]
    fn generated_frames_round_trip(
        tag in 0u8..4, dst in any::<[u8; 32]>(), alias in 0u8..32, flag in any::<u8>(),
        packet in proptest::collection::vec(any::<u8>(), 1..MAX_PACKET_LEN),
        which in 0usize..9,
    ) {
        let alg = [IdentityAlg::Ed25519, IdentityAlg::EcdsaP256, IdentityAlg::MlDsa65, IdentityAlg::Hybrid][usize::from(tag)];
        let n = NodeId { alg, bytes: dst };
        let f = match which {
            0 => Frame::Send { dst: n, flag, packet: &packet },
            1 => Frame::Recv { src: n, flag, packet: &packet },
            2 => Frame::SendNew { dst: n, alias, flag, packet: &packet },
            3 => Frame::SendAlias { alias, flag, packet: &packet },
            4 => Frame::RecvNew { src: n, alias, flag, packet: &packet },
            5 => Frame::RecvAlias { alias, flag, packet: &packet },
            6 => Frame::SelfSend { packet: &packet },
            7 => Frame::Forward { src: n, dst: nid(flag), flag, packet: &packet },
            _ => Frame::DnsReply { peer: n, answer: DnsAnswer::Record(&packet) },
        };
        let bytes = enc(&f);
        prop_assert_eq!(Frame::decode(&bytes).unwrap(), f);
    }

    #[test]
    fn generated_batches_round_trip(lens in proptest::collection::vec(1usize..600, 2..40), fill in any::<u8>()) {
        let pkts: Vec<Vec<u8>> = lens.iter().map(|n| vec![fill & 0x7f; *n]).collect();
        let frames: Vec<Frame<'_>> = pkts.iter().map(|p| Frame::SelfRecv { packet: p }).collect();
        let (bytes, added) = build_batch(&frames);
        match Frame::decode(&bytes).unwrap() {
            Frame::Batch(b) => prop_assert_eq!(b.frames().collect::<Vec<_>>(), frames[..added].to_vec()),
            f => prop_assert_eq!(f, frames[0]),
        }
    }
}

#[test]
fn datagrams_round_trip_and_are_strict() {
    const SPU_TYPE: u8 = 9;
    let a = nid(1);
    let addr: SocketAddr = "203.0.113.7:4433".parse().unwrap();
    let v6: SocketAddr = "[2001:db8::1]:443".parse().unwrap();
    let rec = [3u8; 200];
    let all = [
        Datagram::Qad { nonce: [1; 8] },
        Datagram::Qadr { nonce: [1; 8], addr },
        Datagram::Qadr {
            nonce: [2; 8],
            addr: v6,
        },
        Datagram::DnsQuery { peer: a },
        Datagram::DnsReply {
            peer: a,
            answer: DnsAnswer::Absent,
        },
        Datagram::DnsReply {
            peer: a,
            answer: DnsAnswer::Record(&rec),
        },
        Datagram::DnsReply {
            peer: a,
            answer: DnsAnswer::TooLarge,
        },
        Datagram::Sleep { notice: &rec },
        Datagram::Spl {
            src: a,
            flag: 1,
            packet: &[9; 100],
        },
        Datagram::Spu {
            dst: a,
            flag: 1,
            packet: &[9; 100],
        },
    ];
    for d in &all {
        let b = connect_common::dg(d);
        assert_eq!(&Datagram::decode(&b).unwrap(), d);
    }
    assert_eq!(connect_common::dg(&Datagram::Qad { nonce: [7; 8] })[0], 1);
    // the removed and unknown types
    for t in [0u8, 5, 7, 10, 255] {
        assert_eq!(Datagram::decode(&[t, 0, 0]).unwrap_err(), DatagramError::UnknownType(t));
    }
    // trailing bytes
    let mut q = connect_common::dg(&Datagram::Qad { nonce: [1; 8] });
    q.push(0);
    assert_eq!(Datagram::decode(&q).unwrap_err(), DatagramError::Trailing);
    // a tunnelled packet fits the datagram bound exactly
    let max = vec![0x41u8; MAX_TUNNEL_DATAGRAM - 35];
    let d = Datagram::Spu {
        dst: a,
        flag: 0,
        packet: &max,
    };
    assert_eq!(Datagram::decode(&connect_common::dg(&d)).unwrap(), d);
    // the bytes of an over-long or empty packet are refused by the decoder, and the encoder refuses to write them
    let over = vec![0x41u8; MAX_TUNNEL_DATAGRAM - 34];
    let mut buf = vec![0u8; 2048];
    let mut head = vec![SPU_TYPE];
    head.extend_from_slice(&connect_common::node_bytes(&a));
    head.push(0);
    head.extend_from_slice(&over);
    assert_eq!(Datagram::decode(&head).unwrap_err(), DatagramError::PacketSize);
    assert_eq!(
        Datagram::Spu {
            dst: a,
            flag: 0,
            packet: &over
        }
        .encode(&mut buf),
        Err(DatagramError::PacketSize)
    );
    assert_eq!(
        Datagram::Spl {
            src: a,
            flag: 0,
            packet: &[]
        }
        .encode(&mut buf),
        Err(DatagramError::PacketSize)
    );
}

/// `Datagram::encode` refuses every field the decoder refuses: a tunnelled packet that is empty or does not fit the
/// datagram, a record or a notice that is empty or too long. (It once wrote them, and the datagram then failed to
/// decode at the receiver.)
#[test]
fn datagram_encode_refuses_what_decode_refuses() {
    let a = nid(1);
    let mut buf = vec![0u8; 4 * 1024];
    let too_long_packet = vec![1u8; MAX_TUNNEL_DATAGRAM - 34];
    let fits = vec![1u8; MAX_TUNNEL_DATAGRAM - 35];
    let long_record = vec![1u8; MAX_RECORD_LEN + 1];
    let long_notice = vec![1u8; MAX_NOTICE_LEN + 1];
    let refused = [
        (
            Datagram::Spl {
                src: a,
                flag: 0,
                packet: &[],
            },
            DatagramError::PacketSize,
        ),
        (
            Datagram::Spu {
                dst: a,
                flag: 0,
                packet: &too_long_packet,
            },
            DatagramError::PacketSize,
        ),
        (
            Datagram::Sleep { notice: &[] },
            DatagramError::Frame(FrameError::BodySize),
        ),
        (
            Datagram::Sleep { notice: &long_notice },
            DatagramError::Frame(FrameError::BodySize),
        ),
        (
            Datagram::DnsReply {
                peer: a,
                answer: DnsAnswer::Record(&[]),
            },
            DatagramError::Frame(FrameError::BodySize),
        ),
        (
            Datagram::DnsReply {
                peer: a,
                answer: DnsAnswer::Record(&long_record),
            },
            DatagramError::Frame(FrameError::BodySize),
        ),
    ];
    let mut big = vec![0u8; 16 * 1024];
    for (d, e) in &refused {
        assert_eq!(d.encode(&mut big), Err(*e), "{d:?}");
        assert_eq!(d.encode(&mut buf), Err(*e), "{d:?}");
    }
    // and what fits is written and decodes back
    let ok = Datagram::Spl {
        src: a,
        flag: 3,
        packet: &fits,
    };
    let n = ok.encode(&mut buf).unwrap();
    assert_eq!(Datagram::decode(&buf[..n]).unwrap(), ok);
}

fn fields<'a>(addrs: &'a [SocketAddr], hints: &'a [u8]) -> RecordFields<'a> {
    RecordFields {
        home: nid(0x77),
        seq: 42,
        reach: Reach::Nat,
        addrs,
        hints,
    }
}

#[test]
fn a_signed_record_round_trips_and_verifies_for_every_algorithm() {
    big_stack(|| {
        let addrs: Vec<SocketAddr> = vec![
            "203.0.113.7:4433".parse().unwrap(),
            "[2001:db8::1]:443".parse().unwrap(),
        ];
        for alg in [
            IdentityAlg::Ed25519,
            IdentityAlg::EcdsaP256,
            IdentityAlg::MlDsa65,
            IdentityAlg::Hybrid,
        ] {
            let kp = keypair(alg, 5);
            let mut buf = vec![0u8; MAX_RECORD_LEN];
            let n = sign(&kp, &fields(&addrs, b"ticket"), &mut buf).unwrap();
            assert!(n <= MAX_RECORD_LEN);
            let rec = Record::parse_verified(&buf[..n]).unwrap();
            assert_eq!(rec.node, id(&kp));
            assert_eq!(
                (rec.home, rec.seq, rec.reach, rec.hints),
                (nid(0x77), 42, Reach::Nat, &b"ticket"[..])
            );
            assert_eq!(rec.addrs().collect::<Vec<_>>(), addrs);
        }
        // the largest record fits MAX_RECORD_LEN
        let kp = keypair(IdentityAlg::Hybrid, 6);
        let eight: Vec<SocketAddr> = (0..MAX_ADDRS)
            .map(|i| format!("[2001:db8::{i}]:443").parse().unwrap())
            .collect();
        let mut buf = vec![0u8; MAX_RECORD_LEN];
        let n = sign(&kp, &fields(&eight, &[7; MAX_HINT_LEN]), &mut buf).unwrap();
        assert_eq!(n, MAX_RECORD_LEN);
        Record::parse_verified(&buf[..n]).unwrap();
    });
}

#[test]
fn a_record_that_was_altered_or_forged_does_not_verify() {
    big_stack(|| {
        let kp = ed(5);
        let addrs: Vec<SocketAddr> = vec!["203.0.113.7:4433".parse().unwrap()];
        let mut buf = vec![0u8; MAX_RECORD_LEN];
        let n = sign(&kp, &fields(&addrs, b"h"), &mut buf).unwrap();
        let good = buf[..n].to_vec();
        // every single-bit flip is refused by parse or verify
        for i in 0..good.len() {
            for bit in [0x01u8, 0x80] {
                let mut bad = good.clone();
                bad[i] ^= bit;
                let ok = Record::parse_verified(&bad).is_ok();
                assert!(!ok, "flip at byte {i} bit {bit:#x} was accepted");
            }
        }
        // a record signed by another key but claiming this node id
        let other = ed(6);
        let mut forged = vec![0u8; MAX_RECORD_LEN];
        let m = sign(&other, &fields(&addrs, b"h"), &mut forged).unwrap();
        forged[8..8 + 33].copy_from_slice(&connect_common::node_bytes(&id(&kp)));
        assert!(matches!(
            Record::parse_verified(&forged[..m]),
            Err(RecordError::Signature(_))
        ));
        // trailing bytes, truncation, wrong magic
        let mut extra = good.clone();
        extra.push(0);
        assert!(matches!(
            Record::parse(&extra),
            Err(RecordError::Trailing | RecordError::Wire(_))
        ));
        for cut in 0..good.len() {
            assert!(Record::parse_verified(&good[..cut]).is_err());
        }
        // too many addresses and hints are refused when signing
        let nine: Vec<SocketAddr> = vec!["1.2.3.4:5".parse().unwrap(); MAX_ADDRS + 1];
        assert_eq!(
            sign(&kp, &fields(&nine, b""), &mut buf).unwrap_err(),
            RecordError::TooManyAddrs
        );
        assert_eq!(
            sign(&kp, &fields(&[], &[0; MAX_HINT_LEN + 1]), &mut buf).unwrap_err(),
            RecordError::HintsTooLong
        );
        assert!(sign(&kp, &fields(&addrs, b""), &mut buf[..50]).is_err());
    });
}

proptest! {
    #[test]
    fn record_garbage_never_panics(bytes in proptest::collection::vec(any::<u8>(), 0..400)) {
        let _ = Record::parse_verified(&bytes);
        let _ = Notice::parse(&bytes);
    }
}

#[test]
fn a_sleep_notice_is_signed_for_one_relay_and_one_sender() {
    let kp = ed(9);
    let relay = nid(0x50);
    let mut buf = vec![0u8; sleep::MAX_LEN];
    let n = sleep::sign(&kp, &relay, 123_456, &mut buf).unwrap();
    let notice = Notice::parse(&buf[..n]).unwrap();
    assert_eq!((notice.node, notice.ts_ms), (id(&kp), 123_456));
    notice.verify(&relay).unwrap();
    assert!(
        matches!(notice.verify(&nid(0x51)), Err(SleepError::Signature(_))),
        "another relay"
    );
    for i in 0..n {
        let mut bad = buf[..n].to_vec();
        bad[i] ^= 1;
        let ok = Notice::parse(&bad).is_ok_and(|x| x.verify(&relay).is_ok());
        assert!(!ok, "flip at {i}");
    }
}

#[test]
fn a_record_notice_and_beacon_signed_in_two_steps_equal_the_one_step_form_and_refuse_a_short_buffer() {
    use vinc_connect::local;
    let kp = ed(0x44);
    let me = id(&kp);
    let mut pk = [0u8; 2000];
    let n = kp.public_key(&mut pk).unwrap();
    let pk = &pk[..n];
    let addrs: [SocketAddr; 2] = ["192.0.2.1:4000".parse().unwrap(), "[2001:db8::1]:4000".parse().unwrap()];
    // Record.
    let fields = RecordFields {
        home: nid(9),
        seq: 77,
        reach: Reach::Nat,
        addrs: &addrs,
        hints: b"h",
    };
    let mut one = vec![0u8; MAX_RECORD_LEN];
    let one_len = sign(&kp, &fields, &mut one).unwrap();
    let mut two = vec![0u8; MAX_RECORD_LEN];
    let signed = vinc_connect::record::prepare(&me, pk, &fields, &mut two).unwrap();
    let mut sig = [0u8; 200];
    let s = kp.sign(&two[..signed], &mut sig).unwrap();
    let two_len = vinc_connect::record::finish(&mut two, signed, &sig[..s]).unwrap();
    assert_eq!(one[..one_len], two[..two_len]);
    assert!(Record::parse_verified(&two[..two_len]).is_ok());
    assert!(vinc_connect::record::prepare(&me, pk, &fields, &mut [0u8; 20]).is_err());
    assert!(vinc_connect::record::finish(&mut two[..signed + 3], signed, &sig[..s]).is_err());
    // Sleep notice.
    let relay = nid(5);
    let mut one = vec![0u8; sleep::MAX_LEN];
    let one_len = sleep::sign(&kp, &relay, 1234, &mut one).unwrap();
    let mut two = vec![0u8; sleep::MAX_LEN];
    let head = sleep::prepare(&me, pk, 1234, &mut two).unwrap();
    let msg = sleep::message(&relay, &me, 1234).unwrap();
    let s = kp.sign(&msg, &mut sig).unwrap();
    let two_len = sleep::finish(&mut two, head, &sig[..s]).unwrap();
    assert_eq!(one[..one_len], two[..two_len]);
    Notice::parse(&two[..two_len]).unwrap().verify(&relay).unwrap();
    // Beacon.
    let mut one = vec![0u8; local::MAX_LEN];
    let one_len = local::sign(&kp, 9, &addrs, b"x", &mut one).unwrap();
    let mut two = vec![0u8; local::MAX_LEN];
    let signed = local::prepare(&me, pk, 9, &addrs, b"x", &mut two).unwrap();
    let s = kp.sign(&two[..signed], &mut sig).unwrap();
    let two_len = local::finish(&mut two, signed, &sig[..s]).unwrap();
    assert_eq!(one[..one_len], two[..two_len]);
    local::Beacon::parse_verified(&two[..two_len]).unwrap();
}

#[test]
fn a_batch_resumes_from_its_state_and_keeps_its_limits() {
    use vinc_connect::carrier::BatchState;
    let mut buf = vec![0u8; MAX_FRAME_LEN + 64];
    let pkt = [0x41u8; 100];
    let f = Frame::Send {
        dst: nid(3),
        flag: 0,
        packet: &pkt,
    };
    let mut st = BatchState::new();
    for i in 0..BATCH_MAX_FRAMES {
        let mut b = BatchBuilder::resume(&mut buf, st);
        assert_eq!(b.offer(&f).unwrap(), Offer::Added, "frame {i}");
        st = b.state();
    }
    assert_eq!(st.len(), BATCH_MAX_FRAMES);
    assert_eq!(
        BatchBuilder::resume(&mut buf, st).offer(&f).unwrap(),
        Offer::Refused,
        "the 65th frame"
    );
    let sealed = BatchBuilder::resume(&mut buf, st).finish().unwrap().unwrap().to_vec();
    let Frame::Batch(b) = Frame::decode(&sealed).unwrap() else {
        panic!("not a batch")
    };
    assert_eq!(b.frames().count(), BATCH_MAX_FRAMES);
    assert!(sealed.len() <= MAX_FRAME_LEN);
    assert!(!st.is_empty());
}
