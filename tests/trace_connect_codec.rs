//! Trace generation for the wire formats of `vinc-connect`: the carrier frame, the relay datagram, the signed record,
//! the beacon, the sleep notice, the ticket (binary and text) and the candidate list of a REACH_OUT, recorded as ndjson
//! (`connect_codec.ndjson`) for the TLA+ trace check (`TraceConnectCodec.tla`) and the Lean replay
//! (`Vinc/TraceConnectCodec.lean`).
//!
//! Every event is one call of the real code on bytes: valid values of every kind and boundary, every proper cut of
//! them, trailing bytes, single bytes changed, encodings into buffers of every nearby size, and seeded random garbage
//! with a valid type byte. What is recorded is the input bytes and the result: the decoded fields as byte sequences
//! (a node is its 33 bytes, a flag one byte, a batch its member frames) or the refusal as the tag of its error. The
//! test also asserts what the decoders must satisfy on their own: a decoded value re-encodes to its input.
//! The trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::type_complexity,
    unreachable_pub
)]

mod connect_codec_out;
mod connect_common;

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use connect_codec_out::{Out, enc};
use connect_common::{keypair, nid, node_bytes};
use vinc_connect::carrier::frame::{
    BATCH_MAX_BYTES, BATCH_MAX_FRAMES, DnsAnswer, Frame, MAX_FRAME_LEN, MAX_NOTICE_LEN, MAX_PACKET_LEN,
};
use vinc_connect::client::punch;
use vinc_connect::local;
use vinc_connect::record::{self, MAX_RECORD_LEN, Reach, Record, RecordFields};
use vinc_connect::relay::datagram::{Datagram, MAX_TUNNEL_DATAGRAM};
use vinc_connect::relay::sleep;
use vinc_connect::ticket::{Ticket, TicketError};
use vinc_crypto::{IdentityAlg, NodeId};
use vinc_tests::SplitMix64;

fn a4(i: u8, port: u16) -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, i, 1)), port)
}

fn a6(i: u8, port: u16) -> SocketAddr {
    SocketAddr::new(
        IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, u16::from(i), 1)),
        port,
    )
}

/// The positions to change in `len` bytes: all of them when there are at most `k`, otherwise the first ones (the
/// header), the last ones and random ones.
fn positions(len: usize, k: usize, rng: &mut SplitMix64) -> Vec<usize> {
    if len <= k {
        return (0..len).collect();
    }
    let mut v: Vec<usize> = (0..(k / 2).min(8)).chain(len - (k / 4).max(1)..len).collect();
    while v.len() < k {
        let p = (rng.next_u64() % len as u64) as usize;
        if !v.contains(&p) {
            v.push(p);
        }
    }
    v
}

/// Single-byte changes at up to `k` positions, proper cuts (all of them for short inputs, a sample otherwise) and one
/// byte appended: the neighbours of a valid encoding.
fn around(b: &[u8], vals: &[u8], rng: &mut SplitMix64, k: usize) -> Vec<Vec<u8>> {
    let mut v = Vec::new();
    for i in positions(b.len(), k, rng) {
        for &x in vals {
            if b[i] != x {
                let mut m = b.to_vec();
                m[i] = x;
                v.push(m);
            }
        }
    }
    for c in positions(b.len(), k, rng) {
        v.push(b[..c].to_vec());
    }
    for x in [0u8, 7, 255] {
        let mut m = b.to_vec();
        m.push(x);
        v.push(m);
    }
    v
}

const VALS: [u8; 5] = [0, 2, 13, 32, 255];

fn nodes() -> Vec<NodeId> {
    vec![
        nid(1),
        nid(2),
        NodeId {
            alg: IdentityAlg::EcdsaP256,
            bytes: [3; 32],
        },
        NodeId {
            alg: IdentityAlg::MlDsa65,
            bytes: [4; 32],
        },
        NodeId {
            alg: IdentityAlg::Hybrid,
            bytes: [5; 32],
        },
    ]
}

fn gen_frames(o: &mut Out, rng: &mut SplitMix64) {
    let ns = nodes();
    let pkts: Vec<Vec<u8>> = vec![
        vec![3],
        vec![1, 2],
        vec![0x80, 9, 9],
        (0..MAX_PACKET_LEN).map(|i| i as u8).collect(),
    ];
    let rec = vec![9u8; 60];
    let mut frames: Vec<Vec<u8>> = Vec::new();
    for p in &pkts {
        for (i, n) in ns.iter().enumerate() {
            let f = (i as u8).wrapping_mul(61);
            frames.push(enc(&Frame::Send {
                dst: *n,
                flag: f,
                packet: p,
            }));
            frames.push(enc(&Frame::Recv {
                src: *n,
                flag: f,
                packet: p,
            }));
            frames.push(enc(&Frame::Forward {
                src: *n,
                dst: ns[(i + 1) % 5],
                flag: f,
                packet: p,
            }));
        }
        for a in [0u8, 1, 31] {
            frames.push(enc(&Frame::SendNew {
                dst: ns[0],
                alias: a,
                flag: 255,
                packet: p,
            }));
            frames.push(enc(&Frame::RecvNew {
                src: ns[3],
                alias: a,
                flag: 0,
                packet: p,
            }));
            frames.push(enc(&Frame::SendAlias {
                alias: a,
                flag: 7,
                packet: p,
            }));
            frames.push(enc(&Frame::RecvAlias {
                alias: a,
                flag: 8,
                packet: p,
            }));
        }
        frames.push(enc(&Frame::SelfSend { packet: p }));
        frames.push(enc(&Frame::SelfRecv { packet: p }));
    }
    frames.push(enc(&Frame::Ping));
    frames.push(enc(&Frame::Pong));
    for n in &ns {
        frames.push(enc(&Frame::DnsQuery { peer: *n }));
        frames.push(enc(&Frame::DnsReply {
            peer: *n,
            answer: DnsAnswer::Absent,
        }));
        frames.push(enc(&Frame::DnsReply {
            peer: *n,
            answer: DnsAnswer::TooLarge,
        }));
        frames.push(enc(&Frame::DnsReply {
            peer: *n,
            answer: DnsAnswer::Record(&rec),
        }));
    }
    for body in [vec![1u8], rec.clone(), vec![6u8; MAX_RECORD_LEN]] {
        frames.push(enc(&Frame::Publish { record: &body }));
        frames.push(enc(&Frame::Sync { record: &body }));
        frames.push(enc(&Frame::DnsReply {
            peer: ns[1],
            answer: DnsAnswer::Record(&body),
        }));
    }
    for body in [vec![1u8], vec![6u8; MAX_NOTICE_LEN]] {
        frames.push(enc(&Frame::Sleep { notice: &body }));
    }
    // batches: pairs of members, a full count of 64, and the byte limit exactly
    let members: Vec<Vec<u8>> = vec![
        enc(&Frame::Ping),
        enc(&Frame::Pong),
        enc(&Frame::SelfSend { packet: &[7, 3] }),
        enc(&Frame::Send {
            dst: ns[0],
            flag: 0,
            packet: &[3],
        }),
        enc(&Frame::DnsQuery { peer: ns[2] }),
        enc(&Frame::SendAlias {
            alias: 1,
            flag: 2,
            packet: &[9],
        }),
    ];
    let build = |ms: &[&[u8]]| -> Vec<u8> {
        let mut buf = vec![0u8; MAX_FRAME_LEN + 64];
        let mut bb = vinc_connect::carrier::BatchBuilder::new(&mut buf);
        for m in ms {
            let f = Frame::decode(m).unwrap();
            assert_eq!(bb.offer(&f).unwrap(), vinc_connect::carrier::Offer::Added);
        }
        bb.finish().unwrap().unwrap().to_vec()
    };
    for a in &members {
        for b in &members {
            frames.push(build(&[a, b]));
        }
    }
    frames.push(build(&[&members[0], &members[3], &members[1]]));
    frames.push(build(&vec![members[0].as_slice(); BATCH_MAX_FRAMES]));
    let big = enc(&Frame::SelfSend {
        packet: &vec![5u8; MAX_PACKET_LEN],
    });
    let tail = enc(&Frame::SelfSend {
        packet: &vec![1u8; BATCH_MAX_BYTES - 11 * big.len() - 1],
    });
    let mut ms: Vec<&[u8]> = vec![big.as_slice(); 11];
    ms.push(&tail);
    frames.push(build(&ms));
    for (n, f) in frames.iter().enumerate() {
        o.fdec(f);
        if f.len() <= 100 && n % 3 == 0 {
            for m in around(f, &VALS, rng, 80) {
                o.fdec(&m);
            }
            for cap in (0..=f.len() + 1).filter(|c| *c < 40 || *c + 4 >= f.len()) {
                o.fenc(&Frame::decode(f).unwrap(), cap);
            }
        } else {
            for m in around(f, &VALS, rng, 3) {
                o.fdec(&m);
            }
            let d = Frame::decode(f).unwrap();
            for cap in [0, 1, 2, 34, 35, f.len() - 1, f.len(), f.len() + 1] {
                o.fenc(&d, cap);
            }
        }
    }
    // frames the decoder refuses, built by hand: bad fields for the encoder, and byte patterns for the decoder
    for a in [32u8, 33, 255] {
        o.fenc(
            &Frame::SendAlias {
                alias: a,
                flag: 0,
                packet: &[1],
            },
            64,
        );
        o.fenc(
            &Frame::RecvNew {
                src: ns[0],
                alias: a,
                flag: 0,
                packet: &[1],
            },
            64,
        );
        o.fenc(
            &Frame::SendNew {
                dst: ns[0],
                alias: a,
                flag: 0,
                packet: &[1],
            },
            5,
        );
    }
    for cap in [0usize, 1, 34, 35, 36, 2000] {
        o.fenc(
            &Frame::Send {
                dst: ns[0],
                flag: 0,
                packet: &[],
            },
            cap,
        );
        o.fenc(&Frame::SelfSend { packet: &[] }, cap);
        o.fenc(
            &Frame::Send {
                dst: ns[0],
                flag: 0,
                packet: &vec![1; MAX_PACKET_LEN + 1],
            },
            cap + 2000,
        );
        o.fenc(&Frame::Publish { record: &[] }, cap);
        o.fenc(
            &Frame::Publish {
                record: &vec![1; MAX_RECORD_LEN + 1],
            },
            cap + 6000,
        );
        o.fenc(&Frame::Sleep { notice: &[] }, cap);
        o.fenc(
            &Frame::Sleep {
                notice: &vec![1; MAX_NOTICE_LEN + 1],
            },
            cap + 9000,
        );
        o.fenc(
            &Frame::DnsReply {
                peer: ns[0],
                answer: DnsAnswer::Record(&[]),
            },
            cap + 40,
        );
    }
    for t in 0u8..=255 {
        o.fdec(&[t]);
        o.fdec(&[t, 1, 2, 3]);
        o.fdec(&[t, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    }
    // random garbage behind a valid type byte
    for _ in 0..1500 {
        let ty = [2u8, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18][(rng.next_u64() % 15) as usize];
        let len = (rng.next_u64() % 120) as usize;
        let mut b = vec![ty];
        for k in 0..len {
            let r = rng.next_u64();
            // bias toward small values (valid tags, aliases, statuses) and the batch count range
            b.push(if k < 40 && r % 3 == 0 {
                (r >> 8) as u8 % 6
            } else {
                (r >> 16) as u8
            });
        }
        o.fdec(&b);
    }
}

fn gen_dgrams(o: &mut Out, rng: &mut SplitMix64) {
    let ns = nodes();
    let rec = vec![9u8; 60];
    let mut ds: Vec<Vec<u8>> = Vec::new();
    let mut put = |d: Datagram<'_>| {
        let mut b = vec![0u8; 10_000];
        let n = d.encode(&mut b).unwrap();
        ds.push(b[..n].to_vec());
    };
    put(Datagram::Qad {
        nonce: [1, 2, 3, 4, 5, 6, 7, 8],
    });
    put(Datagram::Qadr {
        nonce: [0; 8],
        addr: a4(1, 443),
    });
    put(Datagram::Qadr {
        nonce: [255; 8],
        addr: a6(9, 65535),
    });
    for n in &ns {
        put(Datagram::DnsQuery { peer: *n });
        put(Datagram::DnsReply {
            peer: *n,
            answer: DnsAnswer::Absent,
        });
        put(Datagram::DnsReply {
            peer: *n,
            answer: DnsAnswer::TooLarge,
        });
        put(Datagram::DnsReply {
            peer: *n,
            answer: DnsAnswer::Record(&rec),
        });
    }
    put(Datagram::DnsReply {
        peer: ns[0],
        answer: DnsAnswer::Record(&[1]),
    });
    put(Datagram::DnsReply {
        peer: ns[0],
        answer: DnsAnswer::Record(&vec![6u8; MAX_RECORD_LEN]),
    });
    put(Datagram::Sleep { notice: &[1] });
    put(Datagram::Sleep {
        notice: &vec![6u8; MAX_NOTICE_LEN],
    });
    for p in [vec![3u8], vec![1, 2], vec![8u8; MAX_TUNNEL_DATAGRAM - 35]] {
        for (i, n) in ns.iter().enumerate() {
            put(Datagram::Spl {
                src: *n,
                flag: i as u8,
                packet: &p,
            });
            put(Datagram::Spu {
                dst: *n,
                flag: 255,
                packet: &p,
            });
        }
    }
    for (n, d) in ds.iter().enumerate() {
        o.ddec(d);
        if d.len() <= 100 && n % 2 == 0 {
            for m in around(d, &VALS, rng, 80) {
                o.ddec(&m);
            }
            for cap in (0..=d.len() + 1).filter(|c| *c < 40 || *c + 4 >= d.len()) {
                o.denc(&Datagram::decode(d).unwrap(), cap);
            }
        } else {
            for m in around(d, &VALS, rng, 3) {
                o.ddec(&m);
            }
            let x = Datagram::decode(d).unwrap();
            for cap in [0, 1, 34, 35, d.len() - 1, d.len(), d.len() + 1] {
                o.denc(&x, cap);
            }
        }
    }
    // a datagram the encoder must refuse because the decoder would: empty and oversized fields
    for cap in [2usize, 40, 2000] {
        o.denc(
            &Datagram::Spl {
                src: ns[0],
                flag: 0,
                packet: &[],
            },
            cap,
        );
        o.denc(
            &Datagram::Spu {
                dst: ns[0],
                flag: 0,
                packet: &vec![1; MAX_TUNNEL_DATAGRAM - 34],
            },
            cap + 2000,
        );
        o.denc(
            &Datagram::Spu {
                dst: ns[0],
                flag: 0,
                packet: &vec![1; MAX_TUNNEL_DATAGRAM],
            },
            cap + 2000,
        );
        o.denc(&Datagram::Sleep { notice: &[] }, cap);
        o.denc(
            &Datagram::Sleep {
                notice: &vec![1; MAX_NOTICE_LEN + 1],
            },
            cap + 9000,
        );
        o.denc(
            &Datagram::DnsReply {
                peer: ns[0],
                answer: DnsAnswer::Record(&[]),
            },
            cap + 40,
        );
        o.denc(
            &Datagram::DnsReply {
                peer: ns[0],
                answer: DnsAnswer::Record(&vec![1; MAX_RECORD_LEN + 1]),
            },
            cap + 6000,
        );
    }
    for t in 0u8..=255 {
        o.ddec(&[t]);
        o.ddec(&[t, 1, 2, 3]);
        o.ddec(&[t, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    }
    for _ in 0..800 {
        let ty = [1u8, 2, 3, 4, 6, 8, 9][(rng.next_u64() % 7) as usize];
        let len = (rng.next_u64() % 80) as usize;
        let mut b = vec![ty];
        for k in 0..len {
            let r = rng.next_u64();
            b.push(if k < 40 && r % 3 == 0 {
                (r >> 8) as u8 % 6
            } else {
                (r >> 16) as u8
            });
        }
        o.ddec(&b);
    }
}

/// A key pair with the algorithm's real public key, to sign real records.
fn key(alg: IdentityAlg, tag: u8) -> (vinc_crypto::Keypair, NodeId, Vec<u8>) {
    let kp = keypair(alg, tag);
    let node = kp.node_id();
    let mut pk = vec![0u8; vinc_crypto::identity::MAX_PUBLIC_KEY_LEN];
    let n = kp.public_key(&mut pk).unwrap();
    pk.truncate(n);
    (kp, node, pk)
}

fn gen_signed(o: &mut Out, rng: &mut SplitMix64) {
    let algs = [
        (IdentityAlg::Ed25519, 11u8, 30usize),
        (IdentityAlg::EcdsaP256, 12, 20),
        (IdentityAlg::MlDsa65, 13, 3),
        (IdentityAlg::Hybrid, 14, 3),
    ];
    let home = nid(9);
    for (alg, tag, every) in algs {
        let (kp, node, pk) = key(alg, tag);
        let shapes: Vec<(Vec<SocketAddr>, Vec<u8>, Reach, u64)> = vec![
            (vec![], vec![], Reach::Public, 0),
            (vec![a4(1, 1)], vec![7], Reach::PortMapped, 1),
            (vec![a4(2, 5), a6(3, 65535)], vec![3; 64], Reach::Nat, u64::MAX),
            (
                (0..8).map(|i| a6(i, 1000 + u16::from(i))).collect(),
                vec![],
                Reach::Cgnat,
                1 << 63,
            ),
            (vec![a6(1, 2)], vec![1, 2], Reach::UdpBlocked, 258),
        ];
        for (addrs, hints, reach, seq) in &shapes {
            let f = RecordFields {
                home,
                seq: *seq,
                reach: *reach,
                addrs,
                hints,
            };
            let mut out = vec![0u8; MAX_RECORD_LEN];
            let n = record::sign(&kp, &f, &mut out).unwrap();
            let b = &out[..n];
            assert!(Record::parse_verified(b).is_ok());
            o.rdec(b);
            for m in around(b, &VALS, rng, every) {
                o.rdec(&m);
            }
            let head = {
                let mut h = vec![0u8; MAX_RECORD_LEN];
                let hn = record::prepare(&node, &pk, &f, &mut h).unwrap();
                hn
            };
            o.rprep(&node, &pk, &f, head);
            for cap in [0usize, 1, 8, 9, 41, 74, 82, 83, 84, head - 1, head + 1] {
                o.rprep(&node, &pk, &f, cap);
            }
        }
        // too many addresses and hint bytes, with room and without
        let many: Vec<SocketAddr> = (0..9).map(|i| a4(i, 1)).collect();
        for cap in [0usize, 100, MAX_RECORD_LEN] {
            o.rprep(
                &node,
                &pk,
                &RecordFields {
                    home,
                    seq: 1,
                    reach: Reach::Nat,
                    addrs: &many,
                    hints: &[],
                },
                cap,
            );
            o.rprep(
                &node,
                &pk,
                &RecordFields {
                    home,
                    seq: 1,
                    reach: Reach::Nat,
                    addrs: &[],
                    hints: &[1; 65],
                },
                cap,
            );
        }
        // a beacon and a notice of the same key
        for (addrs, hint) in [
            (vec![], vec![]),
            (vec![a4(1, 4435)], vec![1]),
            (vec![a4(2, 1), a6(3, 2), a4(4, 3), a6(5, 4)], vec![9; 8]),
        ] {
            let mut out = vec![0u8; local::MAX_LEN];
            let n = local::sign(&kp, 77, &addrs, &hint, &mut out).unwrap();
            let b = &out[..n];
            o.bdec(b);
            for m in around(b, &VALS, rng, every) {
                o.bdec(&m);
            }
            let mut h = vec![0u8; local::MAX_LEN];
            let hn = local::prepare(&node, &pk, 77, &addrs, &hint, &mut h).unwrap();
            o.bprep(&node, &pk, 77, &addrs, &hint, hn);
            for cap in [0usize, 1, 8, 9, 41, 49, 50, hn - 1] {
                o.bprep(&node, &pk, 77, &addrs, &hint, cap);
            }
        }
        let many: Vec<SocketAddr> = (0..5).map(|i| a4(i, 1)).collect();
        for cap in [0usize, 200, local::MAX_LEN] {
            o.bprep(&node, &pk, 1, &many, &[], cap);
            o.bprep(&node, &pk, 1, &[], &[1; 9], cap);
        }
        for ts in [0u64, 1, 10_000, u64::MAX]
            .into_iter()
            .take(if every < 5 { 2 } else { 4 })
        {
            let mut out = vec![0u8; sleep::MAX_LEN];
            let n = sleep::sign(&kp, &home, ts, &mut out).unwrap();
            let b = &out[..n];
            o.sdec(b);
            for m in around(b, &VALS, rng, every) {
                o.sdec(&m);
            }
            let mut h = vec![0u8; sleep::MAX_LEN];
            let hn = sleep::prepare(&node, &pk, ts, &mut h).unwrap();
            o.sprep(&node, &pk, ts, hn);
            for cap in [0usize, 1, 33, 34, 40, 41, hn - 1] {
                o.sprep(&node, &pk, ts, cap);
            }
            o.smsg(&home, &node, ts);
            o.smsg(&nid(8), &node, ts);
        }
    }
    // random garbage with a valid magic
    for _ in 0..600 {
        let len = (rng.next_u64() % 160) as usize;
        let mut b = Vec::new();
        b.extend_from_slice(match rng.next_u64() % 3 {
            0 => b"VNCREC\x00\x01",
            1 => b"VNCBCN\x00\x01",
            _ => b"\x00\x00\x00\x00\x00\x00\x00\x00",
        });
        let node = nid(1);
        b.extend_from_slice(&node_bytes(&node));
        for k in 0..len {
            let r = rng.next_u64();
            b.push(if k < 60 && r % 3 == 0 {
                (r >> 8) as u8 % 6
            } else {
                (r >> 16) as u8
            });
        }
        o.rdec(&b);
        o.bdec(&b);
        o.sdec(&b[8..]);
    }
}

fn gen_tickets(o: &mut Out, rng: &mut SplitMix64) {
    let ns = nodes();
    let mut tickets = Vec::new();
    for (i, n) in ns.iter().enumerate() {
        tickets.push(Ticket::new(*n));
        tickets.push(Ticket::new(*n).with_home(ns[(i + 1) % 5]));
        tickets.push(Ticket::new(*n).with_addr(a4(1, 1)).unwrap());
        tickets.push(
            Ticket::new(*n)
                .with_home(ns[(i + 2) % 5])
                .with_addr(a6(2, 2))
                .unwrap()
                .with_addr(a4(3, 3))
                .unwrap()
                .with_addr(a4(4, 65535))
                .unwrap()
                .with_addr(a6(5, 0))
                .unwrap(),
        );
    }
    assert_eq!(
        Ticket::new(ns[0])
            .with_addr(a4(1, 1))
            .unwrap()
            .with_addr(a4(2, 1))
            .unwrap()
            .with_addr(a4(3, 1))
            .unwrap()
            .with_addr(a4(4, 1))
            .unwrap()
            .with_addr(a4(5, 1)),
        Err(TicketError::TooManyAddrs)
    );
    for t in &tickets {
        let mut bin = [0u8; 200];
        let n = t.encode(&mut bin).unwrap();
        let b = &bin[..n];
        o.tdec(b);
        for m in around(b, &VALS, rng, 80) {
            o.tdec(&m);
        }
        for cap in 0..=n + 1 {
            o.tenc(t, cap);
        }
        let mut text = [0u8; 400];
        let tn = t.to_text(&mut text).unwrap();
        let s = &text[..tn];
        o.tfrom(s);
        o.tfrom(&s.to_ascii_uppercase());
        for i in positions(s.len(), 20, rng) {
            for c in [b'0', b'1', b'8', b'a', b'7', b'-', 255] {
                let mut m = s.to_vec();
                m[i] = c;
                o.tfrom(&m);
            }
        }
        for k in positions(s.len(), 24, rng) {
            o.tfrom(&s[..k]);
        }
        let mut long = s.to_vec();
        long.extend_from_slice(b"aaaaa");
        o.tfrom(&long);
    }
    for v in [0u8, 2, 255] {
        o.tdec(&[v]);
        o.tdec(&[v, 0]);
    }
    for fl in 0..=255u8 {
        let mut b = vec![1, fl];
        b.extend_from_slice(&node_bytes(&ns[0]));
        o.tdec(&b);
    }
    for _ in 0..600 {
        let len = (rng.next_u64() % 140) as usize;
        let mut b = vec![1u8, (rng.next_u64() % 16) as u8 | 0];
        for k in 0..len {
            let r = rng.next_u64();
            b.push(if k < 90 && r % 3 == 0 {
                (r >> 8) as u8 % 6
            } else {
                (r >> 16) as u8
            });
        }
        o.tdec(&b);
    }
    // random text over the alphabet and a little beyond it
    for _ in 0..400 {
        let len = (rng.next_u64() % 260) as usize;
        let t: Vec<u8> = (0..len)
            .map(|_| match rng.next_u64() % 40 {
                0..=25 => b'a' + (rng.next_u64() % 26) as u8,
                26..=31 => b'2' + (rng.next_u64() % 6) as u8,
                32 => b'A' + (rng.next_u64() % 26) as u8,
                _ => b'a',
            })
            .collect();
        o.tfrom(&t);
    }
}

fn gen_cands(o: &mut Out, rng: &mut SplitMix64) {
    let sets: Vec<Vec<SocketAddr>> = vec![
        vec![],
        vec![a4(1, 1)],
        vec![a6(2, 2), a4(3, 3)],
        (0..8).map(|i| a6(i, 100 + u16::from(i))).collect(),
        (0..9).map(|i| a4(i, 1)).collect(),
        (0..12).map(|i| a4(i, 1)).collect(),
    ];
    for cs in &sets {
        for cap in 0..=170 {
            o.cenc(cs, cap);
        }
        let mut buf = vec![0u8; 400];
        let n = punch::encode(cs, &mut buf).unwrap();
        o.cdec(&buf[..n]);
        for m in around(&buf[..n], &[0, 1, 4, 6, 9, 255], rng, 200) {
            o.cdec(&m);
        }
    }
    for _ in 0..500 {
        let len = (rng.next_u64() % 60) as usize;
        let mut b = vec![(rng.next_u64() % 10) as u8];
        for _ in 0..len {
            let r = rng.next_u64();
            b.push(if r % 3 == 0 {
                [4u8, 6][(r >> 8) as usize % 2]
            } else {
                (r >> 16) as u8
            });
        }
        o.cdec(&b);
    }
}

#[test]
fn connect_codec_trace() {
    let mut o = Out { lines: Vec::new() };
    let mut rng = SplitMix64::new(0xC0DEC);
    o.lines.push(format!(
        r#"{{"t":"consts","rec":{MAX_RECORD_LEN},"pkt":{MAX_PACKET_LEN},"notice":{MAX_NOTICE_LEN},"frames":{BATCH_MAX_FRAMES},"bytes":{BATCH_MAX_BYTES},"frame":{MAX_FRAME_LEN},"tunnel":{MAX_TUNNEL_DATAGRAM},"alias":{},"bcn":{},"ntc":{}}}"#,
        vinc_connect::carrier::ALIAS_MAX,
        local::MAX_LEN,
        sleep::MAX_LEN
    ));
    gen_frames(&mut o, &mut rng);
    gen_dgrams(&mut o, &mut rng);
    gen_signed(&mut o, &mut rng);
    gen_tickets(&mut o, &mut rng);
    gen_cands(&mut o, &mut rng);
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::write(format!("{dir}/connect_codec.ndjson"), o.lines.join("\n") + "\n").unwrap();
    }
    assert!(o.lines.len() > 1000);
}
