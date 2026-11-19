//! Benchmarks of the `pinc-transport` packet layer: building and sealing a short packet, opening and parsing one,
//! and the ACK frame with 32 ranges.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names
)]

use std::hint::black_box;
use std::ops::RangeInclusive;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use pinc_crypto::{Aead, Secret, Software};
use pinc_security::{HeaderKey, Limits, PacketKey};
use pinc_transport::frame::{Frame, FrameIter, stream_overhead, write_ack};
use pinc_transport::packet::{ConnId, PN_LEN_BASE, PnLayout, ShortHeader, encode_pn, open, seal, unprotect_header};
use pinc_wire::Writer;

const DATAGRAM: usize = 1452;
const DCID_LEN: usize = 4;

/// The frames of a packet: one STREAM frame that fills it, or ten small frames and padding.
fn payload_frames(many: bool, data: &[u8], room: usize) -> Vec<Frame<'_>> {
    if many {
        let mut v = vec![
            Frame::Ping,
            Frame::MaxStreamData { id: 4, max: 1 << 20 },
            Frame::PathChallenge([1; 8]),
            Frame::MaxStreamData { id: 8, max: 5000 },
            Frame::Wake,
            Frame::Sleep,
            Frame::Ready,
            Frame::ResetStream {
                id: 16,
                error: 1,
                final_size: 4096,
            },
        ];
        let used: usize = v.iter().map(Frame::encoded_len).sum();
        v.push(Frame::Padding { len: room - used });
        v
    } else {
        let n = room - stream_overhead(4, 1_000_000, 0, true);
        vec![Frame::Stream {
            id: 4,
            offset: 1_000_000,
            fin: false,
            data: &data[..n],
            implicit_len: true,
        }]
    }
}

fn bench_packets(c: &mut Criterion) {
    let p = Software;
    let dcid = ConnId::new(&[1, 2, 3, 4]).unwrap();
    let data = vec![0x5a_u8; DATAGRAM];
    for (aead_name, aead) in [
        ("chacha20poly1305", Aead::ChaCha20Poly1305),
        ("aes128gcm", Aead::Aes128Gcm),
    ] {
        let secret = Secret::new([7u8; 32]);
        let limits = Limits {
            aes_gcm_packets: u64::MAX,
            chacha_failures: u64::MAX,
        };
        let mut tx = PacketKey::from_secret(&p, aead, &secret).unwrap().with_limits(limits);
        let mut rx = PacketKey::from_secret(&p, aead, &secret).unwrap().with_limits(limits);
        let hk = HeaderKey::from_secret(&p, aead, &secret).unwrap();
        let mut g = c.benchmark_group(format!("packet/{aead_name}"));
        g.throughput(Throughput::Bytes(DATAGRAM as u64));
        for (label, many) in [("1_stream", false), ("10_frames", true)] {
            let pn_len = PN_LEN_BASE;
            let pnb = encode_pn(1000, pn_len).unwrap();
            let header_len = 1 + DCID_LEN + pn_len;
            let room = DATAGRAM - header_len - Aead::TAG_LEN;
            let frames = payload_frames(many, &data, room);
            let layout = PnLayout {
                pn_off: 1 + DCID_LEN,
                pn_len,
                long: false,
            };
            let mut buf = vec![0u8; DATAGRAM];
            let build = |buf: &mut [u8], tx: &mut PacketKey<Software>| {
                let mut w = Writer::new(buf);
                ShortHeader { key_phase: false, dcid }
                    .write(&mut w, &pnb[..pn_len])
                    .unwrap();
                for f in &frames {
                    f.write(&mut w).unwrap();
                }
                let payload_len = w.written().len() - header_len;
                seal(tx, &hk, &p, buf, layout, payload_len, 1000).unwrap()
            };
            g.bench_function(format!("build_seal_protect/{label}"), |b| {
                b.iter(|| black_box(build(&mut buf, &mut tx)));
            });
            let len = build(&mut buf, &mut tx);
            assert_eq!(len, DATAGRAM);
            g.bench_function(format!("unprotect_open_parse/{label}"), |b| {
                b.iter_batched_ref(
                    || buf.clone(),
                    |pkt| {
                        let un = unprotect_header(&hk, &p, pkt, 1 + DCID_LEN, false).unwrap();
                        let o = open(&mut rx, &p, pkt, 1 + DCID_LEN, &un, Some(995)).unwrap();
                        let n = FrameIter::new(&pkt[o.payload_start..o.payload_end])
                            .inspect(|f| assert!(f.is_ok()))
                            .count();
                        black_box(n);
                    },
                    BatchSize::SmallInput,
                );
            });
        }
        g.finish();
    }
}

fn bench_ack(c: &mut Criterion) {
    // 32 ranges of 3 packets with a gap of 2 missing between them, highest first.
    let ranges: Vec<RangeInclusive<u64>> = (0..32u64)
        .map(|i| {
            let end = 1_000_000 - i * 5;
            end - 2..=end
        })
        .collect();
    let mut buf = [0u8; 256];
    let mut w = Writer::new(&mut buf);
    write_ack(&mut w, ranges.iter().cloned()).unwrap();
    let len = w.written().len();
    let encoded = buf[..len].to_vec();
    let mut g = c.benchmark_group("ack_32_ranges");
    g.bench_function("encode", |b| {
        b.iter(|| {
            let mut w = Writer::new(&mut buf);
            write_ack(&mut w, ranges.iter().cloned()).unwrap();
            black_box(w.written().len());
        });
    });
    g.bench_function("decode", |b| {
        b.iter(|| {
            let Some(Ok(Frame::Ack(ack))) = FrameIter::new(black_box(&encoded)).next() else {
                panic!("not an ack");
            };
            black_box(ack.ranges().map(|r| *r.end() - *r.start()).sum::<u64>());
        });
    });
    g.finish();
}

criterion_group!(benches, bench_packets, bench_ack);
criterion_main!(benches);
