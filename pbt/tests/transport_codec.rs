//! `pinc-transport` codecs: frames decoded from what a hostile peer sends, and packet-number expansion around every
//! window edge.
//!
//! Where the expected behaviour comes from:
//! - `frame` module docs: "Every length is checked before use; a `FrameIter` ends at the first error and consumes at
//!   least one byte per frame. Encoding checks the frame and the room up front, ... and `Frame::encoded_len` is
//!   exactly what `Frame::write` writes. Nothing here allocates or panics." `Frame::write`: "A canonical encoding is
//!   chosen: the OFF bit is set exactly when the offset is not 0." Varints are the minimal `pinc-wire` varints, ACK
//!   ranges have one encoding ("This encoding cannot express two ranges that touch or overlap"), and the other
//!   fields are fixed width: so a frame the decoder accepts is re-encoded to the bytes it came from, except a STREAM
//!   frame whose OFF bit was set with offset 0 (the existing test
//!   `stream_off_bit_with_zero_offset_is_accepted_and_re_encoded_canonically`).
//! - `decode_pn`: "Expand a truncated packet number of `len` bytes to the closest candidate to the next expected one"
//!   (RFC 9000 appendix A.3): every packet number within half a window of the next expected one comes back.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::cast_possible_truncation)]

use ephyra::gens;
use ephyra::prelude::*;
use pinc_pbt::mostly_valid;
use pinc_security::{Rekey, TicketBatch, TicketEntry};
use pinc_transport::frame::{Frame, MAX_STREAM_END, write_ack};
use pinc_transport::packet::{MAX_PN, PN_LEN_BASE, PN_LEN_WIDE, decode_pn, encode_pn};
use pinc_wire::{Reader, Writer};

/// A field value: small, any 62-bit, or an edge of the varint space.
fn value(g: &mut Source) -> u64 {
    match g.int(0u8..=4) {
        0 => g.int(0u64..=300),
        1 => g.int(0u64..=(1u64 << 62) - 1),
        2 => *g.pick(&[0, 63, 64, 16_383, 16_384, (1u64 << 62) - 1, (1u64 << 63) - 1]),
        3 => g.int(0u64..=(1u64 << 63) - 1),
        _ => 1u64 << g.int(0u32..=62),
    }
}

/// Encode one valid frame of any kind with fields at their extremes into `w`; `last` allows an implicit length.
fn one_frame(g: &mut Source, out: &mut Vec<u8>, last: bool) {
    let data: Vec<u8> = (0..g.int(0usize..=40)).map(|_| g.int(0u8..=255)).collect();
    let implicit = last && g.bool();
    let mut buf = vec![0u8; 4096];
    let mut w = Writer::new(&mut buf);
    let kind = g.int(0u8..=22);
    if kind == 22 {
        // ACK: descending ranges with gaps of at least one, anywhere below 2^62.
        let mut top = value(g).min(MAX_PN);
        let mut ranges = Vec::new();
        for _ in 0..g.int(1usize..=34) {
            let len = g.int(0u64..=6).min(top);
            ranges.push(top - len..=top);
            let Some(next) = (top - len).checked_sub(2 + g.int(0u64..=5)) else {
                break;
            };
            top = next;
        }
        write_ack(&mut w, ranges).unwrap();
    } else {
        let f = match kind {
            0 => Frame::Padding { len: g.int(1usize..=5) },
            1 => Frame::Ping,
            2 => Frame::ResetStream {
                id: value(g),
                error: value(g),
                final_size: value(g),
            },
            3 => Frame::StopSending {
                id: value(g),
                error: value(g),
            },
            4 => {
                let end = MAX_STREAM_END - data.len() as u64;
                Frame::Stream {
                    id: value(g),
                    offset: if g.bool() { 0 } else { value(g).min(end) },
                    fin: g.bool(),
                    data: &data,
                    implicit_len: implicit,
                }
            }
            5 => Frame::MaxStreamData {
                id: value(g),
                max: value(g),
            },
            6 => Frame::MaxStreams { limit: value(g) },
            7 => Frame::PathChallenge(g.int(0u64..=u64::MAX).to_be_bytes()),
            8 => Frame::PathResponse(g.int(0u64..=u64::MAX).to_be_bytes()),
            9 => Frame::Close { error: value(g) },
            10 => Frame::Datagram {
                data: &data,
                implicit_len: implicit,
            },
            11 => Frame::MtuProbeEcho {
                mtu: g.int(0u16..=u16::MAX),
            },
            12 => Frame::Sleep,
            13 => Frame::Wake,
            14 => Frame::Ready,
            15 => {
                let answer = g.bool();
                let mut share = [0u8; 32];
                share.iter_mut().for_each(|b| *b = g.int(0u8..=255));
                Frame::Rekey(Rekey {
                    answer,
                    share,
                    echo: if answer {
                        g.int(0u64..=u64::MAX).to_be_bytes()
                    } else {
                        [0; 8]
                    },
                    switch_pn: if answer { value(g) } else { 0 },
                    // The sender's roll count: a roll of 2^63 is refused by the encoder (the frame is then not emitted).
                    roll: if answer {
                        0
                    } else {
                        [0, 63, 64, 127, 128, 1 << 62, (1 << 63) - 1, 1 << 63][g.int(0usize..=7)]
                    },
                })
            }
            16 => {
                let mut batch = TicketBatch::new();
                for _ in 0..g.int(0usize..=4) {
                    let mut id = [0u8; 16];
                    id.iter_mut().for_each(|b| *b = g.int(0u8..=255));
                    let _ = batch.push(TicketEntry {
                        tid: id,
                        lifetime_s: g.int(0u32..=u32::MAX),
                    });
                }
                Frame::NewTickets(batch)
            }
            _ => Frame::Extension {
                ty: 0x40 + value(g) % ((1u64 << 62) - 0x40),
                body: &data,
            },
        };
        if f.write(&mut w).is_err() {
            // A field of 2^62 or more is refused by the encoder: such a frame is never on the wire.
            return;
        }
    }
    let n = w.written().len();
    out.extend_from_slice(&buf[..n]);
}

fn payload(g: &mut Source) -> Vec<u8> {
    let n = g.int(1usize..=6);
    let mut out = Vec::new();
    for i in 0..n {
        one_frame(g, &mut out, i + 1 == n);
    }
    out
}

/// Every frame the decoder accepts from any bytes encodes back to the exact bytes it took, and decodes again to the
/// same frame; at the first error the iteration ends.
#[ephyra::test(gen = mostly_valid(payload), tests = 20_000)]
fn accepted_frames_are_their_canonical_encoding(input: Vec<u8>) {
    let mut r = Reader::new(&input);
    let mut frames = 0usize;
    while !r.is_empty() {
        let before = r.position();
        let Ok(f) = Frame::decode(&mut r) else { break };
        let after = r.position();
        frames += 1;
        assert!(after > before, "a frame consumed no byte");
        assert!(frames <= input.len(), "more frames than bytes");
        let taken = &input[before..after];
        let mut buf = vec![0u8; f.encoded_len() + 8];
        let mut w = Writer::new(&mut buf);
        let wrote = f.write(&mut w);
        assert!(wrote.is_ok(), "a decoded frame {f:?} does not encode: {wrote:?}");
        let n = w.written().len();
        assert_eq!(n, f.encoded_len(), "encoded_len of {f:?}");
        let again = &buf[..n];
        let off_zero = matches!(f, Frame::Stream { offset: 0, .. }) && taken[0] & 0x04 != 0;
        if !off_zero {
            assert_eq!(again, taken, "{f:?} was accepted from bytes other than its encoding");
        }
        let mut r2 = Reader::new(again);
        let back = Frame::decode(&mut r2);
        assert_eq!(back.as_ref(), Ok(&f), "re-encoding of {f:?} decodes to something else");
        assert!(r2.is_empty(), "re-encoding of {f:?} leaves bytes");
    }
}

/// The packet numbers around a window edge, with the receiver's largest within half a window behind or ahead of it.
fn pn_case() -> impl Gen<Value = (u64, u64, bool, bool)> {
    (
        gens::frequency(vec![
            (3, gens::int(0u64..=MAX_PN).boxed()),
            (2, gens::int((MAX_PN - (1 << 25))..=MAX_PN).boxed()),
            (2, gens::int(0u64..=(1 << 25)).boxed()),
            // Just below and above a multiple of 2^16 (the edge of a 2-byte window).
            (
                2,
                (gens::int(0u64..=(1u64 << 38)), gens::int(0u64..=0x2_0000))
                    .map(|(k, d)| ((k << 16) + d).min(MAX_PN))
                    .boxed(),
            ),
        ]),
        gens::frequency(vec![
            (2, gens::int(0u64..=8).boxed()),
            (3, gens::int(0u64..=(1 << 23)).boxed()),
        ]),
        gens::bool(),
        gens::bool(),
    )
}

#[ephyra::test(gen = pn_case(), tests = 50_000)]
fn every_packet_number_within_half_a_window_expands_back(case: (u64, u64, bool, bool)) {
    let (pn, dist, wide, behind) = case;
    let len = if wide { PN_LEN_WIDE } else { PN_LEN_BASE };
    let half = 1u64 << (8 * len - 1);
    // The next expected number is within half a window: pn is in (expected - half, expected + half).
    let d = dist % half;
    let expected = if behind { pn.checked_add(d) } else { pn.checked_sub(d) };
    let Some(expected) = expected.filter(|e| *e >= 1 && *e <= MAX_PN + 1) else {
        return;
    };
    let largest = expected - 1;
    let bytes = encode_pn(pn, len).unwrap();
    let truncated = bytes[..len].iter().fold(0u32, |a, b| (a << 8) | u32::from(*b));
    assert_eq!(
        decode_pn(truncated, len, Some(largest)),
        pn,
        "pn {pn} truncated to {len} bytes, largest received {largest}"
    );
}
