//! Frame encode and decode: every frame type, the ACK canonical form, extension frames and the frame iterator.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::items_after_statements,
    clippy::unreadable_literal,
    clippy::identity_op,
    clippy::assert_is_empty,
    clippy::int_plus_one,
    clippy::single_range_in_vec_init,
    clippy::reversed_empty_ranges
)]

use std::ops::RangeInclusive;

use proptest::prelude::*;
use pinc_security::{Rekey, TicketBatch, TicketEntry};
use pinc_tests::SplitMix64;
use pinc_transport::frame::{
    Ack, Frame, FrameError, FrameIter, MAX_ACK_RANGES, MAX_STREAM_END, ack_len, datagram_overhead, stream_overhead, ty,
    write_ack,
};
use pinc_wire::{WireError, Writer};

pinc_tests::install_counting_allocator!();

fn encode(f: &Frame<'_>) -> Vec<u8> {
    let mut buf = vec![0u8; f.encoded_len() + 4];
    let mut w = Writer::new(&mut buf);
    f.write(&mut w).unwrap();
    let n = w.written().len();
    assert_eq!(n, f.encoded_len(), "encoded_len of {f:?}");
    buf.truncate(n);
    buf
}

fn decode_all(bytes: &[u8]) -> Vec<Result<Frame<'_>, FrameError>> {
    FrameIter::new(bytes).collect()
}

fn one(bytes: &[u8]) -> Frame<'_> {
    let mut all = decode_all(bytes);
    assert_eq!(all.len(), 1, "{bytes:02x?}");
    all.pop().unwrap().unwrap()
}

fn ranges_of(bytes: &[u8]) -> (Ack<'_>, Vec<RangeInclusive<u64>>) {
    let Frame::Ack(ack) = one(bytes) else {
        panic!("not an ack")
    };
    let ranges = ack.ranges().collect();
    (ack, ranges)
}

fn ack_bytes(ranges: &[RangeInclusive<u64>]) -> Result<Vec<u8>, FrameError> {
    let mut buf = vec![0u8; 1024];
    let mut w = Writer::new(&mut buf);
    write_ack(&mut w, ranges.iter().cloned())?;
    let n = w.written().len();
    buf.truncate(n);
    Ok(buf)
}

// ---- exact wire bytes ----

#[test]
fn frames_have_the_documented_bytes() {
    let cases: Vec<(Frame<'_>, Vec<u8>)> = vec![
        (Frame::Ping, vec![0x01]),
        (Frame::Padding { len: 3 }, vec![0, 0, 0]),
        (
            Frame::ResetStream {
                id: 4,
                error: 9,
                final_size: 300,
            },
            vec![0x04, 4, 9, 0xac, 0x02],
        ),
        (
            Frame::Stream {
                id: 4,
                offset: 0,
                fin: false,
                data: b"ab",
                implicit_len: false,
            },
            vec![0x0a, 4, 2, b'a', b'b'],
        ),
        (
            Frame::Stream {
                id: 4,
                offset: 10,
                fin: true,
                data: b"x",
                implicit_len: true,
            },
            vec![0x0d, 4, 10, b'x'],
        ),
        (
            Frame::Stream {
                id: 1,
                offset: 7,
                fin: true,
                data: b"",
                implicit_len: false,
            },
            vec![0x0f, 1, 7, 0],
        ),
        (Frame::MaxStreamData { id: 8, max: 5 }, vec![0x11, 8, 5]),
        (Frame::MaxStreams { limit: 9 }, vec![0x12, 9]),
        (Frame::MaxStreams { limit: 300 }, vec![0x12, 0xac, 0x02]),
        (Frame::StopSending { id: 4, error: 9 }, vec![0x05, 4, 9]),
        (
            Frame::StopSending {
                id: 1 << 20,
                error: 300,
            },
            vec![0x05, 0x80, 0x80, 0x40, 0xac, 0x02],
        ),
        (
            Frame::PathChallenge([1, 2, 3, 4, 5, 6, 7, 8]),
            vec![0x1a, 1, 2, 3, 4, 5, 6, 7, 8],
        ),
        (
            Frame::PathResponse([1, 2, 3, 4, 5, 6, 7, 8]),
            vec![0x1b, 1, 2, 3, 4, 5, 6, 7, 8],
        ),
        (Frame::Close { error: 3 }, vec![0x1c, 3]),
        (Frame::Close { error: 0x4c }, vec![0x1c, 0x4c]),
        (
            Frame::Datagram {
                data: b"dg",
                implicit_len: true,
            },
            vec![0x30, b'd', b'g'],
        ),
        (
            Frame::Datagram {
                data: b"dg",
                implicit_len: false,
            },
            vec![0x31, 2, b'd', b'g'],
        ),
        (Frame::MtuProbeEcho { mtu: 1452 }, vec![0x3a, 0x05, 0xac]),
        (Frame::Sleep, vec![0x3b]),
        (Frame::Wake, vec![0x3c]),
        (
            Frame::Rekey(Rekey {
                answer: false,
                share: [7; 32],
                echo: [0; 8],
                switch_pn: 0,
            }),
            [vec![0x3d, 0], vec![7; 32]].concat(),
        ),
        (
            Frame::Rekey(Rekey {
                answer: true,
                share: [8; 32],
                echo: [5; 8],
                switch_pn: 300,
            }),
            [vec![0x3d, 1], vec![8; 32], vec![5; 8], vec![0xac, 0x02]].concat(),
        ),
        (Frame::Ready, vec![0x3e]),
        (
            Frame::Extension { ty: 0x40, body: b"abc" },
            vec![0x40, 3, b'a', b'b', b'c'],
        ),
        (Frame::Extension { ty: 0x80, body: b"" }, vec![0x80, 0x01, 0]),
    ];
    for (frame, bytes) in cases {
        assert_eq!(encode(&frame), bytes, "{frame:?}");
        assert_eq!(one(&bytes), frame, "{bytes:02x?}");
    }
}

#[test]
fn new_tickets_carries_a_batch() {
    let mut batch = TicketBatch::new();
    for i in 0..3u8 {
        assert!(batch.push(TicketEntry {
            tid: [i; 16],
            lifetime_s: 86_400 + u32::from(i)
        }));
    }
    let f = Frame::NewTickets(batch);
    let bytes = encode(&f);
    assert_eq!(bytes.len(), 1 + 1 + 3 * 20);
    assert_eq!(bytes[..2], [0x3f, 3]);
    assert_eq!(&bytes[2..18], &[0u8; 16]);
    assert_eq!(&bytes[18..22], &86_400u32.to_be_bytes());
    assert_eq!(one(&bytes), f);
    assert_eq!(encode(&Frame::NewTickets(TicketBatch::new())), vec![0x3f, 0]);
    assert_eq!(one(&[0x3f, 0]), Frame::NewTickets(TicketBatch::new()));
    // More than four tickets is not a batch, and a cut batch is a wire error.
    assert!(matches!(decode_all(&[0x3f, 5])[0], Err(FrameError::Wire(_))));
    assert!(matches!(
        decode_all(&bytes[..bytes.len() - 1])[0],
        Err(FrameError::Wire(_))
    ));
    // Following frames are not swallowed.
    let mut two = bytes.clone();
    two.push(0x01);
    let all = decode_all(&two);
    assert_eq!(all.len(), 2);
    assert_eq!(all[1], Ok(Frame::Ping));
}

#[test]
fn stream_off_bit_with_zero_offset_is_accepted_and_re_encoded_canonically() {
    let f = one(&[0x0e, 4, 0, 1, b'z']); // OFF and LEN, offset 0
    assert_eq!(
        f,
        Frame::Stream {
            id: 4,
            offset: 0,
            fin: false,
            data: b"z",
            implicit_len: false
        }
    );
    assert_eq!(encode(&f), vec![0x0a, 4, 1, b'z']);
}

// ---- errors ----

#[test]
fn unassigned_types_below_0x40_are_errors() {
    let assigned = [
        0x00u64, 0x01, 0x02, 0x04, 0x05, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x11, 0x12, 0x1a, 0x1b, 0x1c,
        0x30, 0x31, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
    ];
    for t in 0..0x40u64 {
        let mut payload = vec![t as u8];
        payload.extend_from_slice(&[0u8; 48]);
        let first = FrameIter::new(&payload).next().unwrap();
        if assigned.contains(&t) {
            assert_ne!(first, Err(FrameError::UnknownType(t)), "type {t:#x}");
        } else {
            assert_eq!(first, Err(FrameError::UnknownType(t)), "type {t:#x}");
        }
    }
    // Extension frames of any type from 0x40, including multi-byte types.
    for t in [0x40u64, 0x41, 0x7f, 0x80, 0x3fff, 1 << 40] {
        let f = Frame::Extension { ty: t, body: b"body" };
        assert_eq!(one(&encode(&f)), f);
    }
}

#[test]
fn the_iterator_stops_at_the_first_error() {
    let got = decode_all(&[0x01, 0x03, 0x01]);
    assert_eq!(got, vec![Ok(Frame::Ping), Err(FrameError::UnknownType(3))]);
    let mut it = FrameIter::new(&[0x03, 0x01]);
    assert!(it.next().unwrap().is_err());
    assert!(it.next().is_none());
    assert!(FrameIter::new(&[]).next().is_none());
    // A non-minimal type varint, and a length past the payload.
    assert_eq!(
        decode_all(&[0x81, 0x00]),
        vec![Err(FrameError::Wire(WireError::VarintNonMinimal))]
    );
    assert!(matches!(
        decode_all(&[0x0a, 4, 9, 1, 2]).as_slice(),
        [Err(FrameError::Wire(WireError::Truncated { .. }))]
    ));
    assert!(matches!(
        decode_all(&[0x40, 5, 1]).as_slice(),
        [Err(FrameError::Wire(WireError::Truncated { .. }))]
    ));
}

#[test]
fn padding_runs_are_one_step() {
    let mut payload = vec![0u8; 1200];
    payload.extend_from_slice(&[0x01]);
    payload.extend_from_slice(&[0u8; 7]);
    assert_eq!(
        decode_all(&payload),
        vec![
            Ok(Frame::Padding { len: 1200 }),
            Ok(Frame::Ping),
            Ok(Frame::Padding { len: 7 })
        ]
    );
    assert_eq!(encode(&Frame::Padding { len: 1200 }), vec![0u8; 1200]);
}

#[test]
fn validation_errors() {
    // Stream end past 2^62 - 1.
    let f = Frame::Stream {
        id: 0,
        offset: MAX_STREAM_END,
        fin: false,
        data: b"a",
        implicit_len: true,
    };
    let mut buf = [0u8; 64];
    assert_eq!(f.write(&mut Writer::new(&mut buf)), Err(FrameError::StreamEnd));
    let f = Frame::Stream {
        id: 0,
        offset: MAX_STREAM_END,
        fin: true,
        data: b"",
        implicit_len: true,
    };
    assert!(f.write(&mut Writer::new(&mut buf)).is_ok());
    // Decode the same overflow by hand: offset 2^62 - 1 is 9 varint bytes (7-bit groups).
    let off = {
        let mut o = [0u8; 9];
        let n = pinc_wire::varint::encode(MAX_STREAM_END, &mut o).unwrap();
        o[..n].to_vec()
    };
    let mut wire = vec![0x0e, 1];
    wire.extend_from_slice(&off);
    wire.extend_from_slice(&[1, b'a']);
    assert_eq!(decode_all(&wire), vec![Err(FrameError::StreamEnd)]);
    // An extension below 0x40 cannot be written, and a field of 2^63 or more does not fit a varint.
    let ext = Frame::Extension { ty: 0x3f, body: b"" };
    assert_eq!(
        ext.write(&mut Writer::new(&mut buf)),
        Err(FrameError::UnknownType(0x3f))
    );
    let big = Frame::MaxStreamData { id: 0, max: 1 << 63 };
    let mut w = Writer::new(&mut buf);
    assert_eq!(big.write(&mut w), Err(FrameError::Wire(WireError::VarintOverflow)));
    assert!(w.written().is_empty());
    let big = Frame::MaxStreams { limit: 1 << 63 };
    let mut w = Writer::new(&mut buf);
    assert_eq!(big.write(&mut w), Err(FrameError::Wire(WireError::VarintOverflow)));
    assert!(w.written().is_empty());
    let big = Frame::StopSending { id: 0, error: 1 << 63 };
    let mut w = Writer::new(&mut buf);
    assert_eq!(big.write(&mut w), Err(FrameError::Wire(WireError::VarintOverflow)));
    assert!(w.written().is_empty());
    // A stop frame cut short is an error, not a frame.
    assert!(matches!(decode_all(&[0x05, 4]).as_slice(), [Err(FrameError::Wire(_))]));
}

proptest! {
    #[test]
    fn a_failed_write_leaves_the_writer_unchanged(spec in spec(), cut in 0usize..40) {
        let f = frame(&spec);
        let need = f.encoded_len();
        let cut = cut.min(need.saturating_sub(1));
        prop_assume!(need > 0);
        let mut buf = vec![0xeeu8; cut];
        let mut w = Writer::new(&mut buf);
        let res = f.write(&mut w);
        prop_assert!(matches!(res, Err(FrameError::Wire(WireError::BufferTooSmall { .. }))), "{res:?}");
        prop_assert!(w.written().is_empty());
        prop_assert!(buf.iter().all(|b| *b == 0xee));
    }
}

// ---- size functions ----

#[test]
fn size_functions_match_the_encoding() {
    for id in [0u64, 127, 128, 1 << 40] {
        for offset in [0u64, 1, 128, 1 << 50] {
            for len in [0usize, 5, 127, 128, 70_000] {
                for implicit_len in [false, true] {
                    let data = vec![0u8; len];
                    let f = Frame::Stream {
                        id,
                        offset,
                        fin: false,
                        data: &data,
                        implicit_len,
                    };
                    assert_eq!(stream_overhead(id, offset, len, implicit_len) + len, f.encoded_len());
                }
                let data = vec![0u8; len];
                for implicit_len in [false, true] {
                    let f = Frame::Datagram {
                        data: &data,
                        implicit_len,
                    };
                    assert_eq!(datagram_overhead(len, implicit_len) + len, f.encoded_len());
                }
            }
        }
    }
}

// ---- ACK ----

#[test]
fn ack_exact_bytes_and_decode() {
    // Ranges 12..=14 and 5..=7: largest 14, first_range 2, one more range with gap 12-7-2 = 3 and length 2.
    let bytes = ack_bytes(&[12..=14, 5..=7]).unwrap();
    assert_eq!(bytes, vec![0x02, 14, 1, 2, 3, 2]);
    let (ack, ranges) = ranges_of(&bytes);
    assert_eq!((ack.largest(), ack.range_count()), (14, 2));
    assert_eq!(ranges, vec![12..=14, 5..=7]);
    // A single range, and a range down to packet 0.
    assert_eq!(ack_bytes(&[0..=0]).unwrap(), vec![0x02, 0, 0, 0]);
    assert_eq!(ranges_of(&[0x02, 0, 0, 0]).1, vec![0..=0]);
    // The smallest gap that is expressible: exactly one packet missing between ranges.
    assert_eq!(ack_bytes(&[10..=10, 8..=8]).unwrap(), vec![0x02, 10, 1, 0, 0, 0]);
    assert_eq!(ack_len([12..=14, 5..=7]).unwrap(), bytes.len());
    // Re-encoding a decoded frame keeps the bytes.
    assert_eq!(encode(&Frame::Ack(ack)), bytes);
}

#[test]
fn ack_encoding_rejects_non_canonical_ranges() {
    let max = (1u64 << 62) - 1;
    let bad: Vec<(Vec<RangeInclusive<u64>>, &str)> = vec![
        (vec![], "no ranges"),
        (vec![5..=3], "empty range"),
        (vec![5..=7, 8..=9], "ascending order"),
        (vec![5..=7, 3..=4], "touching ranges must be merged"),
        (vec![5..=7, 2..=6], "overlapping ranges"),
        (vec![5..=7, 5..=7], "duplicate range"),
        (vec![5..=7, 3..=8], "a range reaching above the previous one"),
        (vec![0..=max + 1], "above the packet number space"),
        (vec![10..=12, 3..=3, 3..=3], "a repeat after a valid pair"),
    ];
    for (ranges, why) in bad {
        assert_eq!(ack_bytes(&ranges), Err(FrameError::Ack), "{why}");
        assert_eq!(ack_len(ranges.iter().cloned()), Err(FrameError::Ack), "{why}");
    }
    // A gap of exactly one missing packet is fine; zero missing is not.
    assert!(ack_bytes(&[5..=7, 3..=3]).is_ok());
    assert_eq!(ack_bytes(&[5..=7, 3..=4]), Err(FrameError::Ack));
    assert!(ack_bytes(&[max..=max]).is_ok());
    // A too-small buffer writes nothing.
    let mut tiny = [0u8; 3];
    let mut w = Writer::new(&mut tiny);
    assert!(matches!(
        write_ack(&mut w, [5..=7, 3..=3]),
        Err(FrameError::Wire(WireError::BufferTooSmall { .. }))
    ));
    assert!(w.written().is_empty());
}

#[test]
fn ack_decoding_rejects_malformed_frames() {
    // first_range larger than largest: a range below packet number 0.
    assert_eq!(decode_all(&[0x02, 5, 0, 6]), vec![Err(FrameError::Ack)]);
    // Gap or length that goes below 0.
    assert_eq!(decode_all(&[0x02, 10, 1, 0, 9, 0]), vec![Err(FrameError::Ack)]);
    assert_eq!(decode_all(&[0x02, 10, 1, 0, 0, 9]), vec![Err(FrameError::Ack)]);
    assert_eq!(decode_all(&[0x02, 10, 1, 0, 8, 1]), vec![Err(FrameError::Ack)]); // ends at 0, starts at -1
    // The last valid values: the range ends at 0 and starts at 0.
    assert_eq!(ranges_of(&[0x02, 10, 1, 0, 8, 0]).1, vec![10..=10, 0..=0]);
    // Largest above 2^62 - 1.
    let mut wire = vec![0x02];
    let mut v = [0u8; 9];
    let n = pinc_wire::varint::encode(1 << 62, &mut v).unwrap();
    wire.extend_from_slice(&v[..n]);
    wire.extend_from_slice(&[0, 0]);
    assert_eq!(decode_all(&wire), vec![Err(FrameError::Ack)]);
    // Too many ranges (32 extra means 33 in total), and a count that promises more than the bytes hold.
    assert_eq!(decode_all(&[0x02, 100, 32, 0]), vec![Err(FrameError::TooManyRanges)]);
    assert!(matches!(
        decode_all(&[0x02, 100, 3, 0, 1, 0]).as_slice(),
        [Err(FrameError::Wire(WireError::Truncated { .. }))]
    ));
    assert!(matches!(
        decode_all(&[0x02, 100]).as_slice(),
        [Err(FrameError::Wire(WireError::Truncated { .. }))]
    ));
    // A frame after the ACK is parsed from the right place.
    assert_eq!(
        decode_all(&[0x02, 14, 1, 2, 3, 2, 0x01]).len(),
        2,
        "the iterator resumes after the last range"
    );
}

fn descending(base: u64, parts: &[(u64, u64)]) -> Vec<RangeInclusive<u64>> {
    // parts are (missing, extra) from the lowest range up; missing >= 1.
    let mut out = Vec::new();
    let mut start = base;
    for (missing, extra) in parts {
        out.push(start..=start + extra);
        start = start + extra + 1 + missing;
    }
    out.reverse();
    out
}

proptest! {
    #[test]
    fn ack_round_trips_and_is_trimmed_to_32_ranges(
        base in 0u64..(1 << 40),
        parts in proptest::collection::vec((1u64..2000, 0u64..2000), 1..48),
    ) {
        let ranges = descending(base, &parts);
        let bytes = ack_bytes(&ranges).unwrap();
        prop_assert_eq!(bytes.len(), ack_len(ranges.iter().cloned()).unwrap());
        let (ack, got) = ranges_of(&bytes);
        let want: Vec<_> = ranges.iter().take(MAX_ACK_RANGES).cloned().collect();
        prop_assert_eq!(&got, &want);
        prop_assert_eq!(ack.range_count(), want.len());
        prop_assert_eq!(ack.largest(), *want[0].end());
        prop_assert_eq!(ack.ranges().size_hint(), (want.len(), Some(want.len())));
        // Decoded ranges are canonical: strictly descending with at least one missing packet between them.
        for pair in got.windows(2) {
            prop_assert!(pair[1].end() + 1 < *pair[0].start());
        }
        prop_assert_eq!(encode(&Frame::Ack(ack)), bytes);
    }
}

// ---- every frame type round-trips ----

#[derive(Debug, Clone)]
struct Spec {
    sel: u8,
    a: u64,
    b: u64,
    c: u64,
    data: Vec<u8>,
    token: [u8; 16],
    path: [u8; 8],
    flag: bool,
    implicit: bool,
}

fn value() -> impl Strategy<Value = u64> {
    prop_oneof![0u64..300, 0u64..(1 << 62), Just((1u64 << 62) - 1)]
}

fn spec() -> impl Strategy<Value = Spec> {
    (
        0u8..=255,
        (value(), value(), value()),
        proptest::collection::vec(any::<u8>(), 0..300),
        any::<[u8; 16]>(),
        any::<[u8; 8]>(),
        (any::<bool>(), any::<bool>()),
    )
        .prop_map(|(sel, (a, b, c), data, token, path, (flag, implicit))| Spec {
            sel,
            a,
            b,
            c,
            data,
            token,
            path,
            flag,
            implicit,
        })
}

const KINDS: u8 = 26;

impl Spec {
    fn token_share(&self) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[..16].copy_from_slice(&self.token);
        out[16..].copy_from_slice(&self.token);
        out
    }
}

/// A frame of every kind but ACK (which has its own tests), chosen by `sel`.
fn frame(s: &Spec) -> Frame<'_> {
    let (a, b, c) = (s.a, s.b, s.c);
    match s.sel % KINDS {
        0 => Frame::Padding {
            len: usize::from(s.sel) + 1,
        },
        1 => Frame::Ping,
        2 => Frame::ResetStream {
            id: a,
            error: b,
            final_size: c,
        },
        5 => Frame::Stream {
            id: a,
            offset: b % ((1 << 62) - 1 - 400),
            fin: s.flag,
            data: &s.data,
            implicit_len: s.implicit,
        },
        7 => Frame::MaxStreamData { id: a, max: b },
        25 => Frame::StopSending { id: a, error: b },
        14 => Frame::PathChallenge(s.path),
        15 => Frame::PathResponse(s.path),
        16 => Frame::Close { error: a },
        17 => Frame::Rekey(Rekey {
            answer: s.flag,
            share: s.token_share(),
            echo: if s.flag { [3; 8] } else { [0; 8] },
            switch_pn: if s.flag { a } else { 0 },
        }),
        18 => Frame::Datagram {
            data: &s.data,
            implicit_len: s.implicit,
        },
        19 => Frame::MtuProbeEcho { mtu: a as u16 },
        20 => Frame::Sleep,
        21 => Frame::Wake,
        22 => Frame::Ready,
        23 => Frame::Extension {
            ty: 0x40 + (a >> 3),
            body: &s.data,
        },
        _ => Frame::Extension {
            ty: 0x40,
            body: &s.data,
        },
    }
}

proptest! {
    #[test]
    fn every_frame_round_trips_with_exact_size(s in spec()) {
        let f = frame(&s);
        let bytes = encode(&f);
        prop_assert_eq!(decode_all(&bytes), vec![Ok(f.clone())]);
        // A strict prefix never panics; it is an error unless the frame has no closing length.
        let tolerant = matches!(
            f,
            Frame::Padding { .. }
                | Frame::Stream { implicit_len: true, .. }
                | Frame::Datagram { implicit_len: true, .. }
        );
        for cut in 1..bytes.len() {
            let got = decode_all(&bytes[..cut]);
            if !tolerant {
                prop_assert!(got.last().is_some_and(Result::is_err), "cut {} of {:?}", cut, f);
            }
        }
    }

    #[test]
    fn frame_sequences_round_trip(specs in proptest::collection::vec(spec(), 1..8)) {
        let mut frames: Vec<Frame<'_>> = specs.iter().map(frame).filter(|f| !matches!(f, Frame::Padding { .. })).collect();
        let n = frames.len();
        for (i, f) in frames.iter_mut().enumerate() {
            // Only the last frame may drop its length.
            match f {
                Frame::Stream { implicit_len, .. } | Frame::Datagram { implicit_len, .. } if i + 1 < n => *implicit_len = false,
                _ => {}
            }
        }
        let total: usize = frames.iter().map(Frame::encoded_len).sum();
        let mut buf = vec![0u8; total];
        let mut w = Writer::new(&mut buf);
        for f in &frames {
            f.write(&mut w).unwrap();
        }
        prop_assert_eq!(w.written().len(), total);
        let got: Result<Vec<_>, _> = FrameIter::new(&buf).collect();
        prop_assert_eq!(got.unwrap(), frames);
    }

    #[test]
    fn arbitrary_bytes_never_panic_and_always_progress(bytes in proptest::collection::vec(any::<u8>(), 0..400)) {
        let mut count = 0usize;
        let mut failed = false;
        for item in FrameIter::new(&bytes) {
            prop_assert!(!failed, "an item followed an error");
            count += 1;
            prop_assert!(count <= bytes.len());
            match item {
                // Whatever decodes encodes back to a frame that decodes to the same value.
                Ok(f) => {
                    let again = encode(&f);
                    prop_assert_eq!(decode_all(&again), vec![Ok(f)]);
                }
                Err(_) => failed = true,
            }
        }
    }

    #[test]
    fn structured_garbage_is_handled(
        first in 0u8..0x50,
        rest in proptest::collection::vec(any::<u8>(), 0..60),
    ) {
        let mut payload = vec![first];
        payload.extend_from_slice(&rest);
        for item in FrameIter::new(&payload) {
            if item.is_err() {
                break;
            }
        }
    }
}

// ---- allocation ----

#[test]
fn frame_paths_allocate_nothing() {
    let data = [7u8; 200];
    let frames = [
        Frame::Padding { len: 40 },
        Frame::Ping,
        Frame::ResetStream {
            id: 4,
            error: 9,
            final_size: 300,
        },
        Frame::Stream {
            id: 4,
            offset: 99,
            fin: true,
            data: &data,
            implicit_len: false,
        },
        Frame::MaxStreamData { id: 4, max: 1 << 20 },
        Frame::StopSending { id: 4, error: 7 },
        Frame::PathChallenge([1; 8]),
        Frame::PathResponse([1; 8]),
        Frame::Close { error: 1 },
        Frame::Rekey(Rekey {
            answer: true,
            share: [3; 32],
            echo: [4; 8],
            switch_pn: 9,
        }),
        Frame::Datagram {
            data: &data,
            implicit_len: false,
        },
        Frame::MtuProbeEcho { mtu: 1452 },
        Frame::Sleep,
        Frame::Wake,
        Frame::Ready,
        Frame::Extension {
            ty: 0x41,
            body: &data[..50],
        },
    ];
    let ranges: Vec<RangeInclusive<u64>> = (0..32u64).map(|i| (1000 - i * 5 - 2)..=(1000 - i * 5)).collect();
    let mut rng = SplitMix64::new(3);
    let mut junk = [0u8; 256];
    rng.fill(&mut junk);
    let mut buf = [0u8; 2048];
    let stats = pinc_tests::measure(|| {
        let mut w = Writer::new(&mut buf);
        for f in &frames {
            f.write(&mut w).unwrap();
        }
        write_ack(&mut w, ranges.iter().cloned()).unwrap();
        let n = w.written().len();
        let mut seen = 0;
        for f in FrameIter::new(&buf[..n]) {
            if let Frame::Ack(ack) = f.unwrap() {
                assert_eq!(ack.ranges().count(), 32);
            }
            seen += 1;
        }
        assert_eq!(seen, frames.len() + 1);
        assert!(FrameIter::new(&junk).count() > 0);
        assert!(ack_len(ranges.iter().cloned()).unwrap() > 0);
        assert!(stream_overhead(1, 2, 3, false) + datagram_overhead(3, false) > 0);
    });
    assert_eq!(stats.count(), 0, "{stats:?}");
    assert_eq!(ty::STREAM, 8);
}
