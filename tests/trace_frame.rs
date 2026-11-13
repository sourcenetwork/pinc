//! Trace generation for the VINCER frame codecs: seeded calls of the real `Frame::decode`, `Frame::write`,
//! `Frame::encoded_len`, `FrameIter`, `write_ack`, `ack_len`, `Ack::ranges`, `stream_overhead` and
//! `datagram_overhead` (`vinc-transport`), recorded as ndjson for the TLA+ trace check (`TraceFrame.tla`) and the
//! Lean replay (`Vinc/TraceFrame.lean`).
//!
//! Every frame kind is built with its fields at the varint boundaries, written into buffers with room, exactly
//! enough, one byte short and none, read back followed by nothing, by a nonzero byte, by zeros and by the start of
//! a varint, cut at every length, with single bytes changed and with bytes appended; every frame that decodes is
//! written again. ACK frames come from range lists of 1 to 40 ranges, valid and broken (touching, overlapping,
//! reversed, out of order, beyond the packet-number space, empty), and their ranges are read back. Garbage follows
//! every type below `0x46`, and payloads of several frames, whole and damaged, go through `FrameIter`.
//!
//! Two files are written: `frame.ndjson` holds the calls whose numbers stay below 2^28 (the TLA+ checker has 32-bit
//! integers), `frame_wide.ndjson` holds every call, with numbers up to `2^64 - 1`, for the Lean replay.
//!
//! The test asserts the properties itself, so it is meaningful without the proof tools: a frame followed by what
//! may follow it decodes to itself and takes exactly `encoded_len` bytes; a decoded frame is written back as the
//! bytes read (except the OFF bit of a STREAM frame at offset 0); a cut is `Truncated`; a refused write leaves the
//! buffer untouched; `write_ack` accepts exactly the lists a naive check accepts, and the ranges come back.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::missing_panics_doc,
    unreachable_pub
)]

use vinc_security::{Rekey, TicketBatch, TicketEntry};
use vinc_tests::SplitMix64;
use vinc_transport::frame::{
    Frame, FrameError, FrameIter, MAX_ACK_RANGES, MAX_STREAM_END, ack_len, datagram_overhead, stream_overhead,
    write_ack,
};
use vinc_wire::{Reader, WireError, Writer, varint};

/// Numbers below this fit the TLA+ checker with room for its arithmetic.
const NARROW: u64 = 1 << 28;
const MAX_PN: u64 = (1 << 62) - 1;

#[derive(Default)]
struct Out {
    narrow: String,
    wide: String,
    events: usize,
    narrow_events: usize,
    pool: Vec<Vec<u8>>,
}

impl Out {
    fn push(&mut self, narrow: bool, line: &str) {
        self.wide.push_str(line);
        self.wide.push('\n');
        self.events += 1;
        if narrow {
            self.narrow.push_str(line);
            self.narrow.push('\n');
            self.narrow_events += 1;
        }
    }
}

fn arr(b: &[u8]) -> String {
    let v: Vec<String> = b.iter().map(u8::to_string).collect();
    format!("[{}]", v.join(","))
}

fn tag(e: &FrameError) -> (String, u64) {
    match e {
        FrameError::Wire(WireError::Truncated { needed }) => ("Truncated".into(), *needed as u64),
        FrameError::Wire(WireError::BufferTooSmall { needed }) => ("BufferTooSmall".into(), *needed as u64),
        FrameError::Wire(WireError::VarintTooLong) => ("VarintTooLong".into(), 0),
        FrameError::Wire(WireError::VarintOverflow) => ("VarintOverflow".into(), 0),
        FrameError::Wire(WireError::VarintNonMinimal) => ("VarintNonMinimal".into(), 0),
        FrameError::Wire(WireError::Unexpected(what)) => ((*what).into(), 0),
        FrameError::Wire(_) => ("other".into(), 0),
        FrameError::UnknownType(t) => ("UnknownType".into(), *t),
        FrameError::Ack => ("Ack".into(), 0),
        FrameError::TooManyRanges => ("TooManyRanges".into(), 0),
        FrameError::StreamEnd => ("StreamEnd".into(), 0),
        FrameError::RekeyKind => ("RekeyKind".into(), 0),
    }
}

/// No varint read anywhere in `b` goes past four bytes, so every number the decoder meets is below 2^28.
fn runs_ok(b: &[u8]) -> bool {
    let mut run = 0;
    for x in b {
        if *x >= 0x80 {
            run += 1;
            if run >= 4 {
                return false;
            }
        } else {
            run = 0;
        }
    }
    true
}

/// The frame as the models hold it. `raw` is the encoding of the frame, used for the range bytes of an ACK.
fn frame_json(f: &Frame<'_>, raw: &[u8]) -> String {
    match f {
        Frame::Padding { len } => format!(r#"{{"k":"Padding","len":{len}}}"#),
        Frame::Ping => r#"{"k":"Ping"}"#.into(),
        Frame::Sleep => r#"{"k":"Sleep"}"#.into(),
        Frame::Wake => r#"{"k":"Wake"}"#.into(),
        Frame::Ready => r#"{"k":"Ready"}"#.into(),
        Frame::Ack(a) => {
            let first = a.ranges().next().map_or(0, |r| a.largest() - *r.start());
            let extra = a.range_count() - 1;
            let head =
                1 + varint::encoded_len(a.largest()) + varint::encoded_len(extra as u64) + varint::encoded_len(first);
            format!(
                r#"{{"k":"Ack","largest":{},"first":{first},"extra":{extra},"tail":{}}}"#,
                a.largest(),
                arr(&raw[head..])
            )
        }
        Frame::ResetStream { id, error, final_size } => {
            format!(r#"{{"k":"ResetStream","id":{id},"error":{error},"fs":{final_size}}}"#)
        }
        Frame::StopSending { id, error } => format!(r#"{{"k":"StopSending","id":{id},"error":{error}}}"#),
        Frame::Stream {
            id,
            offset,
            fin,
            data,
            implicit_len,
        } => format!(
            r#"{{"k":"Stream","id":{id},"off":{offset},"fin":{fin},"data":{},"imp":{implicit_len}}}"#,
            arr(data)
        ),
        Frame::MaxStreamData { id, max } => format!(r#"{{"k":"MaxStreamData","id":{id},"max":{max}}}"#),
        Frame::MaxStreams { limit } => format!(r#"{{"k":"MaxStreams","limit":{limit}}}"#),
        Frame::PathChallenge(d) => format!(r#"{{"k":"PathChallenge","d":{}}}"#, arr(d)),
        Frame::PathResponse(d) => format!(r#"{{"k":"PathResponse","d":{}}}"#, arr(d)),
        Frame::Close { error } => format!(r#"{{"k":"Close","error":{error}}}"#),
        Frame::Datagram { data, implicit_len } => {
            format!(r#"{{"k":"Datagram","data":{},"imp":{implicit_len}}}"#, arr(data))
        }
        Frame::MtuProbeEcho { mtu } => format!(r#"{{"k":"MtuProbeEcho","mtu":{mtu}}}"#),
        Frame::Rekey(r) => format!(
            r#"{{"k":"Rekey","ans":{},"sh":{},"echo":{},"spn":{}}}"#,
            r.answer,
            arr(&r.share),
            arr(&r.echo),
            r.switch_pn
        ),
        Frame::NewTickets(b) => {
            let es: Vec<String> = b
                .entries()
                .iter()
                .map(|e| {
                    format!(
                        r#"{{"tid":{},"lt":[{},{}]}}"#,
                        arr(&e.tid),
                        e.lifetime_s >> 16,
                        e.lifetime_s & 0xffff
                    )
                })
                .collect();
            format!(r#"{{"k":"NewTickets","es":[{}]}}"#, es.join(","))
        }
        Frame::Extension { ty, body } => format!(r#"{{"k":"Extension","ty":{ty},"body":{}}}"#, arr(body)),
    }
}

/// Every number of the frame is below 2^28.
fn small(f: &Frame<'_>) -> bool {
    let nums: [u64; 3] = match f {
        Frame::Ack(a) => [a.largest(), 0, 0],
        Frame::ResetStream { id, error, final_size } => [*id, *error, *final_size],
        Frame::StopSending { id, error } => [*id, *error, 0],
        Frame::Stream { id, offset, .. } => [*id, *offset, 0],
        Frame::MaxStreamData { id, max } => [*id, *max, 0],
        Frame::MaxStreams { limit } => [*limit, 0, 0],
        Frame::Close { error } => [*error, 0, 0],
        Frame::Rekey(r) => [r.switch_pn, 0, 0],
        Frame::Extension { ty, .. } => [*ty, 0, 0],
        _ => [0; 3],
    };
    nums.iter().all(|v| *v < NARROW)
}

/// `Frame::write` into a writer that already holds `prefix` bytes and has `room` more: the bytes written, or the
/// error. A refusal must leave the buffer as it was.
fn enc_event(out: &mut Out, f: &Frame<'_>, raw: &[u8], room: usize, prefix: usize) -> Result<Vec<u8>, FrameError> {
    let mut buf = vec![0xaau8; prefix + room];
    let len = f.encoded_len();
    let (res, written) = {
        let mut w = Writer::new(&mut buf);
        w.put_slice(&vec![0x55u8; prefix]).unwrap();
        let res = f.write(&mut w);
        (res, w.written().len())
    };
    let fj = frame_json(f, raw);
    let narrow = small(f) && runs_ok(raw);
    match res {
        Ok(()) => {
            let b = buf[prefix..written].to_vec();
            assert_eq!(b.len(), len, "encoded_len is not what write wrote");
            assert!(buf[written..].iter().all(|x| *x == 0xaa));
            out.push(
                narrow,
                &format!(
                    r#"{{"t":"txfr","op":"enc","f":{fj},"cap":{room},"len":{len},"ok":true,"b":{}}}"#,
                    arr(&b)
                ),
            );
            Ok(b)
        }
        Err(e) => {
            assert_eq!(written, prefix, "a refused write moved the writer");
            assert!(buf[prefix..].iter().all(|x| *x == 0xaa), "a refused write wrote bytes");
            let (name, n) = tag(&e);
            out.push(
                narrow,
                &format!(
                    r#"{{"t":"txfr","op":"enc","f":{fj},"cap":{room},"len":{len},"ok":false,"err":"{name}","en":{n}}}"#
                ),
            );
            Err(e)
        }
    }
}

fn ranges_json<I: Iterator<Item = (u64, u64)>>(rs: I) -> String {
    let v: Vec<String> = rs.map(|(s, e)| format!("[{s},{e}]")).collect();
    format!("[{}]", v.join(","))
}

/// `Frame::decode` at the front of `b`: the frame and the bytes it took, or the error. A frame that decodes is
/// written again: it must come back as the bytes read, except the OFF bit of a STREAM frame at offset 0.
fn dec_event<'a>(out: &mut Out, b: &'a [u8]) -> Result<(Frame<'a>, usize), FrameError> {
    let mut r = Reader::new(b);
    let narrow = runs_ok(b);
    match Frame::decode(&mut r) {
        Ok(f) => {
            let n = r.position();
            assert!(n >= 1 && n <= b.len());
            let rg = match &f {
                Frame::Ack(a) => {
                    let got: Vec<(u64, u64)> = a.ranges().map(|r| (*r.start(), *r.end())).collect();
                    assert_eq!(got.len(), a.range_count());
                    ranges_json(got.into_iter())
                }
                _ => "[]".into(),
            };
            out.push(
                narrow,
                &format!(
                    r#"{{"t":"txfr","op":"dec","b":{},"ok":true,"f":{},"n":{n},"rg":{rg}}}"#,
                    arr(b),
                    frame_json(&f, &b[..n])
                ),
            );
            let again = enc_event(out, &f, &b[..n], n + 8, 0).expect("a decoded frame is refused by write");
            let off_bit = matches!(f, Frame::Stream { offset: 0, .. }) && b[0] & 0x04 != 0;
            if off_bit {
                assert_eq!(again.len() + 1, n);
            } else {
                assert_eq!(
                    &again[..],
                    &b[..n],
                    "a decoded frame is not written back as the bytes read"
                );
            }
            Ok((f, n))
        }
        Err(e) => {
            let (name, en) = tag(&e);
            assert_ne!(name, "other");
            out.push(
                narrow && en < NARROW,
                &format!(
                    r#"{{"t":"txfr","op":"dec","b":{},"ok":false,"err":"{name}","en":{en}}}"#,
                    arr(b)
                ),
            );
            Err(e)
        }
    }
}

/// `FrameIter` over `b`, beside a reader that decodes the same frames to learn where each one ends.
fn iter_event(out: &mut Out, b: &[u8]) {
    let mut r = Reader::new(b);
    let mut it = FrameIter::new(b);
    let mut items = Vec::new();
    let mut err = ("none".to_string(), 0u64);
    loop {
        let next = it.next();
        if r.is_empty() {
            assert!(next.is_none());
            break;
        }
        let start = r.position();
        match (Frame::decode(&mut r), next) {
            (Ok(f), Some(Ok(g))) => {
                assert_eq!(f, g);
                assert!(r.position() > start, "a frame took no byte");
                items.push(frame_json(&g, &b[start..r.position()]));
            }
            (Err(e), Some(Err(e2))) => {
                assert_eq!(e, e2);
                err = tag(&e);
                assert!(it.next().is_none(), "the iterator went on after an error");
                break;
            }
            _ => panic!("the iterator and the decoder disagree"),
        }
    }
    out.push(
        runs_ok(b) && err.1 < NARROW,
        &format!(
            r#"{{"t":"txfr","op":"iter","b":{},"fs":[{}],"e":"{}","en":{}}}"#,
            arr(b),
            items.join(","),
            err.0,
            err.1
        ),
    );
}

/// `write_ack` and `ack_len` on `rs`, into a buffer of `room` bytes.
fn ack_event(out: &mut Out, rs: &[(u64, u64)], room: usize) -> Result<Vec<u8>, FrameError> {
    let ranges = rs.iter().map(|&(s, e)| s..=e);
    let mut buf = vec![0xaau8; room];
    let (res, written) = {
        let mut w = Writer::new(&mut buf);
        let res = write_ack(&mut w, ranges.clone());
        (res, w.written().len())
    };
    let l = ack_len(ranges);
    let lj = match &l {
        Ok(n) => format!(r#""lok":true,"len":{n}"#),
        Err(e) => format!(r#""lok":false,"lerr":"{}""#, tag(e).0),
    };
    // the naive check: the first 32 ranges are non-empty, inside the packet-number space, descending, not touching
    let head = &rs[..rs.len().min(MAX_ACK_RANGES)];
    let valid = !head.is_empty()
        && head.iter().all(|(s, e)| s <= e && *e <= MAX_PN)
        && head
            .windows(2)
            .all(|w| w[1].1.checked_add(2).is_some_and(|x| x <= w[0].0));
    assert_eq!(l.is_ok(), valid, "ack_len and the naive check disagree on {rs:?}");
    let narrow = rs.iter().all(|(s, e)| *s < NARROW && *e < NARROW);
    let rj = ranges_json(rs.iter().copied());
    match res {
        Ok(()) => {
            let b = buf[..written].to_vec();
            assert_eq!(l, Ok(b.len()), "ack_len is not what write_ack wrote");
            out.push(
                narrow,
                &format!(
                    r#"{{"t":"txfr","op":"ack","rs":{rj},"cap":{room},{lj},"ok":true,"b":{}}}"#,
                    arr(&b)
                ),
            );
            Ok(b)
        }
        Err(e) => {
            assert!(
                written == 0 && buf.iter().all(|x| *x == 0xaa),
                "a refused write_ack wrote bytes"
            );
            if let Err(le) = &l {
                assert_eq!(*le, e);
                assert_eq!(e, FrameError::Ack);
            }
            let (name, n) = tag(&e);
            out.push(
                narrow,
                &format!(r#"{{"t":"txfr","op":"ack","rs":{rj},"cap":{room},{lj},"ok":false,"err":"{name}","en":{n}}}"#),
            );
            Err(e)
        }
    }
}

fn num(rng: &mut SplitMix64, wide: bool) -> u64 {
    if wide {
        let j = rng.next_u64() % 65;
        let base = if j == 64 { u64::MAX } else { 1u64 << j };
        match rng.next_u64() % 4 {
            0 => base.wrapping_sub(1),
            1 => base,
            2 => base.wrapping_add(1),
            _ => rng.next_u64() >> (rng.next_u64() % 64),
        }
    } else {
        const EDGES: [u64; 9] = [0, 1, 127, 128, 16383, 16384, (1 << 21) - 1, 1 << 21, NARROW - 1];
        if rng.next_u64().is_multiple_of(3) {
            rng.next_u64() % NARROW
        } else {
            EDGES[(rng.next_u64() % 9) as usize]
        }
    }
}

/// Random bytes; the narrow ones never have two bytes in a row with the high bit.
fn bytes(rng: &mut SplitMix64, n: usize, wide: bool) -> Vec<u8> {
    let mut v = vec![0u8; n];
    rng.fill(&mut v);
    if !wide {
        for i in 1..n {
            if v[i - 1] >= 0x80 {
                v[i] &= 0x7f;
            }
        }
    }
    v
}

const KINDS: u64 = 18;

fn gen_frame<'a>(rng: &mut SplitMix64, wide: bool, kind: u64, data: &'a [u8]) -> Frame<'a> {
    let arr8 = |rng: &mut SplitMix64| -> [u8; 8] { bytes(rng, 8, wide).try_into().unwrap() };
    match kind {
        0 => Frame::Padding {
            len: match rng.next_u64() % 8 {
                0 => 0,
                1 => 64,
                2 => 65,
                3 => 128,
                4 => 129,
                _ => 1 + (rng.next_u64() % 200) as usize,
            },
        },
        1 => Frame::Ping,
        2 => Frame::Sleep,
        3 => Frame::Wake,
        4 => Frame::Ready,
        5 => Frame::ResetStream {
            id: num(rng, wide),
            error: num(rng, wide),
            final_size: num(rng, wide),
        },
        6 => Frame::StopSending {
            id: num(rng, wide),
            error: num(rng, wide),
        },
        7 => Frame::MaxStreamData {
            id: num(rng, wide),
            max: num(rng, wide),
        },
        8 => Frame::MaxStreams { limit: num(rng, wide) },
        9 => Frame::Close { error: num(rng, wide) },
        10 => Frame::PathChallenge(arr8(rng)),
        11 => Frame::PathResponse(arr8(rng)),
        12 => Frame::MtuProbeEcho {
            mtu: match rng.next_u64() % 4 {
                0 => 0,
                1 => 1200,
                2 => u16::MAX,
                _ => rng.next_u64() as u16,
            },
        },
        13 => {
            let len = data.len() as u64;
            let offset = match (rng.next_u64() % 5, wide) {
                (0 | 1, _) => 0,
                (2, true) => MAX_STREAM_END - len,
                (3, true) => MAX_STREAM_END - len + 1,
                _ => num(rng, wide),
            };
            Frame::Stream {
                id: num(rng, wide),
                offset,
                fin: rng.next_u64().is_multiple_of(2),
                data,
                implicit_len: rng.next_u64().is_multiple_of(2),
            }
        }
        14 => Frame::Datagram {
            data,
            implicit_len: rng.next_u64().is_multiple_of(2),
        },
        15 => {
            let answer = rng.next_u64().is_multiple_of(2);
            // a request normally carries zeros; one in four carries an echo and a number that are not written
            let plain = !answer && !rng.next_u64().is_multiple_of(4);
            Frame::Rekey(Rekey {
                answer,
                share: bytes(rng, 32, wide).try_into().unwrap(),
                echo: if plain { [0; 8] } else { arr8(rng) },
                switch_pn: if plain { 0 } else { num(rng, wide) },
            })
        }
        16 => {
            let mut batch = TicketBatch::new();
            for _ in 0..rng.next_u64() % 5 {
                assert!(batch.push(TicketEntry {
                    tid: bytes(rng, 16, wide).try_into().unwrap(),
                    lifetime_s: match rng.next_u64() % 4 {
                        0 => 0,
                        1 => u32::MAX,
                        _ => rng.next_u64() as u32,
                    },
                }));
            }
            Frame::NewTickets(batch)
        }
        _ => Frame::Extension {
            ty: match rng.next_u64() % 6 {
                0 => 0x40,
                1 => 0x40 + rng.next_u64() % 0x40,
                2 => 0x80 + rng.next_u64() % 0x4000,
                3 => rng.next_u64() % 0x40,
                _ => num(rng, wide).max(0x40),
            },
            body: data,
        },
    }
}

const RESTS: [&[u8]; 5] = [&[], &[1], &[0], &[0, 0, 9], &[0x80]];

/// What may follow the frame for it to be read back as itself.
fn sep(f: &Frame<'_>, rest: &[u8]) -> bool {
    match f {
        Frame::Padding { .. } => rest.first() != Some(&0),
        Frame::Stream { implicit_len: true, .. } | Frame::Datagram { implicit_len: true, .. } => rest.is_empty(),
        _ => true,
    }
}

fn greedy(f: &Frame<'_>) -> bool {
    matches!(
        f,
        Frame::Padding { .. } | Frame::Stream { implicit_len: true, .. } | Frame::Datagram { implicit_len: true, .. }
    )
}

/// The frame as it is read back: a REKEY request carries zeros.
fn normal<'a>(f: &Frame<'a>) -> Frame<'a> {
    match f {
        Frame::Rekey(r) if !r.answer => Frame::Rekey(Rekey {
            answer: false,
            share: r.share,
            echo: [0; 8],
            switch_pn: 0,
        }),
        other => other.clone(),
    }
}

/// Cuts, changed bytes and appended bytes of an encoding.
fn damage(rng: &mut SplitMix64, out: &mut Out, enc: &[u8], known_end: bool) {
    let len = enc.len();
    let cuts: Vec<usize> = if len <= 48 {
        (1..len).collect()
    } else {
        let mut v: Vec<usize> = (1..24).collect();
        v.push(len - 1);
        v.extend((0..23).map(|_| 1 + (rng.next_u64() as usize) % (len - 1)));
        v
    };
    for n in cuts {
        let r = dec_event(out, &enc[..n]);
        if known_end {
            assert!(
                matches!(r, Err(FrameError::Wire(WireError::Truncated { .. }))),
                "a cut of a frame with a known end is not Truncated"
            );
        }
    }
    for _ in 0..12 {
        let mut b = enc.to_vec();
        let i = (rng.next_u64() as usize) % len.min(14);
        b[i] = match rng.next_u64() % 9 {
            0 => 0,
            1 => 1,
            2 => 2,
            3 => 5,
            4 => 12,
            5 => 64,
            6 => 128,
            7 => 255,
            _ => rng.next_u64() as u8,
        };
        let _ = dec_event(out, &b);
    }
    for x in [0u8, 1, 0x80] {
        let mut b = enc.to_vec();
        b.push(x);
        let _ = dec_event(out, &b);
    }
}

fn exercise(rng: &mut SplitMix64, out: &mut Out, f: &Frame<'_>) {
    let len = f.encoded_len();
    let Ok(enc) = enc_event(out, f, &[], len + 16, 3) else {
        // refused: the same refusal whatever the room
        let e0 = enc_event(out, f, &[], 0, 0).unwrap_err();
        let e1 = enc_event(out, f, &[], len.min(400), 1).unwrap_err();
        assert_eq!(e0, e1);
        return;
    };
    assert_eq!(enc.len(), len);
    if len == 0 {
        return;
    }
    for room in [0, len - 1, (rng.next_u64() as usize) % len] {
        let e = enc_event(out, f, &[], room, (rng.next_u64() % 4) as usize).unwrap_err();
        assert_eq!(e, FrameError::Wire(WireError::BufferTooSmall { needed: len - room }));
    }
    assert_eq!(enc_event(out, f, &[], len, 0).unwrap(), enc);
    let want = normal(f);
    for rest in RESTS {
        let mut b = enc.clone();
        b.extend_from_slice(rest);
        let got = dec_event(out, &b);
        if sep(f, rest) {
            let (g, n) = got.expect("the encoding of a frame does not decode");
            assert_eq!(n, len, "decode did not take exactly the bytes of the frame");
            assert_eq!(g, want, "decode did not give the frame back");
        }
    }
    damage(rng, out, &enc, !greedy(f));
    if out.pool.len() < 600 {
        out.pool.push(enc);
    }
}

/// A valid list of `count` ranges, highest first.
fn valid_ranges(rng: &mut SplitMix64, wide: bool, count: usize) -> Vec<(u64, u64)> {
    let top = match (rng.next_u64() % 4, wide) {
        (0, true) => MAX_PN,
        (1, true) => MAX_PN - rng.next_u64() % 1000,
        (_, true) => rng.next_u64() >> (2 + rng.next_u64() % 60),
        (0, false) => NARROW - 1,
        _ => rng.next_u64() % NARROW,
    };
    let mut rs = Vec::new();
    let mut end = top;
    for _ in 0..count {
        let span = match rng.next_u64() % 4 {
            0 => 0,
            1 => rng.next_u64() % 200,
            2 => rng.next_u64() % 20000,
            _ => rng.next_u64() % 3,
        }
        .min(end);
        let start = end - span;
        rs.push((start, end));
        let gap = match rng.next_u64() % 4 {
            0 => 0,
            1 => rng.next_u64() % 200,
            2 => rng.next_u64() % 20000,
            _ => rng.next_u64() % 2,
        };
        match start.checked_sub(gap + 2) {
            Some(e) => end = e,
            None => break,
        }
    }
    rs
}

fn ack_case(rng: &mut SplitMix64, out: &mut Out, rs: &[(u64, u64)]) {
    let Ok(enc) = ack_event(out, rs, 1024) else {
        assert!(ack_event(out, rs, 0).is_err());
        return;
    };
    let len = enc.len();
    for room in [0, len - 1, (rng.next_u64() as usize) % len] {
        let e = ack_event(out, rs, room).unwrap_err();
        assert_eq!(e, FrameError::Wire(WireError::BufferTooSmall { needed: len - room }));
    }
    assert_eq!(ack_event(out, rs, len).unwrap(), enc);
    for rest in RESTS {
        let mut b = enc.clone();
        b.extend_from_slice(rest);
        let (f, n) = dec_event(out, &b).expect("an ACK that write_ack wrote does not decode");
        assert_eq!(n, len);
        let Frame::Ack(a) = &f else { panic!("not an ACK") };
        let got: Vec<(u64, u64)> = a.ranges().map(|r| (*r.start(), *r.end())).collect();
        assert_eq!(
            &got[..],
            &rs[..rs.len().min(MAX_ACK_RANGES)],
            "the ranges did not come back"
        );
        assert_eq!(f.encoded_len(), len);
    }
    damage(rng, out, &enc, true);
    if out.pool.len() < 600 {
        out.pool.push(enc);
    }
}

fn put_v(b: &mut Vec<u8>, v: u64) {
    let mut tmp = [0u8; 9];
    let n = varint::encode(v, &mut tmp).unwrap();
    b.extend_from_slice(&tmp[..n]);
}

#[test]
fn frame_codecs_match_the_models() {
    let mut rng = SplitMix64::new(0x4652_0001);
    let mut out = Out::default();

    // every frame kind, narrow and wide numbers
    for round in 0..36u64 {
        let wide = round % 3 == 2;
        for kind in 0..KINDS {
            let n = match rng.next_u64() % 6 {
                0 => 0,
                1 => 1,
                2 => 127 + (rng.next_u64() % 3) as usize,
                _ => (rng.next_u64() % 40) as usize,
            };
            let data = bytes(&mut rng, n, wide);
            let f = gen_frame(&mut rng, wide, kind, &data);
            exercise(&mut rng, &mut out, &f);
        }
    }

    // ACK: valid lists of 1 to 40 ranges, and each broken in one place
    for round in 0..60u64 {
        let wide = round % 3 == 2;
        let count = match round % 6 {
            0 => 1,
            1 => 2,
            2 => 31 + (rng.next_u64() % 4) as usize,
            3 => 40,
            _ => 1 + (rng.next_u64() % 12) as usize,
        };
        let rs = valid_ranges(&mut rng, wide, count);
        ack_case(&mut rng, &mut out, &rs);
        for _ in 0..4 {
            let mut bad = rs.clone();
            let i = (rng.next_u64() as usize) % bad.len();
            match rng.next_u64() % 7 {
                0 => bad[i] = (bad[i].1.saturating_add(1), bad[i].1),
                1 if i > 0 => bad[i].1 = bad[i - 1].0.saturating_sub(1),
                2 if i > 0 => bad[i].1 = bad[i - 1].0,
                3 if i > 0 => bad.swap(i, i - 1),
                4 if wide => bad[i].1 = MAX_PN + 1 + rng.next_u64() % 5,
                5 => bad.truncate(i),
                _ => bad.push((0, 0)),
            }
            ack_case(&mut rng, &mut out, &bad);
        }
    }
    ack_case(&mut rng, &mut out, &[]);
    ack_case(&mut rng, &mut out, &[(0, 0)]);
    ack_case(&mut rng, &mut out, &[(MAX_PN, MAX_PN)]);
    ack_case(&mut rng, &mut out, &[(0, MAX_PN)]);
    ack_case(&mut rng, &mut out, &[(3, 3), (0, 1)]);
    ack_case(&mut rng, &mut out, &[(2, 3), (0, 0)]);

    // garbage behind every type up to 0x45, an empty input, and varint faults in the type
    let _ = dec_event(&mut out, &[]);
    for t in 0..0x46u8 {
        for k in 0..6 {
            let n = if k == 0 { 0 } else { (rng.next_u64() % 44) as usize };
            let mut b = vec![t];
            b.extend(bytes(&mut rng, n, k % 2 == 1));
            let _ = dec_event(&mut out, &b);
        }
    }
    for b in [
        &[0x80u8, 0x00][..],
        &[0x80, 0x01, 0x00],
        &[0x81, 0x00],
        &[0xc0, 0x00, 0x00],
        &[0x80],
        &[0xff, 0xff, 0xff],
        &[0x80; 8],
        &[0x80; 9],
        &[0xff; 12],
        &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0, 0],
    ] {
        let _ = dec_event(&mut out, b);
    }
    // ACK bodies built from small varints: ranges below packet number 0, too many ranges, short tails
    for _ in 0..500 {
        let mut b = vec![2u8];
        let largest = rng.next_u64() % 300;
        let extra = match rng.next_u64() % 8 {
            0 => 31 + rng.next_u64() % 3,
            _ => rng.next_u64() % 5,
        };
        put_v(&mut b, largest);
        put_v(&mut b, extra);
        put_v(&mut b, rng.next_u64() % (largest + 3));
        for _ in 0..(extra + rng.next_u64() % 2).saturating_sub(rng.next_u64() % 2) {
            put_v(&mut b, rng.next_u64() % 40);
            put_v(&mut b, rng.next_u64() % 40);
        }
        let _ = dec_event(&mut out, &b);
    }
    // REKEY kinds, ticket counts, STREAM headers
    for _ in 0..200 {
        let n = 30 + (rng.next_u64() % 16) as usize;
        let mut b = vec![0x3d, (rng.next_u64() % 4) as u8];
        b.extend(bytes(&mut rng, n, false));
        let _ = dec_event(&mut out, &b);
        let count = (rng.next_u64() % 7) as usize;
        let n = (count * 20 + 2).saturating_sub((rng.next_u64() % 4) as usize);
        let mut b = vec![0x3f, count as u8];
        b.extend(bytes(&mut rng, n, false));
        let _ = dec_event(&mut out, &b);
        let mut b = vec![8 + (rng.next_u64() % 8) as u8];
        put_v(&mut b, num(&mut rng, false));
        put_v(&mut b, rng.next_u64() % 6);
        let n = (rng.next_u64() % 8) as usize;
        b.extend(bytes(&mut rng, n, false));
        let _ = dec_event(&mut out, &b);
    }
    // a STREAM frame at the stream end, and one byte beyond it
    for extra in 0..2u64 {
        let mut b = vec![0x0e];
        put_v(&mut b, 5);
        put_v(&mut b, MAX_STREAM_END - 3 + extra);
        put_v(&mut b, 3);
        b.extend([7, 8, 9]);
        let r = dec_event(&mut out, &b);
        assert_eq!(r.is_ok(), extra == 0);
    }

    // payloads of several frames through the iterator, whole, damaged and random
    let pool = std::mem::take(&mut out.pool);
    for _ in 0..1500 {
        let mut b = Vec::new();
        for _ in 0..=rng.next_u64() % 6 {
            let e = &pool[(rng.next_u64() as usize) % pool.len()];
            if e.len() <= 200 {
                b.extend_from_slice(e);
            }
        }
        iter_event(&mut out, &b);
        if !b.is_empty() {
            let i = (rng.next_u64() as usize) % b.len();
            b[i] = rng.next_u64() as u8;
            iter_event(&mut out, &b);
        }
    }
    for _ in 0..300 {
        let n = (rng.next_u64() % 30) as usize;
        let wide = rng.next_u64().is_multiple_of(2);
        iter_event(&mut out, &bytes(&mut rng, n, wide));
    }
    iter_event(&mut out, &[]);

    // the overheads the packet builder uses to fit a frame
    for i in 0..400u64 {
        let wide = i % 3 == 2;
        let (id, off) = (num(&mut rng, wide), if i % 4 == 0 { 0 } else { num(&mut rng, wide) });
        let dlen = (num(&mut rng, false) % 70000) as usize;
        let imp = i % 2 == 0;
        let so = stream_overhead(id, off, dlen, imp);
        let d = datagram_overhead(dlen, imp);
        out.push(
            id < NARROW && off < NARROW,
            &format!(r#"{{"t":"txfr","op":"ovh","id":{id},"off":{off},"dlen":{dlen},"imp":{imp},"so":{so},"do":{d}}}"#),
        );
    }

    for kind in [
        "Padding",
        "Ping",
        "Ack",
        "ResetStream",
        "StopSending",
        "Stream",
        "MaxStreamData",
        "MaxStreams",
        "PathChallenge",
        "PathResponse",
        "Close",
        "Datagram",
        "MtuProbeEcho",
        "Sleep",
        "Wake",
        "Rekey",
        "Ready",
        "NewTickets",
        "Extension",
    ] {
        let dec = format!(r#""ok":true,"f":{{"k":"{kind}""#);
        assert!(
            out.narrow.contains(&dec),
            "no {kind} frame was decoded in the narrow trace"
        );
    }
    for err in [
        "Truncated",
        "VarintNonMinimal",
        "UnknownType",
        "Ack",
        "TooManyRanges",
        "RekeyKind",
        "ticket count",
        "BufferTooSmall",
    ] {
        let e = format!(r#""err":"{err}""#);
        assert!(out.narrow.contains(&e), "the narrow trace has no {err}");
    }
    for err in ["VarintTooLong", "VarintOverflow", "StreamEnd"] {
        let e = format!(r#""err":"{err}""#);
        assert!(out.wide.contains(&e), "the wide trace has no {err}");
    }
    assert!(out.narrow_events > 20_000 && out.events > out.narrow_events);
    println!("trace_frame: {} events, {} narrow", out.events, out.narrow_events);
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        let dir = std::path::Path::new(&dir);
        std::fs::write(dir.join("frame.ndjson"), &out.narrow).unwrap();
        std::fs::write(dir.join("frame_wide.ndjson"), &out.wide).unwrap();
    }
}
