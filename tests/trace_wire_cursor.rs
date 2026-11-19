//! Trace generation for the TLA+ specification of the wire cursors (`WireCursor.tla`): the `Reader` and the `Writer`
//! of `pinc-wire`, recorded as ndjson (`tla/wire_cursor.ndjson`) for the trace check (`TraceWireCursor.tla`).
//!
//! The real code runs on the same boundary sets the model enumerates (every short input over a small alphabet and
//! eight longer ones, a call from every position; every buffer of 0 to 10 bytes, a call from every position) and on
//! seeded random runs. A `u64` is written as four 16-bit limbs, least significant first, which `U64.tla` reads. Every
//! call is also checked here against a naive reference (the bytes taken, the big-endian value, the exact shortfall,
//! nothing consumed or written on a refusal), so the test is meaningful without the proof tools. The file goes to
//! `tla/` under `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop,
    clippy::too_many_lines,
    clippy::panic,
    clippy::many_single_char_names
)]

use std::collections::BTreeSet;
use std::fmt::Write as _;

use pinc_tests::SplitMix64;
use pinc_wire::{Reader, WireError, Writer, varint};

/// A value below `n` (`n > 0`).
fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

/// A `u64` as the four 16-bit limbs `U64.tla` reads.
fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

/// A byte list as a JSON array.
fn arr(b: &[u8]) -> String {
    let body: Vec<String> = b.iter().map(u8::to_string).collect();
    format!("[{}]", body.join(","))
}

/// The class of an error, for the coverage check.
fn kind(e: &WireError) -> &'static str {
    match e {
        WireError::Truncated { .. } => "truncated",
        WireError::VarintTooLong => "toolong",
        WireError::VarintNonMinimal => "nonminimal",
        WireError::BufferTooSmall { .. } => "small",
        WireError::VarintOverflow => "overflow",
        _ => "other",
    }
}

/// What the runs reached: `(op, outcome)` pairs, and the two refusals with room or input left.
#[derive(Default)]
struct Seen {
    reached: BTreeSet<(&'static str, &'static str)>,
    short_with_bytes_left: bool,
    small_with_room_left: bool,
}

// ---------------------------------------------------------------- reader

#[derive(Clone, Copy)]
enum RCall {
    Peek,
    Bytes(usize),
    U8,
    U16,
    U32,
    U64,
    Varint,
}

impl RCall {
    fn op(self) -> &'static str {
        match self {
            Self::Peek => "peek",
            Self::Bytes(_) => "bytes",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::Varint => "varint",
        }
    }
}

/// What a successful read returned.
enum Val {
    Byte(u8),
    Bytes(Vec<u8>),
    Num(u64),
}

/// One reader call: made, checked against the naive reference, and recorded.
fn rcall(r: &mut Reader<'_>, input: &[u8], c: RCall, seen: &mut Seen) -> String {
    let (before, left) = (r.position(), r.remaining());
    let (res, asked): (Result<Val, WireError>, usize) = match c {
        RCall::Peek => (r.peek_u8().map(Val::Byte), 1),
        RCall::Bytes(n) => (r.read_bytes(n).map(|b| Val::Bytes(b.to_vec())), n),
        RCall::U8 => (r.read_u8().map(|v| Val::Num(u64::from(v))), 1),
        RCall::U16 => (r.read_u16().map(|v| Val::Num(u64::from(v))), 2),
        RCall::U32 => (r.read_u32().map(|v| Val::Num(u64::from(v))), 4),
        RCall::U64 => (r.read_u64().map(Val::Num), 8),
        RCall::Varint => (r.read_varint().map(Val::Num), 1),
    };
    assert_eq!(r.position() + r.remaining(), input.len());
    let exact_short = !matches!(c, RCall::Peek | RCall::Varint);
    if exact_short {
        assert_eq!(
            res.is_ok(),
            asked <= left,
            "a read does not succeed exactly when the input holds it"
        );
    }
    let (r_json, outcome) = match &res {
        Ok(v) => {
            let taken = match (c, v) {
                (RCall::Peek, Val::Byte(b)) => {
                    assert_eq!(*b, input[before]);
                    0
                }
                (RCall::Bytes(n), Val::Bytes(b)) => {
                    assert_eq!(&input[before..before + n], b.as_slice());
                    n
                }
                (RCall::Varint, Val::Num(x)) => {
                    let mut scratch = [0u8; 10];
                    let k = varint::encode(*x, &mut scratch).unwrap();
                    assert_eq!(
                        &scratch[..k],
                        &input[before..before + k],
                        "a varint is not the bytes it read"
                    );
                    k
                }
                (_, Val::Num(x)) => {
                    let mut be = [0u8; 8];
                    be[8 - asked..].copy_from_slice(&input[before..before + asked]);
                    assert_eq!(u64::from_be_bytes(be), *x);
                    asked
                }
                _ => panic!("a read returned the wrong kind of value"),
            };
            assert_eq!(
                r.position(),
                before + taken,
                "the position did not advance by the bytes taken"
            );
            let j = match v {
                Val::Byte(b) => format!(r#"{{"ok":true,"b":{b}}}"#),
                Val::Bytes(b) => format!(r#"{{"ok":true,"bytes":{}}}"#, arr(b)),
                Val::Num(x) => format!(r#"{{"ok":true,"v":{}}}"#, limbs(*x)),
            };
            (j, "ok")
        }
        Err(e) => {
            assert_eq!(
                (r.position(), r.remaining()),
                (before, left),
                "a refused read consumed input"
            );
            let j = match *e {
                WireError::Truncated { needed } => {
                    if exact_short {
                        assert_eq!(asked.checked_sub(left), Some(needed), "the shortfall is not exact");
                    } else {
                        assert_eq!(needed, 1);
                    }
                    seen.short_with_bytes_left |= left > 0;
                    format!(r#"{{"ok":false,"err":"truncated","needed":{}}}"#, limbs(needed as u64))
                }
                WireError::VarintTooLong if matches!(c, RCall::Varint) => r#"{"ok":false,"err":"toolong"}"#.to_owned(),
                WireError::VarintNonMinimal if matches!(c, RCall::Varint) => {
                    r#"{"ok":false,"err":"nonminimal"}"#.to_owned()
                }
                other => panic!("a read returned {other:?}, which the reader cannot"),
            };
            (j, kind(e))
        }
    };
    seen.reached.insert((c.op(), outcome));
    let n = if let RCall::Bytes(n) = c {
        format!(r#","n":{}"#, limbs(n as u64))
    } else {
        String::new()
    };
    format!(
        r#"{{"op":"{}"{n},"r":{r_json},"pos":{},"rem":{}}}"#,
        c.op(),
        r.position(),
        r.remaining()
    )
}

/// One reader run: a fresh reader over `input`, the calls in order.
fn reader_run(input: &[u8], calls: &[RCall], out: &mut String, seen: &mut Seen) {
    let mut r = Reader::new(input);
    let recorded: Vec<String> = calls.iter().map(|&c| rcall(&mut r, input, c, seen)).collect();
    let _ = writeln!(
        out,
        r#"{{"t":"rrun","in":{},"calls":[{}]}}"#,
        arr(input),
        recorded.join(",")
    );
}

/// The 93 inputs of the boundary runs.
fn reader_inputs() -> Vec<Vec<u8>> {
    let alphabet = [0u8, 1, 128, 255];
    let mut inputs: Vec<Vec<u8>> = vec![Vec::new()];
    let mut layer: Vec<Vec<u8>> = vec![Vec::new()];
    for _ in 0..3 {
        layer = layer
            .iter()
            .flat_map(|p| {
                alphabet.iter().map(move |&b| {
                    let mut v = p.clone();
                    v.push(b);
                    v
                })
            })
            .collect();
        inputs.extend(layer.iter().cloned());
    }
    inputs.push((1..=8).collect());
    inputs.push((1..=9).collect());
    inputs.push(vec![255; 8]);
    inputs.push([vec![128; 8], vec![1]].concat());
    inputs.push([vec![255; 8], vec![127]].concat());
    inputs.push(vec![255; 9]);
    inputs.push([vec![128; 8], vec![0]].concat());
    inputs.push(vec![128; 10]);
    inputs
}

fn reader_boundary(out: &mut String, seen: &mut Seen) -> usize {
    let mut calls = vec![RCall::Peek];
    calls.extend([0, 1, 2, 3, 4, 8, 9, 10, usize::MAX].map(RCall::Bytes));
    calls.extend([RCall::U8, RCall::U16, RCall::U32, RCall::U64, RCall::Varint]);
    assert_eq!(calls.len(), 15);
    let mut runs = 0;
    for input in reader_inputs() {
        for p in 0..=input.len() {
            for &c in &calls {
                let mut r = Reader::new(&input);
                let a = rcall(&mut r, &input, RCall::Bytes(p), seen);
                assert!(a.contains(r#""ok":true"#), "a read of the bytes held failed");
                let b = rcall(&mut r, &input, c, seen);
                let _ = writeln!(out, r#"{{"t":"rrun","in":{},"calls":[{a},{b}]}}"#, arr(&input));
                runs += 1;
            }
        }
    }
    runs
}

fn reader_random(out: &mut String, seen: &mut Seen) {
    let mut rng = SplitMix64::traced(0x5743_5552);
    for i in 0..300u32 {
        let len = below(&mut rng, 25) as usize;
        let mut input = vec![0u8; len];
        if i % 2 == 0 {
            rng.fill(&mut input);
        } else {
            for b in &mut input {
                *b = [0u8, 1, 127, 128, 255][below(&mut rng, 5) as usize];
            }
        }
        let count = 1 + below(&mut rng, 12);
        let mut calls = Vec::new();
        for _ in 0..count {
            calls.push(match below(&mut rng, 7) {
                0 => RCall::Peek,
                1 => RCall::Bytes(if below(&mut rng, 16) == 0 {
                    usize::MAX
                } else {
                    below(&mut rng, len as u64 + 3) as usize
                }),
                2 => RCall::U8,
                3 => RCall::U16,
                4 => RCall::U32,
                5 => RCall::U64,
                _ => RCall::Varint,
            });
        }
        reader_run(&input, &calls, out, seen);
    }
}

// ---------------------------------------------------------------- writer

#[derive(Clone)]
enum WCall {
    Slice(Vec<u8>),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    Varint(u64),
    Ensure(usize),
}

impl WCall {
    fn op(&self) -> &'static str {
        match self {
            Self::Slice(_) => "slice",
            Self::U8(_) => "u8",
            Self::U16(_) => "u16",
            Self::U32(_) => "u32",
            Self::U64(_) => "u64",
            Self::Varint(_) => "varint",
            Self::Ensure(_) => "ensure",
        }
    }

    /// The `ARG` field of the record.
    fn arg(&self) -> String {
        match self {
            Self::Slice(b) => format!(r#""b":{}"#, arr(b)),
            Self::U8(v) => format!(r#""v":{v}"#),
            Self::U16(v) => format!(r#""v":{}"#, limbs(u64::from(*v))),
            Self::U32(v) => format!(r#""v":{}"#, limbs(u64::from(*v))),
            Self::U64(v) | Self::Varint(v) => format!(r#""v":{}"#, limbs(*v)),
            Self::Ensure(n) => format!(r#""n":{}"#, limbs(*n as u64)),
        }
    }

    /// The bytes the call appends on success (none for `ensure`); `None` for a varint of 2^63 or more.
    fn bytes(&self) -> Option<Vec<u8>> {
        Some(match self {
            Self::Slice(b) => b.clone(),
            Self::U8(v) => vec![*v],
            Self::U16(v) => v.to_be_bytes().to_vec(),
            Self::U32(v) => v.to_be_bytes().to_vec(),
            Self::U64(v) => v.to_be_bytes().to_vec(),
            Self::Varint(v) => {
                let mut scratch = [0u8; 10];
                let k = varint::encode(*v, &mut scratch).ok()?;
                scratch[..k].to_vec()
            }
            Self::Ensure(_) => Vec::new(),
        })
    }
}

/// One writer call: made, checked against the naive reference, and recorded.
fn wcall(w: &mut Writer<'_>, cap: usize, c: &WCall, seen: &mut Seen) -> String {
    let (w0, r0) = (w.written().to_vec(), w.remaining());
    let res = match c {
        WCall::Slice(b) => w.put_slice(b),
        WCall::U8(v) => w.put_u8(*v),
        WCall::U16(v) => w.put_u16(*v),
        WCall::U32(v) => w.put_u32(*v),
        WCall::U64(v) => w.put_u64(*v),
        WCall::Varint(v) => w.put_varint(*v),
        WCall::Ensure(n) => w.ensure(*n),
    };
    assert_eq!(w.written().len() + w.remaining(), cap);
    let want = c.bytes();
    // the shortfall is the bytes asked, or for `ensure` the argument, less the room
    let asked = match c {
        WCall::Ensure(n) => *n,
        _ => want.as_ref().map_or(0, Vec::len),
    };
    if let WCall::Varint(v) = c {
        assert_eq!(want.is_none(), *v >= 1 << 63);
    }
    let (r_json, outcome) = match &res {
        Ok(()) => {
            let mut expect = w0.clone();
            expect.extend(want.as_ref().unwrap());
            if matches!(c, WCall::Ensure(_)) {
                assert_eq!(w.written(), w0.as_slice(), "ensure changed the content");
            } else {
                assert_eq!(
                    w.written(),
                    expect.as_slice(),
                    "a write is not the bytes given after the content before"
                );
            }
            assert!(asked <= r0, "a write succeeded without the room");
            (r#"{"ok":true}"#.to_owned(), "ok")
        }
        Err(e) => {
            assert_eq!(w.written(), w0.as_slice(), "a refused write changed the content");
            assert_eq!(w.remaining(), r0, "a refused write changed the room");
            let j = match *e {
                WireError::BufferTooSmall { needed } => {
                    assert!(want.is_some() && asked > r0);
                    assert_eq!(needed, asked - r0, "the shortfall is not exact");
                    seen.small_with_room_left |= r0 > 0;
                    format!(r#"{{"ok":false,"err":"small","needed":{}}}"#, limbs(needed as u64))
                }
                WireError::VarintOverflow => {
                    assert!(want.is_none());
                    r#"{"ok":false,"err":"overflow"}"#.to_owned()
                }
                other => panic!("a write returned {other:?}, which the writer cannot"),
            };
            (j, kind(e))
        }
    };
    seen.reached.insert((c.op(), outcome));
    format!(
        r#"{{"op":"{}",{},"r":{r_json},"written":{},"rem":{}}}"#,
        c.op(),
        c.arg(),
        arr(w.written()),
        w.remaining()
    )
}

/// One writer run: a buffer of `cap` fill bytes, a writer over it, the calls in order.
fn writer_run(cap: usize, calls: &[WCall], out: &mut String, seen: &mut Seen) {
    let mut buf = vec![0xAAu8; cap];
    let (recorded, used) = {
        let mut w = Writer::new(&mut buf);
        let recorded: Vec<String> = calls.iter().map(|c| wcall(&mut w, cap, c, seen)).collect();
        (recorded, w.written().len())
    };
    assert!(
        buf[used..].iter().all(|&b| b == 0xAA),
        "a write went past the written length"
    );
    let _ = writeln!(
        out,
        r#"{{"t":"wrun","cap":{cap},"calls":[{}],"buf":{}}}"#,
        recorded.join(","),
        arr(&buf)
    );
}

fn writer_boundary(out: &mut String, seen: &mut Seen) -> usize {
    let mut calls: Vec<WCall> = [0u8, 1, 2, 3, 9, 10, 11]
        .iter()
        .map(|&k| WCall::Slice((1..=k).collect()))
        .collect();
    calls.extend([
        WCall::U8(0xAB),
        WCall::U16(0x0102),
        WCall::U32(0x0102_0304),
        WCall::U64(0x0102_0304_0506_0708),
        WCall::U64(u64::MAX),
    ]);
    calls.extend([0, 127, 128, (1u64 << 63) - 1, 1 << 63, u64::MAX].map(WCall::Varint));
    calls.extend([0, 1, 10, 11, usize::MAX].map(WCall::Ensure));
    assert_eq!(calls.len(), 23);
    let mut runs = 0;
    for cap in 0..=10usize {
        for p in 0..=cap {
            for c in &calls {
                writer_run(cap, &[WCall::Slice(vec![9; p]), c.clone()], out, seen);
                runs += 1;
            }
        }
    }
    runs
}

fn writer_random(out: &mut String, seen: &mut Seen) {
    let mut rng = SplitMix64::traced(0x5743_5553);
    for _ in 0..300 {
        let cap = below(&mut rng, 41) as usize;
        let count = 1 + below(&mut rng, 12);
        let mut calls = Vec::new();
        for _ in 0..count {
            calls.push(match below(&mut rng, 7) {
                0 => {
                    let mut b = vec![0u8; below(&mut rng, 12) as usize];
                    rng.fill(&mut b);
                    WCall::Slice(b)
                }
                1 => WCall::U8(rng.next_u64() as u8),
                2 => WCall::U16(rng.next_u64() as u16),
                3 => WCall::U32(rng.next_u64() as u32),
                4 => WCall::U64(rng.next_u64()),
                5 => {
                    let v = rng.next_u64();
                    WCall::Varint(v >> below(&mut rng, 64))
                }
                _ => WCall::Ensure(below(&mut rng, cap as u64 + 4) as usize),
            });
        }
        writer_run(cap, &calls, out, seen);
    }
}

#[test]
fn wire_cursor_traces_are_consistent_with_the_code() {
    let (mut out, mut seen) = (String::new(), Seen::default());
    assert_eq!(reader_inputs().len(), 93);
    assert_eq!(reader_boundary(&mut out, &mut seen), 5880);
    reader_random(&mut out, &mut seen);
    assert_eq!(writer_boundary(&mut out, &mut seen), 1518);
    writer_random(&mut out, &mut seen);
    if !pinc_tests::soaking() {
        for op in ["peek", "bytes", "u8", "u16", "u32", "u64", "varint"] {
            for outcome in ["ok", "truncated"] {
                assert!(
                    seen.reached.contains(&(op, outcome)),
                    "the reader never reached {outcome} on {op}"
                );
            }
        }
        for outcome in ["toolong", "nonminimal"] {
            assert!(
                seen.reached.contains(&("varint", outcome)),
                "the reader never reached {outcome}"
            );
        }
        assert!(seen.short_with_bytes_left, "no read was refused with bytes left");
        for op in ["slice", "u8", "u16", "u32", "u64", "varint", "ensure"] {
            for outcome in ["ok", "small"] {
                assert!(
                    seen.reached.contains(&(op, outcome)),
                    "the writer never reached {outcome} on {op}"
                );
            }
        }
        assert!(seen.small_with_room_left, "no write was refused with room left");
        assert!(seen.reached.contains(&("varint", "overflow")), "no varint overflowed");
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = std::path::Path::new(&dir).join("tla");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("wire_cursor.ndjson"), &out).unwrap();
    }
}
