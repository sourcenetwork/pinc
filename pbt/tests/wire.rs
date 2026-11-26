//! `pinc-wire`: the unsigned varint, the strict DAG-CBOR codec, `Reader`, `Writer` and `Hlc`.
//!
//! Where the expected behaviour comes from:
//! - the module documentation of `pinc_wire::varint`, "an encoding is at most 9 bytes, the value is below 2^63, and
//!   the encoding is minimal. `decode` accepts exactly what `encode` produces."
//! - `pinc_wire::cbor`: "the decoder accepts only the canonical DAG-CBOR subset (minimal arguments, definite lengths,
//!   valid UTF-8, 64-bit finite floats, only tag 42 over a `0x00`-prefixed byte string, text map keys unique and in
//!   length-then-bytewise order) and the encoder emits exactly that subset, so decode then encode is the identity."
//!   and "Map keys are checked wherever a map is walked: by `MapReader` and by `Decoder::skip_value`".
//! - `pinc_wire::cbor::Encoder`: "Every method is atomic: on `WireError::BufferTooSmall` nothing is written."
//! - `pinc_wire::reader`: "every read checks bounds first and, on failure, consumes nothing and returns
//!   `WireError::Truncated`"; `pinc_wire::writer`: "a write that does not fit fails with `BufferTooSmall` and leaves
//!   the written content and position unchanged".
//! - `pinc_wire::hlc`: "`Hlc::tick` and `Hlc::observe` return a value strictly greater than their receiver (until the
//!   32-bit counter saturates ...) and never below the physical reading they are given ... Every operation is
//!   saturating, so none panics."

use std::ops::ControlFlow;

use ephyra::prelude::*;
use ephyra::{check_generator, gens};
use pinc_pbt::{bytes, mangle, shrink_bytes};
use pinc_wire::cbor::{Decoder, Encoder, Item, MAX_DEPTH, MapReader, head_len};
use pinc_wire::hlc::Hlc;
use pinc_wire::{Reader, WireError, Writer, varint};

/// Values across every encoded length: uniform values are almost all 9 bytes long, so the length is drawn first.
fn varint_values() -> impl Gen<Value = u64> {
    gens::frequency(vec![
        (4, gens::dependent(gens::int(0u32..=62), |bits| gens::int(0u64..=(1u64 << bits))).map(|(_, v)| v).boxed()),
        (1, gens::edges(0u64..=(1u64 << 63) - 1).boxed()),
        (1, gens::int(0u64..=u64::MAX).boxed()),
    ])
}

#[ephyra::test(gen = varint_values(), tests = 20_000)]
fn varint_decode_inverts_encode(value: u64) {
    let mut buf = [0xaau8; varint::MAX_LEN + 1];
    match varint::encode(value, &mut buf) {
        Ok(n) => {
            assert!(value < 1 << 63, "a value of 2^63 or more was encoded");
            assert_eq!(n, varint::encoded_len(value));
            assert!(n <= varint::MAX_LEN);
            assert_eq!(buf.get(n), Some(&0xaa), "encode wrote past the length it returned");
            assert_eq!(varint::decode(&buf), Ok((value, n)));
        },
        Err(e) => {
            assert!(value >= 1 << 63, "an encodable value was refused: {e:?}");
            assert_eq!(buf, [0xaau8; varint::MAX_LEN + 1], "a refused encode touched the buffer");
        },
    }
}

#[ephyra::test(gen = bytes(12), tests = 50_000)]
fn varint_decode_accepts_exactly_what_encode_produces(input: Vec<u8>) {
    let Ok((value, used)) = varint::decode(&input) else { return };
    let mut buf = [0u8; varint::MAX_LEN];
    let n = varint::encode(value, &mut buf);
    assert_eq!(n, Ok(used), "decode accepted {used} bytes that encode does not produce for {value}");
    assert_eq!(buf.get(..used), input.get(..used));
}

// ---------------------------------------------------------------------------------------------------------------
// DAG-CBOR documents.

/// A DAG-CBOR value, the model the generator draws and the structured decoder reads back. Floats are kept as bits so
/// equality is exact (`-0.0` and `0.0` differ on the wire).
#[derive(Debug, Clone, PartialEq)]
enum Val {
    U(u64),
    N(u64),
    B(Vec<u8>),
    T(String),
    A(Vec<Val>),
    M(Vec<(String, Val)>),
    Cid(Vec<u8>),
    Bool(bool),
    Null,
    F(u64),
}

/// An argument of a header, spread over every head width and its edges.
fn arg(g: &mut Source) -> u64 {
    match g.int(0u8..=5) {
        0 => g.int(0u64..=23),
        1 => *g.pick(&[23, 24, 0xff, 0x100, 0xffff, 0x1_0000, 0xffff_ffff, 0x1_0000_0000, u64::MAX]),
        2 => g.int(24u64..=0xff),
        3 => g.int(0x100u64..=0xffff),
        4 => g.int(0x1_0000u64..=0xffff_ffff),
        _ => g.int(0x1_0000_0000u64..=u64::MAX),
    }
}

/// Text from a small alphabet that has multi-byte characters, so key order by bytes and by chars can differ.
fn text(g: &mut Source, max: usize) -> String {
    let n = g.int(0usize..=max);
    (0..n).map(|_| *g.pick(&['a', 'b', 'z', '0', 'é', 'ß', '\u{7f}', '\u{800}', '\u{10000}'])).collect()
}

/// A length that sometimes crosses the 23 and 255 head boundaries.
fn small_len(g: &mut Source, max: usize) -> usize {
    if g.bool_with(0.1) { *g.pick(&[23usize, 24, 255, 256]).min(&max) } else { g.int(0usize..=max.min(6)) }
}

fn float_bits(g: &mut Source) -> u64 {
    let f = match g.int(0u8..=4) {
        0 => 0.0,
        1 => -0.0,
        2 => f64::MIN_POSITIVE / 2.0,
        3 => *g.pick(&[f64::MAX, f64::MIN, 1.5, -2.25, f64::EPSILON]),
        _ => f64::from_bits(g.int(..)),
    };
    if f.is_finite() { f.to_bits() } else { 1.0f64.to_bits() }
}

/// A valid value, with nesting at most `depth`.
fn val(g: &mut Source, depth: usize) -> Val {
    let top = if depth == 0 { 8 } else { 10 };
    match g.int(0u8..=top) {
        0 => Val::U(arg(g)),
        1 => Val::N(arg(g)),
        2 => {
            let n = small_len(g, 300);
            Val::B((0..n).map(|_| g.int(0u8..=255)).collect())
        },
        3 => Val::T(text(g, 8)),
        4 => {
            let n = g.int(0usize..=40);
            Val::Cid((0..n).map(|_| g.int(0u8..=255)).collect())
        },
        5 => Val::Bool(g.bool()),
        6 => Val::Null,
        7 | 8 => Val::F(float_bits(g)),
        9 => {
            let n = small_len(g, 30);
            Val::A((0..n).map(|_| val(g, depth - 1)).collect())
        },
        _ => {
            let n = g.int(0usize..=5);
            let mut entries: Vec<(String, Val)> = (0..n).map(|_| (text(g, 4), val(g, depth - 1))).collect();
            entries.sort_by(|a, b| (a.0.len(), a.0.as_bytes()).cmp(&(b.0.len(), b.0.as_bytes())));
            entries.dedup_by(|a, b| a.0 == b.0);
            Val::M(entries)
        },
    }
}

fn encode_val(v: &Val, e: &mut Encoder<'_>) -> Result<(), WireError> {
    match v {
        Val::U(n) => e.unsigned(*n),
        Val::N(n) => e.negative(*n),
        Val::B(b) => e.bytes(b),
        Val::T(t) => e.text(t),
        Val::A(items) => {
            e.array(items.len() as u64)?;
            items.iter().try_for_each(|i| encode_val(i, e))
        },
        Val::M(entries) => {
            let mut keys = e.ordered_map(entries.len() as u64)?;
            for (k, v) in entries {
                keys.key(e, k)?;
                encode_val(v, e)?;
            }
            Ok(())
        },
        Val::Cid(c) => e.tag_cid(c),
        Val::Bool(b) => e.bool(*b),
        Val::Null => e.null(),
        Val::F(bits) => e.float(f64::from_bits(*bits)),
    }
}

fn to_bytes(v: &Val) -> Vec<u8> {
    let mut buf = vec![0u8; 1 << 16];
    let mut e = Encoder::new(&mut buf);
    encode_val(v, &mut e).expect("a generated value fits 64 KiB");
    e.written().to_vec()
}

/// The strict structured decoder: a map through `MapReader`, recursion bounded by `MAX_DEPTH` levels.
fn decode_val(d: &mut Decoder<'_>, depth: usize) -> Result<Val, WireError> {
    if depth > MAX_DEPTH {
        return Err(WireError::DepthExceeded);
    }
    let mut probe = *d;
    if let Item::Map(_) = probe.next_item()? {
        let mut map = MapReader::new(d)?;
        let mut entries = Vec::new();
        while let Some(k) = map.next_key(d)? {
            entries.push((k.to_string(), decode_val(d, depth + 1)?));
        }
        return Ok(Val::M(entries));
    }
    Ok(match d.next_item()? {
        Item::Unsigned(n) => Val::U(n),
        Item::Negative(n) => Val::N(n),
        Item::Bytes(b) => Val::B(b.to_vec()),
        Item::Text(t) => Val::T(t.to_string()),
        Item::Array(n) => {
            let mut items = Vec::new();
            for _ in 0..n {
                items.push(decode_val(d, depth + 1)?);
            }
            Val::A(items)
        },
        Item::Map(_) => unreachable!("handled above"),
        Item::Tag(_) => match d.next_item()? {
            Item::Bytes([0, cid @ ..]) => Val::Cid(cid.to_vec()),
            other => panic!("the decoder let tag 42 carry {other:?}"),
        },
        Item::Bool(b) => Val::Bool(b),
        Item::Null => Val::Null,
        Item::Float(f) => Val::F(f.to_bits()),
    })
}

/// Re-encode the one complete item at the start of `bytes` item by item, as the decoder yields them.
fn reencode_items(bytes: &[u8]) -> Result<Vec<u8>, WireError> {
    let mut d = Decoder::new(bytes);
    let mut buf = vec![0u8; bytes.len() + 64];
    let mut e = Encoder::new(&mut buf);
    let mut pending: u128 = 1;
    while pending > 0 {
        pending -= 1;
        match d.next_item()? {
            Item::Unsigned(n) => e.unsigned(n)?,
            Item::Negative(n) => e.negative(n)?,
            Item::Bytes(b) => e.bytes(b)?,
            Item::Text(t) => e.text(t)?,
            Item::Array(n) => {
                e.array(n)?;
                pending += u128::from(n);
            },
            Item::Map(n) => {
                e.map(n)?;
                pending += 2 * u128::from(n);
            },
            Item::Tag(_) => match d.next_item()? {
                Item::Bytes([0, cid @ ..]) => e.tag_cid(cid)?,
                other => panic!("the decoder let tag 42 carry {other:?}"),
            },
            Item::Bool(b) => e.bool(b)?,
            Item::Null => e.null()?,
            Item::Float(f) => e.float(f)?,
        }
    }
    Ok(e.written().to_vec())
}

/// Edits aimed at canonical-form rules: a head widened to a non-minimal width, an indefinite form, a float narrowed,
/// two neighbouring map keys swapped by a byte swap. Applied on top of `mangle`'s generic edits.
fn canonical_edit(g: &mut Source, valid: &[u8]) -> Vec<u8> {
    let mut out = valid.to_vec();
    if out.is_empty() {
        return out;
    }
    let at = g.index(out.len());
    let b = out[at];
    let (major, info) = (b >> 5, b & 0x1f);
    match g.int(0u8..=4) {
        // A minimal 1-byte head re-encoded with a one-byte argument.
        0 if info < 24 && major != 7 => {
            out[at] = major << 5 | 24;
            out.insert(at + 1, info);
        },
        // Widen an argument by one width step.
        1 if (24..=26).contains(&info) && major != 7 => {
            let w = 1usize << (info - 24);
            let end = (at + 1 + w).min(out.len());
            let mut arg = out[at + 1..end].to_vec();
            arg.splice(0..0, vec![0u8; w]);
            out[at] = major << 5 | (info + 1);
            out.splice(at + 1..end, arg);
        },
        // Indefinite length for a string or container.
        2 if (2..=5).contains(&major) => out[at] = major << 5 | 31,
        // A half or single float header.
        3 if b == 0xfb => out[at] = *g.pick(&[0xf9, 0xfa]),
        _ => {
            let j = g.index(out.len());
            out.swap(at, j);
        },
    }
    out
}

/// Encodings of generated values: valid 40% of the time, otherwise edited once or a few times by `mangle` and the
/// canonical-form edits.
fn cbor_documents() -> BoxGen<Vec<u8>> {
    (|g: &mut Source| {
        let depth = g.int(0usize..=4);
        let mut out = to_bytes(&val(g, depth));
        if g.bool_with(0.6) {
            for _ in 0..g.int(1u8..=3) {
                out = if g.bool() { mangle(g, &out) } else { canonical_edit(g, &out) };
            }
        }
        out
    })
    .with_shrink(shrink_bytes)
    .boxed()
}

/// A value whose encoding is checked against the value through the structured decoder.
fn values() -> BoxGen<Val> {
    (|g: &mut Source| {
        let depth = g.int(0usize..=4);
        val(g, depth)
    })
    .with_shrink(shrink_val)
    .boxed()
}

fn shrink_val(v: &Val, visit: &mut dyn FnMut(Val) -> ControlFlow<()>) -> ControlFlow<()> {
    match v {
        Val::A(items) => {
            for i in items {
                visit(i.clone())?;
            }
            for k in 0..items.len() {
                let mut fewer = items.clone();
                fewer.remove(k);
                visit(Val::A(fewer))?;
            }
        },
        Val::M(entries) => {
            for (_, i) in entries {
                visit(i.clone())?;
            }
            for k in 0..entries.len() {
                let mut fewer = entries.clone();
                fewer.remove(k);
                visit(Val::M(fewer))?;
            }
        },
        Val::Null => return ControlFlow::Continue(()),
        _ => {},
    }
    visit(Val::Null)
}

/// Every generated valid encoding is one complete item.
#[test]
fn cbor_value_generator_is_valid() {
    let docs = |g: &mut Source| {
        let depth = g.int(0usize..=4);
        to_bytes(&val(g, depth))
    };
    check_generator(&Config::default().tests(2_000), docs, |b: &Vec<u8>| {
        let mut d = Decoder::new(b);
        d.skip_value().is_ok() && d.is_empty()
    })
    .assert_passed();
}

/// Encode then the structured decode gives the value back and uses every byte; `skip_value` agrees on the length.
#[ephyra::test(gen = values(), tests = 5_000)]
fn cbor_encode_then_decode_is_the_value(v: Val) {
    let bytes = to_bytes(&v);
    let mut d = Decoder::new(&bytes);
    assert_eq!(decode_val(&mut d, 0), Ok(v));
    assert!(d.is_empty(), "the structured decode left bytes");
    let mut s = Decoder::new(&bytes);
    assert_eq!(s.skip_value(), Ok(()));
    assert_eq!(s.position(), bytes.len(), "skip_value stopped early");
}

/// "decode then encode is the identity": whatever prefix `skip_value` accepts re-encodes, item by item, to exactly
/// those bytes. Then the strict structured decoder (maps through `MapReader`) accepts the same prefix and nothing
/// else, unless one of them hit the depth bound.
#[ephyra::test(gen = cbor_documents(), tests = 30_000)]
fn cbor_accepted_bytes_reencode_identically(input: Vec<u8>) {
    let mut d = Decoder::new(&input);
    let skipped = d.skip_value();
    let mut s = Decoder::new(&input);
    let structured = decode_val(&mut s, 0);
    if skipped == Err(WireError::DepthExceeded) || structured == Err(WireError::DepthExceeded) {
        return;
    }
    assert_eq!(skipped.is_ok(), structured.is_ok(), "skip_value {skipped:?} and MapReader {structured:?} disagree");
    if skipped.is_err() {
        return;
    }
    let used = d.position();
    assert_eq!(used, s.position(), "skip_value and the structured decode end at different bytes");
    let item = &input[..used];
    let again = reencode_items(item);
    assert_eq!(again.as_deref(), Ok(item), "accepted bytes are not canonical");
}

/// `skip_value` over arbitrary bytes never panics, and never consumes past the input.
#[ephyra::test(gen = bytes(64), tests = 30_000)]
fn cbor_skip_value_on_noise(input: Vec<u8>) {
    let mut d = Decoder::new(&input);
    if d.skip_value().is_ok() {
        assert!(d.position() <= input.len());
        assert_eq!(reencode_items(&input[..d.position()]).as_deref(), Ok(&input[..d.position()]));
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Encoder atomicity.

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum EncOp {
    Null,
    Bool(bool),
    Unsigned(#[ephyra(gen = gens::int(0u64..=u64::MAX))] u64),
    Negative(#[ephyra(gen = gens::int(0u64..=u64::MAX))] u64),
    Bytes(#[ephyra(gen = gens::int(0usize..=300))] usize),
    Text(#[ephyra(gen = gens::int(0usize..=30))] usize),
    Array(#[ephyra(gen = gens::int(0u64..=u64::MAX))] u64),
    Map(#[ephyra(gen = gens::int(0u64..=70_000))] u64),
    Cid(#[ephyra(gen = gens::int(0usize..=300))] usize),
    Float(#[ephyra(gen = gens::int(0u64..=u64::MAX))] u64),
}

fn apply(op: &EncOp, e: &mut Encoder<'_>) -> Result<(), WireError> {
    match op {
        EncOp::Null => e.null(),
        EncOp::Bool(b) => e.bool(*b),
        EncOp::Unsigned(n) => e.unsigned(*n),
        EncOp::Negative(n) => e.negative(*n),
        EncOp::Bytes(n) => e.bytes(&vec![7u8; *n]),
        EncOp::Text(n) => e.text(&"x".repeat(*n)),
        EncOp::Array(n) => e.array(*n),
        EncOp::Map(n) => e.map(*n),
        EncOp::Cid(n) => e.tag_cid(&vec![9u8; *n]),
        EncOp::Float(bits) => e.float(f64::from_bits(*bits)),
    }
}

fn enc_cases() -> impl Gen<Value = (usize, Vec<EncOp>)> {
    (gens::int(0usize..=400), gens::vec(ephyra::any::<EncOp>()).len(0..=12))
}

/// A refused write leaves the bytes written so far, and every byte after them, untouched; a successful one writes
/// exactly the canonical bytes of that item (checked by decoding them back).
#[ephyra::test(gen = enc_cases(), tests = 20_000)]
fn encoder_refusals_write_nothing(case: (usize, Vec<EncOp>)) {
    let (cap, ops) = case;
    let mut buf = vec![0xa5u8; cap];
    let written;
    let mut failed = false;
    {
        let mut e = Encoder::new(&mut buf);
        for op in &ops {
            let before = e.written().to_vec();
            match apply(op, &mut e) {
                Ok(()) => {
                    let after = e.written();
                    assert!(after.starts_with(&before), "a write changed earlier bytes");
                    let item = &after[before.len()..];
                    let mut d = Decoder::new(item);
                    let first = d.next_item();
                    assert!(first.is_ok(), "{op:?} wrote {item:02x?}, which does not decode: {first:?}");
                    if matches!(op, EncOp::Cid(_)) {
                        assert!(matches!(d.next_item(), Ok(Item::Bytes([0, ..]))));
                    }
                    assert!(d.is_empty(), "{op:?} wrote more than one item: {item:02x?}");
                },
                Err(err) => {
                    assert_eq!(e.written(), &before[..], "a refused {op:?} changed the written bytes");
                    if let EncOp::Float(bits) = op
                        && !f64::from_bits(*bits).is_finite()
                    {
                        assert!(matches!(err, WireError::NonCanonical(_)));
                        continue;
                    }
                    assert!(matches!(err, WireError::BufferTooSmall { .. }), "{op:?}: {err:?}");
                    failed = true;
                    break;
                },
            }
        }
        written = e.written().len();
    }
    if failed {
        assert!(buf[written..].iter().all(|&b| b == 0xa5), "a refused write touched the buffer past the position");
    }
}

/// `head_len` is the size of the header the encoder writes for every argument.
#[ephyra::test(gen = gens::int(0u64..=u64::MAX), tests = 5_000)]
fn head_len_is_the_written_header(n: u64) {
    for value in [n, n >> 8, n >> 24, n >> 40, n & 0xff, n % 24] {
        let mut buf = [0u8; 9];
        let mut e = Encoder::new(&mut buf);
        assert_eq!(e.array(value), Ok(()));
        assert_eq!(e.written().len(), head_len(value), "head_len({value})");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Reader and Writer against a plain cursor.

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum ReadOp {
    U8,
    U16,
    U32,
    U64,
    Peek,
    Varint,
    Bytes(#[ephyra(gen = gens::int(0usize..=20))] usize),
    Array4,
}

fn read_cases() -> impl Gen<Value = (Vec<u8>, Vec<ReadOp>)> {
    (bytes(40), gens::vec(ephyra::any::<ReadOp>()).len(0..=20))
}

/// Every read returns the next bytes of the input or refuses with nothing consumed, against an index into the input.
#[ephyra::test(gen = read_cases(), tests = 20_000)]
fn reader_matches_a_cursor(case: (Vec<u8>, Vec<ReadOp>)) {
    let (input, ops) = case;
    let mut r = Reader::new(&input);
    let mut pos = 0usize;
    for op in &ops {
        let rest = &input[pos..];
        let want = |n: usize| rest.get(..n).ok_or_else(|| WireError::Truncated { needed: n - rest.len() });
        let (got, n) = match op {
            ReadOp::U8 => (r.read_u8().map(|v| vec![v]), 1),
            ReadOp::U16 => (r.read_u16().map(|v| v.to_be_bytes().to_vec()), 2),
            ReadOp::U32 => (r.read_u32().map(|v| v.to_be_bytes().to_vec()), 4),
            ReadOp::U64 => (r.read_u64().map(|v| v.to_be_bytes().to_vec()), 8),
            ReadOp::Array4 => (r.read_array::<4>().map(|v| v.to_vec()), 4),
            ReadOp::Bytes(n) => (r.read_bytes(*n).map(<[u8]>::to_vec), *n),
            ReadOp::Peek => {
                assert_eq!(r.peek_u8().ok(), rest.first().copied());
                assert_eq!(r.position(), pos, "peek consumed");
                continue;
            },
            ReadOp::Varint => {
                let model = varint::decode(rest);
                assert_eq!(r.read_varint(), model.map(|(v, _)| v));
                if let Ok((_, n)) = model {
                    pos += n;
                }
                assert_eq!(r.position(), pos);
                continue;
            },
        };
        match want(n) {
            Ok(b) => {
                assert_eq!(got, Ok(b.to_vec()), "{op:?} at {pos}");
                pos += n;
            },
            Err(e) => assert_eq!(got, Err(e), "{op:?} at {pos}"),
        }
        assert_eq!(r.position(), pos, "{op:?}");
        assert_eq!(r.remaining(), input.len() - pos, "{op:?}");
    }
}

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum WriteOp {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(#[ephyra(gen = gens::int(0u64..=u64::MAX))] u64),
    Slice(#[ephyra(gen = gens::int(0usize..=12))] usize),
    Varint(#[ephyra(gen = gens::int(0u64..=u64::MAX))] u64),
}

fn write_cases() -> impl Gen<Value = (usize, Vec<WriteOp>)> {
    (gens::int(0usize..=40), gens::vec(ephyra::any::<WriteOp>()).len(0..=20))
}

/// Every write appends exactly its bytes or refuses with the written content unchanged, against a `Vec`.
#[ephyra::test(gen = write_cases(), tests = 20_000)]
fn writer_matches_a_vec(case: (usize, Vec<WriteOp>)) {
    let (cap, ops) = case;
    let mut buf = vec![0u8; cap];
    let mut w = Writer::new(&mut buf);
    let mut model: Vec<u8> = Vec::new();
    for op in &ops {
        let (bytes, got): (Vec<u8>, _) = match op {
            WriteOp::U8(v) => (vec![*v], w.put_u8(*v)),
            WriteOp::U16(v) => (v.to_be_bytes().to_vec(), w.put_u16(*v)),
            WriteOp::U32(v) => (v.to_be_bytes().to_vec(), w.put_u32(*v)),
            WriteOp::U64(v) => (v.to_be_bytes().to_vec(), w.put_u64(*v)),
            WriteOp::Slice(n) => {
                let s: Vec<u8> = (0..*n as u8).collect();
                let r = w.put_slice(&s);
                (s, r)
            },
            WriteOp::Varint(v) => {
                let mut tmp = [0u8; 9];
                let enc = varint::encode(*v, &mut tmp).map(|n| tmp[..n].to_vec());
                let r = w.put_varint(*v);
                if let Err(e) = enc {
                    assert_eq!(r, Err(e));
                    assert_eq!(w.written(), &model[..]);
                    continue;
                }
                (enc.unwrap_or_default(), r)
            },
        };
        if model.len() + bytes.len() <= cap {
            assert_eq!(got, Ok(()), "{op:?}");
            model.extend(&bytes);
        } else {
            assert!(matches!(got, Err(WireError::BufferTooSmall { .. })), "{op:?}: {got:?}");
        }
        assert_eq!(w.written(), &model[..], "{op:?}");
        assert_eq!(w.remaining(), cap - model.len());
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The hybrid logical clock.

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum ClockOp {
    Tick(#[ephyra(gen = clock_time())] u64),
    Observe(
        #[ephyra(gen = clock_time())] u64,
        #[ephyra(gen = clock_counter())] u32,
        #[ephyra(gen = clock_time())] u64,
    ),
}

/// Times near each other (so walls tie), with the top of the range mixed in.
fn clock_time() -> BoxGen<u64> {
    gens::frequency(vec![
        (6, gens::int(0u64..=8).boxed()),
        (1, gens::int(u64::MAX - 3..=u64::MAX).boxed()),
        (1, gens::int(0u64..=u64::MAX).boxed()),
    ])
    .boxed()
}

fn clock_counter() -> BoxGen<u32> {
    gens::frequency(vec![
        (4, gens::int(0u32..=4).boxed()),
        (1, gens::int(u32::MAX - 2..=u32::MAX).boxed()),
    ])
    .boxed()
}

fn clock_cases() -> impl Gen<Value = (u64, u32, Vec<ClockOp>)> {
    (clock_time(), clock_counter(), gens::vec(ephyra::any::<ClockOp>()).len(0..=30))
}

/// Each event's timestamp is strictly above the clock it advanced (unless the counter is saturated, the documented
/// exception) and never below the physical reading it was given.
#[ephyra::test(gen = clock_cases(), tests = 20_000)]
fn hlc_moves_forward(case: (u64, u32, Vec<ClockOp>)) {
    let (wall, counter, ops) = case;
    let mut clock = Hlc::new(wall, counter);
    for op in &ops {
        let (next, now) = match op {
            ClockOp::Tick(now) => (clock.tick(*now), *now),
            ClockOp::Observe(rw, rc, now) => (clock.observe(Hlc::new(*rw, *rc), *now), *now),
        };
        let saturated = next.counter == u32::MAX && next.wall == clock.wall;
        if !saturated {
            assert!(next > clock, "{op:?} took {clock:?} to {next:?}");
        } else {
            assert!(next >= clock, "{op:?} took {clock:?} back to {next:?}");
        }
        assert!(next.wall >= now, "{op:?} gave {next:?}, below the physical time {now}");
        clock = next;
    }
}
