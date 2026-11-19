//! Trace generation for the CAR v1 archives of `pinc-dag` (`car/*`): the real `CarWriter` (every `new` and `section`
//! call with its buffer size, `header_len` and `section_len`), `CarReader` (with and without verify, under several
//! maxima, on whole CARs and on every cut) and `CarDecoder` (driven by feeding exactly the bytes it asks for and
//! seven more, every `decode` call recorded), on the domain of `DagCar.cfg` and on seeded random CARs with byte flips
//! and cuts, recorded as ndjson (`tla/dag_car.ndjson` under `PINC_TRACE_DIR`) for the TLA+ trace check
//! (`TraceDagCar.tla`).
//!
//! A `u64` is written as four 16-bit limbs, least significant first, which `U64.tla` reads (TLC integers are 32 bits
//! wide). A header body is recorded as the items `pinc-wire`'s `Decoder::next_item` yields from it (`hdr`, only when
//! its frame is complete); the genuine digests of the section blocks under a known hash, computed here with the
//! reference `sha2` and `blake3` crates, as triples `[code, block, digest]` (`genj`). The test checks every call against
//! the documented properties as well (the bytes written, the reader's sections, the cuts, the stream decoder against
//! the reader, the bound on what the decoder asks to hold), so it is meaningful without the proof tools. Nothing is
//! written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop,
    clippy::too_many_lines,
    clippy::panic,
    clippy::type_complexity
)]

use std::fmt::Write as _;

use pinc_dag::car::{CarDecoder, CarError, CarReader, CarWriter, Decoded};
use pinc_dag::cid::{Cid, CidError};
use pinc_tests::SplitMix64;
use pinc_wire::cbor::{Decoder, Encoder, Item};
use pinc_wire::{WireError, varint};
use sha2::{Digest, Sha256};

/// The buffer of the writer for the random CARs; the domain uses 4096.
const BIG: usize = 16384;

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

/// A JSON array of the bytes.
fn arr(bytes: &[u8]) -> String {
    let body: Vec<String> = bytes.iter().map(u8::to_string).collect();
    format!("[{}]", body.join(","))
}

fn roots_json(roots: &[Vec<u8>]) -> String {
    let body: Vec<String> = roots.iter().map(|r| arr(r)).collect();
    format!("[{}]", body.join(","))
}

/// The reference digest of `blk` under a known hash code, empty for any other code.
fn oracle(hash: u64, blk: &[u8]) -> Vec<u8> {
    match hash {
        0x12 => Sha256::digest(blk).to_vec(),
        0x1e => blake3::hash(blk).as_bytes().to_vec(),
        _ => Vec::new(),
    }
}

fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

fn random_bytes(rng: &mut SplitMix64, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    rng.fill(&mut v);
    v
}

// ---------------------------------------------------------------- the item stream

/// Counts and integers above this are recorded as this.
const SAT: u64 = 1 << 20;

fn sat(v: u64) -> u64 {
    v.min(SAT)
}

fn item_json(it: &Item<'_>) -> String {
    match it {
        Item::Unsigned(v) => format!(r#"{{"k":"uint","v":{}}}"#, sat(*v)),
        Item::Negative(v) => format!(r#"{{"k":"nint","v":{}}}"#, sat(*v)),
        Item::Bytes(b) => format!(r#"{{"k":"bytes","b":{}}}"#, arr(b)),
        Item::Text(t) => format!(r#"{{"k":"text","b":{}}}"#, arr(t.as_bytes())),
        Item::Array(n) => format!(r#"{{"k":"array","n":{}}}"#, sat(*n)),
        Item::Map(n) => format!(r#"{{"k":"map","n":{}}}"#, sat(*n)),
        Item::Tag(v) => format!(r#"{{"k":"tag","v":{}}}"#, sat(*v)),
        Item::Bool(_) => r#"{"k":"bool"}"#.to_owned(),
        Item::Null => r#"{"k":"null"}"#.to_owned(),
        Item::Float(_) => r#"{"k":"float"}"#.to_owned(),
    }
}

/// The JSON array of the items of `bytes` and whether the bytes end right after the last one.
fn items(bytes: &[u8]) -> (String, bool) {
    let mut dec = Decoder::new(bytes);
    let mut parts = Vec::new();
    let end = loop {
        if dec.is_empty() {
            break true;
        }
        match dec.next_item() {
            Ok(it) => parts.push(item_json(&it)),
            Err(_) => break false,
        }
    };
    (format!("[{}]", parts.join(",")), end)
}

/// An item the tests build header bodies from. A CID link is the two items `Tag` and `Bts(0 ++ cid)`, which is what
/// `Encoder::tag_cid` writes.
#[derive(Clone, Debug, PartialEq)]
enum T {
    U(u64),
    Txt(Vec<u8>),
    Bts(Vec<u8>),
    Arr(u64),
    Map(u64),
    Tag,
}

fn txt(s: &str) -> T {
    T::Txt(s.as_bytes().to_vec())
}

fn cid_items(raw: &[u8]) -> Vec<T> {
    vec![T::Tag, T::Bts([&[0u8][..], raw].concat())]
}

/// The bytes of a test item list; `end` false appends one byte `0xff`, which is not an item.
fn write_items(list: &[T], end: bool) -> Vec<u8> {
    let mut v = Vec::new();
    for it in list {
        let payload = match it {
            T::Txt(b) | T::Bts(b) => b.len(),
            _ => 0,
        };
        let mut buf = vec![0u8; payload + 16];
        let mut enc = Encoder::new(&mut buf);
        let written = match it {
            T::U(n) => enc.unsigned(*n),
            T::Txt(b) => enc.text(std::str::from_utf8(b).unwrap()),
            T::Bts(b) => enc.bytes(b),
            T::Arr(n) => enc.array(*n),
            T::Map(n) => enc.map(*n),
            T::Tag => {
                v.extend_from_slice(&[0xd8, 0x2a]);
                continue;
            }
        };
        written.unwrap();
        v.extend_from_slice(enc.written());
    }
    if !end {
        v.push(0xff);
    }
    v
}

/// The header body `{"roots": [..], "version": 1}` of raw CIDs, as items.
fn header_items_raw(roots: &[&[u8]]) -> Vec<T> {
    let mut v = vec![T::Map(2), txt("roots"), T::Arr(roots.len() as u64)];
    for r in roots {
        v.extend(cid_items(r));
    }
    v.extend([txt("version"), T::U(1)]);
    v
}

fn header_body(roots: &[Cid]) -> Vec<u8> {
    let raw: Vec<&[u8]> = roots.iter().map(Cid::as_bytes).collect();
    write_items(&header_items_raw(&raw), true)
}

/// `varint(len) body`.
fn framed(body: &[u8]) -> Vec<u8> {
    let mut prefix = [0u8; 16];
    let n = varint::encode(body.len() as u64, &mut prefix).unwrap();
    [&prefix[..n], body].concat()
}

// ---------------------------------------------------------------- JSON of the model's records

fn wire_err(e: &WireError) -> String {
    match e {
        WireError::VarintTooLong => r#"{"k":"wire","w":"toolong"}"#.to_owned(),
        WireError::VarintNonMinimal => r#"{"k":"wire","w":"nonminimal"}"#.to_owned(),
        WireError::BufferTooSmall { needed } => format!(r#"{{"k":"wire","w":"small","needed":{needed}}}"#),
        _ => r#"{"k":"wire","w":"cbor"}"#.to_owned(),
    }
}

fn cid_kind(e: &CidError) -> &'static str {
    match e {
        CidError::CidV0 => "v0",
        CidError::UnsupportedVersion(_) => "version",
        CidError::DigestTooLong(_) => "toolong",
        CidError::DigestLenMismatch { .. } => "mismatch",
        CidError::TrailingBytes => "trailing",
        CidError::Wire(_) => "wire",
        CidError::UnsupportedHash(_) => "unsupported",
        CidError::DigestMismatch => "digest",
        other => panic!("a CID error the model does not know: {other:?}"),
    }
}

/// A `CarError` as the model's error record.
fn err(e: &CarError) -> String {
    match e {
        CarError::Wire(w) => wire_err(w),
        CarError::Cid(c) => format!(r#"{{"k":"cid","c":"{}"}}"#, cid_kind(c)),
        CarError::Truncated { needed } => format!(r#"{{"k":"truncated","needed":{}}}"#, limbs(*needed as u64)),
        CarError::TooLarge { len, max } => {
            format!(
                r#"{{"k":"toolarge","len":{},"max":{}}}"#,
                limbs(*len),
                limbs(*max as u64)
            )
        }
        CarError::BadHeader(why) => {
            assert!(!why.contains(['"', '\\']), "a reason that needs escaping in JSON");
            format!(r#"{{"k":"badheader","why":"{why}"}}"#)
        }
    }
}

/// A section: a CID and its block.
#[derive(Clone)]
struct Sec {
    cid: Cid,
    blk: Vec<u8>,
}

fn sec_bytes(cid: &[u8], blk: &[u8]) -> Vec<u8> {
    framed(&[cid, blk].concat())
}

/// The frame's header body as items, when its frame is complete and within the maximum.
fn hdr(buf: &[u8], max: usize) -> String {
    let body = varint::decode(buf).ok().and_then(|(len, p)| {
        let len = usize::try_from(len).ok().filter(|&l| l <= max)?;
        buf.get(p..p.checked_add(len)?)
    });
    match body {
        Some(b) => {
            let (its, end) = items(b);
            format!(r#"{{"items":{its},"end":{end}}}"#)
        }
        None => r#"{"items":[],"end":false}"#.to_owned(),
    }
}

/// The genuine digests of the sections' blocks under a known hash, as triples `[code, block, digest]`.
fn gen_json(secs: &[Sec]) -> String {
    let body: Vec<String> = secs
        .iter()
        .filter(|s| matches!(s.cid.hash_code(), 0x12 | 0x1e))
        .map(|s| {
            format!(
                "[{},{},{}]",
                limbs(s.cid.hash_code()),
                arr(&s.blk),
                arr(&oracle(s.cid.hash_code(), &s.blk))
            )
        })
        .collect();
    format!("[{}]", body.join(","))
}

// ---------------------------------------------------------------- the writer

/// `CarWriter::new` into a buffer of `cap` bytes, recorded.
fn wnew_ev(out: &mut String, roots: &[Cid], cap: usize) -> Result<Vec<u8>, CarError> {
    let hl = CarWriter::header_len(roots);
    let mut buf = vec![0u8; cap];
    let r = CarWriter::new(&mut buf, roots).map(|w| w.written().to_vec());
    let res = match &r {
        Ok(b) => {
            assert_eq!(b.len(), hl, "header_len is not the bytes written");
            assert_eq!(
                *b,
                framed(&header_body(roots)),
                "the header is not `varint(len) header`"
            );
            format!(r#"{{"ok":{{"bytes":{},"pos":{}}}}}"#, arr(b), b.len())
        }
        Err(e) => {
            if cap < hl {
                assert_eq!(*e, CarError::Wire(WireError::BufferTooSmall { needed: hl - cap }));
            }
            format!(r#"{{"err":{}}}"#, err(e))
        }
    };
    let roots_raw: Vec<Vec<u8>> = roots.iter().map(|c| c.as_bytes().to_vec()).collect();
    let _ = writeln!(
        out,
        r#"{{"t":"wnew","roots":{},"cap":{cap},"hl":{hl},"r":{res}}}"#,
        roots_json(&roots_raw)
    );
    r
}

/// `CarWriter::section` after the sections `before`, into a buffer of `cap` bytes, recorded.
fn wsec_ev(out: &mut String, roots: &[Cid], before: &[Sec], sec: &Sec, cap: usize) -> Result<(), CarError> {
    let mut buf = vec![0u8; cap];
    let mut w = CarWriter::new(&mut buf, roots).unwrap();
    for s in before {
        w.section(s.cid.as_ref(), &s.blk).unwrap();
    }
    let pos = w.written().len();
    let sl = CarWriter::section_len(sec.cid.as_ref(), &sec.blk);
    let r = w.section(sec.cid.as_ref(), &sec.blk);
    let after = w.written();
    let res = match &r {
        Ok(()) => {
            assert_eq!(after.len(), pos + sl, "section_len is not the bytes written");
            let app = after[pos..].to_vec();
            assert_eq!(app, sec_bytes(sec.cid.as_bytes(), &sec.blk));
            format!(r#"{{"ok":{{"app":{},"pos":{}}}}}"#, arr(&app), after.len())
        }
        Err(e) => {
            assert_eq!(after.len(), pos, "a refused section changed the written bytes");
            if cap + 1 == pos + sl {
                assert_eq!(*e, CarError::Wire(WireError::BufferTooSmall { needed: 1 }));
            }
            format!(r#"{{"err":{},"pos":{}}}"#, err(e), after.len())
        }
    };
    let _ = writeln!(
        out,
        r#"{{"t":"wsec","pos":{pos},"cap":{cap},"cid":{},"blk":{},"sl":{sl},"r":{res}}}"#,
        arr(sec.cid.as_bytes()),
        arr(&sec.blk)
    );
    r
}

/// A CAR through the writer, checked against the bytes the format states.
fn build_car(roots: &[Cid], secs: &[Sec], cap: usize) -> Vec<u8> {
    let mut buf = vec![0u8; cap];
    let mut w = CarWriter::new(&mut buf, roots).unwrap();
    for s in secs {
        w.section(s.cid.as_ref(), &s.blk).unwrap();
    }
    let car = w.written().to_vec();
    let mut want = framed(&header_body(roots));
    for s in secs {
        want.extend(sec_bytes(s.cid.as_bytes(), &s.blk));
    }
    assert_eq!(
        car, want,
        "the CAR is not `varint(len) header` then `varint(len) cid block` per section"
    );
    car
}

/// Every writer call of a roots set and a section list: the header at four buffer sizes, every section at its position
/// at four buffer sizes.
fn writer_events(out: &mut String, roots: &[Cid], secs: &[Sec], big: usize) {
    let hl = CarWriter::header_len(roots);
    for cap in [hl, hl - 1, 0, big] {
        let _ = wnew_ev(out, roots, cap);
    }
    let mut pos = hl;
    for (i, s) in secs.iter().enumerate() {
        let sl = CarWriter::section_len(s.cid.as_ref(), &s.blk);
        for cap in [pos + sl, pos + sl - 1, pos, big] {
            let r = wsec_ev(out, roots, &secs[..i], s, cap);
            assert_eq!(r.is_ok(), cap >= pos + sl);
        }
        pos += sl;
    }
}

// ---------------------------------------------------------------- the reader and the decoder

/// What a reader returns for a CAR: the roots and every section (an error ends the list).
#[derive(Debug, PartialEq)]
struct Reading {
    roots: Vec<Vec<u8>>,
    secs: Vec<Result<(Vec<u8>, Vec<u8>), CarError>>,
}

fn sec_json(s: &Result<(Vec<u8>, Vec<u8>), CarError>) -> String {
    match s {
        Ok((c, b)) => format!(r#"{{"ok":{{"cid":{},"blk":{}}}}}"#, arr(c), arr(b)),
        Err(e) => format!(r#"{{"err":{}}}"#, err(e)),
    }
}

/// `CarReader::new` and its sections, recorded.
fn read_ev(out: &mut String, buf: &[u8], max: usize, verify: bool, genj: &str) -> Result<Reading, CarError> {
    let result = CarReader::new(buf, max).map(|r| {
        let r = r.with_verify(verify);
        Reading {
            roots: r.roots().map(|c| c.as_bytes().to_vec()).collect(),
            secs: r
                .sections()
                .map(|s| s.map(|(c, b)| (c.as_bytes().to_vec(), b.to_vec())))
                .collect(),
        }
    });
    let res = match &result {
        Ok(rd) => {
            let secs: Vec<String> = rd.secs.iter().map(sec_json).collect();
            format!(
                r#"{{"ok":{{"roots":{},"secs":[{}]}}}}"#,
                roots_json(&rd.roots),
                secs.join(",")
            )
        }
        Err(e) => format!(r#"{{"err":{}}}"#, err(e)),
    };
    let _ = writeln!(
        out,
        r#"{{"t":"read","buf":{},"max":{},"verify":{verify},"hdr":{},"gen":{genj},"r":{res}}}"#,
        arr(buf),
        limbs(max as u64),
        hdr(buf, max)
    );
    result
}

/// What the stream decoder produced, in order.
#[derive(Debug, PartialEq)]
enum Entry {
    Hdr(Vec<Vec<u8>>),
    Sec(Vec<u8>, Vec<u8>),
    Err(CarError),
    /// The stream ended; whether between frames after the header.
    End(bool),
}

enum Step {
    Need(usize),
    Drop(usize, Entry),
    Stop(CarError),
}

/// One `CarDecoder::decode` call on `buf`, recorded; `done` is whether the decoder returned `Header` before.
fn dec_ev(
    out: &mut String,
    dec: &mut CarDecoder,
    buf: &[u8],
    done: bool,
    max: usize,
    verify: bool,
    genj: &str,
) -> Step {
    let hdr = hdr(buf, max);
    let (res, step) = match dec.decode(buf) {
        Ok(Decoded::NeedMore(n)) => (format!(r#"{{"need":{}}}"#, limbs(n as u64)), Step::Need(n)),
        Ok(Decoded::Header { consumed, roots }) => {
            let roots: Vec<Vec<u8>> = roots.map(|c| c.as_bytes().to_vec()).collect();
            (
                format!(r#"{{"hdr":{{"consumed":{consumed},"roots":{}}}}}"#, roots_json(&roots)),
                Step::Drop(consumed, Entry::Hdr(roots)),
            )
        }
        Ok(Decoded::Section { consumed, cid, block }) => {
            let (c, b) = (cid.as_bytes().to_vec(), block.to_vec());
            (
                format!(
                    r#"{{"sec":{{"consumed":{consumed},"cid":{},"blk":{}}}}}"#,
                    arr(&c),
                    arr(&b)
                ),
                Step::Drop(consumed, Entry::Sec(c, b)),
            )
        }
        Err(e) => (format!(r#"{{"err":{}}}"#, err(&e)), Step::Stop(e)),
    };
    let _ = writeln!(
        out,
        r#"{{"t":"dec","done":{done},"in":{},"max":{},"verify":{verify},"hdr":{hdr},"gen":{genj},"r":{res}}}"#,
        arr(buf),
        limbs(max as u64)
    );
    step
}

/// Drive a decoder over `car`: feed what `NeedMore` asks (and seven more when `more`), drop what is consumed, until an
/// error or the end of the input. Asserts that the buffer plus what it asks for stays within `max` plus a 9 byte prefix.
fn drive(out: &mut String, car: &[u8], max: usize, verify: bool, more: bool, genj: &str) -> Vec<Entry> {
    let mut dec = CarDecoder::new(max).with_verify(verify);
    let (mut buf, mut k, mut done) = (Vec::<u8>::new(), 0usize, false);
    let mut entries = Vec::new();
    loop {
        match dec_ev(out, &mut dec, &buf, done, max, verify, genj) {
            Step::Need(n) => {
                assert!(
                    buf.len() as u128 + n as u128 <= max as u128 + 9,
                    "the decoder asks the caller to hold more than a section and a prefix"
                );
                if k >= car.len() {
                    entries.push(Entry::End(buf.is_empty() && done));
                    break;
                }
                let want = if more { n.saturating_add(7) } else { n };
                let take = want.min(car.len() - k);
                buf.extend_from_slice(&car[k..k + take]);
                k += take;
            }
            Step::Drop(consumed, entry) => {
                buf.drain(..consumed);
                done |= matches!(entry, Entry::Hdr(_));
                entries.push(entry);
            }
            Step::Stop(e) => {
                entries.push(Entry::Err(e));
                break;
            }
        }
    }
    entries
}

/// A decoder called once on the whole `input`, recorded; the error it gave, if any.
fn dec_once(out: &mut String, input: &[u8], max: usize, genj: &str) -> Option<CarError> {
    let mut dec = CarDecoder::new(max);
    match dec_ev(out, &mut dec, input, false, max, false, genj) {
        Step::Stop(e) => Some(e),
        Step::Need(_) | Step::Drop(..) => None,
    }
}

/// The reader's result as the decoder's sequence.
fn as_stream(r: &Result<Reading, CarError>) -> Vec<Entry> {
    match r {
        Err(e) => vec![Entry::Err(*e)],
        Ok(rd) => {
            let mut v = vec![Entry::Hdr(rd.roots.clone())];
            let mut failed = false;
            for s in &rd.secs {
                match s {
                    Ok((c, b)) => v.push(Entry::Sec(c.clone(), b.clone())),
                    Err(e) => {
                        v.push(Entry::Err(*e));
                        failed = true;
                    }
                }
            }
            if !failed {
                v.push(Entry::End(true));
            }
            v
        }
    }
}

/// The reader's result the documentation states for a whole CAR, computed apart from the code.
fn want_read(roots: &[Cid], secs: &[Sec], max: usize, verify: bool) -> Result<Reading, CarError> {
    let hb = header_body(roots).len();
    if hb > max {
        return Err(CarError::TooLarge { len: hb as u64, max });
    }
    let mut rd = Reading {
        roots: roots.iter().map(|c| c.as_bytes().to_vec()).collect(),
        secs: Vec::new(),
    };
    for s in secs {
        let body = s.cid.as_bytes().len() + s.blk.len();
        let hash = s.cid.hash_code();
        let refusal = if body > max {
            Some(CarError::TooLarge { len: body as u64, max })
        } else if verify && !matches!(hash, 0x12 | 0x1e) {
            Some(CarError::Cid(CidError::UnsupportedHash(hash)))
        } else if verify && oracle(hash, &s.blk) != s.cid.digest() {
            Some(CarError::Cid(CidError::DigestMismatch))
        } else {
            None
        };
        if let Some(e) = refusal {
            rd.secs.push(Err(e));
            break;
        }
        rd.secs.push(Ok((s.cid.as_bytes().to_vec(), s.blk.clone())));
    }
    Ok(rd)
}

/// The reader's result for the first `j` bytes of a CAR (no maximum, no verify): a cut between two frames is a shorter
/// CAR, any other cut is `Truncated` with the missing bytes of the frame, 1 inside a length prefix.
fn want_cut(roots: &[Cid], secs: &[Sec], j: usize) -> Result<Reading, CarError> {
    let hb = header_body(roots).len();
    let pl = varint::encoded_len(hb as u64);
    let hl = pl + hb;
    if j < hl {
        return Err(CarError::Truncated {
            needed: if j < pl { 1 } else { hl - j },
        });
    }
    let mut rd = Reading {
        roots: roots.iter().map(|c| c.as_bytes().to_vec()).collect(),
        secs: Vec::new(),
    };
    let mut start = hl;
    for s in secs {
        if start == j {
            break;
        }
        let body = s.cid.as_bytes().len() + s.blk.len();
        let spl = varint::encoded_len(body as u64);
        let sl = spl + body;
        if start + sl <= j {
            rd.secs.push(Ok((s.cid.as_bytes().to_vec(), s.blk.clone())));
            start += sl;
        } else {
            rd.secs.push(Err(CarError::Truncated {
                needed: if j - start < spl { 1 } else { start + sl - j },
            }));
            break;
        }
    }
    Ok(rd)
}

/// A whole CAR: one read, checked against the documentation, and the decoder driven two ways, checked against the
/// reader.
fn check_car(out: &mut String, car: &[u8], roots: &[Cid], secs: &[Sec], max: usize, verify: bool) {
    let genj = gen_json(secs);
    let r = read_ev(out, car, max, verify, &genj);
    assert_eq!(
        r,
        want_read(roots, secs, max, verify),
        "the reader does not return what was written"
    );
    for more in [false, true] {
        assert_eq!(
            drive(out, car, max, verify, more, &genj),
            as_stream(&r),
            "the decoder does not yield the reader's header and sections"
        );
    }
}

/// The largest header or section body of a CAR.
fn largest_body(roots: &[Cid], secs: &[Sec]) -> usize {
    secs.iter()
        .map(|s| s.cid.as_bytes().len() + s.blk.len())
        .chain([header_body(roots).len()])
        .max()
        .unwrap()
}

// ---------------------------------------------------------------- the checked domain

fn domain(out: &mut String) {
    let b1 = vec![1u8, 2, 3];
    let b2 = vec![9u8];
    let bb: Vec<u8> = (1..=100usize).map(|i| ((37 * i + 11) % 256) as u8).collect();
    let g1 = Cid::for_block(0x71, 0x1e, &b1).unwrap();
    let g2 = Cid::for_block(0x55, 0x12, &bb).unwrap();
    let x = Cid::from_bytes(&[1, 0x71, 0, 1, 7]).unwrap();
    let s1 = Sec { cid: g1, blk: b1 };
    let s2 = Sec {
        cid: g1,
        blk: b2.clone(),
    };
    let s3 = Sec { cid: g2, blk: bb };
    let s4 = Sec { cid: x, blk: b2 };
    let root_sets: [Vec<Cid>; 3] = [vec![], vec![x], vec![g1, x]];
    let lists: [Vec<Sec>; 6] = [
        vec![],
        vec![s1.clone()],
        vec![s3.clone()],
        vec![s1.clone(), s2],
        vec![s4, s1.clone()],
        vec![s3, s1],
    ];
    for roots in &root_sets {
        for secs in &lists {
            writer_events(out, roots, secs, 4096);
            let car = build_car(roots, secs, 4096);
            let largest = largest_body(roots, secs);
            for max in [largest, largest - 1, usize::MAX] {
                for verify in [false, true] {
                    check_car(out, &car, roots, secs, max, verify);
                }
            }
            // every cut, with no maximum and no verify
            let genj = gen_json(secs);
            for j in 0..car.len() {
                let r = read_ev(out, &car[..j], usize::MAX, false, &genj);
                assert_eq!(r, want_cut(roots, secs, j), "a cut CAR is not read as documented");
                for more in [false, true] {
                    drive(out, &car[..j], usize::MAX, false, more, &genj);
                }
            }
        }
    }
}

const BAD_V2: [u8; 4] = [2, 0x71, 0, 0];

/// The 13 header bodies of `DagCar.BadHdrs`: items, whether the bytes end after them, the error expected.
fn bad_headers() -> Vec<(Vec<T>, bool, &'static str)> {
    let roots0 = || vec![txt("roots"), T::Arr(0)];
    let ver = |v: T| vec![txt("version"), v];
    let version_not_1 = r#"{"k":"badheader","why":"version is not 1"}"#;
    let unknown_key = r#"{"k":"badheader","why":"unknown key"}"#;
    let required = r#"{"k":"badheader","why":"roots and version are required"}"#;
    let follows = r#"{"k":"badheader","why":"bytes follow the header map"}"#;
    let cid_version = r#"{"k":"cid","c":"version"}"#;
    let cid_wire = r#"{"k":"cid","c":"wire"}"#;
    let cbor = r#"{"k":"wire","w":"cbor"}"#;
    vec![
        ([vec![T::Map(2)], roots0(), ver(T::U(2))].concat(), true, version_not_1),
        ([vec![T::Map(2)], roots0(), ver(txt("1"))].concat(), true, version_not_1),
        (
            [vec![T::Map(3), txt("zz"), T::U(0)], roots0(), ver(T::U(1))].concat(),
            true,
            unknown_key,
        ),
        ([vec![T::Map(1)], roots0()].concat(), true, required),
        ([vec![T::Map(1)], ver(T::U(1))].concat(), true, required),
        (vec![T::Map(0)], true, required),
        ([header_items_raw(&[]), vec![T::U(0)]].concat(), true, follows),
        (header_items_raw(&[]), false, follows),
        (header_items_raw(&[&BAD_V2]), true, cid_version),
        (
            [vec![T::Map(2), txt("roots"), T::U(0)], ver(T::U(1))].concat(),
            true,
            cid_wire,
        ),
        (vec![T::Arr(0)], true, cbor),
        ([vec![T::Map(2)], roots0(), vec![txt("version")]].concat(), true, cbor),
        ([vec![T::Map(2)], ver(T::U(1)), roots0()].concat(), true, cbor),
    ]
}

fn headers(out: &mut String) {
    let cases = bad_headers();
    assert_eq!(cases.len(), 13);
    for (list, end, want) in cases {
        let car = framed(&write_items(&list, end));
        let e = read_ev(out, &car, usize::MAX, false, "[]").unwrap_err();
        assert_eq!(err(&e), want, "a bad header gave another error");
        assert_eq!(
            dec_once(out, &car, usize::MAX, "[]"),
            Some(e),
            "the decoder differs from the reader"
        );
    }
}

fn frames(out: &mut String) {
    let body = header_body(&[]);
    assert_eq!(body.len(), 17);
    let mut huge = [0u8; 16];
    let n = varint::encode(1 << 62, &mut huge).unwrap();
    let huge = &huge[..n];
    let nonminimal = [&[0x80 | body.len() as u8, 0][..], &body].concat();
    let cases: Vec<(Vec<u8>, usize, Result<(), CarError>)> = vec![
        (nonminimal, usize::MAX, Err(CarError::Wire(WireError::VarintNonMinimal))),
        (
            [&[0x80u8; 9][..], &[0]].concat(),
            usize::MAX,
            Err(CarError::Wire(WireError::VarintTooLong)),
        ),
        (huge.to_vec(), 17, Err(CarError::TooLarge { len: 1 << 62, max: 17 })),
        (huge.to_vec(), usize::MAX, Err(CarError::Truncated { needed: 1 << 62 })),
        (vec![], usize::MAX, Err(CarError::Truncated { needed: 1 })),
        (framed(&body), 17, Ok(())),
        (framed(&body), 16, Err(CarError::TooLarge { len: 17, max: 16 })),
    ];
    for (input, max, want) in cases {
        let r = read_ev(out, &input, max, false, "[]");
        assert_eq!(r.map(|_| ()), want, "a frame was not read as documented");
        dec_once(out, &input, max, "[]");
    }
}

// ---------------------------------------------------------------- random CARs

fn random_sec(rng: &mut SplitMix64) -> Sec {
    let n = below(rng, 301) as usize;
    let blk = random_bytes(rng, n);
    let codec = [0x55, 0x71][below(rng, 2) as usize];
    let hash = [0x12, 0x1e, 0][below(rng, 3) as usize];
    let cid = if hash == 0 {
        let digest = random_bytes(rng, 32);
        Cid::new(codec, 0, &digest).unwrap()
    } else {
        Cid::for_block(codec, hash, &blk).unwrap()
    };
    Sec { cid, blk }
}

fn random(out: &mut String, rng: &mut SplitMix64) {
    for _ in 0..200 {
        let mut secs: Vec<Sec> = (0..below(rng, 5)).map(|_| random_sec(rng)).collect();
        if !secs.is_empty() && below(rng, 2) == 0 {
            let i = below(rng, secs.len() as u64) as usize;
            let n = below(rng, 301) as usize;
            secs[i].blk = random_bytes(rng, n);
        }
        let roots: Vec<Cid> = (0..below(rng, 4))
            .map(|_| {
                if !secs.is_empty() && below(rng, 2) == 0 {
                    secs[below(rng, secs.len() as u64) as usize].cid
                } else {
                    let seed = random_bytes(rng, 8);
                    Cid::for_block(0x71, 0x1e, &seed).unwrap()
                }
            })
            .collect();
        writer_events(out, &roots, &secs, BIG);
        let car = build_car(&roots, &secs, BIG);
        let largest = largest_body(&roots, &secs);
        let max = [largest, largest - 1, largest + 1, usize::MAX][below(rng, 4) as usize];
        let verify = below(rng, 2) == 0;
        check_car(out, &car, &roots, &secs, max, verify);
        // three byte flips and a cut
        let mut broken = car.clone();
        for _ in 0..3 {
            let i = below(rng, broken.len() as u64) as usize;
            broken[i] = rng.next_u64() as u8;
        }
        broken.truncate(below(rng, broken.len() as u64 + 1) as usize);
        let genj = gen_json(&secs);
        read_ev(out, &broken, max, verify, &genj).ok();
        for more in [false, true] {
            drive(out, &broken, max, verify, more, &genj);
        }
    }
}

#[test]
fn dag_car_traces_are_consistent_with_the_code() {
    let mut out = String::new();
    let mut rng = SplitMix64::traced(0xda9c_ca12);
    domain(&mut out);
    headers(&mut out);
    frames(&mut out);
    random(&mut out, &mut rng);
    assert!(out.lines().count() > 10_000);
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir).join("tla");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("dag_car.ndjson"), out).unwrap();
}
