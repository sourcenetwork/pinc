//! Trace generation for the blocks of `pinc-dag` (`block/*`): the real `BlockRef::parse` on hand-built blocks, on
//! single-item mutations of canonical blocks and on seeded random blocks, and `encode_block` on the parts of
//! `DagBlock.cfg` with every buffer size class and on seeded random parts, recorded as ndjson (`tla/dag_block.ndjson`
//! under `PINC_TRACE_DIR`) for the TLA+ trace check (`TraceDagBlock.tla`).
//!
//! A CBOR input is recorded as the items `pinc-wire`'s `Decoder::next_item` yields from it, up to the first error or
//! the end (`end` is true when the bytes end right after the last item); counts and integers above 2^20 are recorded
//! as 2^20. An encode event also records the heads and links after the call (`encode_block` sorts them in place). The
//! test checks every call against the documented properties as well (the round trip, the buffer sizes, the refusals,
//! the one byte form of a block that uses no tolerance), so it is meaningful without the proof tools. Nothing is
//! written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop,
    clippy::too_many_lines,
    clippy::panic,
    clippy::range_plus_one,
    clippy::type_complexity
)]

use std::fmt::Write as _;

use pinc_dag::block::{BlockError, BlockParts, BlockRef, Link, encode_block};
use pinc_dag::cid::{Cid, CidError, CidRef};
use pinc_tests::SplitMix64;
use pinc_wire::WireError;
use pinc_wire::cbor::{Decoder, Encoder, Item, MapReader};

const K1: [u8; 5] = [1, 0x71, 0, 1, 25];
const K2: [u8; 5] = [1, 0x71, 0, 1, 26];
const K3: [u8; 4] = [1, 0x55, 0, 0];
const K3_TRAILING: [u8; 5] = [1, 0x55, 0, 0, 0];
const BAD_V2: [u8; 4] = [2, 0x71, 0, 0];

/// A JSON array of the bytes.
fn arr(bytes: &[u8]) -> String {
    let body: Vec<String> = bytes.iter().map(u8::to_string).collect();
    format!("[{}]", body.join(","))
}

fn cid(raw: &[u8]) -> Cid {
    Cid::from_bytes(raw).unwrap()
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

/// An item the tests build blocks from. A CID link is the two items `Tag` and `Bts(0 ++ cid)`, which is what
/// `Encoder::tag_cid` writes.
#[derive(Clone, Debug, PartialEq)]
enum T {
    U(u64),
    Null,
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
            T::Null => enc.null(),
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

/// The test items of a canonical byte string.
fn to_items(bytes: &[u8]) -> Vec<T> {
    let mut dec = Decoder::new(bytes);
    let mut out = Vec::new();
    while !dec.is_empty() {
        out.push(match dec.next_item().unwrap() {
            Item::Unsigned(v) => T::U(v),
            Item::Null => T::Null,
            Item::Text(t) => T::Txt(t.as_bytes().to_vec()),
            Item::Bytes(b) => T::Bts(b.to_vec()),
            Item::Array(n) => T::Arr(n),
            Item::Map(n) => T::Map(n),
            Item::Tag(_) => T::Tag,
            other => panic!("an item the tests do not build: {other:?}"),
        });
    }
    out
}

// ---------------------------------------------------------------- blocks as items

fn delta_e(d: &[T]) -> Vec<T> {
    [vec![txt("delta")], d.to_vec()].concat()
}

fn heads_e(hs: &[&[u8]]) -> Vec<T> {
    let mut v = vec![txt("heads"), T::Arr(hs.len() as u64)];
    for h in hs {
        v.extend(cid_items(h));
    }
    v
}

fn link_items(c: &[u8], name: &str) -> Vec<T> {
    [vec![T::Map(2), txt("link")], cid_items(c), vec![txt("name"), txt(name)]].concat()
}

fn links_e(ls: &[(&[u8], &str)]) -> Vec<T> {
    let mut v = vec![txt("links"), T::Arr(ls.len() as u64)];
    for (c, n) in ls {
        v.extend(link_items(c, n));
    }
    v
}

fn sig_e(c: &[u8]) -> Vec<T> {
    [vec![txt("signature")], cid_items(c)].concat()
}

fn blk(n: u64, body: Vec<T>) -> Vec<T> {
    [vec![T::Map(n)], body].concat()
}

fn deep(n: usize) -> Vec<T> {
    let mut v = vec![T::Arr(1); n];
    v.push(T::U(0));
    v
}

// ---------------------------------------------------------------- errors and JSON

fn berr(e: &BlockError) -> String {
    match e {
        BlockError::Wire(WireError::BufferTooSmall { needed }) => {
            format!(r#"{{"k":"wire","w":"small","needed":{needed}}}"#)
        }
        BlockError::Wire(_) => r#"{"k":"wire","w":"cbor"}"#.to_owned(),
        BlockError::Cid(c) => {
            let kind = match c {
                CidError::CidV0 => "v0",
                CidError::UnsupportedVersion(_) => "version",
                CidError::DigestTooLong(_) => "toolong",
                CidError::DigestLenMismatch { .. } => "mismatch",
                CidError::TrailingBytes => "trailing",
                CidError::Wire(_) => "wire",
                other => panic!("a CID error the model does not know: {other:?}"),
            };
            format!(r#"{{"k":"cid","c":"{kind}"}}"#)
        }
        BlockError::TrailingBytes => r#"{"k":"trailing"}"#.to_owned(),
        BlockError::MissingDelta => r#"{"k":"missingDelta"}"#.to_owned(),
        BlockError::Malformed(w) => {
            assert!(!w.contains(['"', '\\']), "a reason that needs escaping in JSON");
            format!(r#"{{"k":"malformed","what":"{w}"}}"#)
        }
        BlockError::Unordered(w) => {
            assert!(!w.contains(['"', '\\']), "a reason that needs escaping in JSON");
            format!(r#"{{"k":"unordered","what":"{w}"}}"#)
        }
    }
}

fn heads_json(hs: &[Cid]) -> String {
    let body: Vec<String> = hs.iter().map(|c| arr(c.as_bytes())).collect();
    format!("[{}]", body.join(","))
}

fn link_json(c: &Cid, name: &str) -> String {
    format!(r#"{{"cid":{},"name":{}}}"#, arr(c.as_bytes()), arr(name.as_bytes()))
}

fn links_json(ls: &[Link<'_>]) -> String {
    let body: Vec<String> = ls.iter().map(|l| link_json(&l.cid, l.name)).collect();
    format!("[{}]", body.join(","))
}

fn opt_json(c: Option<Cid>) -> String {
    c.map_or_else(|| "[]".to_owned(), |c| format!("[{}]", arr(c.as_bytes())))
}

// ---------------------------------------------------------------- parse

/// Whether a block that parses uses a tolerance: an unknown key (also inside a link), a null, or an empty array for
/// heads or links.
fn is_loose(input: &[u8]) -> bool {
    let mut dec = Decoder::new(input);
    let mut map = MapReader::new(&mut dec).unwrap();
    let mut loose = false;
    while let Some(key) = map.next_key(&mut dec).unwrap() {
        match key {
            "delta" => dec.skip_value().unwrap(),
            "heads" | "links" | "signature" | "encryption" => {
                let mut probe = dec;
                match probe.next_item().unwrap() {
                    Item::Null => {
                        loose = true;
                        dec.skip_value().unwrap();
                    }
                    Item::Array(0) if matches!(key, "heads" | "links") => {
                        loose = true;
                        dec.skip_value().unwrap();
                    }
                    Item::Array(n) if key == "links" => {
                        dec.next_item().unwrap();
                        for _ in 0..n {
                            let mut link = MapReader::new(&mut dec).unwrap();
                            while let Some(k) = link.next_key(&mut dec).unwrap() {
                                loose |= !matches!(k, "link" | "name");
                                dec.skip_value().unwrap();
                            }
                        }
                    }
                    _ => dec.skip_value().unwrap(),
                }
            }
            _ => {
                loose = true;
                dec.skip_value().unwrap();
            }
        }
    }
    loose
}

/// A block that parses re-encodes to exactly its bytes unless it uses a tolerance; then to a canonical block that
/// does.
fn assert_reencodes(b: &BlockRef<'_>, input: &[u8]) {
    let mut heads: Vec<Cid> = b.heads().map(CidRef::into_owned).collect();
    let named: Vec<(Cid, String)> = b.links().map(|l| (l.cid.into_owned(), l.name.to_owned())).collect();
    let mut links: Vec<Link<'_>> = named
        .iter()
        .map(|(c, n)| Link {
            name: n.as_str(),
            cid: *c,
        })
        .collect();
    let mut buf = vec![0u8; input.len() + 64];
    let mut parts = BlockParts {
        delta: b.delta(),
        heads: &mut heads,
        links: &mut links,
        encryption: b.encryption().map(CidRef::into_owned),
        signature: b.signature().map(CidRef::into_owned),
    };
    let len = encode_block(&mut buf, &mut parts).unwrap();
    if is_loose(input) {
        let canonical = &buf[..len];
        assert!(!is_loose(canonical));
        assert_reencodes(&BlockRef::parse(canonical).unwrap(), canonical);
    } else {
        assert_eq!(
            &buf[..len],
            input,
            "a block that uses no tolerance does not re-encode to its bytes"
        );
    }
}

/// `BlockRef::parse`, recorded; the error's JSON on a refusal.
fn parse_ev(out: &mut String, input: &[u8]) -> Option<String> {
    let (its, end) = items(input);
    let (r, error) = match BlockRef::parse(input) {
        Ok(b) => {
            assert_reencodes(&b, input);
            let (d, dend) = items(b.delta());
            assert!(dend, "the delta is not one whole item");
            let heads: Vec<String> = b.heads().map(|c| arr(c.as_bytes())).collect();
            let links: Vec<String> = b.links().map(|l| link_json(&l.cid.into_owned(), l.name)).collect();
            let r = format!(
                r#"{{"ok":{{"delta":{d},"heads":[{}],"links":[{}],"sig":{},"enc":{}}}}}"#,
                heads.join(","),
                links.join(","),
                opt_json(b.signature().map(CidRef::into_owned)),
                opt_json(b.encryption().map(CidRef::into_owned))
            );
            (r, None)
        }
        Err(e) => {
            let j = berr(&e);
            (format!(r#"{{"err":{j}}}"#), Some(j))
        }
    };
    let _ = writeln!(out, r#"{{"t":"parse","items":{its},"end":{end},"r":{r}}}"#);
    error
}

// ---------------------------------------------------------------- encode

/// What `encode_block` is given: the delta bytes and the parts around it.
#[derive(Clone)]
struct Part {
    d: Vec<u8>,
    heads: Vec<Cid>,
    links: Vec<(Cid, String)>,
    sig: Option<Cid>,
    enc: Option<Cid>,
}

impl Part {
    fn encoded_len(&self) -> usize {
        let mut heads = self.heads.clone();
        let mut links: Vec<Link<'_>> = self.links.iter().map(|(c, n)| Link { name: n, cid: *c }).collect();
        BlockParts {
            delta: &self.d,
            heads: &mut heads,
            links: &mut links,
            encryption: self.enc,
            signature: self.sig,
        }
        .encoded_len()
    }

    fn has_duplicate_heads(&self) -> bool {
        (0..self.heads.len()).any(|i| self.heads[..i].contains(&self.heads[i]))
    }

    fn has_duplicate_links(&self) -> bool {
        (0..self.links.len()).any(|i| self.links[..i].contains(&self.links[i]))
    }
}

/// `encode_block` into a buffer of `cap` bytes, recorded; the block on success.
fn enc_ev(out: &mut String, p: &Part, cap: usize) -> Result<Vec<u8>, BlockError> {
    let (d_items, dend) = items(&p.d);
    let mut heads = p.heads.clone();
    let mut links: Vec<Link<'_>> = p.links.iter().map(|(c, n)| Link { name: n, cid: *c }).collect();
    let (heads_before, links_before) = (heads_json(&heads), links_json(&links));
    let mut buf = vec![0u8; cap];
    let r = encode_block(
        &mut buf,
        &mut BlockParts {
            delta: &p.d,
            heads: &mut heads,
            links: &mut links,
            encryption: p.enc,
            signature: p.sig,
        },
    );
    let (res, block) = match r {
        Ok(len) => {
            let block = buf[..len].to_vec();
            let (its, end) = items(&block);
            (
                format!(r#"{{"ok":{{"len":{len},"items":{its},"end":{end}}}}}"#),
                Ok(block),
            )
        }
        Err(e) => (format!(r#"{{"err":{}}}"#, berr(&e)), Err(e)),
    };
    let _ = writeln!(
        out,
        r#"{{"t":"enc","d":{d_items},"dend":{dend},"heads":{heads_before},"links":{links_before},"sig":{},"enc":{},"cap":{cap},"r":{res},"after":{{"heads":{},"links":{}}}}}"#,
        opt_json(p.sig),
        opt_json(p.enc),
        heads_json(&heads),
        links_json(&links)
    );
    block
}

/// The parts, sorted as `encode_block` sorts them, are what `parse` reads back.
fn check_roundtrip(p: &Part, block: &[u8]) {
    let b = BlockRef::parse(block).unwrap();
    assert_eq!(b.delta(), p.d.as_slice());
    let mut heads = p.heads.clone();
    heads.sort_by(Cid::cmp_text);
    let got: Vec<Vec<u8>> = b.heads().map(|c| c.as_bytes().to_vec()).collect();
    assert_eq!(got, heads.iter().map(|c| c.as_bytes().to_vec()).collect::<Vec<_>>());
    let mut links = p.links.clone();
    links.sort_by(|a, b| a.0.cmp_text(&b.0).then_with(|| a.1.cmp(&b.1)));
    let got: Vec<(Vec<u8>, String)> = b
        .links()
        .map(|l| (l.cid.as_bytes().to_vec(), l.name.to_owned()))
        .collect();
    assert_eq!(
        got,
        links
            .iter()
            .map(|(c, n)| (c.as_bytes().to_vec(), n.clone()))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        b.signature().map(|c| c.as_bytes().to_vec()),
        p.sig.map(|c| c.as_bytes().to_vec())
    );
    assert_eq!(
        b.encryption().map(|c| c.as_bytes().to_vec()),
        p.enc.map(|c| c.as_bytes().to_vec())
    );
}

/// One combination of `DagBlock.EncCases` with a good delta: at 4096 bytes, at the exact size, one byte less and none.
fn good_case(out: &mut String, p: &Part, blocks: &mut Vec<Vec<u8>>) {
    let r = enc_ev(out, p, 4096);
    if p.has_duplicate_heads() {
        assert_eq!(r, Err(BlockError::Unordered("heads")));
    } else if p.has_duplicate_links() {
        assert_eq!(r, Err(BlockError::Unordered("links")));
    } else {
        let block = r.unwrap();
        let el = p.encoded_len();
        assert_eq!(block.len(), el, "encoded_len is not the bytes written");
        check_roundtrip(p, &block);
        assert_eq!(enc_ev(out, p, el).as_ref(), Ok(&block));
        assert_eq!(
            enc_ev(out, p, el - 1),
            Err(BlockError::Wire(WireError::BufferTooSmall { needed: 1 }))
        );
        assert_eq!(
            enc_ev(out, p, 0),
            Err(BlockError::Wire(WireError::BufferTooSmall { needed: el }))
        );
        blocks.push(block);
    }
}

// ---------------------------------------------------------------- the checked domain

enum Want {
    Accept,
    Refuse(&'static str),
}

const TRAILING: &str = r#"{"k":"trailing"}"#;
const MISSING: &str = r#"{"k":"missingDelta"}"#;
const UNORD_HEADS: &str = r#"{"k":"unordered","what":"heads"}"#;
const UNORD_LINKS: &str = r#"{"k":"unordered","what":"links"}"#;
const CID_VERSION: &str = r#"{"k":"cid","c":"version"}"#;
const CID_TRAILING: &str = r#"{"k":"cid","c":"trailing"}"#;
const CID_WIRE: &str = r#"{"k":"cid","c":"wire"}"#;
const WIRE: &str = r#"{"k":"wire","w":"cbor"}"#;

/// The 32 hand-built blocks of `DagBlock.StrictCases`: the items, whether the bytes end after them, the expectation.
fn strict_cases() -> Vec<(Vec<T>, bool, Want)> {
    use Want::{Accept, Refuse};
    let d1 = vec![T::U(0)];
    let (la, lb) = ((&K1[..], "a"), (&K1[..], "b"));
    let unordered_map = vec![T::Map(2), txt("b"), T::Null, txt("a"), T::Null];
    vec![
        (blk(1, delta_e(&d1)), false, Refuse(TRAILING)),
        ([blk(1, delta_e(&d1)), vec![T::U(0)]].concat(), true, Refuse(TRAILING)),
        (blk(1, heads_e(&[&K2])), true, Refuse(MISSING)),
        (
            blk(2, [delta_e(&d1), heads_e(&[&K1, &K2])].concat()),
            true,
            Refuse(UNORD_HEADS),
        ),
        (
            blk(2, [delta_e(&d1), heads_e(&[&K1, &K1])].concat()),
            true,
            Refuse(UNORD_HEADS),
        ),
        (
            blk(2, [delta_e(&d1), links_e(&[lb, la])].concat()),
            true,
            Refuse(UNORD_LINKS),
        ),
        (
            blk(2, [delta_e(&d1), links_e(&[la, la])].concat()),
            true,
            Refuse(UNORD_LINKS),
        ),
        (
            blk(2, [delta_e(&d1), heads_e(&[&BAD_V2])].concat()),
            true,
            Refuse(CID_VERSION),
        ),
        (
            blk(2, [delta_e(&d1), heads_e(&[&K3_TRAILING])].concat()),
            true,
            Refuse(CID_TRAILING),
        ),
        (
            blk(2, [delta_e(&d1), vec![txt("heads"), T::U(0)]].concat()),
            true,
            Refuse(CID_WIRE),
        ),
        (
            blk(2, [delta_e(&d1), vec![txt("links"), T::U(0)]].concat()),
            true,
            Refuse(r#"{"k":"malformed","what":"links is not an array"}"#),
        ),
        (
            blk(
                2,
                [
                    delta_e(&d1),
                    vec![txt("links"), T::Arr(1), T::Map(2), txt("link")],
                    cid_items(&K1),
                    vec![txt("name"), T::U(0)],
                ]
                .concat(),
            ),
            true,
            Refuse(r#"{"k":"malformed","what":"link name is not text"}"#),
        ),
        (
            blk(
                2,
                [
                    delta_e(&d1),
                    vec![txt("links"), T::Arr(1), T::Map(1), txt("link")],
                    cid_items(&K1),
                ]
                .concat(),
            ),
            true,
            Refuse(r#"{"k":"malformed","what":"link needs a link and a name"}"#),
        ),
        (
            blk(
                2,
                [
                    delta_e(&d1),
                    vec![txt("links"), T::Arr(1), T::Map(2), txt("name"), txt("a"), txt("link")],
                    cid_items(&K1),
                ]
                .concat(),
            ),
            true,
            Refuse(WIRE),
        ),
        (
            blk(
                2,
                [
                    delta_e(&d1),
                    vec![txt("signature"), T::Tag, T::Bts([&[1u8][..], &K1].concat())],
                ]
                .concat(),
            ),
            true,
            Refuse(CID_WIRE),
        ),
        (
            blk(2, [delta_e(&d1), vec![txt("signature"), T::U(0)]].concat()),
            true,
            Refuse(CID_WIRE),
        ),
        (blk(2, [heads_e(&[&K1]), delta_e(&d1)].concat()), true, Refuse(WIRE)),
        (blk(2, [delta_e(&d1), delta_e(&d1)].concat()), true, Refuse(WIRE)),
        (blk(1, vec![T::U(0), T::U(0)]), true, Refuse(WIRE)),
        (vec![T::Arr(0)], true, Refuse(WIRE)),
        (vec![], true, Refuse(WIRE)),
        (blk(3, delta_e(&d1)), true, Refuse(WIRE)),
        (blk(1, delta_e(&unordered_map)), true, Refuse(WIRE)),
        (blk(1, delta_e(&deep(64))), true, Accept),
        (blk(1, delta_e(&deep(65))), true, Refuse(WIRE)),
        (blk(2, [vec![txt("z"), T::U(0)], delta_e(&d1)].concat()), true, Accept),
        (
            blk(
                2,
                [
                    delta_e(&d1),
                    vec![txt("links"), T::Arr(1), T::Map(3), txt("a"), T::U(0), txt("link")],
                    cid_items(&K1),
                    vec![txt("name"), txt("a")],
                ]
                .concat(),
            ),
            true,
            Accept,
        ),
        (
            blk(2, [delta_e(&d1), vec![txt("heads"), T::Null]].concat()),
            true,
            Accept,
        ),
        (
            blk(2, [delta_e(&d1), vec![txt("heads"), T::Arr(0)]].concat()),
            true,
            Accept,
        ),
        (
            blk(2, [delta_e(&d1), vec![txt("links"), T::Null]].concat()),
            true,
            Accept,
        ),
        (
            blk(2, [delta_e(&d1), vec![txt("signature"), T::Null]].concat()),
            true,
            Accept,
        ),
        (blk(2, [delta_e(&d1), sig_e(&K3)].concat()), true, Accept),
    ]
}

/// The single-item mutations of an item list: swap, drop, duplicate, replace by seven fillers, count plus and minus
/// one, an item appended.
fn mutations(s: &[T]) -> Vec<Vec<T>> {
    let fillers = [T::U(0), T::Null, txt("a"), T::Arr(0), T::Map(0), T::Tag, txt("name")];
    let mut v = Vec::new();
    for i in 0..s.len() - 1 {
        let mut m = s.to_vec();
        m.swap(i, i + 1);
        v.push(m);
    }
    for i in 0..s.len() {
        let mut m = s.to_vec();
        m.remove(i);
        v.push(m);
        let mut m = s.to_vec();
        m.insert(i, s[i].clone());
        v.push(m);
        for f in &fillers {
            let mut m = s.to_vec();
            m[i] = f.clone();
            v.push(m);
        }
        for dn in [-1i64, 1] {
            let counted = match s[i] {
                T::Arr(n) => n.checked_add_signed(dn).map(T::Arr),
                T::Map(n) => n.checked_add_signed(dn).map(T::Map),
                _ => None,
            };
            if let Some(c) = counted {
                let mut m = s.to_vec();
                m[i] = c;
                v.push(m);
            }
        }
    }
    let mut m = s.to_vec();
    m.push(T::U(0));
    v.push(m);
    v
}

// ---------------------------------------------------------------- random inputs

fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

fn random_bytes(rng: &mut SplitMix64, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    rng.fill(&mut v);
    v
}

fn letters(rng: &mut SplitMix64, max: u64) -> Vec<u8> {
    (0..below(rng, max + 1)).map(|_| b'a' + below(rng, 3) as u8).collect()
}

/// One random item (a container with its content) of nesting depth up to `depth`, with map keys in canonical order.
fn random_value(rng: &mut SplitMix64, depth: u32) -> Vec<T> {
    let kind = if depth == 0 { below(rng, 4) } else { below(rng, 7) };
    match kind {
        0 => vec![T::U(below(rng, 300))],
        1 => vec![T::Null],
        2 => vec![T::Txt(letters(rng, 3))],
        3 => {
            let n = below(rng, 5) as usize;
            vec![T::Bts(random_bytes(rng, n))]
        }
        4 | 5 => {
            let n = below(rng, 4);
            let mut v = vec![T::Arr(n)];
            for _ in 0..n {
                v.extend(random_value(rng, depth - 1));
            }
            v
        }
        _ => {
            let mut keys: Vec<&str> = ["a", "b", "c", "ab", "zz"]
                .into_iter()
                .filter(|_| below(rng, 2) == 0)
                .collect();
            keys.sort_by_key(|k| (k.len(), *k));
            let mut v = vec![T::Map(keys.len() as u64)];
            for k in keys {
                v.push(txt(k));
                v.extend(random_value(rng, depth - 1));
            }
            v
        }
    }
}

/// Random parts over a pool of six CIDs.
fn random_part(rng: &mut SplitMix64, pool: &[Cid]) -> Part {
    let mut delta = random_value(rng, 4);
    match below(rng, 12) {
        0 => delta.push(T::U(0)),
        1 => delta.clear(),
        _ => {}
    }
    let some = |rng: &mut SplitMix64| pool[below(rng, pool.len() as u64) as usize];
    let heads = (0..below(rng, 5)).map(|_| some(rng)).collect();
    let links = (0..below(rng, 5))
        .map(|_| {
            let c = some(rng);
            (c, String::from_utf8(letters(rng, 3)).unwrap())
        })
        .collect();
    let sig = (below(rng, 2) == 0).then(|| some(rng));
    let enc = (below(rng, 2) == 0).then(|| some(rng));
    Part {
        d: write_items(&delta, true),
        heads,
        links,
        sig,
        enc,
    }
}

fn random_item_list(rng: &mut SplitMix64, pool: &[Cid]) -> Vec<T> {
    let keys = ["delta", "heads", "links", "signature", "encryption", "zz", "a"];
    if below(rng, 2) == 0 {
        let n = below(rng, 4);
        let mut v = vec![T::Map(n + u64::from(below(rng, 6) == 0))];
        for _ in 0..n {
            v.push(txt(keys[below(rng, keys.len() as u64) as usize]));
            let c = pool[below(rng, pool.len() as u64) as usize];
            match below(rng, 8) {
                0 => v.push(T::U(below(rng, 3))),
                1 => v.push(T::Null),
                2 => v.push(txt("a")),
                3 => v.push(T::Arr(0)),
                4 => {
                    v.push(T::Arr(1));
                    v.extend(cid_items(c.as_bytes()));
                }
                5 => v.extend(cid_items(c.as_bytes())),
                6 => v.extend([T::Map(1), txt("name"), T::Null]),
                _ => v.extend(random_value(rng, 2)),
            }
        }
        v
    } else {
        (0..1 + below(rng, 12))
            .flat_map(|_| match below(rng, 7) {
                0 => vec![T::U(below(rng, 3))],
                1 => vec![T::Null],
                2 => vec![txt("delta")],
                3 => vec![T::Arr(below(rng, 3))],
                4 => vec![T::Map(below(rng, 3))],
                5 => vec![T::Tag],
                _ => vec![T::Bts(random_bytes(rng, 3))],
            })
            .collect()
    }
}

#[test]
fn dag_block_traces_are_consistent_with_the_code() {
    let mut out = String::new();
    let mut rng = SplitMix64::traced(0xda9c_b10c);
    let mut blocks: Vec<Vec<u8>> = Vec::new();

    // encode: every combination of DagBlock.EncCases
    let deltas: [Vec<u8>; 3] = [
        write_items(&[T::U(0)], true),
        write_items(&[T::Map(1), txt("a"), T::Arr(2), T::U(1), T::Null], true),
        write_items(&cid_items(&K3), true),
    ];
    let head_seqs: [&[&[u8]]; 7] = [
        &[],
        &[&K1],
        &[&K1, &K2],
        &[&K2, &K1],
        &[&K1, &K1],
        &[&K3, &K2, &K1],
        &[&K1, &K3, &K2],
    ];
    let (la, lb, lab, lc, le): (
        (&[u8], &str),
        (&[u8], &str),
        (&[u8], &str),
        (&[u8], &str),
        (&[u8], &str),
    ) = ((&K1, "a"), (&K1, "b"), (&K1, "ab"), (&K2, "a"), (&K3, ""));
    let link_seqs: [&[(&[u8], &str)]; 7] = [&[], &[la], &[lb, la], &[lc, la], &[la, la], &[lb, lab], &[le, lc, lb]];
    for d in &deltas {
        for hs in head_seqs {
            for ls in link_seqs {
                for sig in [None, Some(K1)] {
                    for enc in [None, Some(K2)] {
                        let p = Part {
                            d: d.clone(),
                            heads: hs.iter().map(|h| cid(h)).collect(),
                            links: ls.iter().map(|(c, n)| (cid(c), (*n).to_owned())).collect(),
                            sig: sig.map(|c| cid(&c)),
                            enc: enc.map(|c| cid(&c)),
                        };
                        good_case(&mut out, &p, &mut blocks);
                    }
                }
            }
        }
    }
    let bad_deltas: [Vec<u8>; 5] = [
        write_items(&[T::U(0), T::U(1)], true),
        write_items(&[T::Arr(2), T::U(0)], true),
        write_items(&[T::Map(2), txt("b"), T::Null, txt("a"), T::Null], true),
        write_items(&[], true),
        write_items(&[T::U(0)], false),
    ];
    for d in &bad_deltas {
        let p = Part {
            d: d.clone(),
            heads: vec![cid(&K1)],
            links: vec![],
            sig: None,
            enc: None,
        };
        let r = enc_ev(&mut out, &p, 4096);
        assert!(
            matches!(r, Err(BlockError::Wire(_))),
            "a delta that is not one item was accepted"
        );
    }
    let pool: Vec<Cid> = (0..6)
        .map(|i| {
            let hash = [0x12, 0x1e, 0, 0, 0x13, 0][i];
            let digest = random_bytes(&mut rng, if hash == 0x12 || hash == 0x1e { 32 } else { i % 4 });
            Cid::new(if i % 2 == 0 { 0x55 } else { 0x71 }, hash, &digest).unwrap()
        })
        .collect();
    for _ in 0..300 {
        let p = random_part(&mut rng, &pool);
        let el = p.encoded_len();
        let caps = [el, el.saturating_sub(1), el + 3, 0, el / 2, 4096];
        for cap in caps {
            if let Ok(block) = enc_ev(&mut out, &p, cap) {
                check_roundtrip(&p, &block);
                blocks.push(block);
            }
        }
    }

    // parse: the hand-built blocks
    for (list, end, want) in strict_cases() {
        let got = parse_ev(&mut out, &write_items(&list, end));
        match (want, got) {
            (Want::Accept, None) => {}
            (Want::Refuse(w), Some(g)) => assert_eq!(w, g, "a hand-built block gave another error"),
            (_, g) => panic!("a hand-built block gave the wrong verdict: {g:?}"),
        }
    }

    // parse: every single-item mutation of the three bases of DagBlock.MutParts
    let d2 = deltas[1].clone();
    let mut_parts = [
        Part {
            d: d2,
            heads: vec![cid(&K1), cid(&K2)],
            links: vec![(cid(&K1), "a".to_owned())],
            sig: Some(cid(&K1)),
            enc: Some(cid(&K2)),
        },
        Part {
            d: deltas[0].clone(),
            heads: vec![],
            links: vec![(cid(&K1), "b".to_owned()), (cid(&K1), "ab".to_owned())],
            sig: None,
            enc: None,
        },
        Part {
            d: deltas[2].clone(),
            heads: vec![cid(&K3)],
            links: vec![(cid(&K3), String::new()), (cid(&K2), "a".to_owned())],
            sig: None,
            enc: Some(cid(&K2)),
        },
    ];
    for p in &mut_parts {
        let base = enc_ev(&mut String::new(), p, 4096).unwrap();
        let base_items = to_items(&base);
        assert_eq!(write_items(&base_items, true), base);
        parse_ev(&mut out, &write_items(&base_items, false));
        for m in mutations(&base_items) {
            parse_ev(&mut out, &write_items(&m, true));
        }
    }

    // parse: every block the encoder wrote, random byte flips, cuts and appends of them, random item lists
    let written = blocks.clone();
    for b in &written {
        assert!(parse_ev(&mut out, b).is_none(), "a block the encoder wrote was refused");
    }
    for _ in 0..2000 {
        let mut b = written[below(&mut rng, written.len() as u64) as usize].clone();
        match below(&mut rng, 3) {
            0 => {
                let i = below(&mut rng, b.len() as u64) as usize;
                b[i] = rng.next_u64() as u8;
            }
            1 => b.truncate(below(&mut rng, b.len() as u64) as usize),
            _ => {
                let n = 1 + below(&mut rng, 3) as usize;
                b.extend(random_bytes(&mut rng, n));
            }
        }
        parse_ev(&mut out, &b);
    }
    for _ in 0..300 {
        let list = random_item_list(&mut rng, &pool);
        let end = below(&mut rng, 8) != 0;
        parse_ev(&mut out, &write_items(&list, end));
    }

    assert!(out.lines().count() > 4000);
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir).join("tla");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("dag_block.ndjson"), out).unwrap();
}
