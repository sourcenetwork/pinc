//! Trace generation for the CIDs of `pinc-dag` (`cid/*`): the real `Cid::new`, `CidRef::parse`, `CidRef::parse_prefix`,
//! `CidRef::encode_text`, `Cid::parse_text`, `cmp_text`, `CidRef::verify` and `Cid::for_block`, recorded as ndjson
//! (`tla/dag_cid.ndjson` under `PINC_TRACE_DIR`) for the TLA+ trace check (`TraceDagCid.tla`).
//!
//! A `u64` is written as four 16-bit limbs, least significant first, which `U64.tla` reads (TLC integers are 32 bits
//! wide). One event is written per call, with its result or its error. The calls run on the boundary classes of
//! `DagCid.cfg` (codecs, hash codes, digest lengths, cuts, rests, header mutations, every byte string of up to 4
//! bytes over the class alphabet, texts over the class alphabet and their mutations) and on seeded random inputs. The
//! genuine digest of a block under a known hash is computed here with the reference `sha2` and `blake3` crates,
//! independent of `pinc-dag`, and recorded as `g`. Every call is also checked here against the property the module
//! documents, so the test is meaningful without the proof tools. Nothing is written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop,
    clippy::too_many_lines,
    clippy::panic,
    clippy::many_single_char_names
)]

use std::cmp::Ordering;
use std::fmt::Write as _;

use pinc_dag::cid::{Cid, CidError, CidRef, MAX_TEXT_LEN, cmp_text};
use pinc_tests::{SplitMix64, trace_cases};
use pinc_wire::{WireError, varint};
use sha2::{Digest, Sha256};

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

fn wire_err(e: &WireError) -> String {
    match e {
        WireError::Truncated { needed } => format!(r#"{{"k":"wire","w":"truncated","needed":{needed}}}"#),
        WireError::BufferTooSmall { needed } => format!(r#"{{"k":"wire","w":"small","needed":{needed}}}"#),
        WireError::VarintTooLong => r#"{"k":"wire","w":"toolong","needed":0}"#.to_owned(),
        WireError::VarintNonMinimal => r#"{"k":"wire","w":"nonminimal","needed":0}"#.to_owned(),
        WireError::VarintOverflow => r#"{"k":"wire","w":"overflow","needed":0}"#.to_owned(),
        other => panic!("a wire error the model does not know: {other:?}"),
    }
}

/// A `CidError` as the model's error record.
fn err(e: &CidError) -> String {
    match e {
        CidError::CidV0 => r#"{"k":"v0"}"#.to_owned(),
        CidError::UnsupportedVersion(v) => format!(r#"{{"k":"version","v":{}}}"#, limbs(*v)),
        CidError::DigestTooLong(n) => format!(r#"{{"k":"toolong","len":{}}}"#, limbs(*n)),
        CidError::DigestLenMismatch { hash, len } => {
            format!(r#"{{"k":"mismatch","hash":{},"len":{}}}"#, limbs(*hash), limbs(*len))
        }
        CidError::TrailingBytes => r#"{"k":"trailing"}"#.to_owned(),
        CidError::UnsupportedHash(h) => format!(r#"{{"k":"unsupported","hash":{}}}"#, limbs(*h)),
        CidError::DigestMismatch => r#"{"k":"digest"}"#.to_owned(),
        CidError::BadText(why) => {
            assert!(!why.contains(['"', '\\']), "a reason that needs escaping in JSON");
            format!(r#"{{"k":"text","why":"{why}"}}"#)
        }
        CidError::BufferTooSmall { needed } => format!(r#"{{"k":"small","needed":{needed}}}"#),
        CidError::Wire(w) => wire_err(w),
    }
}

/// A parsed CID as the model's record.
fn cid_obj(c: &CidRef<'_>) -> String {
    format!(
        r#"{{"raw":{},"codec":{},"hash":{},"dlen":{}}}"#,
        arr(c.as_bytes()),
        limbs(c.codec()),
        limbs(c.hash_code()),
        c.digest().len()
    )
}

const DIGITS: &[u8; 32] = b"abcdefghijklmnopqrstuvwxyz234567";

/// The text of `bytes` by the definition (digit `j` holds bits `5j` to `5j + 4`, the bits past the end zero), apart
/// from the code.
fn base32(bytes: &[u8]) -> String {
    let mut s = String::from("b");
    for j in 0..(8 * bytes.len()).div_ceil(5) {
        let (q, r) = (5 * j / 8, 5 * j % 8);
        let b0 = u32::from(bytes.get(q).copied().unwrap_or(0));
        let b1 = u32::from(bytes.get(q + 1).copied().unwrap_or(0));
        s.push(DIGITS[(((b0 << 8 | b1) >> (11 - r)) & 31) as usize] as char);
    }
    s
}

/// The reference digest of `blk` under a known hash code, empty for any other code.
fn oracle(hash: u64, blk: &[u8]) -> Vec<u8> {
    match hash {
        0x12 => Sha256::digest(blk).to_vec(),
        0x1e => blake3::hash(blk).as_bytes().to_vec(),
        _ => Vec::new(),
    }
}

fn ramp(n: usize) -> Vec<u8> {
    (1..=n).map(|i| ((37 * i + 11) % 256) as u8).collect()
}

fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

fn random_bytes(rng: &mut SplitMix64, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    rng.fill(&mut v);
    v
}

fn pick(rng: &mut SplitMix64, set: &[u64]) -> u64 {
    set[below(rng, set.len() as u64) as usize]
}

// ---------------------------------------------------------------- events

/// `Cid::new`, recorded.
fn new_ev(out: &mut String, codec: u64, hash: u64, d: &[u8]) -> Option<Cid> {
    let r = Cid::new(codec, hash, d);
    let res = match &r {
        Ok(c) => {
            let b = c.as_bytes();
            assert!(b.len() <= 84, "a CID longer than 84 bytes");
            let p = CidRef::parse(b).unwrap();
            assert_eq!((p.codec(), p.hash_code(), p.digest()), (codec, hash, d));
            let mut trailing = b.to_vec();
            trailing.push(0);
            assert_eq!(CidRef::parse(&trailing), Err(CidError::TrailingBytes));
            format!(r#"{{"ok":{}}}"#, arr(b))
        }
        Err(e) => format!(r#"{{"err":{}}}"#, err(e)),
    };
    let _ = writeln!(
        out,
        r#"{{"t":"new","codec":{},"hash":{},"d":{},"r":{res}}}"#,
        limbs(codec),
        limbs(hash),
        arr(d)
    );
    r.ok()
}

/// An accepted input is the canonical bytes of its parts.
fn assert_reencodes(c: &CidRef<'_>, input: &[u8]) {
    let again = Cid::new(c.codec(), c.hash_code(), c.digest()).unwrap();
    assert_eq!(again.as_bytes(), input, "an accepted input does not re-encode");
}

fn parse_ev(out: &mut String, input: &[u8]) {
    let r = match CidRef::parse(input) {
        Ok(c) => {
            assert_reencodes(&c, input);
            format!(r#"{{"ok":{}}}"#, cid_obj(&c))
        }
        Err(e) => format!(r#"{{"err":{}}}"#, err(&e)),
    };
    let _ = writeln!(out, r#"{{"t":"parse","in":{},"r":{r}}}"#, arr(input));
}

fn prefix_ev(out: &mut String, input: &[u8]) {
    let r = match CidRef::parse_prefix(input) {
        Ok((c, rest)) => {
            assert_reencodes(&c, c.as_bytes());
            assert_eq!(
                [c.as_bytes(), rest].concat(),
                input,
                "parse_prefix does not split the input"
            );
            format!(r#"{{"ok":{},"rest":{}}}"#, cid_obj(&c), arr(rest))
        }
        Err(e) => format!(r#"{{"err":{}}}"#, err(&e)),
    };
    let _ = writeln!(out, r#"{{"t":"prefix","in":{},"r":{r}}}"#, arr(input));
}

fn parse_and_prefix(out: &mut String, input: &[u8]) {
    parse_ev(out, input);
    prefix_ev(out, input);
}

fn etext_ev(out: &mut String, b: &[u8], cap: usize) {
    let c = CidRef::parse(b).unwrap();
    let n = 1 + (8 * b.len()).div_ceil(5);
    let mut buf = vec![0u8; cap];
    let r = match c.encode_text(&mut buf) {
        Ok(t) => {
            assert!(cap >= n);
            assert_eq!(t.len(), n);
            assert!(t.starts_with('b'));
            assert_eq!(t, base32(b), "encode_text is not the base32 text");
            assert_eq!(
                Cid::parse_text(t).unwrap().as_bytes(),
                b,
                "parse_text does not invert encode_text"
            );
            format!(r#"{{"ok":{}}}"#, arr(t.as_bytes()))
        }
        Err(e) => {
            assert!(cap < n);
            if cap + 1 == n {
                assert_eq!(e, CidError::BufferTooSmall { needed: 1 });
            }
            format!(r#"{{"err":{}}}"#, err(&e))
        }
    };
    let _ = writeln!(out, r#"{{"t":"etext","in":{},"cap":{cap},"r":{r}}}"#, arr(b));
}

fn ptext_ev(out: &mut String, text: &str) {
    let r = match Cid::parse_text(text) {
        Ok(c) => {
            let mut buf = [0u8; MAX_TEXT_LEN];
            assert_eq!(
                c.encode_text(&mut buf).unwrap(),
                text,
                "an accepted text does not re-encode"
            );
            format!(r#"{{"ok":{}}}"#, arr(c.as_bytes()))
        }
        Err(e) => format!(r#"{{"err":{}}}"#, err(&e)),
    };
    let _ = writeln!(out, r#"{{"t":"ptext","in":{},"r":{r}}}"#, arr(text.as_bytes()));
}

fn cmp_ev(out: &mut String, a: &[u8], b: &[u8]) {
    let (ca, cb) = (CidRef::parse(a).unwrap(), CidRef::parse(b).unwrap());
    let ord = cmp_text(ca, cb);
    assert_eq!(
        ord,
        ca.to_string().cmp(&cb.to_string()),
        "cmp_text is not the order of the texts"
    );
    assert_eq!(ord, cmp_text(cb, ca).reverse(), "cmp_text is not antisymmetric");
    assert_eq!(ord == Ordering::Equal, a == b);
    let r = match ord {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    };
    let _ = writeln!(out, r#"{{"t":"cmp","a":{},"b":{},"r":{r}}}"#, arr(a), arr(b));
}

fn verify_ev(out: &mut String, b: &[u8], blk: &[u8]) -> Result<(), CidError> {
    let c = CidRef::parse(b).unwrap();
    let g = oracle(c.hash_code(), blk);
    let r = c.verify(blk);
    let res = match &r {
        Ok(()) => r#"{"ok":true}"#.to_owned(),
        Err(e) => format!(r#"{{"err":{}}}"#, err(e)),
    };
    let _ = writeln!(
        out,
        r#"{{"t":"verify","in":{},"blk":{},"g":{},"r":{res}}}"#,
        arr(b),
        arr(blk),
        arr(&g)
    );
    r
}

fn forblock_ev(out: &mut String, codec: u64, hash: u64, blk: &[u8]) -> Option<Cid> {
    let g = oracle(hash, blk);
    let r = Cid::for_block(codec, hash, blk);
    let res = match &r {
        Ok(c) => {
            assert_eq!(c.digest(), g, "the digest of for_block is not the reference digest");
            format!(r#"{{"ok":{}}}"#, arr(c.as_bytes()))
        }
        Err(e) => {
            assert!(g.is_empty(), "a known hash was refused");
            assert_eq!(*e, CidError::UnsupportedHash(hash));
            format!(r#"{{"err":{}}}"#, err(e))
        }
    };
    let _ = writeln!(
        out,
        r#"{{"t":"forblock","codec":{},"hash":{},"blk":{},"g":{},"r":{res}}}"#,
        limbs(codec),
        limbs(hash),
        arr(blk),
        arr(&g)
    );
    r.ok()
}

// ---------------------------------------------------------------- inputs

/// The inputs derived from an accepted CID: itself, with rests, every cut, every single-byte mutation of the header
/// and the last byte.
fn derived_inputs(b: &[u8]) -> Vec<Vec<u8>> {
    let c = CidRef::parse(b).unwrap();
    // the 0-based index of the digest length byte
    let len_at = varint::encoded_len(c.codec()) + varint::encoded_len(c.hash_code()) + 1;
    let rests: [&[u8]; 5] = [&[], &[0], &[1, 0x71], &[0x12, 0x20], &[0xff]];
    let mut v = vec![b.to_vec()];
    v.extend(rests.iter().map(|r| [b, *r].concat()));
    v.extend((0..b.len()).map(|j| b[..j].to_vec()));
    for j in (0..b.len()).filter(|&j| j <= len_at + 1 || j == b.len() - 1) {
        for m in [0u8, 1, 0x12, 0x80, 0xff] {
            if m != b[j] {
                let mut x = b.to_vec();
                x[j] = m;
                v.push(x);
            }
        }
    }
    v
}

/// The class inputs of `DagCid.Classes` for an accepted CID.
fn class_inputs(b: &[u8]) -> Vec<Vec<u8>> {
    let c = CidRef::parse(b).unwrap();
    let len_at = varint::encoded_len(c.codec()) + varint::encoded_len(c.hash_code()) + 1;
    let with_len = |n: u8| {
        let mut x = b.to_vec();
        x[len_at] = n;
        x
    };
    let mut v = vec![[&[0x12u8, 0x20][..], b].concat()];
    for version in [0u8, 2, 3, 127] {
        let mut x = b.to_vec();
        x[0] = version;
        v.push(x);
    }
    v.push([&[0x81u8, 0][..], &b[1..]].concat());
    v.push([&[0x80u8; 9][..], b].concat());
    v.extend([65u8, 100, 127].map(with_len));
    let dlen = c.digest().len();
    if matches!(c.hash_code(), 0x12 | 0x1e) {
        v.extend([0u8, 31, 33, 64].map(with_len));
    } else if dlen < 64 {
        v.push(with_len(dlen as u8 + 1));
    }
    v
}

/// The mutations of a CID text: characters 2, 3 and the last two set to five values, the last one and two dropped,
/// `a` and `aa` appended.
fn text_mutations(t: &str) -> Vec<String> {
    let b = t.as_bytes();
    let n = b.len();
    let mut v: Vec<Vec<u8>> = Vec::new();
    for j in [2, 3, n - 1, n] {
        for ch in *b"ab72z" {
            let mut m = b.to_vec();
            m[j - 1] = ch;
            v.push(m);
        }
    }
    v.push(b[..n - 1].to_vec());
    v.push(b[..n - 2].to_vec());
    let mut x = b.to_vec();
    x.push(b'a');
    v.push(x.clone());
    x.push(b'a');
    v.push(x);
    v.into_iter().map(|m| String::from_utf8(m).unwrap()).collect()
}

/// Every string of `0..=max_len` bytes over `alphabet`.
fn strings_over(alphabet: &[u8], max_len: usize) -> Vec<Vec<u8>> {
    let mut all = vec![Vec::new()];
    let mut level = vec![Vec::new()];
    for _ in 0..max_len {
        level = level
            .iter()
            .flat_map(|s: &Vec<u8>| {
                alphabet.iter().map(move |&b| {
                    let mut t = s.clone();
                    t.push(b);
                    t
                })
            })
            .collect();
        all.extend(level.iter().cloned());
    }
    all
}

/// A random string with the shape of a CID about two times in three.
fn random_string(rng: &mut SplitMix64) -> Vec<u8> {
    let n = below(rng, 91) as usize;
    let mut v = random_bytes(rng, n);
    if n > 0 && below(rng, 3) != 0 {
        v[0] = 1;
    }
    for b in v.iter_mut().skip(1) {
        if below(rng, 4) != 0 {
            *b &= 0x7f;
        }
    }
    if n >= 5 && below(rng, 2) == 0 {
        v[2] = [0, 0x12, 0x1e, 0x13][below(rng, 4) as usize];
        v[3] = if below(rng, 2) == 0 { 32 } else { v[3] % 70 };
    }
    v
}

#[test]
fn dag_cid_traces_are_consistent_with_the_code() {
    let mut out = String::new();
    let mut rng = SplitMix64::traced(0xda9c_1d01);
    let max63 = (1u64 << 63) - 1;

    // new: the class grid, the fill cases and random calls
    let codecs = [0x55, 0x71, 0x80, max63, 1 << 63, u64::MAX];
    let hashes = [0x12, 0x1e, 0, 0x13, max63, 1 << 63];
    let mut grid: Vec<Cid> = Vec::new();
    for &codec in &codecs {
        for &hash in &hashes {
            for n in [0, 1, 31, 32, 33, 64, 65] {
                grid.extend(new_ev(&mut out, codec, hash, &ramp(n)));
            }
        }
    }
    for (codec, hash, n) in [(0x71, 0x1e, 32), (max63, max63, 64)] {
        for x in [0u8, 0xff] {
            grid.extend(new_ev(&mut out, codec, hash, &vec![x; n]));
        }
    }
    assert!(
        grid.iter().any(|c| c.as_bytes().len() == 84),
        "no CID of the longest size"
    );
    let mut random_ok: Vec<Cid> = Vec::new();
    for _ in 0..trace_cases(100, 500) {
        let class = |rng: &mut SplitMix64, set: &[u64]| {
            if below(rng, 2) == 0 {
                pick(rng, set)
            } else {
                rng.next_u64() >> (1 + below(rng, 63))
            }
        };
        let codec = class(&mut rng, &codecs);
        let hash = class(&mut rng, &hashes);
        let n = if matches!(hash, 0x12 | 0x1e) && below(&mut rng, 2) == 0 {
            32
        } else {
            below(&mut rng, 71) as usize
        };
        let d = random_bytes(&mut rng, n);
        random_ok.extend(new_ev(&mut out, codec, hash, &d));
    }
    assert!(grid.len() > 50 && random_ok.len() > 50);

    // parse and prefix: the derived and class inputs of every grid CID, and its own bytes for the random ones
    // the quick profile derives inputs from every fourth CID of the grid
    for c in grid.iter().step_by(trace_cases(4, 1)) {
        for input in derived_inputs(c.as_bytes()).iter().chain(&class_inputs(c.as_bytes())) {
            parse_and_prefix(&mut out, input);
        }
    }
    for c in &random_ok {
        parse_and_prefix(&mut out, c.as_bytes());
    }
    let strings = strings_over(&[0, 1, 2, 0x12, 0x1e, 0x20, 0x80, 0xff], trace_cases(3, 4));
    for s in strings.iter().cloned().chain((0..=255u8).map(|b| vec![b])) {
        parse_and_prefix(&mut out, &s);
    }
    for _ in 0..trace_cases(200, 1000) {
        parse_and_prefix(&mut out, &random_string(&mut rng));
    }

    // etext: the text of every accepted CID under four buffer sizes
    for c in grid.iter().chain(&random_ok) {
        let b = c.as_bytes();
        let n = 1 + (8 * b.len()).div_ceil(5);
        assert_eq!(c.to_string(), base32(b));
        for cap in [MAX_TEXT_LEN, n, n - 1, 0] {
            etext_ev(&mut out, b, cap);
        }
    }

    // ptext: texts of the accepted CIDs, their mutations, short texts over the class alphabet, random texts
    for c in grid.iter().chain(&random_ok) {
        let t = base32(c.as_bytes());
        ptext_ev(&mut out, &t);
        assert_eq!(Cid::parse_text(&t).unwrap(), *c);
    }
    for c in &grid {
        let t = base32(c.as_bytes());
        for m in text_mutations(&t) {
            ptext_ev(&mut out, &m);
        }
        ptext_ev(&mut out, &t[1..]);
        let mut upper = t.clone().into_bytes();
        upper[1] = upper[1].wrapping_sub(32);
        ptext_ev(&mut out, &String::from_utf8(upper).unwrap());
        if c.as_bytes().len() == 84 {
            ptext_ev(&mut out, &format!("{t}aa"));
        }
    }
    for s in strings_over(b"az27A1", 3) {
        ptext_ev(&mut out, &format!("b{}", String::from_utf8(s).unwrap()));
    }
    ptext_ev(&mut out, "");
    ptext_ev(&mut out, "B");
    for s in strings.iter().cloned().chain((0..=255u8).map(|b| vec![b])) {
        ptext_ev(&mut out, &base32(&s));
    }
    for _ in 0..trace_cases(100, 500) {
        let n = below(&mut rng, 140) as usize;
        let t: String = std::iter::once('b')
            .chain((0..n).map(|_| DIGITS[below(&mut rng, 32) as usize] as char))
            .collect();
        ptext_ev(&mut out, &t);
    }

    // cmp: the 25 pairs of five CIDs and 300 random pairs
    let blake = Cid::new(0x71, 0x1e, &ramp(32)).unwrap();
    let pool: [&[u8]; 5] = [
        &[1, 0x71, 0, 1, 25],
        &[1, 0x71, 0, 1, 26],
        &[1, 0x55, 0, 0],
        &[1, 0x71, 0, 2, 25, 0],
        blake.as_bytes(),
    ];
    for a in pool {
        for b in pool {
            cmp_ev(&mut out, a, b);
        }
    }
    let accepted: Vec<&Cid> = grid.iter().chain(&random_ok).collect();
    for _ in 0..trace_cases(60, 300) {
        let a = accepted[below(&mut rng, accepted.len() as u64) as usize];
        let b = accepted[below(&mut rng, accepted.len() as u64) as usize];
        cmp_ev(&mut out, a.as_bytes(), b.as_bytes());
    }

    // forblock and verify
    let blocks: [Vec<u8>; 4] = [
        Vec::new(),
        vec![1, 2, 3],
        random_bytes(&mut rng, 64),
        random_bytes(&mut rng, 1000),
    ];
    let mut built: Vec<(Cid, &Vec<u8>)> = Vec::new();
    for codec in [0x55, 0x71] {
        for hash in [0x12, 0x1e, 0, 0x13] {
            for blk in &blocks {
                if let Some(c) = forblock_ev(&mut out, codec, hash, blk) {
                    built.push((c, blk));
                }
            }
        }
    }
    assert_eq!(built.len(), 16);
    for (c, own) in &built {
        for blk in &blocks {
            let r = verify_ev(&mut out, c.as_bytes(), blk);
            if blk == *own {
                assert_eq!(r, Ok(()), "a block does not verify against its own CID");
            } else {
                assert_eq!(r, Err(CidError::DigestMismatch), "another block verified");
            }
        }
    }
    let unknown = Cid::new(0x71, 0, &ramp(32)).unwrap();
    for blk in &blocks[..2] {
        assert_eq!(
            verify_ev(&mut out, unknown.as_bytes(), blk),
            Err(CidError::UnsupportedHash(0))
        );
    }

    assert!(out.lines().count() > 10_000);
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir).join("tla");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("dag_cid.ndjson"), out).unwrap();
}
