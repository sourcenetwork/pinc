//! The helpers of the `trace_wire_cbor` test: its records, runs and checks.

use pinc_tests::SplitMix64;
use pinc_wire::WireError;
use pinc_wire::cbor::{Decoder, Encoder, Item, MAX_DEPTH, MapKeys, MapReader};
use std::collections::BTreeSet;
use std::fmt::Write as _;

/// A value below `n` (`n > 0`).
pub fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

/// A `u64` as the four 16-bit limbs `U64.tla` reads.
pub fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

/// A byte list as a JSON array.
pub fn arr(b: &[u8]) -> String {
    let body: Vec<String> = b.iter().map(u8::to_string).collect();
    format!("[{}]", body.join(","))
}

/// `next_u64() >> below(64)`: a value of every width.
pub fn shifted(rng: &mut SplitMix64) -> u64 {
    let v = rng.next_u64();
    v >> below(rng, 64)
}

/// `n` random bytes.
pub fn random_bytes(rng: &mut SplitMix64, n: u64) -> Vec<u8> {
    let mut b = vec![0u8; n as usize];
    rng.fill(&mut b);
    b
}

/// Up to 19 lowercase letters.
pub fn letters(rng: &mut SplitMix64) -> String {
    let n = below(rng, 20);
    (0..n).map(|_| char::from(b'a' + below(rng, 26) as u8)).collect()
}

/// What the runs reached: the decoder's results and the encoder's, by reason.
#[derive(Default)]
pub struct Seen {
    pub dec: BTreeSet<&'static str>,
    pub enc: BTreeSet<&'static str>,
}

/// The reason of a refusal as a JSON string body (written verbatim).
pub fn verbatim(why: &str) -> &str {
    assert!(
        !why.contains('"') && !why.contains('\\'),
        "a reason holds a quote or a backslash"
    );
    why
}

// ---------------------------------------------------------------- decoder

/// An item as the `I` of a record.
pub fn item_json(item: &Item<'_>) -> String {
    match item {
        Item::Unsigned(n) => format!(r#"{{"k":"uns","a":{}}}"#, limbs(*n)),
        Item::Negative(n) => format!(r#"{{"k":"neg","a":{}}}"#, limbs(*n)),
        Item::Bytes(b) => format!(r#"{{"k":"bytes","b":{}}}"#, arr(b)),
        Item::Text(s) => format!(r#"{{"k":"text","b":{}}}"#, arr(s.as_bytes())),
        Item::Array(n) => format!(r#"{{"k":"array","a":{}}}"#, limbs(*n)),
        Item::Map(n) => format!(r#"{{"k":"map","a":{}}}"#, limbs(*n)),
        Item::Tag(n) => format!(r#"{{"k":"tag","a":{}}}"#, limbs(*n)),
        Item::Bool(v) => format!(r#"{{"k":"bool","v":{v}}}"#),
        Item::Null => r#"{"k":"null"}"#.to_owned(),
        Item::Float(f) => format!(r#"{{"k":"float","a":{}}}"#, limbs(f.to_bits())),
    }
}

/// A decoder refusal as the `R` of a record.
pub fn derr(e: &WireError, seen: &mut Seen) -> String {
    match *e {
        WireError::Truncated { needed } => {
            seen.dec.insert("truncated");
            format!(r#"{{"ok":false,"err":"truncated","needed":{}}}"#, limbs(needed as u64))
        }
        WireError::NonCanonical(why) => {
            seen.dec.insert(why);
            format!(r#"{{"ok":false,"err":"noncanon","why":"{}"}}"#, verbatim(why))
        }
        WireError::Unexpected(why) => {
            seen.dec.insert(why);
            format!(r#"{{"ok":false,"err":"unexpected","why":"{}"}}"#, verbatim(why))
        }
        WireError::DepthExceeded => {
            seen.dec.insert("depth");
            r#"{"ok":false,"err":"depth"}"#.to_owned()
        }
        other => panic!("the decoder returned {other:?}, which it cannot"),
    }
}

/// An item written with the matching `Encoder` method into a buffer of exactly the bytes consumed gives those bytes.
pub fn reencode(item: &Item<'_>, consumed: &[u8]) {
    if let Item::Tag(n) = item {
        assert_eq!(
            (*n, consumed),
            (42, &[0xD8u8, 0x2A][..]),
            "a tag did not consume exactly tag 42"
        );
        return;
    }
    let mut buf = vec![0u8; consumed.len()];
    let mut e = Encoder::new(&mut buf);
    let res = match item {
        Item::Unsigned(n) => e.unsigned(*n),
        Item::Negative(n) => e.negative(*n),
        Item::Bytes(b) => e.bytes(b),
        Item::Text(s) => e.text(s),
        Item::Array(n) => e.array(*n),
        Item::Map(n) => e.map(*n),
        Item::Bool(v) => e.bool(*v),
        Item::Null => e.null(),
        Item::Float(f) => e.float(*f),
        Item::Tag(_) => Ok(()),
    };
    res.unwrap();
    assert_eq!(
        e.written(),
        consumed,
        "an accepted item does not re-encode to the bytes it was read from"
    );
}

/// One decoder run: the calls made on one decoder, recorded.
pub struct DRun<'a> {
    pub input: &'a [u8],
    pub dec: Decoder<'a>,
    pub map: Option<MapReader<'a>>,
    pub calls: Vec<String>,
}

impl<'a> DRun<'a> {
    pub fn new(input: &'a [u8]) -> Self {
        Self {
            input,
            dec: Decoder::new(input),
            map: None,
            calls: Vec::new(),
        }
    }

    pub fn record(&mut self, op: &str, r: &str) {
        assert_eq!(self.dec.position() + self.dec.remaining(), self.input.len());
        self.calls
            .push(format!(r#"{{"op":"{op}","r":{r},"pos":{}}}"#, self.dec.position()));
    }

    pub fn next(&mut self, seen: &mut Seen) -> Result<Item<'a>, WireError> {
        let before = self.dec.position();
        let res = self.dec.next_item();
        let r = match &res {
            Ok(item) => {
                reencode(item, &self.input[before..self.dec.position()]);
                format!(r#"{{"ok":true,"item":{}}}"#, item_json(item))
            }
            Err(e) => derr(e, seen),
        };
        self.record("next", &r);
        res
    }

    pub fn skip(&mut self, seen: &mut Seen) -> Result<(), WireError> {
        let res = self.dec.skip_value();
        let r = res
            .as_ref()
            .map_or_else(|e| derr(e, seen), |_| r#"{"ok":true}"#.to_owned());
        self.record("skip", &r);
        res
    }

    pub fn mnew(&mut self, seen: &mut Seen) -> Result<(), WireError> {
        let res = MapReader::new(&mut self.dec);
        let r = res
            .as_ref()
            .map_or_else(|e| derr(e, seen), |_| r#"{"ok":true}"#.to_owned());
        self.record("mnew", &r);
        res.map(|m| self.map = Some(m))
    }

    pub fn mkey(&mut self, seen: &mut Seen) -> Result<Option<&'a str>, WireError> {
        let res = self.map.as_mut().unwrap().next_key(&mut self.dec);
        let r = match &res {
            Ok(Some(k)) => format!(r#"{{"ok":true,"key":{}}}"#, arr(k.as_bytes())),
            Ok(None) => r#"{"ok":true,"none":true}"#.to_owned(),
            Err(e) => derr(e, seen),
        };
        self.record("mkey", &r);
        res
    }

    pub fn finish(self, out: &mut String) {
        let _ = writeln!(
            out,
            r#"{{"t":"drun","in":{},"calls":[{}]}}"#,
            arr(self.input),
            self.calls.join(",")
        );
    }
}

/// A run of `next_item` until an error, the end of the input, or `max` calls. Returns whether every call succeeded,
/// whether the input is consumed, and the calls made.
pub fn next_run(input: &[u8], max: usize, out: &mut String, seen: &mut Seen) -> (bool, bool, usize) {
    let mut run = DRun::new(input);
    let (mut ok, mut n) = (true, 0);
    loop {
        n += 1;
        if run.next(seen).is_err() {
            ok = false;
            break;
        }
        if run.dec.is_empty() || n == max {
            break;
        }
    }
    let empty = run.dec.is_empty();
    run.finish(out);
    (ok, empty, n)
}

/// A run of one `skip_value`. Returns its result and the position after it.
pub fn skip_run(input: &[u8], out: &mut String, seen: &mut Seen) -> (Result<(), WireError>, usize) {
    let mut run = DRun::new(input);
    let res = run.skip(seen);
    let pos = run.dec.position();
    run.finish(out);
    (res, pos)
}

/// A run of a `MapReader` over `input`: its header, then each key and the skip of its value.
pub fn map_run(input: &[u8], out: &mut String, seen: &mut Seen) {
    let mut run = DRun::new(input);
    if run.mnew(seen).is_ok() {
        let mut prev: Option<&str> = None;
        while let Ok(Some(k)) = run.mkey(seen) {
            if let Some(p) = prev {
                assert!(
                    (p.len(), p.as_bytes()) < (k.len(), k.as_bytes()),
                    "map keys came back out of order"
                );
            }
            prev = Some(k);
            if run.skip(seen).is_err() {
                break;
            }
        }
    }
    run.finish(out);
}

/// The skip run of `input`, and its map run when it starts with a map.
pub fn skip_family(input: &[u8], out: &mut String, seen: &mut Seen) {
    let _ = skip_run(input, out, seen);
    if input.first().is_some_and(|b| b >> 5 == 5) {
        map_run(input, out, seen);
    }
}

pub fn decoder_boundary(out: &mut String, seen: &mut Seen) -> usize {
    let tails: Vec<Vec<u8>> = vec![
        vec![],
        vec![23],
        vec![24],
        vec![42],
        vec![43],
        vec![255],
        vec![0, 42],
        vec![0, 255],
        vec![1, 0],
        vec![0, 0, 255, 255],
        vec![0, 1, 0, 0],
        vec![0, 0, 0, 0, 255, 255, 255, 255],
        vec![0, 0, 0, 1, 0, 0, 0, 0],
        vec![255; 8],
        vec![127, 240, 0, 0, 0, 0, 0, 0],
        vec![63, 240, 0, 0, 0, 0, 0, 0],
        vec![128, 0, 0, 0, 0, 0, 0, 0],
        vec![127, 239, 255, 255, 255, 255, 255, 255],
        vec![97; 23],
        [vec![24], vec![97; 24]].concat(),
        [vec![24], vec![97; 23]].concat(),
        vec![42, 65, 0],
        vec![42, 64],
        vec![42, 65, 1],
        vec![42, 1],
        vec![42, 216, 42],
        vec![42, 65],
        vec![195, 169],
        vec![192, 128],
        vec![237, 160, 128],
        vec![240, 159, 152, 128],
        vec![244, 144, 128, 128],
        vec![224, 128, 128],
        vec![128],
        vec![195],
        vec![97, 0],
        vec![0, 97],
    ];
    assert_eq!(tails.len(), 37);
    let mut runs = 0;
    for b in 0..=255u8 {
        for tail in &tails {
            let input = [&[b][..], tail.as_slice()].concat();
            next_run(&input, 4, out, seen);
            runs += 1;
        }
    }
    runs
}

/// One token of the skip family: its bytes, the items it opens, and whether it is a map or a tag.
pub struct Tok {
    pub bytes: &'static [u8],
    pub children: u64,
    pub map: bool,
    pub tag: bool,
}

pub const fn tok(bytes: &'static [u8], children: u64, map: bool, tag: bool) -> Tok {
    Tok {
        bytes,
        children,
        map,
        tag,
    }
}

pub const VALUES: [Tok; 8] = [
    tok(&[0x01], 0, false, false),
    tok(&[0x80], 0, false, false),
    tok(&[0x61, 0x61], 0, false, false),
    tok(&[0x81], 1, false, false),
    tok(&[0x82], 2, false, false),
    tok(&[0xA1], 2, true, false),
    tok(&[0xA2], 4, true, false),
    tok(&[0xD8, 0x2A], 1, false, true),
];
pub const KEYS: [Tok; 4] = [
    tok(&[0x61, 0x61], 0, false, false),
    tok(&[0x61, 0x62], 0, false, false),
    tok(&[0x62, 0x61, 0x61], 0, false, false),
    tok(&[0x01], 0, false, false),
];
pub const TAG_CONTENTS: [Tok; 3] = [
    tok(&[0x41, 0x00], 0, false, false),
    tok(&[0x40], 0, false, false),
    tok(&[0x41, 0x01], 0, false, false),
];

/// An open container of the generator.
#[derive(Clone, Copy)]
pub struct Frame {
    pub left: u64,
    pub map: bool,
    pub tag: bool,
}

/// The tokens offered after a prefix whose open containers are `stack`.
pub fn offered(stack: &[Frame]) -> &'static [Tok] {
    match stack.last() {
        Some(f) if f.tag => &TAG_CONTENTS,
        Some(f) if f.map && f.left % 2 == 0 => &KEYS,
        _ => &VALUES,
    }
}

/// Visit `seq`, then extend it by every offered token while it is short, open and `skip_value` still wants bytes.
pub fn visit(seq: &mut Vec<u8>, stack: &[Frame], tokens: u32, out: &mut String, seen: &mut Seen) -> usize {
    skip_family(seq, out, seen);
    let mut visited = 1;
    let wants_more = matches!(Decoder::new(seq).skip_value(), Err(WireError::Truncated { .. }));
    if tokens < 5 && (tokens == 0 || !stack.is_empty()) && wants_more {
        for t in offered(stack) {
            let mut next = stack.to_vec();
            if let Some(top) = next.last_mut() {
                top.left = top.left.saturating_sub(1);
            }
            if t.children > 0 {
                next.push(Frame {
                    left: t.children,
                    map: t.map,
                    tag: t.tag,
                });
            }
            while next.last().is_some_and(|f| f.left == 0) {
                next.pop();
            }
            let len = seq.len();
            seq.extend_from_slice(t.bytes);
            visited += visit(seq, &next, tokens + 1, out, seen);
            seq.truncate(len);
        }
    }
    visited
}

pub fn decoder_depth(out: &mut String, seen: &mut Seen) {
    assert_eq!(MAX_DEPTH, 64);
    for k in 62..=66usize {
        skip_family(&[vec![0x81; k], vec![0x01]].concat(), out, seen);
        skip_family(&[[0xA1, 0x61, 0x61].repeat(k), vec![0x01]].concat(), out, seen);
    }
    for k in 62..=65usize {
        let _ = skip_run(&[vec![0x81; k], vec![0xD8, 0x2A, 0x41, 0x00]].concat(), out, seen);
    }
}

pub fn decoder_non_maps(out: &mut String, seen: &mut Seen) {
    let inputs: [&[u8]; 8] = [
        &[0x00],
        &[0x80],
        &[0x60],
        &[0xF6],
        &[0xD8, 0x2A, 0x41, 0x00],
        &[],
        &[0x1C],
        &[0xA0],
    ];
    for input in inputs {
        let mut run = DRun::new(input);
        if run.mnew(seen).is_ok() {
            let _ = run.mkey(seen);
        }
        run.finish(out);
    }
}

// ---------------------------------------------------------------- random trees

/// A random value tree, built to be encoded.
pub enum Node {
    Uns(u64),
    Neg(u64),
    Bytes(Vec<u8>),
    Text(String),
    Bool(bool),
    Null,
    Float(f64),
    Cid(Vec<u8>),
    Array(Vec<Node>),
    Map(Vec<(&'static str, Node)>),
}

pub const TREE_KEYS: [&str; 7] = ["a", "b", "c", "aa", "ab", "ba", "abc"];

pub fn make_node(rng: &mut SplitMix64, depth: u32) -> Node {
    match below(rng, if depth < 6 { 11 } else { 8 }) {
        0 => Node::Uns(shifted(rng)),
        1 => Node::Neg(shifted(rng)),
        2 => {
            let n = below(rng, 40);
            Node::Bytes(random_bytes(rng, n))
        }
        3 => {
            let n = below(rng, 20);
            let mut s = String::new();
            for _ in 0..n {
                if below(rng, 8) == 0 {
                    s.push_str(if below(rng, 2) == 0 { "\u{e9}" } else { "\u{1F600}" });
                } else {
                    s.push(char::from(b'a' + below(rng, 26) as u8));
                }
            }
            Node::Text(s)
        }
        4 => Node::Bool(below(rng, 2) == 1),
        5 => Node::Null,
        6 => {
            let list = [0.0, -0.0, 1.5, f64::MAX, f64::MIN_POSITIVE, 5e-324];
            let i = below(rng, 7) as usize;
            Node::Float(list.get(i).copied().unwrap_or_else(|| rng.next_u64() as f64 / 3.0))
        }
        7 => {
            let n = below(rng, 40);
            Node::Cid(random_bytes(rng, n))
        }
        8 => {
            let n = below(rng, 4);
            Node::Array((0..n).map(|_| make_node(rng, depth + 1)).collect())
        }
        9 => {
            let n = below(rng, 4) as usize;
            let mut keys: Vec<&'static str> = Vec::new();
            while keys.len() < n {
                let k = TREE_KEYS[below(rng, 7) as usize];
                if !keys.contains(&k) {
                    keys.push(k);
                }
            }
            keys.sort_by(|a, b| (a.len(), a.as_bytes()).cmp(&(b.len(), b.as_bytes())));
            Node::Map(keys.into_iter().map(|k| (k, make_node(rng, depth + 1))).collect())
        }
        _ => Node::Array(Vec::new()),
    }
}

pub fn encode_node(e: &mut Encoder<'_>, n: &Node) -> Result<(), WireError> {
    match n {
        Node::Uns(v) => e.unsigned(*v),
        Node::Neg(v) => e.negative(*v),
        Node::Bytes(b) => e.bytes(b),
        Node::Text(s) => e.text(s),
        Node::Bool(v) => e.bool(*v),
        Node::Null => e.null(),
        Node::Float(f) => e.float(*f),
        Node::Cid(b) => e.tag_cid(b),
        Node::Array(items) => {
            e.array(items.len() as u64)?;
            items.iter().try_for_each(|c| encode_node(e, c))
        }
        Node::Map(entries) => {
            let mut keys = e.ordered_map(entries.len() as u64)?;
            for (k, v) in entries {
                keys.key(e, k)?;
                encode_node(e, v)?;
            }
            Ok(())
        }
    }
}

pub fn decoder_trees(out: &mut String, seen: &mut Seen) -> usize {
    let mut rng = SplitMix64::traced(0x4342_4F52);
    let mut runs = 0;
    for _ in 0..400 {
        let enc = loop {
            let tree = make_node(&mut rng, 0);
            let mut buf = vec![0u8; 4096];
            let mut e = Encoder::new(&mut buf);
            match encode_node(&mut e, &tree) {
                Ok(()) => {
                    let n = e.written().len();
                    buf.truncate(n);
                    break buf;
                }
                Err(WireError::BufferTooSmall { .. }) => {}
                Err(other) => panic!("a tree did not encode: {other:?}"),
            }
        };
        let len = enc.len() as u64;
        let mut flipped = enc.clone();
        let at = below(&mut rng, len) as usize;
        flipped[at] ^= 1 << below(&mut rng, 8);
        let cut = enc[..below(&mut rng, len) as usize].to_vec();
        let mut appended = enc.clone();
        appended.push(rng.next_u64() as u8);
        for (i, input) in [enc, flipped, cut, appended].iter().enumerate() {
            let (res, pos) = skip_run(input, out, seen);
            let (all_ok, empty, calls) = next_run(input, 64, out, seen);
            if i == 0 {
                assert!(
                    res.is_ok() && pos == input.len(),
                    "skip_value did not take a whole encoding"
                );
                // a tree of more than 64 items is cut by the call limit, not by the input
                assert!(
                    all_ok && (empty || calls == 64),
                    "next_item did not read a whole encoding"
                );
            }
            runs += 2;
        }
    }
    runs
}

// ---------------------------------------------------------------- encoder

/// One encoder call.
pub enum ECall {
    Uns(u64),
    Neg(u64),
    Array(u64),
    Map(u64),
    OMap(u64),
    Float(u64),
    Bytes(Vec<u8>),
    Cid(Vec<u8>),
    Text(String),
    Key(&'static str),
    Bool(bool),
    Null,
}

impl ECall {
    pub fn op(&self) -> &'static str {
        match self {
            Self::Uns(_) => "uns",
            Self::Neg(_) => "neg",
            Self::Array(_) => "array",
            Self::Map(_) => "map",
            Self::OMap(_) => "omap",
            Self::Float(_) => "float",
            Self::Bytes(_) => "bytes",
            Self::Cid(_) => "cid",
            Self::Text(_) => "text",
            Self::Key(_) => "key",
            Self::Bool(_) => "bool",
            Self::Null => "null",
        }
    }

    /// The `ARG` of the record, with its leading comma (empty for `null`).
    pub fn arg(&self) -> String {
        match self {
            Self::Uns(a) | Self::Neg(a) | Self::Array(a) | Self::Map(a) | Self::OMap(a) | Self::Float(a) => {
                format!(r#","a":{}"#, limbs(*a))
            }
            Self::Bytes(b) | Self::Cid(b) => format!(r#","b":{}"#, arr(b)),
            Self::Text(s) => format!(r#","b":{}"#, arr(s.as_bytes())),
            Self::Key(s) => format!(r#","b":{}"#, arr(s.as_bytes())),
            Self::Bool(v) => format!(r#","v":{v}"#),
            Self::Null => String::new(),
        }
    }
}

/// The call on a bare encoder (the header of an ordered map, the text of a key).
pub fn apply(e: &mut Encoder<'_>, c: &ECall) -> Result<(), WireError> {
    match c {
        ECall::Uns(a) => e.unsigned(*a),
        ECall::Neg(a) => e.negative(*a),
        ECall::Array(a) => e.array(*a),
        ECall::Map(a) | ECall::OMap(a) => e.map(*a),
        ECall::Float(bits) => e.float(f64::from_bits(*bits)),
        ECall::Bytes(b) => e.bytes(b),
        ECall::Cid(b) => e.tag_cid(b),
        ECall::Text(s) => e.text(s),
        ECall::Key(s) => e.text(s),
        ECall::Bool(v) => e.bool(*v),
        ECall::Null => e.null(),
    }
}

/// The bytes the call writes into a 300-byte encoder; `None` when it is refused (a non-finite float).
pub fn reference(c: &ECall) -> Option<Vec<u8>> {
    let mut buf = [0u8; 300];
    let mut e = Encoder::new(&mut buf);
    apply(&mut e, c).ok()?;
    Some(e.written().to_vec())
}

/// What an encoder run did: each call, whether it succeeded and (for a key) whether the map is complete, and the
/// bytes written.
pub struct Done {
    pub calls: Vec<(ECall, bool, Option<bool>)>,
    pub written: Vec<u8>,
}

/// One encoder run over `cap` fill bytes. `drive` gives the next call, told whether a `MapKeys` is held and whether
/// the last call succeeded, or `None` to stop.
pub fn erun(cap: usize, mut drive: impl FnMut(bool, bool) -> Option<ECall>, out: &mut String, seen: &mut Seen) -> Done {
    let mut buf = vec![0xAAu8; cap];
    let (recorded, calls, written) = {
        let mut enc = Encoder::new(&mut buf);
        let mut keys: Option<MapKeys<'static>> = None;
        let mut ok = true;
        let (mut recorded, mut calls) = (Vec::new(), Vec::new());
        while let Some(c) = drive(keys.is_some(), ok) {
            let w0 = enc.written().to_vec();
            let room = cap - w0.len();
            let res = match &c {
                ECall::OMap(a) => enc.ordered_map(*a).map(|k| keys = Some(k)),
                ECall::Key(s) => keys.as_mut().unwrap().key(&mut enc, *s),
                other => apply(&mut enc, other),
            };
            let complete = matches!(c, ECall::Key(_)).then(|| keys.is_some_and(|k| k.is_complete()));
            let want = reference(&c);
            let r = match &res {
                Ok(()) => {
                    let mut expect = w0.clone();
                    expect.extend(want.as_ref().unwrap());
                    assert_eq!(
                        enc.written(),
                        expect.as_slice(),
                        "a call did not write exactly its encoding"
                    );
                    r#"{"ok":true}"#.to_owned()
                }
                Err(e) => {
                    assert_eq!(enc.written(), w0.as_slice(), "a refused call wrote");
                    match *e {
                        WireError::BufferTooSmall { needed } => {
                            seen.enc.insert("small");
                            assert_eq!(
                                needed,
                                want.as_ref().unwrap().len() - room,
                                "the shortfall is not exact"
                            );
                            format!(r#"{{"ok":false,"err":"small","needed":{}}}"#, limbs(needed as u64))
                        }
                        WireError::NonCanonical(why) => {
                            seen.enc.insert(why);
                            format!(r#"{{"ok":false,"err":"noncanon","why":"{}"}}"#, verbatim(why))
                        }
                        other => panic!("the encoder returned {other:?}, which it cannot"),
                    }
                }
            };
            if !matches!(c, ECall::Key(_)) {
                assert_eq!(
                    res.is_ok(),
                    want.as_ref().is_some_and(|b| b.len() <= room),
                    "a call did not succeed exactly when its encoding fits"
                );
            }
            if let ECall::Float(bits) = c
                && !f64::from_bits(bits).is_finite()
            {
                assert_eq!(res, Err(WireError::NonCanonical("NaN and infinity are not allowed")));
            }
            let done = complete.map_or_else(String::new, |b| format!(r#","complete":{b}"#));
            recorded.push(format!(
                r#"{{"op":"{}"{},"r":{r},"written":{}{done}}}"#,
                c.op(),
                c.arg(),
                arr(enc.written())
            ));
            ok = res.is_ok();
            calls.push((c, ok, complete));
        }
        (recorded, calls, enc.written().to_vec())
    };
    assert!(
        buf[written.len()..].iter().all(|&b| b == 0xAA),
        "a call wrote past the written length"
    );
    let _ = writeln!(
        out,
        r#"{{"t":"erun","cap":{cap},"calls":[{}],"buf":{}}}"#,
        recorded.join(","),
        arr(&buf)
    );
    Done { calls, written }
}

/// A driver that makes one call and stops.
pub fn single(c: ECall) -> impl FnMut(bool, bool) -> Option<ECall> {
    let mut once = Some(c);
    move |_, _| once.take()
}

/// The decode of a call written whole into exactly its encoding returns the same item, and ends there.
pub fn roundtrip(c: &ECall, written: &[u8]) {
    let mut d = Decoder::new(written);
    let item = d.next_item().unwrap();
    match (c, item) {
        (ECall::Uns(a), Item::Unsigned(b))
        | (ECall::Neg(a), Item::Negative(b))
        | (ECall::Array(a), Item::Array(b))
        | (ECall::Map(a) | ECall::OMap(a), Item::Map(b)) => assert_eq!(*a, b),
        (ECall::Float(bits), Item::Float(f)) => assert_eq!(*bits, f.to_bits()),
        (ECall::Bytes(b), Item::Bytes(x)) => assert_eq!(b.as_slice(), x),
        (ECall::Text(s), Item::Text(t)) => assert_eq!(s, t),
        (ECall::Bool(v), Item::Bool(x)) => assert_eq!(*v, x),
        (ECall::Null, Item::Null) => {}
        (ECall::Cid(b), Item::Tag(42)) => match d.next_item().unwrap() {
            Item::Bytes(x) => assert_eq!((x[0], &x[1..]), (0, b.as_slice())),
            other => panic!("a cid did not decode to a byte string: {other:?}"),
        },
        (_, other) => panic!("a call decoded to another item: {other:?}"),
    }
    assert_eq!(
        d.position(),
        written.len(),
        "a call did not decode to exactly the bytes it wrote"
    );
}

pub fn boundary_calls() -> Vec<ECall> {
    let args = [
        0u64,
        1,
        23,
        24,
        42,
        255,
        256,
        65535,
        65536,
        u64::from(u32::MAX),
        1 << 32,
        u64::MAX,
    ];
    let mut calls: Vec<ECall> = Vec::new();
    for make in [ECall::Uns, ECall::Neg, ECall::Array, ECall::Map] {
        calls.extend(args.map(make));
    }
    for n in [0usize, 1, 23, 24, 255, 256] {
        calls.push(ECall::Bytes((1..=n).map(|i| ((i * 7) % 256) as u8).collect()));
    }
    for s in ["", "a", "\u{e9}", "\u{1F600}"] {
        calls.push(ECall::Text(s.to_owned()));
    }
    for n in [23usize, 24, 255, 256] {
        calls.push(ECall::Text("a".repeat(n)));
    }
    for n in [0usize, 1, 22, 23, 254, 255] {
        calls.push(ECall::Cid((1..=n).map(|i| (i % 256) as u8).collect()));
    }
    calls.extend([ECall::Bool(false), ECall::Bool(true), ECall::Null]);
    calls.extend(
        [
            0u64,
            1,
            0x8000_0000_0000_0000,
            0x3FF0_0000_0000_0000,
            0x7FEF_FFFF_FFFF_FFFF,
            0x7FF0_0000_0000_0000,
            0xFFF0_0000_0000_0000,
            0x7FF8_0000_0000_0000,
            0x7FF0_0000_0000_0001,
        ]
        .map(ECall::Float),
    );
    assert_eq!(calls.len(), 80);
    calls
}

/// Each boundary call at the five buffer sizes around its length.
pub fn encoder_boundary(out: &mut String, seen: &mut Seen) -> usize {
    let mut runs = 0;
    for idx in 0..boundary_calls().len() {
        let len = reference(&boundary_calls()[idx]).map_or(0, |b| b.len());
        let mut caps: Vec<usize> = [Some(0), Some(1), len.checked_sub(1), Some(len), Some(len + 1)]
            .into_iter()
            .flatten()
            .collect();
        caps.sort_unstable();
        caps.dedup();
        for cap in caps {
            // a fresh call each time, since a call owns its bytes
            let call = boundary_calls().swap_remove(idx);
            let done = erun(cap, single(call), out, seen);
            let (c, ok, _) = &done.calls[0];
            if *ok && cap == len {
                roundtrip(c, &done.written);
            }
            if let Some(w) = reference(c) {
                assert_eq!(*ok, w.len() <= cap);
            }
            runs += 1;
        }
    }
    runs
}

pub const MAP_KEYS: [&str; 4] = ["", "a", "b", "aa"];

pub fn omap_runs(out: &mut String, seen: &mut Seen) -> usize {
    let mut sequences: Vec<Vec<&'static str>> = vec![Vec::new()];
    let mut layer: Vec<Vec<&'static str>> = vec![Vec::new()];
    for _ in 0..4 {
        layer = layer
            .iter()
            .flat_map(|p| {
                MAP_KEYS.iter().map(move |&k| {
                    let mut v = p.clone();
                    v.push(k);
                    v
                })
            })
            .collect();
        sequences.extend(layer.iter().cloned());
    }
    assert_eq!(sequences.len(), 341);
    let mut runs = 0;
    for len in 0..=3u64 {
        for keys in &sequences {
            let (mut queue, mut first, mut after_key) = (keys.iter(), true, false);
            let done = erun(
                7,
                |held, last_ok| {
                    if std::mem::take(&mut first) {
                        return Some(ECall::OMap(len));
                    }
                    if !held {
                        return None;
                    }
                    if std::mem::take(&mut after_key) && last_ok {
                        return Some(ECall::Null);
                    }
                    let k = *queue.next()?;
                    after_key = true;
                    Some(ECall::Key(k))
                },
                out,
                seen,
            );
            runs += 1;
            let key_calls: Vec<&(ECall, bool, Option<bool>)> = done
                .calls
                .iter()
                .filter(|(c, _, _)| matches!(c, ECall::Key(_)))
                .collect();
            let nulls: Vec<&(ECall, bool, Option<bool>)> =
                done.calls.iter().filter(|(c, _, _)| matches!(c, ECall::Null)).collect();
            let complete = done.calls[0].1
                && key_calls.len() as u64 == len
                && key_calls.iter().all(|(_, ok, _)| *ok)
                && nulls.len() == key_calls.len()
                && nulls.iter().all(|(_, ok, _)| *ok)
                && key_calls.last().is_none_or(|(_, _, complete)| *complete == Some(true));
            if complete {
                let mut d = Decoder::new(&done.written);
                d.skip_value().unwrap();
                assert_eq!(
                    d.position(),
                    done.written.len(),
                    "skip_value did not take a complete map whole"
                );
                let mut d = Decoder::new(&done.written);
                let mut m = MapReader::new(&mut d).unwrap();
                for k in keys {
                    assert_eq!(m.next_key(&mut d).unwrap(), Some(*k));
                    d.skip_value().unwrap();
                }
                assert_eq!(m.next_key(&mut d).unwrap(), None);
                assert!(d.is_empty());
            }
        }
    }
    runs
}

pub fn encoder_random(out: &mut String, seen: &mut Seen) {
    const NON_FINITE: [u64; 4] = [
        0x7FF0_0000_0000_0000,
        0xFFF0_0000_0000_0000,
        0x7FF8_0000_0000_0000,
        0x7FF0_0000_0000_0001,
    ];
    const KEYS6: [&str; 6] = ["", "a", "b", "aa", "ab", "ba"];
    let mut rng = SplitMix64::traced(0x4342_4F53);
    for _ in 0..300 {
        let cap = below(&mut rng, 65) as usize;
        let mut left = 1 + below(&mut rng, 10);
        erun(
            cap,
            |held, _| {
                if left == 0 {
                    return None;
                }
                left -= 1;
                Some(match below(&mut rng, 12) {
                    0 => ECall::Uns(shifted(&mut rng)),
                    1 => ECall::Neg(shifted(&mut rng)),
                    2 => {
                        let n = below(&mut rng, 20);
                        ECall::Bytes(random_bytes(&mut rng, n))
                    }
                    3 => ECall::Text(letters(&mut rng)),
                    4 => ECall::Array(shifted(&mut rng)),
                    5 => ECall::Map(shifted(&mut rng)),
                    6 => {
                        let n = below(&mut rng, 40);
                        ECall::Cid(random_bytes(&mut rng, n))
                    }
                    7 => ECall::Bool(below(&mut rng, 2) == 1),
                    8 => ECall::Null,
                    9 => ECall::Float(if below(&mut rng, 8) == 0 {
                        NON_FINITE[below(&mut rng, 4) as usize]
                    } else {
                        rng.next_u64()
                    }),
                    10 => ECall::OMap(below(&mut rng, 4)),
                    _ if held => ECall::Key(KEYS6[below(&mut rng, 6) as usize]),
                    _ => ECall::Null,
                })
            },
            out,
            seen,
        );
    }
}
