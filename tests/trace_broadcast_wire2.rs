//! Trace generation for the version 2 message head of the topic broadcast: the real `Head2::{parse, parse_prefix,
//! write}` of `pinc-broadcast` called on heads of every identity algorithm at the edges of every field, on cut and
//! altered bytes, and on seeded random strings and heads. Every call is one line of `bcast/wire2.ndjson` for the TLA+
//! trace check (`TraceBroadcastWire2.tla`), which checks it against the model's `Parse`, `ParsePrefix` and `Write`.
//!
//! The test asserts the facts it relies on itself: a written head parses back to the same head, length and body
//! length, no proper prefix of a head parses, each refused head fails with the reason the inputs name, and every
//! reason the parser has occurred. The trace is written to the directory in `PINC_TRACE_DIR` when it is set;
//! otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    unreachable_pub,
    clippy::many_single_char_names
)]

use std::collections::{BTreeSet, HashSet};
use std::fmt::Write as _;

use pinc_broadcast::wire::Malformed;
use pinc_broadcast::wire2::{Head2, MAX_HEAD2, VERSION};
use pinc_crypto::IdentityAlg;
use pinc_tests::{SplitMix64, soaking};
use pinc_wire::hlc::Hlc;

const REASONS: [&str; 7] = [
    "message cut short",
    "version",
    "algorithm",
    "parents",
    "flags",
    "key or signature",
    "body length",
];

fn arr(b: &[u8]) -> String {
    let v: Vec<String> = b.iter().map(u8::to_string).collect();
    format!("[{}]", v.join(","))
}

/// The head as the model writes it.
fn head_json(h: &Head2<'_>) -> String {
    let parents: Vec<String> = h.parents.iter().map(|p| arr(p)).collect();
    format!(
        r#"{{"alg":{},"flags":{},"origin":{},"inc":{},"seq":{},"wall":{},"ctr":{},"parents":[{}],"pk":{},"sig":{}}}"#,
        h.alg.tag(),
        h.flags,
        arr(h.origin),
        arr(&h.incarnation.to_be_bytes()),
        arr(&h.seq.to_be_bytes()),
        arr(&h.ts.wall.to_be_bytes()),
        arr(&h.ts.counter.to_be_bytes()),
        parents.join(","),
        arr(h.pk),
        arr(h.sig),
    )
}

/// A head, owned.
#[derive(Clone)]
struct Owned {
    alg: IdentityAlg,
    flags: u8,
    origin: [u8; 32],
    inc: u64,
    seq: u64,
    wall: u64,
    ctr: u32,
    parents: Vec<[u8; 32]>,
    pk: Vec<u8>,
    sig: Vec<u8>,
}

impl Owned {
    /// The base head of `tag`, its key and signature filled from `rng`.
    fn base(tag: u8, rng: &mut SplitMix64) -> Self {
        let alg = IdentityAlg::from_tag(tag).unwrap();
        let mut pk = vec![0u8; if tag == 1 { 0 } else { alg.public_key_len() }];
        let mut sig = vec![0u8; alg.signature_len()];
        rng.fill(&mut pk);
        rng.fill(&mut sig);
        Self {
            alg,
            flags: 0,
            origin: [5; 32],
            inc: 1,
            seq: 2,
            wall: 3,
            ctr: 4,
            parents: Vec::new(),
            pk,
            sig,
        }
    }

    fn with(&self, f: impl FnOnce(&mut Self)) -> Self {
        let mut c = self.clone();
        f(&mut c);
        c
    }

    fn head(&self) -> Head2<'_> {
        Head2 {
            alg: self.alg,
            flags: self.flags,
            origin: &self.origin,
            incarnation: self.inc,
            seq: self.seq,
            ts: Hlc::new(self.wall, self.ctr),
            parents: &self.parents,
            pk: &self.pk,
            sig: &self.sig,
        }
    }
}

#[derive(Default)]
struct Run {
    out: String,
    reasons: HashSet<&'static str>,
}

impl Run {
    fn note(&mut self, e: Malformed) -> &'static str {
        self.reasons.insert(e.0);
        e.0
    }

    /// `Head2::parse(b)`, recorded; the head's JSON and length, or the reason.
    fn parse(&mut self, b: &[u8]) -> Result<usize, &'static str> {
        let mut line = format!(r#"{{"t":"w2","op":"parse","b":{}"#, arr(b));
        let r = match Head2::parse(b) {
            Ok((h, n)) => {
                let _ = write!(line, r#","h":{},"len":{n}"#, head_json(&h));
                Ok(n)
            }
            Err(e) => {
                let why = self.note(e);
                let _ = write!(line, r#","why":"{why}""#);
                Err(why)
            }
        };
        line.push_str("}\n");
        self.out.push_str(&line);
        r
    }

    /// `Head2::parse_prefix(b)`, recorded; the length and body length, or the reason.
    fn prefix(&mut self, b: &[u8]) -> Result<(usize, usize), &'static str> {
        let mut line = format!(r#"{{"t":"w2","op":"prefix","b":{}"#, arr(b));
        let r = match Head2::parse_prefix(b) {
            Ok((h, n, blen)) => {
                let _ = write!(
                    line,
                    r#","h":{},"len":{n},"blen":{}"#,
                    head_json(&h),
                    arr(&(blen as u32).to_be_bytes())
                );
                Ok((n, blen))
            }
            Err(e) => {
                let why = self.note(e);
                let _ = write!(line, r#","why":"{why}""#);
                Err(why)
            }
        };
        line.push_str("}\n");
        self.out.push_str(&line);
        r
    }

    /// `h.write(blen, ..)`, recorded; the bytes, or the reason.
    fn write(&mut self, o: &Owned, blen: u32) -> Result<Vec<u8>, &'static str> {
        let h = o.head();
        let mut v: Vec<u8> = Vec::new();
        let mut line = format!(
            r#"{{"t":"w2","op":"write","h":{},"blen":{}"#,
            head_json(&h),
            arr(&blen.to_be_bytes())
        );
        let r = match h.write(blen, &mut v) {
            Ok(()) => {
                let _ = write!(line, r#","b":{}"#, arr(&v));
                Ok(v)
            }
            Err(e) => {
                let why = self.note(e);
                let _ = write!(line, r#","why":"{why}""#);
                Err(why)
            }
        };
        line.push_str("}\n");
        self.out.push_str(&line);
        r
    }

    /// A head that must be written, checked to parse back whole.
    fn written(&mut self, o: &Owned, blen: u32) -> Vec<u8> {
        let v = self.write(o, blen).unwrap();
        let h = o.head();
        assert_eq!(v.len(), h.len());
        assert!(v.len() <= MAX_HEAD2);
        let (p, n, b) = Head2::parse_prefix(&v).unwrap();
        assert_eq!((p, n, b), (h, v.len(), blen as usize));
        v
    }

    /// A head that must be refused with `why`.
    fn refused(&mut self, o: &Owned, blen: u32, why: &str) {
        assert_eq!(self.write(o, blen), Err(why_static(why)), "the refusal of a head");
    }
}

fn why_static(why: &str) -> &'static str {
    REASONS.into_iter().find(|r| *r == why).unwrap()
}

fn asc(from: u8, n: usize) -> Vec<[u8; 32]> {
    (0..n).map(|i| [from + u8::try_from(i).unwrap(); 32]).collect()
}

/// The heads of input 1 that are written, with their body length and bytes.
fn writes(run: &mut Run, rng: &mut SplitMix64) -> Vec<(Owned, u32, Vec<u8>)> {
    let mut done = Vec::new();
    for tag in 1..=4u8 {
        let b = Owned::base(tag, rng);
        let mut ok: Vec<(Owned, u32)> = vec![(b.clone(), 0)];
        for n in [0usize, 1, 8] {
            ok.push((b.with(|c| c.parents = asc(1, n)), 0));
        }
        for f in [0u8, 1] {
            ok.push((b.with(|c| c.flags = f), 0));
        }
        for v in [0u64, 1 << 32, u64::MAX] {
            ok.push((b.with(|c| c.inc = v), 0));
            ok.push((b.with(|c| c.seq = v), 0));
            ok.push((b.with(|c| c.wall = v), 0));
        }
        for v in [0u32, u32::MAX] {
            ok.push((b.with(|c| c.ctr = v), 0));
        }
        for blen in [0u32, 1, 3, 65535, u32::MAX] {
            ok.push((b.clone(), blen));
        }
        for (o, blen) in ok {
            let v = run.written(&o, blen);
            done.push((o, blen, v));
        }
        for f in [2u8, 255] {
            run.refused(&b.with(|c| c.flags = f), 0, "flags");
        }
        run.refused(&b.with(|c| c.parents = asc(1, 9)), 0, "parents");
        run.refused(&b.with(|c| c.parents = vec![[2; 32], [1; 32]]), 0, "parents");
        run.refused(&b.with(|c| c.parents = vec![[1; 32], [1; 32]]), 0, "parents");
        if tag != 1 {
            run.refused(
                &b.with(|c| {
                    c.pk.pop();
                }),
                0,
                "key or signature",
            );
        }
        run.refused(&b.with(|c| c.pk.push(0)), 0, "key or signature");
        run.refused(
            &b.with(|c| {
                c.sig.pop();
            }),
            0,
            "key or signature",
        );
        run.refused(&b.with(|c| c.sig.push(0)), 0, "key or signature");
    }
    done
}

/// The cut lengths of a head of `len` bytes.
fn cuts(len: usize) -> BTreeSet<usize> {
    if len <= 200 {
        (0..len).collect()
    } else {
        (0..=72)
            .chain((0..len).filter(|c| c % 32 == 0))
            .chain(len - 8..len)
            .collect()
    }
}

fn mutations(run: &mut Run, o: &Owned, full: &[u8]) {
    let np = o.parents.len();
    let mut set = |pos: usize, v: u8| {
        let mut m = full.to_vec();
        m[pos] = v;
        run.parse(&m).ok();
        run.prefix(&m).ok();
    };
    for v in [1u8, 3] {
        set(0, v);
    }
    for v in [0u8, 5, 255] {
        set(1, v);
    }
    set(2, 2);
    set(3, 9);
    if np > 0 {
        set(3, u8::try_from(np + 1).unwrap());
        set(3, u8::try_from(np - 1).unwrap());
    }
}

fn damaged(run: &mut Run, done: &[(Owned, u32, Vec<u8>)]) {
    for (o, blen, v) in done.iter().filter(|(_, b, _)| [0, 1, 3].contains(b)) {
        let blen = *blen as usize;
        let mut full = v.clone();
        full.extend(std::iter::repeat_n(0xab, blen));
        let n = run.parse(&full).unwrap();
        assert_eq!(n, v.len());
        assert_eq!(run.prefix(&full), Ok((v.len(), blen)));
        for cut in cuts(v.len()) {
            assert_eq!(
                run.parse(&v[..cut]),
                Err("message cut short"),
                "a proper prefix of a head parsed"
            );
            assert_eq!(
                run.prefix(&v[..cut]),
                Err("message cut short"),
                "a proper prefix of a head parsed"
            );
        }
        let mut longer = full.clone();
        longer.push(0);
        assert_eq!(run.parse(&longer), Err("body length"));
        if blen > 0 {
            assert_eq!(run.parse(&full[..full.len() - 1]), Err("body length"));
        }
        mutations(run, o, &full);
    }
}

/// The widest head: the last of every parse and every bound.
fn widest(run: &mut Run, rng: &mut SplitMix64) {
    let b = Owned::base(4, rng).with(|c| {
        c.parents = asc(0xf8, 8);
        c.flags = 1;
        c.inc = u64::MAX;
        c.seq = u64::MAX;
        c.wall = u64::MAX;
        c.ctr = u32::MAX;
    });
    let v = run.written(&b, u32::MAX);
    assert!(v.len() <= MAX_HEAD2);
    assert_eq!(run.prefix(&v), Ok((v.len(), u32::MAX as usize)));
    assert_eq!(run.parse(&v), Err("body length"));
}

fn seeded(run: &mut Run, rng: &mut SplitMix64) {
    for _ in 0..1500 {
        let len = usize::try_from(rng.next_u64() % 300).unwrap();
        let mut b = vec![0u8; len];
        rng.fill(&mut b);
        if rng.next_u64() % 4 < 3 && !b.is_empty() {
            b[0] = VERSION;
        }
        if rng.next_u64() % 4 < 3 && b.len() > 1 {
            b[1] = u8::try_from(1 + rng.next_u64() % 4).unwrap();
        }
        run.parse(&b).ok();
        run.prefix(&b).ok();
    }
    for _ in 0..500 {
        let tag = u8::try_from(1 + rng.next_u64() % 4).unwrap();
        let mut o = Owned::base(tag, rng);
        rng.fill(&mut o.origin);
        o.flags = u8::try_from(rng.next_u64() % 2).unwrap();
        o.inc = rng.next_u64();
        o.seq = rng.next_u64();
        o.wall = rng.next_u64();
        o.ctr = rng.next_u64() as u32;
        let n = usize::try_from(rng.next_u64() % 9).unwrap();
        o.parents = (0..n)
            .map(|_| {
                let mut p = [0u8; 32];
                rng.fill(&mut p);
                p
            })
            .collect();
        o.parents.sort_unstable();
        o.parents.dedup();
        let blen = u32::try_from(rng.next_u64() % 65).unwrap();
        let v = run.written(&o, blen);
        let mut full = v.clone();
        full.extend(std::iter::repeat_n(0u8, blen as usize));
        assert_eq!(run.prefix(&full), Ok((v.len(), blen as usize)));
        assert_eq!(run.parse(&full), Ok(v.len()));
    }
}

#[test]
fn wire2_trace() {
    let mut rng = SplitMix64::traced(0x5747_0002);
    let mut run = Run::default();
    let done = writes(&mut run, &mut rng);
    damaged(&mut run, &done);
    widest(&mut run, &mut rng);
    seeded(&mut run, &mut rng);
    // The reasons are reached by the fixed inputs, not by the seeded part.
    for r in REASONS {
        assert!(run.reasons.contains(r), "no call failed with {r}");
    }
    if !soaking() {
        assert!(run.out.lines().count() > 5000);
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = std::path::Path::new(&dir).join("bcast");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("wire2.ndjson"), &run.out).unwrap();
    }
}
