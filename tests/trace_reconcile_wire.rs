//! Trace generation for the reconcile wire layer: the real `put_bound`, `read_bound`, `common_prefix`, `count`,
//! `put_parts`, `read_parts`, `frame_body`, `frame_len` and `first_set_ref` of `vinc-reconcile` on generated, boundary
//! and mutated inputs, and the head and count field of the messages a real session writes (and of mutations of them),
//! recorded as ndjson (`reconcile_wire.ndjson`) for the TLA+ trace check (`TraceReconcileWire.tla`) and the Lean
//! replay (`Vinc/TraceReconcileWire.lean`).
//!
//! Every line is `{"t":"rw","e":<event>,...}`; bytes, bounds and messages are int arrays and every number is below
//! 2^31 (a varint of 2^30 or more is recorded as 2^30, the value the checkers saturate at). The test asserts the
//! properties itself (round trip, one encoding per bound, the reasons of the refusals), so it is meaningful without the
//! proof tools. The trace is written to `$VINC_TRACE_DIR` when it is set and the lines are not even built otherwise.
//! `Items` is crate-private: the item lists are checked through the session traces (`trace_reconcile`) and, over all
//! inputs, by the specification and the Lean proofs only.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::type_complexity,
    unreachable_pub
)]

#[path = "reconcile_common.rs"]
mod common;

use std::fmt::Write as _;

use common::{Dir, fixed_set, index, mutate, run_with, var_set};
use vinc_reconcile::wire::{
    common_prefix, count, first_set_ref, frame_body, frame_len, put_bound, put_parts, read_bound, read_parts, tag,
};
use vinc_reconcile::{Initiator, Limits, Reason, Responder};
use vinc_tests::SplitMix64;
use vinc_wire::{Reader, varint};

const SAT: u64 = 1 << 30;

/// The lines of the trace; built only when `$VINC_TRACE_DIR` is set.
struct Trace(Option<String>);

impl Trace {
    fn new() -> Self {
        Self(std::env::var_os("VINC_TRACE_DIR").map(|_| String::new()))
    }

    fn line(&mut self, f: impl FnOnce() -> String) {
        if let Some(s) = &mut self.0 {
            s.push_str(&f());
            s.push('\n');
        }
    }
}

fn list(bytes: &[u8]) -> String {
    let mut s = String::from("[");
    for (i, x) in bytes.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, "{x}").unwrap();
    }
    s.push(']');
    s
}

fn why(r: Reason) -> &'static str {
    match r {
        Reason::Frame => "frame",
        Reason::Truncated => "truncated",
        Reason::Tag => "tag",
        Reason::Bound => "bound",
        Reason::Count => "count",
        Reason::Item => "item",
        Reason::State => "state",
    }
}

/// `read_bound` of `bytes` against `last`: the new bound and the bytes used.
fn read(last: &[u8], bytes: &[u8], mx: usize) -> Result<(Vec<u8>, usize), Reason> {
    let mut l = last.to_vec();
    let mut r = Reader::new(bytes);
    read_bound(&mut l, &mut r, mx).map(|()| (l, r.position()))
}

fn put(last: &[u8], b: &[u8]) -> Vec<u8> {
    let (mut l, mut out) = (last.to_vec(), Vec::new());
    put_bound(&mut out, &mut l, b).unwrap();
    assert_eq!(l, b, "put_bound makes the bound the new previous bound");
    out
}

fn bound_event(tr: &mut Trace, last: &[u8], bytes: &[u8], mx: usize) -> Result<(Vec<u8>, usize), Reason> {
    let res = read(last, bytes, mx);
    tr.line(|| match &res {
        Ok((b, used)) => format!(
            "{{\"t\":\"rw\",\"e\":\"rb\",\"last\":{},\"in\":{},\"mx\":{mx},\"ok\":{},\"used\":{used}}}",
            list(last),
            list(bytes),
            list(b)
        ),
        Err(e) => format!(
            "{{\"t\":\"rw\",\"e\":\"rb\",\"last\":{},\"in\":{},\"mx\":{mx},\"err\":\"{}\"}}",
            list(last),
            list(bytes),
            why(*e)
        ),
    });
    res
}

/// A bound against a previous bound: the encoding, its round trip with every limit and cut, and the one-encoding
/// property.
fn bound_case(tr: &mut Trace, last: &[u8], b: &[u8]) {
    let enc = put(last, b);
    tr.line(|| {
        format!(
            "{{\"t\":\"rw\",\"e\":\"pb\",\"last\":{},\"b\":{},\"out\":{}}}",
            list(last),
            list(b),
            list(&enc)
        )
    });
    let mut with_rest = enc.clone();
    with_rest.extend_from_slice(&[0, 9]);
    assert_eq!(bound_event(tr, last, &with_rest, b.len()), Ok((b.to_vec(), enc.len())));
    if !b.is_empty() {
        assert_eq!(bound_event(tr, last, &enc, b.len() - 1), Err(Reason::Bound));
    }
    for cut in 0..enc.len() {
        assert_eq!(bound_event(tr, last, &enc[..cut], b.len()), Err(Reason::Truncated));
    }
}

/// An arbitrary byte string read as a bound: an accepted one is the encoding of the bound it yields.
fn bound_probe(tr: &mut Trace, last: &[u8], bytes: &[u8], mx: usize) {
    match bound_event(tr, last, bytes, mx) {
        Ok((b, used)) => {
            assert_eq!(put(last, &b), bytes[..used], "an accepted bound is its encoding");
            assert!(b.len() <= mx);
        }
        Err(e) => assert!(matches!(e, Reason::Truncated | Reason::Bound)),
    }
}

fn strings(alpha: &[u8], max: usize) -> Vec<Vec<u8>> {
    let mut all = vec![Vec::new()];
    let mut layer = vec![Vec::new()];
    for _ in 0..max {
        let mut next = Vec::new();
        for s in &layer {
            for &a in alpha {
                let mut t = s.clone();
                t.push(a);
                next.push(t);
            }
        }
        all.extend(next.iter().cloned());
        layer = next;
    }
    all
}

fn bounds_traces(tr: &mut Trace) {
    let small = strings(&[0, 1], 3);
    for last in &small {
        for b in &small {
            bound_case(tr, last, b);
            assert_eq!(
                common_prefix(last, b),
                last.iter().zip(b).take_while(|(x, y)| x == y).count()
            );
            tr.line(|| {
                format!(
                    "{{\"t\":\"rw\",\"e\":\"cp\",\"a\":{},\"b\":{},\"out\":{}}}",
                    list(last),
                    list(b),
                    common_prefix(last, b)
                )
            });
        }
    }
    // Every short byte string over a small alphabet as a bound, against every short previous bound.
    for last in strings(&[0, 1], 2) {
        for r in strings(&[0, 1, 2, 3], 4) {
            for mx in [0, 1, 2, 3] {
                bound_probe(tr, &last, &r, mx);
            }
        }
    }
    // The cap of the shared prefix at 255 and bounds of 254..300 bytes.
    let mut rng = SplitMix64::new(5);
    for n in [254usize, 255, 256, 257, 300] {
        let last = vec![0u8; n];
        let mut cands: Vec<Vec<u8>> = vec![
            last.clone(),
            [last.clone(), vec![0]].concat(),
            vec![0; n - 1],
            vec![0; n + 1],
            Vec::new(),
            vec![1],
            [vec![0u8; 255], vec![5]].concat(),
            [vec![0u8; 254], vec![5]].concat(),
        ];
        for at in [n - 1, 254, 255, 256] {
            if at < n {
                let mut c = last.clone();
                c[at] = 7;
                cands.push(c);
            }
        }
        for b in &cands {
            bound_case(tr, &last, b);
        }
        for c in [0u8, 1, 253, 254, 255] {
            for m in [0usize, 1, 2, 46, 47] {
                let mut r = vec![c];
                r.extend(varint_bytes(m as u64));
                r.extend(std::iter::repeat_n(0u8, m));
                r.push(9);
                bound_probe(tr, &last, &r, 400);
            }
        }
        // Random strings against a random previous bound.
        for _ in 0..40 {
            let mut l = vec![0u8; (rng.next_u64() % 6) as usize];
            rng.fill(&mut l);
            let mut r = vec![0u8; (rng.next_u64() % 9) as usize];
            rng.fill(&mut r);
            for x in &mut r {
                *x %= 4;
            }
            for x in &mut l {
                *x %= 3;
            }
            bound_probe(tr, &l, &r, 8);
        }
    }
    // Varints of every width in the length field: huge lengths are refused with Bound, cut ones with Truncated.
    for k in [6u32, 7, 13, 14, 20, 21, 27, 28, 29, 30, 31, 40, 62] {
        for d in [0u64, 1] {
            let v = (1u64 << k) - 1 + d;
            let mut r = vec![0u8];
            r.extend(varint_bytes(v));
            bound_probe(tr, &[1, 2], &r, 4096);
            bound_probe(tr, &[], &r, 4096);
        }
    }
    for bad in [
        vec![0u8, 128, 0],
        vec![0, 128],
        vec![0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 1],
    ] {
        bound_probe(tr, &[], &bad, 4096);
    }
}

fn varint_bytes(v: u64) -> Vec<u8> {
    let mut buf = [0u8; varint::MAX_LEN];
    let n = varint::encode(v, &mut buf).unwrap();
    buf[..n].to_vec()
}

fn sat(v: usize) -> u64 {
    (v as u64).min(SAT)
}

fn count_event(tr: &mut Trace, bytes: &[u8]) {
    let mut r = Reader::new(bytes);
    let res = count(&mut r);
    tr.line(|| match &res {
        Ok(v) => format!(
            "{{\"t\":\"rw\",\"e\":\"ct\",\"in\":{},\"ok\":{},\"used\":{}}}",
            list(bytes),
            sat(*v),
            r.position()
        ),
        Err(e) => format!(
            "{{\"t\":\"rw\",\"e\":\"ct\",\"in\":{},\"err\":\"{}\"}}",
            list(bytes),
            why(*e)
        ),
    });
    match res {
        Ok(v) => assert_eq!(
            varint_bytes(v as u64),
            bytes[..r.position()],
            "a count has one encoding"
        ),
        Err(e) => assert_eq!(e, Reason::Truncated),
    }
}

fn parts_event(tr: &mut Trace, bytes: &[u8]) -> Result<(usize, bool, usize), Reason> {
    let mut r = Reader::new(bytes);
    let res = read_parts(&mut r).map(|(c, m)| (c, m, r.position()));
    tr.line(|| match &res {
        Ok((c, m, used)) => format!(
            "{{\"t\":\"rw\",\"e\":\"rp\",\"in\":{},\"cnt\":{},\"more\":{m},\"used\":{used}}}",
            list(bytes),
            sat(*c)
        ),
        Err(e) => format!(
            "{{\"t\":\"rw\",\"e\":\"rp\",\"in\":{},\"err\":\"{}\"}}",
            list(bytes),
            why(*e)
        ),
    });
    res
}

fn counts_traces(tr: &mut Trace) {
    for s in strings(&[0, 1, 127, 128, 129, 255], 2) {
        count_event(tr, &s);
        parts_event(tr, &s).ok();
    }
    for k in [6u32, 7, 13, 14, 20, 21, 27, 28, 29, 30, 31, 40, 62] {
        for d in [0u64, 1, 2] {
            let b = varint_bytes((1u64 << k) - 1 + d);
            count_event(tr, &b);
            parts_event(tr, &b).ok();
        }
    }
    for bad in [
        vec![128u8],
        vec![128, 0],
        vec![255; 9],
        vec![255, 255, 255, 255, 255, 255, 255, 255, 255, 1],
    ] {
        count_event(tr, &bad);
        parts_event(tr, &bad).ok();
    }
    let edges: Vec<usize> = (0..301usize)
        .chain([
            (1 << 6) - 1,
            1 << 6,
            (1 << 7) - 1,
            1 << 7,
            (1 << 14) - 1,
            1 << 14,
            (1 << 21) - 1,
            1 << 21,
            (1 << 28) - 1,
        ])
        .collect();
    for cnt in edges {
        for more in [false, true] {
            let mut buf = Vec::new();
            put_parts(&mut buf, cnt, more).unwrap();
            tr.line(|| {
                format!(
                    "{{\"t\":\"rw\",\"e\":\"pp\",\"cnt\":{cnt},\"more\":{more},\"out\":{}}}",
                    list(&buf)
                )
            });
            let mut with_rest = buf.clone();
            with_rest.extend_from_slice(&[0, 1]);
            let got = parts_event(tr, &with_rest);
            if cnt == 0 && more {
                assert_eq!(got, Err(Reason::Count), "an empty message cannot hold more");
            } else {
                assert_eq!(got, Ok((cnt, more, buf.len())));
            }
        }
    }
}

fn frame_traces(tr: &mut Trace) {
    for s in strings(&[0, 1, 2, 255], 4) {
        let res = frame_body(&s).map(<[u8]>::len);
        tr.line(|| match &res {
            Ok(n) => format!("{{\"t\":\"rw\",\"e\":\"fb\",\"in\":{},\"ok\":{n}}}", list(&s)),
            Err(e) => format!(
                "{{\"t\":\"rw\",\"e\":\"fb\",\"in\":{},\"err\":\"{}\"}}",
                list(&s),
                why(*e)
            ),
        });
        assert_eq!(
            res.is_ok(),
            s.len() >= 3 && frame_len([s[0], s[1], s[2]]) == s.len() - 3
        );
        if s.len() < 3 {
            assert_eq!(res, Err(Reason::Truncated));
        } else if res.is_err() {
            assert_eq!(res, Err(Reason::Frame));
        }
    }
    // Real bodies up to 300 bytes and at the edges of the three-byte length, with the right and a wrong length.
    let lens: Vec<usize> = (0..301usize)
        .chain([65_535, 65_536, 65_537, 0xff_fffe, 0xff_ffff, 0x100_0000])
        .collect();
    for len in lens {
        for skew in [0usize, 1] {
            let announced = len + skew;
            let header = [(announced >> 16) as u8, (announced >> 8) as u8, announced as u8];
            let mut msg = header.to_vec();
            msg.resize(3 + len, 0);
            let res = frame_body(&msg).map(<[u8]>::len);
            let fits = announced <= 0xff_ffff;
            if len > 0xff_ffff {
                // The announced length wraps in three bytes: the header cannot say this body.
                assert_eq!(res, Err(Reason::Frame));
            } else if skew == 0 {
                assert_eq!(res, Ok(len));
            } else {
                assert_eq!(res, Err(Reason::Frame));
            }
            if fits || len > 0xff_ffff {
                tr.line(|| match &res {
                    Ok(n) => format!(
                        "{{\"t\":\"rw\",\"e\":\"fl\",\"hdr\":{},\"blen\":{len},\"ok\":{n}}}",
                        list(&header)
                    ),
                    Err(e) => format!(
                        "{{\"t\":\"rw\",\"e\":\"fl\",\"hdr\":{},\"blen\":{len},\"err\":\"{}\"}}",
                        list(&header),
                        why(*e)
                    ),
                });
            }
            assert_eq!(frame_len(header), announced & 0xff_ffff);
        }
    }
}

/// The count and the head of the first part of a message, as the machine reads them.
fn message_event(tr: &mut Trace, msg: &[u8], mx: usize) {
    let res: Result<(usize, bool, Option<(u8, Vec<u8>, Option<Vec<u8>>, usize)>), Reason> = (|| {
        let body = frame_body(msg)?;
        let mut r = Reader::new(body);
        let (cnt, more) = read_parts(&mut r)?;
        if cnt == 0 {
            return Ok((cnt, more, None));
        }
        let t = r.read_u8().map_err(|_| Reason::Truncated)?;
        let mut last = Vec::new();
        read_bound(&mut last, &mut r, mx)?;
        let lo = last.clone();
        let hi = if t & tag::INF == 0 {
            read_bound(&mut last, &mut r, mx)?;
            Some(last.clone())
        } else {
            None
        };
        Ok((cnt, more, Some((t & !tag::INF, lo, hi, r.position()))))
    })();
    tr.line(|| match &res {
        Ok((cnt, more, head)) => {
            let h = head.as_ref().map_or_else(String::new, |(kind, lo, hi, used)| {
                format!(
                    ",\"head\":{{\"kind\":{kind},\"lo\":{}{},\"used\":{used}}}",
                    list(lo),
                    hi.as_ref().map_or_else(String::new, |h| format!(",\"hi\":{}", list(h)))
                )
            });
            format!(
                "{{\"t\":\"rw\",\"e\":\"msg\",\"in\":{},\"mx\":{mx},\"cnt\":{},\"more\":{more}{h}}}",
                list(msg),
                sat(*cnt)
            )
        }
        Err(e) => format!(
            "{{\"t\":\"rw\",\"e\":\"msg\",\"in\":{},\"mx\":{mx},\"err\":\"{}\"}}",
            list(msg),
            why(*e)
        ),
    });
    let fsr = first_set_ref(msg);
    tr.line(|| match &fsr {
        Ok(r) => format!("{{\"t\":\"rw\",\"e\":\"fsr\",\"in\":{},\"ok\":{}}}", list(msg), list(r)),
        Err(e) => format!(
            "{{\"t\":\"rw\",\"e\":\"fsr\",\"in\":{},\"err\":\"{}\"}}",
            list(msg),
            why(*e)
        ),
    });
}

/// Every message of real sessions (both directions), then mutations of the short ones: every cut, a few flipped
/// bytes and one extra byte.
fn message_traces(tr: &mut Trace) {
    let mut rng = SplitMix64::new(21);
    let mut sets: Vec<(Vec<Vec<u8>>, Vec<Vec<u8>>)> = Vec::new();
    for (n, d, len) in [(60usize, 4usize, 3usize), (120, 10, 4), (50, 2, 2), (200, 6, 5)] {
        let a = fixed_set(&mut rng, n, len);
        let (b, ..) = mutate(&mut rng, &a, d, len);
        sets.push((a, b));
    }
    let a = var_set(&mut rng, 80, 5);
    let (b, ..) = mutate(&mut rng, &a, 6, 4);
    sets.push((a, b));
    let a = fixed_set(&mut rng, 30, 3);
    let mut b = a.clone();
    b.extend(fixed_set(&mut rng, 12, 3));
    sets.push((a, common::sorted(b)));
    let mut msgs: Vec<Vec<u8>> = Vec::new();
    for (a, b) in &sets {
        let lim = Limits {
            max_item: 64,
            max_message: 600,
            ..Limits::default()
        };
        let (ia, ib) = (index(a), index(b));
        run_with(
            &mut Initiator::new(lim),
            &mut Responder::new(lim),
            &ia,
            &ib,
            |_: Dir, m| msgs.push(m.clone()),
        )
        .unwrap();
    }
    assert!(msgs.len() > 20);
    for m in &msgs {
        message_event(tr, m, 64);
    }
    // An empty message that claims to hold more, and a frame without parts.
    message_event(tr, &[0, 0, 1, 1], 64);
    message_event(tr, &[0, 0, 0], 64);
    message_event(tr, &[0, 0, 1, 0], 64);
    for m in msgs.iter().filter(|m| m.len() < 400) {
        for cut in 0..m.len() {
            message_event(tr, &m[..cut], 64);
        }
        for _ in 0..4 {
            let mut x = m.clone();
            let at = (rng.next_u64() as usize) % x.len();
            x[at] = rng.next_u64() as u8;
            message_event(tr, &x, 64);
        }
        let mut x = m.clone();
        x.push(0);
        message_event(tr, &x, 64);
    }
}

#[test]
fn reconcile_wire_traces_are_consistent_with_the_code() {
    let mut tr = Trace::new();
    bounds_traces(&mut tr);
    counts_traces(&mut tr);
    frame_traces(&mut tr);
    message_traces(&mut tr);
    if let (Some(text), Some(dir)) = (tr.0, std::env::var_os("VINC_TRACE_DIR")) {
        assert!(text.lines().count() > 5000);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("reconcile_wire.ndjson"), text).unwrap();
    }
}
