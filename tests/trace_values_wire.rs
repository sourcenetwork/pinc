//! Trace generation for the value wire codecs (`vinc-values` `wire.rs`): REQ (`Req::parse`, `total_len`, `encode`), the
//! GROUP header (`GroupHeader::parse`, `encode`), PROOF (`ProofFrame::parse`, `write_head`) and `PROOF_REQ`
//! (`ProofReq::parse`, `encode`), recorded as ndjson (`values_wire.ndjson`) for the TLA+ trace check
//! (`TraceValuesWire.tla`) and the Lean replay (`Vinc/ValuesWireTrace.lean`).
//!
//! The real codecs run on seeded random valid values, every cut length of valid inputs, mutated inputs (a flipped byte, a
//! wrong type byte, a count over 32, a bad flag, a zero length, a non-whole proof, a non-canonical id, trailing bytes)
//! and garbage; the encoders run into buffers of every size around the edges, pre-filled with a sentinel so that a
//! failed encode is seen to write nothing. A `u64` is recorded as four 16-bit limbs (TLC integers are 32 bits wide).
//!
//! The test also checks every answer against a plain reference written here from the format, so it is meaningful
//! without the proof tools: the accepted inputs and their fields, the error kind and the `Truncated` shortfall of every
//! refusal, that an accepted input re-encodes to the bytes consumed, that `total_len` agrees with the parse, and that a
//! failed encode leaves the buffer as it was.
//! The trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::type_complexity,
    clippy::doc_markdown,
    unreachable_pub
)]

use std::fmt::Write as _;

use vinc_tests::SplitMix64;
use vinc_values::span::Span;
use vinc_values::wire::{GROUP_HDR, GroupHeader, ProofFrame, ProofReq, REQ_FIXED, REQ_MAX, Req};
use vinc_wire::WireError;

const SENTINEL: u8 = 0xaa;

/// The trace, one ndjson line per event.
#[derive(Default)]
struct Trace(String);

impl Trace {
    fn line(&mut self, s: &str) {
        self.0.push_str(s);
        self.0.push('\n');
    }
}

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        (v >> 48) & 0xffff
    )
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

/// The error of a refusal as the trace records it: kind, shortfall and reason.
fn err_fields(e: &WireError) -> String {
    let (kind, needed, msg) = match e {
        WireError::Truncated { needed } => ("truncated", *needed, ""),
        WireError::BufferTooSmall { needed } => ("small", *needed, ""),
        WireError::VarintTooLong => ("toolong", 0, ""),
        WireError::VarintOverflow => ("overflow", 0, ""),
        WireError::VarintNonMinimal => ("nonminimal", 0, ""),
        WireError::Unexpected(m) => ("unexpected", 0, *m),
        other => panic!("the value wire produced {other:?}"),
    };
    format!("\"err\":\"{kind}\",\"needed\":{needed},\"msg\":\"{msg}\"")
}

fn res_err(e: &WireError) -> String {
    format!("{{\"ok\":false,{}}}", err_fields(e))
}

fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

/// A `u64` from the edge values and random ones.
fn word(rng: &mut SplitMix64) -> u64 {
    match below(rng, 6) {
        0 => 0,
        1 => u64::MAX,
        2 => 1 << below(rng, 64),
        3 => (1u64 << below(rng, 63)) - 1,
        _ => rng.next_u64() >> below(rng, 64),
    }
}

/// An id below 2^63 (a varint), from every width.
fn sid(rng: &mut SplitMix64) -> u64 {
    word(rng) >> 1
}

fn rand_bytes(rng: &mut SplitMix64, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    rng.fill(&mut v);
    v
}

// ---- the reference, written from the format and not from the code ----

#[derive(Debug, PartialEq, Eq)]
enum Ref<T> {
    Ok(T),
    Truncated(usize),
    Unexpected(&'static str),
    VarintTooLong,
    VarintNonMinimal,
}

fn be(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0u64, |a, &b| (a << 8) | u64::from(b))
}

/// The first field that does not fit in `len` bytes: the shortfall is its end less `len`.
fn short(ends: &[usize], len: usize) -> Option<usize> {
    ends.iter().find(|&&e| e > len).map(|e| e - len)
}

/// A varint as the format says: at most 9 bytes, the last below 128 and not zero unless alone.
fn ref_varint(b: &[u8]) -> Ref<(u64, usize)> {
    for (i, &x) in b.iter().take(9).enumerate() {
        if x < 128 {
            if x == 0 && i > 0 {
                return Ref::VarintNonMinimal;
            }
            let v = b[..=i]
                .iter()
                .enumerate()
                .fold(0u64, |a, (k, &y)| a | (u64::from(y & 0x7f) << (7 * k)));
            return Ref::Ok((v, i + 1));
        }
    }
    if b.len() >= 9 {
        Ref::VarintTooLong
    } else {
        Ref::Truncated(1)
    }
}

fn ref_req(b: &[u8]) -> Ref<(Vec<u8>, Vec<Span>, usize)> {
    if b.is_empty() {
        return Ref::Truncated(1);
    }
    if b[0] != 1 {
        return Ref::Unexpected("not a request");
    }
    if b.len() < REQ_FIXED {
        return Ref::Truncated(short(&[33, 34], b.len()).unwrap());
    }
    let c = usize::from(b[33]);
    if c > 255 {
        return Ref::Unexpected("too many ranges");
    }
    let n = 34 + 16 * c;
    if b.len() < n {
        return Ref::Truncated(n - b.len());
    }
    let spans = (0..c)
        .map(|i| Span {
            off: be(&b[34 + 16 * i..42 + 16 * i]),
            len: be(&b[42 + 16 * i..50 + 16 * i]),
        })
        .collect();
    Ref::Ok((b[1..33].to_vec(), spans, n))
}

fn ref_gh(b: &[u8]) -> Ref<GroupHeader> {
    if b.len() < GROUP_HDR {
        return Ref::Truncated(GROUP_HDR - b.len());
    }
    if b[0] != 2 {
        return Ref::Unexpected("not a group");
    }
    if b[15] > 1 {
        return Ref::Unexpected("bad follows flag");
    }
    let (len, plen) = (be(&b[9..13]) as u32, be(&b[13..15]) as u16);
    if len == 0 || plen % 64 != 0 {
        return Ref::Unexpected("bad group lengths");
    }
    Ref::Ok(GroupHeader {
        off: be(&b[1..9]),
        len,
        plen,
        follows: b[15] == 1,
    })
}

fn ref_pf(b: &[u8]) -> Ref<(u64, u8, u64, u32, u64, Vec<u8>)> {
    let (sid, n) = match ref_varint(b) {
        Ref::Ok(x) => x,
        Ref::Truncated(k) => return Ref::Truncated(k),
        Ref::Unexpected(m) => return Ref::Unexpected(m),
        Ref::VarintTooLong => return Ref::VarintTooLong,
        Ref::VarintNonMinimal => return Ref::VarintNonMinimal,
    };
    if let Some(k) = short(&[n + 1, n + 9, n + 13, n + 21], b.len()) {
        return Ref::Truncated(k);
    }
    let proof = &b[n + 21..];
    if !proof.len().is_multiple_of(64) || proof.len() > 1100 {
        return Ref::Unexpected("bad proof length");
    }
    Ref::Ok((
        sid,
        b[n],
        be(&b[n + 1..n + 9]),
        be(&b[n + 9..n + 13]) as u32,
        be(&b[n + 13..n + 21]),
        proof.to_vec(),
    ))
}

fn ref_pr(b: &[u8]) -> Ref<ProofReq> {
    let (sid, n) = match ref_varint(b) {
        Ref::Ok(x) => x,
        Ref::Truncated(k) => return Ref::Truncated(k),
        Ref::Unexpected(m) => return Ref::Unexpected(m),
        Ref::VarintTooLong => return Ref::VarintTooLong,
        Ref::VarintNonMinimal => return Ref::VarintNonMinimal,
    };
    if let Some(k) = short(&[n + 8, n + 16], b.len()) {
        return Ref::Truncated(k);
    }
    if b.len() > n + 16 {
        return Ref::Unexpected("trailing bytes");
    }
    Ref::Ok(ProofReq {
        sid,
        from: be(&b[n..n + 8]),
        upto: be(&b[n + 8..n + 16]),
    })
}

/// Compare a real result with the reference's, error kinds and shortfalls included.
fn agree<T, U: std::fmt::Debug>(real: &Result<T, WireError>, reference: &Ref<U>, what: &str) {
    match (real, reference) {
        (Err(WireError::Truncated { needed }), Ref::Truncated(k)) => assert_eq!(needed, k, "{what}: shortfall"),
        (Err(WireError::Unexpected(m)), Ref::Unexpected(r)) => assert_eq!(m, r, "{what}: reason"),
        (Ok(_), Ref::Ok(_))
        | (Err(WireError::VarintTooLong), Ref::VarintTooLong)
        | (Err(WireError::VarintNonMinimal), Ref::VarintNonMinimal) => {}
        (_, r) => panic!("{what}: the code and the reference disagree, reference {r:?}"),
    }
}

// ---- the events ----

fn ev_req(tr: &mut Trace, b: &[u8]) {
    let real = Req::parse(b);
    let reference = ref_req(b);
    agree(&real, &reference, "Req::parse");
    let tot = Req::total_len(b);
    match &real {
        Ok((req, n)) => {
            let Ref::Ok((root, spans, rn)) = &reference else {
                panic!()
            };
            assert_eq!(
                (req.root().as_slice(), req.ranges().collect::<Vec<_>>(), *n),
                (root.as_slice(), spans.clone(), *rn)
            );
            // canonical: the request re-encodes to the bytes consumed
            let mut out = [SENTINEL; REQ_MAX + 4];
            let m = Req::encode(req.root(), spans, &mut out).unwrap();
            assert_eq!(&out[..m], &b[..*n], "an accepted request re-encodes to itself");
            assert_eq!(tot.unwrap(), *n, "total_len agrees with the parse");
        }
        Err(WireError::Unexpected(_)) if b.len() >= REQ_FIXED => assert!(matches!(tot, Err(WireError::Unexpected(_)))),
        Err(WireError::Truncated { .. }) if b.len() >= REQ_FIXED => assert!(tot.unwrap() > b.len()),
        Err(_) => {}
    }
    let res = match &real {
        Ok((req, n)) => {
            let rs: Vec<String> = req
                .ranges()
                .map(|s| format!("[{},{}]", limbs(s.off), limbs(s.len)))
                .collect();
            format!(
                "{{\"ok\":true,\"root\":{},\"ranges\":[{}],\"n\":{n}}}",
                list(req.root()),
                rs.join(",")
            )
        }
        Err(e) => res_err(e),
    };
    let tr_res = match &tot {
        Ok(n) => format!("{{\"ok\":true,\"n\":{n}}}"),
        Err(e) => res_err(e),
    };
    tr.line(&format!(
        "{{\"t\":\"wreq\",\"in\":{},\"res\":{res},\"tot\":{tr_res}}}",
        list(b)
    ));
}

fn ev_req_enc(tr: &mut Trace, root: &[u8; 32], spans: &[Span], cap: usize) {
    let mut out = vec![SENTINEL; cap];
    let r = Req::encode(root, spans, &mut out);
    let total = REQ_FIXED + 16 * spans.len();
    match &r {
        Ok(n) => {
            assert!(spans.len() <= 255 && cap >= total && *n == total);
            assert!(
                out[*n..].iter().all(|&b| b == SENTINEL),
                "the rest of the buffer is left alone"
            );
            let (req, used) = Req::parse(&out[..*n]).unwrap();
            assert_eq!(
                (req.root(), req.ranges().collect::<Vec<_>>(), used),
                (root, spans.to_vec(), total)
            );
        }
        Err(WireError::Unexpected("too many ranges")) => {
            assert!(spans.len() > 255);
            assert!(out.iter().all(|&b| b == SENTINEL), "a refused encode writes nothing");
        }
        Err(WireError::BufferTooSmall { needed }) => {
            assert!(spans.len() <= 255 && *needed == total - cap);
            assert!(out.iter().all(|&b| b == SENTINEL), "a failed encode writes nothing");
        }
        Err(e) => panic!("{e:?}"),
    }
    let rs: Vec<String> = spans
        .iter()
        .map(|s| format!("[{},{}]", limbs(s.off), limbs(s.len)))
        .collect();
    let res = match &r {
        Ok(n) => format!("{{\"ok\":true,\"n\":{n}}}"),
        Err(e) => res_err(e),
    };
    tr.line(&format!(
        "{{\"t\":\"wreqenc\",\"root\":{},\"spans\":[{}],\"cap\":{cap},\"res\":{res},\"after\":{}}}",
        list(root),
        rs.join(","),
        list(&out)
    ));
}

fn ev_gh(tr: &mut Trace, b: &[u8]) {
    let real = GroupHeader::parse(b);
    let reference = ref_gh(b);
    agree(&real, &reference, "GroupHeader::parse");
    if let (Ok(h), Ref::Ok(r)) = (&real, &reference) {
        assert_eq!(h, r);
        assert_eq!(
            h.encode().as_slice(),
            &b[..GROUP_HDR],
            "an accepted header re-encodes to itself"
        );
    }
    let res = match &real {
        Ok(h) => format!(
            "{{\"ok\":true,\"off\":{},\"len\":{},\"plen\":{},\"follows\":{}}}",
            limbs(h.off),
            limbs(u64::from(h.len)),
            h.plen,
            h.follows
        ),
        Err(e) => res_err(e),
    };
    tr.line(&format!("{{\"t\":\"wgh\",\"in\":{},\"res\":{res}}}", list(b)));
}

fn ev_gh_enc(tr: &mut Trace, h: &GroupHeader) {
    let bytes = h.encode();
    assert_eq!(bytes[0], 2);
    assert_eq!(be(&bytes[1..9]), h.off);
    assert_eq!(be(&bytes[9..13]), u64::from(h.len));
    assert_eq!(be(&bytes[13..15]), u64::from(h.plen));
    assert_eq!(bytes[15], u8::from(h.follows));
    let valid = h.len != 0 && h.plen.is_multiple_of(64);
    assert_eq!(GroupHeader::parse(&bytes).is_ok(), valid);
    if valid {
        assert_eq!(GroupHeader::parse(&bytes).unwrap(), *h);
    }
    tr.line(&format!(
        "{{\"t\":\"wghenc\",\"off\":{},\"len\":{},\"plen\":{},\"follows\":{},\"out\":{}}}",
        limbs(h.off),
        limbs(u64::from(h.len)),
        h.plen,
        h.follows,
        list(&bytes)
    ));
}

fn ev_pf(tr: &mut Trace, b: &[u8]) {
    let real = ProofFrame::parse(b);
    let reference = ref_pf(b);
    agree(&real, &reference, "ProofFrame::parse");
    if let (Ok(pf), Ref::Ok((sid, glog, start, wn, ln, proof))) = (&real, &reference) {
        assert_eq!(
            (pf.sid, pf.glog, pf.start, pf.wn, pf.ln, pf.proof),
            (*sid, *glog, *start, *wn, *ln, proof.as_slice())
        );
        assert!(pf.proof.len() <= 17 * 64, "1100 rounds down to 17 pairs");
        let mut head = [SENTINEL; 40];
        let hn = ProofFrame::write_head(pf.sid, pf.glog, pf.start, pf.wn, pf.ln, &mut head).unwrap();
        assert_eq!(
            [&head[..hn], pf.proof].concat(),
            b,
            "an accepted frame re-encodes to itself"
        );
    }
    let res = match &real {
        Ok(pf) => format!(
            "{{\"ok\":true,\"sid\":{},\"glog\":{},\"start\":{},\"wn\":{},\"ln\":{},\"proof\":{}}}",
            limbs(pf.sid),
            pf.glog,
            limbs(pf.start),
            limbs(u64::from(pf.wn)),
            limbs(pf.ln),
            list(pf.proof)
        ),
        Err(e) => res_err(e),
    };
    tr.line(&format!("{{\"t\":\"wpf\",\"in\":{},\"res\":{res}}}", list(b)));
}

fn ev_pf_head(tr: &mut Trace, sid: u64, glog: u8, start: u64, wn: u32, ln: u64, cap: usize) {
    let mut out = vec![SENTINEL; cap];
    let r = ProofFrame::write_head(sid, glog, start, wn, ln, &mut out);
    match &r {
        Ok(n) => {
            assert!(sid < 1 << 63 && out[*n..].iter().all(|&b| b == SENTINEL));
            let pf = ProofFrame::parse(&out[..*n]).unwrap();
            assert_eq!(
                (pf.sid, pf.glog, pf.start, pf.wn, pf.ln, pf.proof.len()),
                (sid, glog, start, wn, ln, 0)
            );
        }
        Err(WireError::VarintOverflow) => {
            assert!(sid >= 1 << 63);
            assert!(out.iter().all(|&b| b == SENTINEL));
        }
        Err(WireError::BufferTooSmall { needed }) => {
            assert!(sid < 1 << 63 && *needed >= 1);
            assert!(out.iter().all(|&b| b == SENTINEL), "a failed write_head writes nothing");
        }
        Err(e) => panic!("{e:?}"),
    }
    let res = match &r {
        Ok(n) => format!("{{\"ok\":true,\"n\":{n}}}"),
        Err(e) => res_err(e),
    };
    tr.line(&format!(
        "{{\"t\":\"wpfhead\",\"sid\":{},\"glog\":{glog},\"start\":{},\"wn\":{},\"ln\":{},\"cap\":{cap},\"res\":{res},\"after\":{}}}",
        limbs(sid),
        limbs(start),
        limbs(u64::from(wn)),
        limbs(ln),
        list(&out)
    ));
}

fn ev_pr(tr: &mut Trace, b: &[u8]) {
    let real = ProofReq::parse(b);
    let reference = ref_pr(b);
    agree(&real, &reference, "ProofReq::parse");
    if let (Ok(r), Ref::Ok(x)) = (&real, &reference) {
        assert_eq!(r, x);
        let mut out = [SENTINEL; 40];
        let n = r.encode(&mut out).unwrap();
        assert_eq!(&out[..n], b, "an accepted PROOF_REQ re-encodes to the whole input");
    }
    let res = match &real {
        Ok(r) => format!(
            "{{\"ok\":true,\"sid\":{},\"from\":{},\"upto\":{}}}",
            limbs(r.sid),
            limbs(r.from),
            limbs(r.upto)
        ),
        Err(e) => res_err(e),
    };
    tr.line(&format!("{{\"t\":\"wpr\",\"in\":{},\"res\":{res}}}", list(b)));
}

fn ev_pr_enc(tr: &mut Trace, r: &ProofReq, cap: usize) {
    let mut out = vec![SENTINEL; cap];
    let res = r.encode(&mut out);
    match &res {
        Ok(n) => {
            assert!(r.sid < 1 << 63 && out[*n..].iter().all(|&b| b == SENTINEL));
            assert_eq!(ProofReq::parse(&out[..*n]).unwrap(), *r);
            if cap > *n {
                assert!(ProofReq::parse(&out[..=*n]).is_err(), "a trailing byte is refused");
            }
        }
        Err(WireError::VarintOverflow) => {
            assert!(r.sid >= 1 << 63);
            assert!(out.iter().all(|&b| b == SENTINEL));
        }
        Err(WireError::BufferTooSmall { .. }) => {
            assert!(r.sid < 1 << 63);
            assert!(out.iter().all(|&b| b == SENTINEL), "a failed encode writes nothing");
        }
        Err(e) => panic!("{e:?}"),
    }
    let rs = match &res {
        Ok(n) => format!("{{\"ok\":true,\"n\":{n}}}"),
        Err(e) => res_err(e),
    };
    tr.line(&format!(
        "{{\"t\":\"wprenc\",\"sid\":{},\"from\":{},\"upto\":{},\"cap\":{cap},\"res\":{rs},\"after\":{}}}",
        limbs(r.sid),
        limbs(r.from),
        limbs(r.upto),
        list(&out)
    ));
}

/// Every byte string with one byte changed to one of a few values, at a few positions; plus the whole string cut at
/// every length in `cuts` and extended by a trailing byte.
fn mutations(rng: &mut SplitMix64, base: &[u8], hot: &[usize]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let positions: Vec<usize> = hot.iter().copied().filter(|&p| p < base.len()).collect();
    for &p in &positions {
        for v in [0u8, 1, 2, 3, 0x7f, 0x80, 0xff, rng.next_u64() as u8] {
            let mut m = base.to_vec();
            m[p] = v;
            out.push(m);
        }
    }
    for _ in 0..6 {
        let mut m = base.to_vec();
        if !m.is_empty() {
            let p = below(rng, m.len() as u64) as usize;
            m[p] ^= 1 << below(rng, 8);
        }
        out.push(m);
    }
    let mut ext = base.to_vec();
    ext.push(rng.next_u64() as u8);
    out.push(ext);
    out
}

#[test]
fn value_wire_trace() {
    let mut tr = Trace::default();
    let mut rng = SplitMix64::traced(0x5eed_0007);

    // ---- REQ ----
    let mut reqs: Vec<Vec<u8>> = Vec::new();
    for k in (0..=34).chain([40, 100, 255, 256]) {
        for _ in 0..2 {
            let root: [u8; 32] = rand_bytes(&mut rng, 32).try_into().unwrap();
            let spans: Vec<Span> = (0..k)
                .map(|_| Span {
                    off: word(&mut rng),
                    len: word(&mut rng),
                })
                .collect();
            ev_req_enc(&mut tr, &root, &spans, REQ_FIXED + 16 * k.min(33));
            if k <= 255 {
                let mut buf = vec![0u8; REQ_FIXED + 16 * k];
                Req::encode(&root, &spans, &mut buf).unwrap();
                reqs.push(buf);
            }
        }
    }
    let root1: [u8; 32] = rand_bytes(&mut rng, 32).try_into().unwrap();
    for k in [0usize, 1, 2, 3, 31, 32, 33, 34, 255, 256] {
        let spans: Vec<Span> = (0..k)
            .map(|_| Span {
                off: word(&mut rng),
                len: word(&mut rng),
            })
            .collect();
        let total = REQ_FIXED + 16 * k;
        let caps: Vec<usize> = if k <= 3 {
            (0..=total + 2).collect()
        } else {
            vec![0, 1, 33, 34, 35, total - 1, total, total + 1, 600]
        };
        for cap in caps {
            ev_req_enc(&mut tr, &root1, &spans, cap);
        }
    }
    for (i, r) in reqs.iter().enumerate() {
        // trailing bytes are left for the caller, every cut is truncated
        ev_req(&mut tr, r);
        for tail in [&[0u8][..], &[7, 9, 11][..]] {
            ev_req(&mut tr, &[r.as_slice(), tail].concat());
        }
        let cuts: Vec<usize> = if r.len() <= 70 {
            (0..r.len()).collect()
        } else {
            vec![0, 1, 2, 32, 33, 34, 35, 49, 50, r.len() - 17, r.len() - 16, r.len() - 1]
        };
        for c in cuts {
            ev_req(&mut tr, &r[..c]);
        }
        if i % 5 == 0 {
            for m in mutations(&mut rng, r, &[0, 1, 17, 32, 33, 34, 35]) {
                ev_req(&mut tr, &m);
            }
        }
    }
    for c in 0..=255u8 {
        // every count byte, with a body of 17 bytes after it
        let mut b = vec![1u8];
        b.extend(rand_bytes(&mut rng, 32));
        b.push(c);
        b.extend(rand_bytes(&mut rng, 16 * usize::from(c)));
        ev_req(&mut tr, &b);
        ev_req(&mut tr, &b[..34]);
    }
    for t in 0..=255u8 {
        let mut b = vec![t];
        b.extend(rand_bytes(&mut rng, 32));
        b.push(2);
        b.extend(rand_bytes(&mut rng, 32));
        ev_req(&mut tr, &b);
    }
    for _ in 0..200 {
        let n = below(&mut rng, 90) as usize;
        let mut g = rand_bytes(&mut rng, n);
        if n > 0 && below(&mut rng, 2) == 0 {
            g[0] = 1;
        }
        ev_req(&mut tr, &g);
    }
    for a in 0..=255u8 {
        for b in [0u8, 1, 255] {
            ev_req(&mut tr, &[a, b][..if b == 0 { 1 } else { 2 }]);
        }
    }

    // ---- GROUP ----
    let hdr = |off: u64, len: u32, plen: u16, follows: bool| GroupHeader {
        off,
        len,
        plen,
        follows,
    };
    let mut valid_hdrs = Vec::new();
    for _ in 0..40 {
        let h = hdr(
            word(&mut rng),
            (below(&mut rng, u64::from(u32::MAX)) + 1) as u32,
            (below(&mut rng, 1024) * 64) as u16,
            below(&mut rng, 2) == 0,
        );
        valid_hdrs.push(h);
    }
    valid_hdrs.push(hdr(0, 1, 0, false));
    valid_hdrs.push(hdr(u64::MAX, u32::MAX, 65472, true));
    for h in &valid_hdrs {
        ev_gh_enc(&mut tr, h);
        let b = h.encode();
        ev_gh(&mut tr, &b);
        ev_gh(&mut tr, &[b.as_slice(), &[1, 2, 3]].concat());
        for c in 0..GROUP_HDR {
            ev_gh(&mut tr, &b[..c]);
        }
        for m in mutations(&mut rng, &b, &[0, 9, 10, 11, 12, 13, 14, 15]) {
            ev_gh(&mut tr, &m);
        }
    }
    for (len, plen) in [
        (0u32, 0u16),
        (0, 64),
        (1, 1),
        (1, 63),
        (1, 65),
        (7, 65535),
        (u32::MAX, 192),
        (3, 100),
    ] {
        for follows in [false, true] {
            ev_gh_enc(&mut tr, &hdr(rng.next_u64(), len, plen, follows));
        }
    }
    for t in 0..=255u8 {
        let mut b = valid_hdrs[2].encode();
        b[0] = t;
        ev_gh(&mut tr, &b);
    }
    for f in 0..=255u8 {
        let mut b = valid_hdrs[3].encode();
        b[15] = f;
        ev_gh(&mut tr, &b);
    }
    for plen in (0..=65535u32).step_by(509).chain([65472, 65535, 64, 128]) {
        let mut b = valid_hdrs[4].encode();
        b[13..15].copy_from_slice(&(plen as u16).to_be_bytes());
        ev_gh(&mut tr, &b);
    }
    for _ in 0..150 {
        let n = below(&mut rng, 24) as usize;
        let mut g = rand_bytes(&mut rng, n);
        if n > 0 && below(&mut rng, 2) == 0 {
            g[0] = 2;
        }
        ev_gh(&mut tr, &g);
    }

    // ---- PROOF ----
    let proof_lens = [
        0usize,
        64,
        128,
        64 * 16,
        64 * 17,
        1,
        63,
        65,
        1087,
        1089,
        1100,
        1101,
        1152,
        1216,
    ];
    let mut pfs: Vec<Vec<u8>> = Vec::new();
    for i in 0..60 {
        let s = if i < 20 {
            (1u64 << (7 * (i % 9))).saturating_sub(i as u64 % 3)
        } else {
            sid(&mut rng)
        };
        let (glog, start, wn, ln) = (
            rng.next_u64() as u8,
            word(&mut rng),
            rng.next_u64() as u32,
            word(&mut rng),
        );
        let mut head = [0u8; 40];
        let hn = ProofFrame::write_head(s, glog, start, wn, ln, &mut head).unwrap();
        let plen = proof_lens[i % proof_lens.len()];
        if plen > 300 && i % 3 != 0 {
            continue;
        }
        let mut body = head[..hn].to_vec();
        body.extend(rand_bytes(&mut rng, plen));
        pfs.push(body);
        ev_pf_head(&mut tr, s, glog, start, wn, ln, hn);
    }
    for body in &pfs {
        ev_pf(&mut tr, body);
        let sid_len = vinc_wire::varint::decode(body).map_or(1, |(_, n)| n);
        let head_len = sid_len + 21;
        for c in 0..head_len.min(body.len()) {
            ev_pf(&mut tr, &body[..c]);
        }
        if body.len() <= 200 {
            for c in head_len..body.len() {
                ev_pf(&mut tr, &body[..c]);
            }
        }
        if body.len() <= 200 {
            for m in mutations(
                &mut rng,
                body,
                &[0, 1, sid_len - 1, sid_len, sid_len + 1, sid_len + 8, sid_len + 20],
            ) {
                ev_pf(&mut tr, &m);
            }
        }
    }
    for (i, s) in [0u64, 1, 127, 128, 16383, 1 << 62, (1 << 63) - 1, u64::MAX, 1 << 63]
        .into_iter()
        .enumerate()
    {
        for cap in [0usize, 1, 2, 9, 10, 21, 22, 29, 30, 31, 40] {
            ev_pf_head(&mut tr, s, 7 + i as u8, i as u64 * 99, 5, 6, cap);
        }
    }
    for _ in 0..80 {
        let s = sid(&mut rng);
        for cap in 0..=34 {
            if cap % 5 == 0 || cap > 29 {
                ev_pf_head(
                    &mut tr,
                    s,
                    0,
                    word(&mut rng),
                    rng.next_u64() as u32,
                    word(&mut rng),
                    cap,
                );
            }
        }
    }
    // the stream id forms: every broken shape in place, with a valid tail and each proof length
    let tail = rand_bytes(&mut rng, 21);
    let forms: Vec<Vec<u8>> = vec![
        vec![],
        vec![0x80],
        vec![0x80, 0x00],
        vec![0x81, 0x80, 0x00],
        vec![0xff; 9],
        vec![0x80; 9],
        vec![0x80; 8],
        vec![0xff; 8],
        vec![0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00],
        vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f],
        vec![0x00],
        vec![0x7f],
        vec![0x80, 0x01],
        vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f],
    ];
    for f in &forms {
        for plen in [0usize, 64, 65, 1100] {
            ev_pf(&mut tr, &[f.as_slice(), &tail, &rand_bytes(&mut rng, plen)].concat());
        }
        ev_pf(&mut tr, f);
        ev_pf(&mut tr, &[f.as_slice(), &tail[..10]].concat());
    }
    for a in 0..=255u8 {
        for b in [0u8, 1, 128, 255] {
            ev_pf(&mut tr, &[a, b]);
        }
        ev_pf(&mut tr, &[a]);
    }
    for _ in 0..150 {
        let n = below(&mut rng, 60) as usize;
        let g = rand_bytes(&mut rng, n);
        ev_pf(&mut tr, &g);
    }
    for _ in 0..40 {
        let mut g = vec![0x05];
        let extra = 21 + 64 * below(&mut rng, 20) as usize + below(&mut rng, 3) as usize;
        g.extend(rand_bytes(&mut rng, extra));
        ev_pf(&mut tr, &g);
    }

    // ---- PROOF_REQ ----
    let mut prs: Vec<Vec<u8>> = Vec::new();
    for i in 0..60u32 {
        let r = ProofReq {
            sid: if i < 20 {
                (1u64 << (7 * (i % 9))).saturating_sub(u64::from(i % 3))
            } else {
                sid(&mut rng)
            },
            from: word(&mut rng),
            upto: word(&mut rng),
        };
        let mut b = [0u8; 32];
        let n = r.encode(&mut b).unwrap();
        prs.push(b[..n].to_vec());
        for cap in [0usize, 1, 2, 8, 9, 10, n - 1, n, n + 1, 25] {
            ev_pr_enc(&mut tr, &r, cap);
        }
    }
    for s in [1u64 << 63, u64::MAX, (1 << 63) + 5] {
        for cap in [0usize, 5, 25, 40] {
            ev_pr_enc(
                &mut tr,
                &ProofReq {
                    sid: s,
                    from: 1,
                    upto: 2,
                },
                cap,
            );
        }
    }
    for b in &prs {
        ev_pr(&mut tr, b);
        for tail in [&[0u8][..], &[255, 255][..]] {
            ev_pr(&mut tr, &[b.as_slice(), tail].concat());
        }
        for c in 0..b.len() {
            ev_pr(&mut tr, &b[..c]);
        }
        let sid_len = vinc_wire::varint::decode(b).map_or(1, |(_, n)| n);
        for m in mutations(&mut rng, b, &[0, sid_len - 1, sid_len, sid_len + 7, sid_len + 15]) {
            ev_pr(&mut tr, &m);
        }
    }
    let pr_tail = rand_bytes(&mut rng, 16);
    for f in &forms {
        ev_pr(&mut tr, &[f.as_slice(), &pr_tail].concat());
        ev_pr(&mut tr, &[f.as_slice(), &pr_tail, &[0]].concat());
        ev_pr(&mut tr, f);
    }
    for a in 0..=255u8 {
        for b in [0u8, 1, 128, 255] {
            ev_pr(&mut tr, &[a, b]);
            ev_pr(&mut tr, &[a, b, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]);
        }
        ev_pr(&mut tr, &[a]);
    }
    // every class alphabet string of up to 4 bytes as an id, followed by a valid tail
    let alpha = [0u8, 1, 2, 64, 127, 128, 129, 192, 255];
    let mut ids: Vec<Vec<u8>> = vec![vec![]];
    let mut layer: Vec<Vec<u8>> = vec![vec![]];
    for _ in 0..3 {
        layer = layer
            .iter()
            .flat_map(|s| alpha.iter().map(move |&x| [s.as_slice(), &[x]].concat()))
            .collect();
        ids.extend(layer.iter().cloned());
    }
    for a in [0u8, 127, 128, 255] {
        for b in [0u8, 127, 128, 255] {
            for c in [0u8, 127, 128, 255] {
                for d in [0u8, 127, 128, 255] {
                    ids.push(vec![a, b, c, d]);
                }
            }
        }
    }
    for s in &ids {
        ev_pr(&mut tr, &[s.as_slice(), &pr_tail].concat());
        ev_pf(&mut tr, &[s.as_slice(), &tail].concat());
    }
    for _ in 0..150 {
        let n = below(&mut rng, 30) as usize;
        ev_pr(&mut tr, &rand_bytes(&mut rng, n));
    }

    assert!(tr.0.lines().count() > 3000);
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("values_wire.ndjson"), &tr.0).unwrap();
    }
}
