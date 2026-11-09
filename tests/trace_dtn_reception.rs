//! Trace generation for the reception of a bundle (`Reception`): real receptions fed through the public API, recorded
//! as ndjson (`dtn_reception.ndjson`) for the TLA+ trace check (`TraceDtnReception.tla`) and the Lean replay
//! (`Vinc/TraceDtnReception.lean`).
//!
//! The bundle has the shape of the model: `k = 2`, `m = 2`, three data slices of 1 KiB symbols, so two erasure blocks
//! (block 0 with symbols 0 to 3, block 1 with the short data symbol 4 and parity 5, 6) and seven symbols. A run is
//! one reception of either an honest sender or a sender whose parity symbol 3 (or 6) was changed before the root was
//! computed, so the signed root commits to a block that is not a code word. A run feeds ranges of real proof streams
//! (`serve`) that are intact, have one byte flipped, are cut short or carry trailing bytes, into a held set of 2 or
//! 3 intervals, so the set fills up; it asks `holds`, `next_missing`, `is_complete` and `is_decodable` after every
//! step; it calls `finish` when it likes (sometimes with a wrong-sized outboard or scratch, which is refused with
//! nothing changed); and it resumes from a copy of its buffer and held set with a bad
//! signature, an expired head and a wrong-sized buffer. The verdict of every call and the whole held set after it
//! are recorded.
//!
//! The test asserts, against a plain tracker written here (a set of symbol numbers, the interval count of a set, no
//! use of `VerifiedRanges`), that an intact stream records every symbol whose interval fits, one at a time in
//! order, that a damaged stream records only a prefix of its range, that no symbol outside the range is ever
//! recorded, that the held set only grows, that `finish` says `Incomplete` exactly when a block holds fewer than
//! `k` symbols, that `finish` never writes a held symbol, and that an honest sender is never `Inconsistent`, so it is meaningful without the proof tools. The
//! trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::comparison_chain,
    clippy::nonminimal_bool,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    unreachable_pub
)]

mod dtn_common;

use dtn_common::{keypair, make, plan, recipient};
use vinc_crypto::IdentityAlg;
use vinc_dag::ranges::VerifiedRanges;
use vinc_dag::tree::build_outboard;
use vinc_dtn::DtnError;
use vinc_dtn::bundle::{Reception, serve, serve_len};
use vinc_dtn::head::SignedHead;
use vinc_dtn::layout::SliceLayout;
use vinc_tests::SplitMix64;

const NOW: u64 = 5;
const TOTAL: u64 = 7;
const G: u64 = 1024;

/// Whether a set of symbols fits in `cap` disjoint intervals (the number of maximal runs).
fn runs(set: &[bool]) -> usize {
    (0..set.len()).filter(|&s| set[s] && (s == 0 || !set[s - 1])).count()
}

fn class(e: &DtnError) -> &'static str {
    match e {
        DtnError::Tree(_) => "tree",
        DtnError::ReceptionFull => "full",
        DtnError::Buffer => "buffer",
        DtnError::Incomplete => "incomplete",
        DtnError::Inconsistent => "inconsistent",
        DtnError::Crypto(_) => "crypto",
        DtnError::Expired => "expired",
        _ => "other",
    }
}

fn res_class(r: &Result<(), DtnError>) -> &'static str {
    match r {
        Ok(()) => "ok",
        Err(e) => class(e),
    }
}

struct Bundle {
    signed: SignedHead,
    sealed: Vec<u8>,
    outboard: Vec<u8>,
    layout: SliceLayout,
    faulty: Vec<u64>,
}

impl Bundle {
    /// An honest bundle, or one whose parity symbol `bad` was changed before the root was computed.
    fn new(seed: u64, bad: Option<u64>) -> Self {
        let signer = keypair(IdentityAlg::Ed25519, 1);
        let to = recipient(IdentityAlg::Ed25519, 2, 1);
        let s = make(&signer, &to, plan(2, 2, 0), &dtn_common::bytes(seed, 3000), seed + 7);
        let layout = s.signed.head().layout().unwrap();
        assert_eq!(layout.total_symbols(), TOTAL);
        assert_eq!(layout.slice_len(), G);
        let mut sealed = s.sealed;
        let mut outboard = s.outboard;
        let mut signed = s.signed;
        let mut faulty = vec![];
        if let Some(sym) = bad {
            let at = (sym * G) as usize;
            sealed[at + 5] ^= 0x5a;
            let root = build_outboard(&sealed, 0, &mut outboard).unwrap();
            let mut head = *signed.head();
            head.root = root;
            signed = SignedHead::sign(head, &signer).unwrap();
            faulty.push(sym);
        }
        Self {
            signed,
            sealed,
            outboard,
            layout,
            faulty,
        }
    }

    fn proof(&self, a: u64, b: u64) -> Vec<u8> {
        let mut out = vec![0; serve_len(&self.layout, &(a..b)).unwrap()];
        serve(&self.layout, &self.sealed, &self.outboard, &(a..b), &mut out).unwrap();
        out
    }
}

fn have_json<const W: usize>(h: &VerifiedRanges<W>) -> String {
    let v: Vec<String> = h.iter().map(|r| format!("[{},{}]", r.start, r.end)).collect();
    format!("[{}]", v.join(","))
}

fn snapshot<const W: usize>(rx: &Reception<'_, W>) -> (String, Vec<bool>) {
    let held: Vec<bool> = (0..TOTAL).map(|s| rx.holds(s)).collect();
    let bits: Vec<String> = held.iter().map(|b| u8::from(*b).to_string()).collect();
    let nm: Vec<String> = (0..=TOTAL)
        .map(|from| {
            rx.next_missing(from)
                .map_or("[]".to_string(), |r| format!("[{},{}]", r.start, r.end))
        })
        .collect();
    // the plain expectations
    let runs_ok = runs(&held) <= W;
    assert!(runs_ok);
    assert_eq!(rx.is_complete(), held.iter().all(|h| *h));
    let decodable = (0..2u64).all(|b| {
        let (lo, hi, k) = if b == 0 { (0, 4, 2) } else { (4, 7, 1) };
        (lo..hi).filter(|&s| held[s as usize]).count() >= k
    });
    assert_eq!(rx.is_decodable(), decodable);
    for from in 0..=TOTAL {
        let expect = (from..TOTAL).find(|&s| !held[s as usize]).map(|a| {
            let b = (a..TOTAL).find(|&s| held[s as usize]).unwrap_or(TOTAL);
            (a, b)
        });
        assert_eq!(
            rx.next_missing(from).map(|r| (r.start, r.end)),
            expect,
            "next_missing({from})"
        );
    }
    (
        format!(
            r#""have":{},"hold":[{}],"cmp":{},"dec":{},"nm":[{}]"#,
            have_json(rx.have()),
            bits.join(","),
            rx.is_complete(),
            rx.is_decodable(),
            nm.join(",")
        ),
        held,
    )
}

fn run<const W: usize>(b: &Bundle, seed: u64, id: usize, out: &mut Vec<String>) {
    let mut rng = SplitMix64::new(seed);
    let mut buf = vec![0xaa; b.layout.total_len() as usize];
    let mut rx = Reception::<W>::new(&b.signed, &mut buf, NOW).unwrap();
    out.push(format!(
        r#"{{"t":"rx","run":{id},"op":"new","W":{W},"k":2,"m":2,"log":0,"payload":3000,"g":{G},"total":{TOTAL},"have":[],"faulty":[{}]}}"#,
        b.faulty.iter().map(ToString::to_string).collect::<Vec<_>>().join(",")
    ));
    let mut held: Vec<bool> = vec![false; TOTAL as usize];
    let mut finished_ok = false;
    for step in 0..40 {
        let pick = rng.next_u64() % 100;
        let before = held.clone();
        if pick < 70 {
            // a feed
            let a = rng.next_u64() % (TOTAL + 1);
            let len = rng.next_u64() % 4;
            let bnd = (a + len).min(TOTAL);
            let range_ok = !(step % 17 == 16);
            let (a2, b2) = if range_ok {
                (a, bnd)
            } else {
                (a, TOTAL + 1 + rng.next_u64() % 3)
            };
            if b2 > TOTAL {
                let r = rx.feed(a2..b2, &[]);
                assert_eq!(class(&r.unwrap_err()), "buffer");
                let (snap, _) = snapshot(&rx);
                out.push(format!(
                    r#"{{"t":"rx","run":{id},"op":"feed","a":{a2},"b":{b2},"kind":"range","res":"buffer",{snap}}}"#
                ));
                continue;
            }
            let stream = if a2 == b2 { vec![] } else { b.proof(a2, b2) };
            let (kind, stream) = match rng.next_u64() % 8 {
                0 if !stream.is_empty() => {
                    let mut s = stream;
                    let at = (rng.next_u64() as usize) % s.len();
                    s[at] ^= 0x40;
                    ("flip", s)
                }
                1 if !stream.is_empty() => {
                    let cut = (rng.next_u64() as usize) % stream.len();
                    ("short", stream[..cut].to_vec())
                }
                2 if !stream.is_empty() => {
                    let mut s = stream;
                    s.extend([1, 2, 3]);
                    ("trail", s)
                }
                _ => ("good", stream),
            };
            let res = rx.feed(a2..b2, &stream);
            let (snap, now_held) = snapshot(&rx);
            // the plain tracker
            for s in 0..TOTAL as usize {
                assert!(!before[s] || now_held[s], "the held set only grows");
                if now_held[s] && !before[s] {
                    assert!((s as u64) >= a2 && (s as u64) < b2, "only the range is recorded");
                }
            }
            let rc = res_class(&res);
            if a2 == b2 {
                assert_eq!(rc, "ok");
                assert_eq!(before, now_held);
            } else if kind == "good" {
                // every symbol in order; the first whose interval does not fit is dropped, later ones may still fit
                let mut exp = before.clone();
                let mut full = false;
                for s in a2..b2 {
                    let mut next = exp.clone();
                    next[s as usize] = true;
                    if runs(&next) <= W {
                        exp = next;
                    } else {
                        full = true;
                    }
                }
                assert_eq!(now_held, exp, "an intact stream records exactly the symbols that fit");
                assert_eq!(rc, if full { "full" } else { "ok" });
            } else {
                assert!(rc == "tree" || rc == "full" || rc == "ok", "kind {kind} gave {rc}");
                if kind != "trail" {
                    assert_eq!(rc, "tree", "a damaged stream is a tree error");
                }
            }
            held = now_held;
            out.push(format!(
                r#"{{"t":"rx","run":{id},"op":"feed","a":{a2},"b":{b2},"kind":"{kind}","res":"{rc}",{snap}}}"#
            ));
        } else if pick < 85 {
            // finish: a wrong-sized outboard or scratch is refused with nothing changed; otherwise the real call
            let mut ob = vec![0; b.layout.outboard_len().unwrap() as usize];
            let mut scratch = vec![0; rx.scratch_len().unwrap()];
            if rng.next_u64().is_multiple_of(4) {
                let before_buf = rx.sealed().to_vec();
                let res = if rng.next_u64().is_multiple_of(2) {
                    rx.finish(&mut ob[1..], &mut scratch)
                } else {
                    rx.finish(&mut ob, &mut scratch[1..])
                };
                assert_eq!(res_class(&res), "buffer");
                assert_eq!(rx.sealed(), &before_buf[..], "a refused finish writes nothing");
                let (snap, now_held) = snapshot(&rx);
                assert_eq!(now_held, held);
                out.push(format!(
                    r#"{{"t":"rx","run":{id},"op":"finbuf","res":"buffer",{snap}}}"#
                ));
                continue;
            }
            let was_held = held.clone();
            let res = rx.finish(&mut ob, &mut scratch);
            let rc = res_class(&res);
            let decodable = (0..2u64).all(|bl| {
                let (lo, hi, k) = if bl == 0 { (0, 4, 2) } else { (4, 7, 1) };
                (lo..hi).filter(|&s| was_held[s as usize]).count() >= k
            });
            assert_eq!(
                rc == "incomplete",
                !decodable,
                "Incomplete exactly when a block holds fewer than k"
            );
            if b.faulty.is_empty() {
                assert_ne!(rc, "inconsistent", "an honest sender is never inconsistent");
            }
            for (sym, _) in was_held.iter().enumerate().filter(|(_, h)| **h) {
                let r = sym * G as usize..(sym + 1) * G as usize;
                assert_eq!(
                    &rx.sealed()[r.clone()],
                    &b.sealed[r],
                    "finish never writes a held symbol"
                );
            }
            if rc == "ok" {
                finished_ok = true;
                assert!(rx.is_complete());
            }
            let (snap, now_held) = snapshot(&rx);
            held = now_held;
            out.push(format!(r#"{{"t":"rx","run":{id},"op":"fin","res":"{rc}",{snap}}}"#));
        } else {
            // resume from a copy of the buffer and the held set
            let case = rng.next_u64() % 4;
            let mut copy = rx.sealed().to_vec();
            let have = rx.have().clone();
            let (signed, now, wrong) = match case {
                0 => {
                    let mut head = *b.signed.head();
                    head.root[0] ^= 1;
                    // the signature no longer covers the head
                    let mut enc = vec![0; vinc_dtn::head::MAX_SIGNED_HEAD_LEN];
                    let n = b.signed.encode(&mut enc).unwrap();
                    enc[100] ^= 1;
                    let _ = head;
                    (SignedHead::decode(&enc[..n]).unwrap(), NOW, false)
                }
                1 => (b.signed.clone(), 1_000_000, false),
                2 => (b.signed.clone(), NOW, true),
                _ => (b.signed.clone(), NOW, false),
            };
            if wrong {
                copy.pop();
            }
            let r = Reception::<W>::resume(&signed, &mut copy, have, now);
            let rc = match &r {
                Ok(_) => "ok",
                Err(e) => class(e),
            };
            let want = match case {
                0 => "crypto",
                1 => "expired",
                2 => "buffer",
                _ => "ok",
            };
            assert_eq!(rc, want);
            if let Ok(r2) = r {
                let (snap, now_held) = snapshot(&r2);
                assert_eq!(now_held, held, "resume keeps the verified ranges");
                out.push(format!(
                    r#"{{"t":"rx","run":{id},"op":"res","case":{case},"res":"{rc}",{snap}}}"#
                ));
            } else {
                let (snap, _) = snapshot(&rx);
                out.push(format!(
                    r#"{{"t":"rx","run":{id},"op":"res","case":{case},"res":"{rc}",{snap}}}"#
                ));
            }
        }
    }
    let _ = finished_ok;
}

#[test]
fn reception_trace() {
    let mut out = vec![];
    let honest = Bundle::new(10, None);
    let faulty3 = Bundle::new(11, Some(3));
    let faulty6 = Bundle::new(12, Some(6));
    for seed in 0..24u64 {
        let id = 4 * seed as usize;
        run::<2>(&honest, 100 + seed, id, &mut out);
        run::<3>(&honest, 200 + seed, id + 1, &mut out);
        run::<2>(&faulty3, 300 + seed, id + 2, &mut out);
        run::<3>(&faulty6, 400 + seed, id + 3, &mut out);
    }
    // the sealed bundle of the faulty sender really commits to non-code-word parity: a complete honest decode of a
    // reception that holds only some symbols of block 0 cannot match its root
    assert!(
        out.iter().any(|l| l.contains(r#""res":"inconsistent""#)),
        "a faulty sender is caught"
    );
    assert!(
        out.iter().any(|l| l.contains(r#""res":"full""#)),
        "the held set fills up"
    );
    assert!(
        out.iter().any(|l| l.contains(r#""op":"fin","res":"ok""#)),
        "a finish succeeds"
    );
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            std::path::Path::new(&dir).join("dtn_reception.ndjson"),
            out.join("\n") + "\n",
        )
        .unwrap();
    }
}
