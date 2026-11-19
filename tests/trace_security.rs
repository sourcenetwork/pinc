//! Trace generation for the pure parts of the security layer: the labels, the credit record, the anti-amplification
//! budget and the padding sizes, driven through the public API and recorded as ndjson (`security.ndjson`) for the
//! TLA+ trace checks (`TraceLabels`, `TraceCredit`, `TraceAmp`, `TracePadding`) and the Lean replay.
//!
//! * `lbl`: every label of `labels::ALL`, the prefix and the labels of `pinc-crypto`, as strings.
//! * `cred`: `CreditRecord::new` (the window request as four 16-bit limbs, since it is a `u64`) with the record it
//!   builds, its `window_bytes` and its 6 bytes; `decode` of random 6-byte strings with the re-encoded bytes; and
//!   `covers` of pairs of records. Every result is also asserted here against an independent computation.
//! * `amp`: one `on_receive`, `on_send`, `validate` or `can_send` of an `AmpBudget`, with the counters after it (as
//!   limbs). A send is recorded only when the sender kept the discipline, or in a run that exercises saturation.
//! * `pad`: `min_initial_len`, `reply_len` and `reply_datagrams` for every identity algorithm and both Initial forms,
//!   with the key and signature lengths of the algorithm, and the public size constants with the connection id lengths
//!   of the transport's default and of the endpoint.
//!
//! The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use std::fmt::Write as _;

use pinc_crypto::provider::KEM_CIPHERTEXT_LEN;
use pinc_crypto::{Aead, IdentityAlg};
use pinc_security::AmpBudget;
use pinc_security::amp::{FACTOR, OVERHEAD};
use pinc_security::credit::{CREDIT_RECORD_LEN, CreditRecord, WINDOW_UNIT};
use pinc_security::ids::MAX_CID_LEN;
use pinc_security::labels;
use pinc_security::message::{
    FRAGMENT_HEADER, FULL_INITIAL_MIN, InitialForm, MAX_ID_SIG_LEN, MAX_MESSAGE_LEN, MAX_SEALED_LEN, MIN_DATAGRAM,
    SHORT_INITIAL_MIN, SPLIT_CID_MAX, WHOLE_REPLY_MAX, min_initial_len, reply_datagrams, reply_len,
};
use pinc_tests::SplitMix64;

/// A `u64` as the four 16-bit limbs the TLA+ `U64` module reads, least significant first.
fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn bytes(b: &[u8]) -> String {
    format!("[{}]", b.iter().map(u8::to_string).collect::<Vec<_>>().join(","))
}

fn labels_trace(out: &mut String) {
    let all = labels::ALL
        .iter()
        .map(|l| format!("\"{l}\""))
        .collect::<Vec<_>>()
        .join(",");
    let _ = writeln!(
        out,
        r#"{{"t":"lbl","prefix":"{}","all":[{all}],"crypto":["{}","{}"]}}"#,
        labels::PREFIX,
        pinc_crypto::labels::NODE_ID,
        pinc_crypto::labels::HYBRID_SIGNATURE
    );
    // the facts the model proves, asserted on the real constants
    assert_eq!(labels::ALL.len(), 23);
    for (i, a) in labels::ALL.iter().enumerate() {
        assert!(a.starts_with(labels::PREFIX) && a.len() > labels::PREFIX.len() && a.is_ascii());
        assert!(!labels::ALL[..i].contains(a), "label {a} repeats");
        assert!(*a != pinc_crypto::labels::NODE_ID && *a != pinc_crypto::labels::HYBRID_SIGNATURE);
    }
    assert_eq!(labels::SIGNATURE_RESPONDER.len(), labels::SIGNATURE_INITIATOR.len());
}

fn rec(r: CreditRecord) -> String {
    format!("[{},{},{}]", r.window_units, r.max_streams, r.max_datagram)
}

fn credit_trace(out: &mut String) {
    let mut rng = SplitMix64::traced(0x5EC0_C0DE);
    let unit = WINDOW_UNIT;
    let max_units = u64::from(u16::MAX);
    // window requests: edges around the unit, the saturation point and u64::MAX, then random sizes of every magnitude
    let mut windows: Vec<u64> = vec![
        0,
        1,
        unit - 1,
        unit,
        unit + 1,
        2 * unit - 1,
        max_units * unit - 1,
        max_units * unit,
        max_units * unit + 1,
        max_units * unit + unit - 1,
        (max_units + 1) * unit - 1,
        (max_units + 1) * unit,
        (max_units + 1) * unit + 1,
        1 << 30,
        (1 << 32) - 1,
        1 << 32,
        1 << 40,
        u64::MAX - unit,
        u64::MAX - 1,
        u64::MAX,
    ];
    for _ in 0..200 {
        let v = rng.next_u64();
        windows.push(v >> (rng.next_u64() % 64));
    }
    let edge16: [u16; 6] = [0, 1, 255, 256, 0x7fff, u16::MAX];
    let mut news = 0u32;
    for (i, &w) in windows.iter().enumerate() {
        let s = if i % 3 == 0 {
            edge16[(rng.next_u64() % 6) as usize]
        } else {
            rng.next_u64() as u16
        };
        let d = if i % 4 == 0 {
            edge16[(rng.next_u64() % 6) as usize]
        } else {
            rng.next_u64() as u16
        };
        let r = CreditRecord::new(w, s, d);
        let units = (w / unit).min(max_units) as u16;
        assert_eq!((r.window_units, r.max_streams, r.max_datagram), (units, s, d));
        assert!(r.window_bytes() <= w && r.window_bytes() == u64::from(units) * unit && r.window_bytes() < 1 << 30);
        assert!(w < r.window_bytes() + unit || r.window_units == u16::MAX);
        let enc = r.encode();
        assert_eq!(enc.len(), CREDIT_RECORD_LEN);
        assert_eq!(CreditRecord::decode(&enc), r);
        assert_eq!(
            enc,
            [
                (units >> 8) as u8,
                units as u8,
                (s >> 8) as u8,
                s as u8,
                (d >> 8) as u8,
                d as u8
            ]
        );
        let _ = writeln!(
            out,
            r#"{{"t":"cred","op":"new","w":{},"s":{s},"d":{d},"rec":{},"wb":{},"enc":{}}}"#,
            limbs(w),
            rec(r),
            r.window_bytes(),
            bytes(&enc)
        );
        news += 1;
    }
    assert!(news > 200);
    // every 6-byte string decodes to one record that re-encodes to the same bytes
    let mut b = [0u8; 6];
    let mut strings: Vec<[u8; 6]> = vec![
        [0; 6],
        [255; 6],
        [0, 1, 0, 2, 0, 3],
        [1, 0, 2, 0, 3, 0],
        [128, 0, 0, 0, 0, 1],
    ];
    for _ in 0..200 {
        rng.fill(&mut b);
        strings.push(b);
    }
    for b in &strings {
        let r = CreditRecord::decode(b);
        assert_eq!(r.encode(), *b);
        let _ = writeln!(
            out,
            r#"{{"t":"cred","op":"dec","b":{},"rec":{},"enc":{}}}"#,
            bytes(b),
            rec(r),
            bytes(&r.encode())
        );
    }
    // covers: random pairs, equal pairs, NONE, and pairs built to cover or to differ in exactly one limit
    let pick = |rng: &mut SplitMix64| {
        let mut f = |m: u64| match rng.next_u64() % 4 {
            0 => 0,
            1 => u16::MAX,
            _ => (rng.next_u64() % m) as u16,
        };
        CreditRecord {
            window_units: f(70000),
            max_streams: f(70000),
            max_datagram: f(70000),
        }
    };
    let mut pairs: Vec<(CreditRecord, CreditRecord)> = vec![(CreditRecord::NONE, CreditRecord::NONE)];
    for _ in 0..300 {
        let a = pick(&mut rng);
        let b = pick(&mut rng);
        pairs.push((a, b));
        pairs.push((a, a));
        pairs.push((CreditRecord::NONE, a));
        pairs.push((a, CreditRecord::NONE));
        let up = CreditRecord {
            window_units: a.window_units.saturating_add((rng.next_u64() % 3) as u16),
            max_streams: a.max_streams.saturating_add((rng.next_u64() % 3) as u16),
            max_datagram: a.max_datagram.saturating_add((rng.next_u64() % 3) as u16),
        };
        pairs.push((up, a));
        pairs.push((a, up));
    }
    let (mut yes, mut no) = (0, 0);
    for (a, b) in &pairs {
        let ok = a.covers(b);
        assert_eq!(
            ok,
            a.window_units >= b.window_units && a.max_streams >= b.max_streams && a.max_datagram >= b.max_datagram
        );
        assert!(a.covers(a) && a.covers(&CreditRecord::NONE));
        if a.covers(b) && b.covers(a) {
            assert_eq!(a, b);
        }
        if CreditRecord::NONE.covers(b) {
            assert_eq!(*b, CreditRecord::NONE);
        }
        if ok {
            yes += 1;
        } else {
            no += 1;
        }
        let _ = writeln!(
            out,
            r#"{{"t":"cred","op":"cov","a":{},"b":{},"ok":{ok}}}"#,
            rec(*a),
            rec(*b)
        );
    }
    assert!(yes > 100 && no > 100, "covers verdicts: {yes} yes, {no} no");
}

fn amp_trace(out: &mut String) {
    let mut rng = SplitMix64::traced(0x5EC0_0001);
    for r in 0..40u32 {
        let mut b = AmpBudget::new();
        let big = r % 4 == 3;
        for seq in 0..120u32 {
            let n = if big && rng.next_u64().is_multiple_of(3) {
                u64::MAX - rng.next_u64() % 100
            } else {
                rng.next_u64() % 4000
            };
            let mut op = match rng.next_u64() % 8 {
                0 | 1 => "rx",
                2..=4 => "tx",
                6 if rng.next_u64().is_multiple_of(4) => "val",
                _ => "can",
            };
            // a send is recorded only when the sender kept the discipline (or the run exercises saturation)
            if op == "tx" && !(b.can_send(n) || big) {
                op = "can";
            }
            let mut can = false;
            match op {
                "rx" => b.on_receive(n),
                "tx" => b.on_send(n),
                "val" => b.validate(),
                _ => can = b.can_send(n),
            }
            if !big && !b.is_validated() {
                assert!(b.sent() <= FACTOR * b.received(), "amplification bound broken");
            }
            let _ = writeln!(
                out,
                r#"{{"t":"amp","run":{},"seq":{seq},"op":"{op}","n":{},"can":{can},"rx":{},"tx":{},"valid":{}}}"#,
                r + 1,
                limbs(n),
                limbs(b.received()),
                limbs(b.sent()),
                b.is_validated()
            );
        }
    }
}

const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

fn pad_trace(out: &mut String) {
    for alg in ALGS {
        let reply = reply_len(alg);
        for (name, form, floor) in [
            ("full", InitialForm::Full, FULL_INITIAL_MIN),
            ("short", InitialForm::Short, SHORT_INITIAL_MIN),
        ] {
            let min = min_initial_len(form, alg);
            let datagrams = reply_datagrams(reply);
            assert!(min >= floor);
            assert!(
                3 * min >= reply + datagrams * (OVERHEAD + FRAGMENT_HEADER),
                "{name} {alg:?}: the budget does not cover the Reply"
            );
            assert!(reply <= MAX_MESSAGE_LEN);
            let _ = writeln!(
                out,
                r#"{{"t":"pad","op":"min","form":"{name}","alg":{},"pk":{},"sig":{},"reply":{reply},"dgs":{datagrams},"min":{min}}}"#,
                alg.tag(),
                alg.public_key_len(),
                alg.signature_len()
            );
        }
        let sealed = 1 + 2 + alg.public_key_len() + 2 + alg.signature_len() + CREDIT_RECORD_LEN + Aead::TAG_LEN;
        assert!(sealed <= MAX_SEALED_LEN);
    }
    assert_eq!(min_initial_len(InitialForm::Short, IdentityAlg::Ed25519), 464);
    assert_eq!(MAX_MESSAGE_LEN, reply_len(IdentityAlg::Hybrid));
    let _ = writeln!(
        out,
        r#"{{"t":"pad","op":"const","full":{FULL_INITIAL_MIN},"short":{SHORT_INITIAL_MIN},"dg":{MIN_DATAGRAM},"frag":{FRAGMENT_HEADER},"whole":{WHOLE_REPLY_MAX},"splitcid":{SPLIT_CID_MAX},"txcid":{},"epcid":{},"idsig":{MAX_ID_SIG_LEN},"sealed":{MAX_SEALED_LEN},"msg":{MAX_MESSAGE_LEN},"overhead":{OVERHEAD},"factor":{FACTOR},"maxpk":{},"maxsig":{},"kemct":{KEM_CIPHERTEXT_LEN},"tag":{},"credit":{CREDIT_RECORD_LEN},"cid":{MAX_CID_LEN}}}"#,
        pinc_transport::conn::Config::new().cid_len,
        pinc_core::CID_LEN,
        pinc_crypto::identity::MAX_PUBLIC_KEY_LEN,
        pinc_crypto::identity::MAX_SIGNATURE_LEN,
        Aead::TAG_LEN
    );
}

#[test]
fn security_traces() {
    let mut out = String::new();
    labels_trace(&mut out);
    credit_trace(&mut out);
    amp_trace(&mut out);
    pad_trace(&mut out);
    for needle in [
        r#""t":"lbl""#,
        r#""op":"new""#,
        r#""op":"dec""#,
        r#""op":"cov""#,
        r#""t":"amp""#,
        r#""op":"min""#,
        r#""op":"const""#,
        r#""op":"tx""#,
        r#""op":"can","n""#,
    ] {
        assert!(
            pinc_tests::soaking() || out.contains(needle),
            "the runs never produce {needle}"
        );
    }
    assert!(out.contains(r#""can":true"#) && out.contains(r#""can":false"#));
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("security.ndjson"), out).unwrap();
}
