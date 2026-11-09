//! Trace generation for the head and acknowledgement codecs: the real `SignedHead` and `CustodyAck` of every identity
//! algorithm, encoded, mutated and decoded, recorded as ndjson (`dtn_codec.ndjson`) for the TLA+ trace check
//! (`TraceDtnCodec.tla`) and the Lean replay (`Vinc/TraceDtnCodec.lean`).
//!
//! An `enc` event is a valid encoding (a byte array) that must decode and re-encode to itself. The events after it,
//! until the next `enc`, are mutations of that encoding (they name it by `base`, the number of `enc` events before it): `mut` replaces one byte (the first 40 bytes, both identity tags, the
//! endorsement length fields, the last bytes and a stride through the rest, each with three replacement bytes),
//! `trunc` cuts the encoding to `n` bytes (the first and last 70 lengths, a stride and the head end for the short keys, a prefix, edges and a stride for the long ones)
//! and `trail` appends bytes. Each records whether the real decoder accepted the result; the test asserts here that
//! truncations and trailing bytes are rejected, that every accepted mutation re-encodes to exactly the mutated bytes
//! (a byte string has one reading), and that a bad identity tag or a wrong endorsement length is rejected, so it is
//! meaningful without the proof tools. The trace is written to the directory in `VINC_TRACE_DIR` when it is set;
//! otherwise nothing is written.
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

use dtn_common::{ALGS, keypair, make, plan, recipient};
use vinc_crypto::IdentityAlg;
use vinc_dtn::custody::CustodyAck;
use vinc_dtn::head::{BundleId, SignedHead};
use vinc_dtn::hlc::Hlc;

fn array(b: &[u8]) -> String {
    let parts: Vec<String> = b.iter().map(ToString::to_string).collect();
    format!("[{}]", parts.join(","))
}

#[derive(Clone, Copy)]
enum Kind {
    Head,
    Ack,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Self::Head => "head",
            Self::Ack => "ack",
        }
    }

    /// Decode, and when accepted, encode again: the bytes must be the input.
    fn accepts(self, bytes: &[u8]) -> bool {
        match self {
            Self::Head => SignedHead::decode(bytes).is_ok_and(|h| {
                let mut out = vec![0; bytes.len() + 8];
                let n = h.encode(&mut out).unwrap();
                assert_eq!(&out[..n], bytes, "an accepted head re-encodes to its input");
                assert_eq!(n, h.encoded_len());
                true
            }),
            Self::Ack => CustodyAck::decode(bytes).is_ok_and(|a| {
                let mut out = vec![0; bytes.len() + 8];
                let n = a.encode(&mut out).unwrap();
                assert_eq!(&out[..n], bytes, "an accepted ack re-encodes to its input");
                assert_eq!(n, a.encoded_len());
                true
            }),
        }
    }
}

fn alg_len(tag: u8) -> (usize, usize) {
    match tag {
        1 => (32, 64),
        2 => (33, 64),
        3 => (1952, 3309),
        _ => (1984, 3373),
    }
}

fn scan(kind: Kind, alg: IdentityAlg, enc: &[u8], base: usize, out: &mut Vec<String>) {
    let name = kind.name();
    let n = enc.len();
    assert!(kind.accepts(enc), "a valid encoding decodes");
    out.push(format!(
        r#"{{"t":"cx","op":"enc","kind":"{name}","alg":{},"b":{}}}"#,
        alg.tag(),
        array(enc)
    ));
    let (pk, sig) = alg_len(alg.tag());
    let body = if matches!(kind, Kind::Head) { 1287 } else { 118 };
    assert_eq!(n, body + 4 + pk + sig);
    let short = alg.tag() <= 2;
    // truncations
    let mut cuts: Vec<usize> = if short {
        (0..n)
            .filter(|c| *c < 70 || *c + 70 > n || c % 11 == 0 || (body..body + 8).contains(c))
            .collect()
    } else {
        (0..200)
            .chain([n - 1, n - 2, n - 3, n - 60, n / 2])
            .chain(body..body + 8)
            .collect()
    };
    cuts.retain(|&c| c < n);
    cuts.sort_unstable();
    cuts.dedup();
    for c in cuts {
        let ok = kind.accepts(&enc[..c]);
        assert!(!ok, "a proper prefix of {c} bytes is rejected");
        out.push(format!(
            r#"{{"t":"cx","op":"trunc","kind":"{name}","base":{base},"n":{c},"ok":false}}"#
        ));
    }
    for extra in 1..=5usize {
        let mut v = enc.to_vec();
        v.extend((0..extra).map(|i| i as u8 + 9));
        let ok = kind.accepts(&v);
        assert!(!ok, "trailing bytes are rejected");
        out.push(format!(
            r#"{{"t":"cx","op":"trail","kind":"{name}","base":{base},"extra":{extra},"ok":false}}"#
        ));
    }
    // single-byte mutations
    let mut pos: Vec<usize> = (0..40.min(n)).collect();
    let tags = [32, 65];
    pos.extend(tags);
    if matches!(kind, Kind::Ack) {
        // the offer id, after the two nodes
        pos.extend(98..106);
    }
    pos.extend((body..body + 4 + pk + 6).filter(|p| p % 7 == 0 || *p < body + 6));
    pos.extend(n.saturating_sub(5)..n);
    pos.extend((40..n).step_by(if short { 41 } else { 97 }));
    pos.retain(|&p| p < n);
    pos.sort_unstable();
    pos.dedup();
    for p in pos {
        for v in [0u8, 255, enc[p].wrapping_add(1)] {
            let mut m = enc.to_vec();
            m[p] = v;
            let ok = kind.accepts(&m);
            if (p == 32 || p == 65) && !(1..=4).contains(&v) {
                assert!(!ok, "an unknown identity tag is rejected");
            }
            if (body..body + 2).contains(&p) && m[body..body + 2] != enc[body..body + 2] {
                assert!(!ok, "a wrong public key length is rejected");
            }
            out.push(format!(
                r#"{{"t":"cx","op":"mut","kind":"{name}","base":{base},"pos":{p},"val":{v},"ok":{ok}}}"#
            ));
        }
    }
}

#[test]
fn codec_trace() {
    let mut out = vec![];
    let mut bases = 0;
    for (i, &alg) in ALGS.iter().enumerate() {
        let alg_to = ALGS[(i + 1) % ALGS.len()];
        let signer = keypair(alg, 100 + i as u64);
        let to = recipient(alg_to, 200 + i as u64, 7);
        for (j, (k, m, log, len)) in [(1u8, 0u8, 0u8, 1usize), (3, 2, 1, 5000)].into_iter().enumerate() {
            let b = make(
                &signer,
                &to,
                plan(k, m, log),
                &dtn_common::bytes(300 + j as u64, len),
                400 + j as u64,
            );
            let mut enc = vec![0; b.signed.encoded_len()];
            let n = b.signed.encode(&mut enc).unwrap();
            assert_eq!(n, enc.len());
            scan(Kind::Head, alg, &enc, bases, &mut out);
            bases += 1;
        }
        let prev = keypair(alg_to, 500 + i as u64).node_id();
        // The offer id is a signed u64 field: distinct bytes for every algorithm, and the extremes once.
        let mut offers = vec![0x0102_0304_0506_0708 ^ i as u64];
        if i == 0 {
            offers.extend([0, 1, u64::MAX]);
        }
        for offer in offers {
            let ack = CustodyAck::sign(BundleId([9 + i as u8; 32]), prev, offer, Hlc::new(5, 1), &signer).unwrap();
            let mut enc = vec![0; ack.encoded_len()];
            let n = ack.encode(&mut enc).unwrap();
            assert_eq!(n, enc.len());
            scan(Kind::Ack, alg, &enc, bases, &mut out);
            bases += 1;
        }
    }
    assert!(out.len() > 1000);
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            std::path::Path::new(&dir).join("dtn_codec.ndjson"),
            out.join("\n") + "\n",
        )
        .unwrap();
    }
}
