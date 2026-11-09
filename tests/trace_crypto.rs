//! Trace generation for `vinc-crypto`: the KDF, node ids and identities, the DRBG, the provider and the secrets,
//! driven through the public API and recorded as ndjson (`crypto.ndjson`) for the TLA+ trace check
//! (`TraceCrypto.tla`) and the Lean replay (`Vinc.TraceCrypto`).
//!
//! Every event is `{"t":"cr","op":...}`. The checkers recompute each answer with the proved model from the recorded
//! inputs, and take the answers of the primitives from the event, where the test computed them by calling the
//! primitive library directly (the oracle):
//! * `lbl`: the label constants of the workspace that reach the BLAKE3 `derive_key` primitive.
//! * `expand`, `extract`: the output of `kdf` with the oracle's input and output (`blake3` called directly).
//! * `alg`, `tags`: the tag, key, signature and seed lengths and `from_tag` for every byte.
//! * `nid`, `match`, `kpid`: `NodeId::from_public`, `matches` and `Keypair::node_id`, with the derive-key oracle.
//! * `ver`, `mlv`, `vnode`: `verify`, `verify_ml_dsa_65` and `verify_node` on genuine and mutated inputs, with the
//!   verdicts of the signature libraries (key parses, signature parses, low `s`, equation holds) called directly.
//! * `kp`, `pubout`, `signout`: key pair construction from seeds and the output buffer rules.
//! * `drbg`: runs of fills and reseeds against the `ChaCha20` stream called directly, and the `MAX_FILL` boundary.
//! * `key`, `aead`, `hpc`, `hpa`, `dh`, `kemkey`, `kemct`: the provider's length checks, the AEAD wrappers, the
//!   header protection mask against the stream and block cipher called directly (and the RFC 9001 vectors), the
//!   X25519 low-order points and the ML-KEM parsers.
//! * `cteq`, `drop`: `ct_eq` and `Secret` comparison, and the bytes of a `Secret` after it is dropped.
//!
//! The trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    unsafe_code,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names
)]

use std::fmt::Write as _;
use std::mem::MaybeUninit;

use aes::Aes128;
use aes::cipher::{BlockCipherEncrypt, KeyInit};
use chacha20::ChaCha20;
use chacha20::cipher::{KeyIvInit, StreamCipher, StreamCipherSeek};
use p256::ecdsa::signature::Verifier as _;
use vinc_crypto::drbg::MAX_FILL;
use vinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN, verify, verify_ml_dsa_65, verify_node};
use vinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use vinc_crypto::{
    Aead, CryptoError, Drbg, IdentityAlg, Keypair, NodeId, Provider, Secret, Software, ct_eq, expand, extract, labels,
};
use vinc_tests::SplitMix64;

const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

/// The order of the P-256 group, big-endian.
const N: [u8; 32] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xBC, 0xE6, 0xFA,
    0xAD, 0xA7, 0x17, 0x9E, 0x84, 0xF3, 0xB9, 0xCA, 0xC2, 0xFC, 0x63, 0x25, 0x51,
];

fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

fn arr(b: &[u8]) -> String {
    format!("[{}]", b.iter().map(u8::to_string).collect::<Vec<_>>().join(","))
}

fn strs(l: &[&str]) -> String {
    format!("[{}]", l.iter().map(|s| format!("\"{s}\"")).collect::<Vec<_>>().join(","))
}

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn flags(f: [bool; 4]) -> String {
    format!("[{},{},{},{}]", f[0], f[1], f[2], f[3])
}

fn res<T>(r: &Result<T, CryptoError>) -> String {
    match r {
        Ok(_) => "ok".into(),
        Err(e) => format!("{e:?}"),
    }
}

fn rand(rng: &mut SplitMix64, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    rng.fill(&mut v);
    v
}

/// `n - s` for a 32-byte big-endian `s` below `n`.
fn negate(s: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut borrow = 0u8;
    for i in (0..32).rev() {
        let (d, b1) = N[i].overflowing_sub(s[i]);
        let (d, b2) = d.overflowing_sub(borrow);
        out[i] = d;
        borrow = u8::from(b1 || b2);
    }
    out
}

/// `n + delta` (delta -1, 0, 1) as 32 big-endian bytes.
fn n_plus(delta: i8) -> [u8; 32] {
    let mut v = N;
    if delta > 0 {
        for b in v.iter_mut().rev() {
            let (x, c) = b.overflowing_add(1);
            *b = x;
            if !c {
                break;
            }
        }
    } else if delta < 0 {
        for b in v.iter_mut().rev() {
            let (x, c) = b.overflowing_sub(1);
            *b = x;
            if !c {
                break;
            }
        }
    }
    v
}

// ---------------------------------------------------------------------------------------------------------------
// labels and the KDF

fn labels_trace(out: &mut String) {
    let all: Vec<&str> = vinc_security::labels::ALL.to_vec();
    let dtn: Vec<&str> = vinc_dtn::labels::ALL.to_vec();
    let crypto = [labels::NODE_ID, labels::HYBRID_SIGNATURE];
    assert_eq!(labels::ALL, crypto);
    let mut every: Vec<&str> = all.iter().chain(crypto.iter()).chain(dtn.iter()).copied().collect();
    assert_eq!(every.len(), 31);
    assert!(every.iter().all(|l| l.starts_with(labels::PREFIX) && l.len() > labels::PREFIX.len() && l.is_ascii()));
    every.sort_unstable();
    every.dedup();
    assert_eq!(every.len(), 31, "a label repeats");
    let _ = writeln!(
        out,
        r#"{{"t":"cr","op":"lbl","prefix":"{}","sec":{},"crypto":{},"dtn":{}}}"#,
        labels::PREFIX,
        strs(&all),
        strs(&crypto),
        strs(&dtn)
    );
}

fn kdf_trace(out: &mut String) {
    let mut rng = SplitMix64::new(0xC0DE_0001);
    let label_set = [
        vinc_security::labels::PACKET_KEY,
        vinc_security::labels::PACKET_IV,
        vinc_security::labels::HEADER_KEY,
        vinc_dtn::labels::SLICE_KEY,
    ];
    for label in label_set {
        for ctx_len in [0usize, 1, 32, 33, 100] {
            let prk: [u8; 32] = rand(&mut rng, 32).try_into().unwrap();
            let ctx = rand(&mut rng, ctx_len);
            let mut mat = prk.to_vec();
            mat.extend_from_slice(&ctx);
            let orc32 = blake3::derive_key(label, &mat);
            for n in [0usize, 1, 16, 31, 32, 33, 64, 65, 100] {
                let mut got = vec![0u8; n];
                expand(&prk, label, &ctx, &mut got);
                let mut orc = vec![0u8; n];
                blake3::Hasher::new_derive_key(label)
                    .update(&mat)
                    .finalize_xof()
                    .fill(&mut orc);
                assert_eq!(got, orc);
                assert_eq!(got[..n.min(32)], orc32[..n.min(32)]);
                let _ = writeln!(
                    out,
                    r#"{{"t":"cr","op":"expand","label":"{label}","prk":{},"ctx":{},"n":{n},"out":{},"orc_in":{},"orc":{},"orc32":{}}}"#,
                    arr(&prk),
                    arr(&ctx),
                    arr(&got),
                    arr(&mat),
                    arr(&orc),
                    arr(&orc32)
                );
            }
        }
    }
    for ikm_len in [0usize, 1, 32, 100] {
        let salt: [u8; 32] = rand(&mut rng, 32).try_into().unwrap();
        let ikm = rand(&mut rng, ikm_len);
        let got = extract(&salt, &ikm);
        let orc = *blake3::keyed_hash(&salt, &ikm).as_bytes();
        assert_eq!(got, orc);
        let _ = writeln!(
            out,
            r#"{{"t":"cr","op":"extract","salt":{},"ikm":{},"out":{},"orc_key":{},"orc_in":{},"orc":{}}}"#,
            arr(&salt),
            arr(&ikm),
            arr(&got),
            arr(&salt),
            arr(&ikm),
            arr(&orc)
        );
    }
}

// ---------------------------------------------------------------------------------------------------------------
// identities

fn alg_trace(out: &mut String) {
    let tags: Vec<u8> = (0..=255u8)
        .map(|t| IdentityAlg::from_tag(t).map_or(0, IdentityAlg::tag))
        .collect();
    let _ = writeln!(out, r#"{{"t":"cr","op":"tags","res":{}}}"#, arr(&tags));
    for alg in ALGS {
        assert_eq!(IdentityAlg::from_tag(alg.tag()), Some(alg));
        let _ = writeln!(
            out,
            r#"{{"t":"cr","op":"alg","alg":{},"pk":{},"sig":{},"seed":{},"maxpk":{MAX_PUBLIC_KEY_LEN},"maxsig":{MAX_SIGNATURE_LEN}}}"#,
            alg.tag(),
            alg.public_key_len(),
            alg.signature_len(),
            alg.seed_len()
        );
    }
}

fn keypair(alg: IdentityAlg, seed: u64) -> Keypair {
    let mut rng = SplitMix64::new(seed);
    Keypair::from_seed(alg, &rand(&mut rng, alg.seed_len())).unwrap()
}

fn public(kp: &Keypair) -> Vec<u8> {
    let mut pk = vec![0u8; kp.alg().public_key_len()];
    kp.public_key(&mut pk).unwrap();
    pk
}

fn sign(kp: &Keypair, msg: &[u8]) -> Vec<u8> {
    let mut sig = vec![0u8; kp.alg().signature_len()];
    kp.sign(msg, &mut sig).unwrap();
    sig
}

/// The derive-key oracle for a node id: `Some` for an algorithm other than Ed25519 and a key of the right length.
fn nid_oracle(alg: IdentityAlg, pk: &[u8]) -> Option<([u8; 32], Vec<u8>)> {
    (alg != IdentityAlg::Ed25519 && pk.len() == alg.public_key_len()).then(|| {
        let mut m = vec![alg.tag()];
        m.extend_from_slice(pk);
        (blake3::derive_key(labels::NODE_ID, &m), m)
    })
}

/// The oracle's output and the input it was computed on (both empty when there is no oracle).
fn orc_json(o: Option<([u8; 32], Vec<u8>)>) -> String {
    o.map_or(r#""orc":[],"orc_in":[]"#.into(), |(b, m)| format!(r#""orc":{},"orc_in":{}"#, arr(&b), arr(&m)))
}

fn id_json(id: &NodeId) -> String {
    format!(r#"{{"alg":{},"bytes":{}}}"#, id.alg.tag(), arr(&id.bytes))
}

fn nid_trace(out: &mut String) {
    for (i, alg) in ALGS.into_iter().enumerate() {
        let kp = keypair(alg, 100 + i as u64);
        let pk = public(&kp);
        let mut cases = vec![pk.clone(), pk[..pk.len() - 1].to_vec(), vec![], pk[..1].to_vec()];
        let mut longer = pk.clone();
        longer.push(7);
        cases.push(longer);
        let mut flipped = pk.clone();
        flipped[pk.len() / 2] ^= 1;
        cases.push(flipped);
        for c in cases {
            let r = NodeId::from_public(alg, &c);
            let rj = match &r {
                Ok(id) => format!(r#"{{"ok":{}}}"#, arr(&id.bytes)),
                Err(e) => format!(r#"{{"err":"{e:?}"}}"#),
            };
            let _ = writeln!(
                out,
                r#"{{"t":"cr","op":"nid","alg":{},"pk":{},{},"res":{rj}}}"#,
                alg.tag(),
                arr(&c),
                orc_json(nid_oracle(alg, &c))
            );
        }
        let id = kp.node_id();
        assert_eq!(id, NodeId::from_public(alg, &pk).unwrap());
        let _ = writeln!(
            out,
            r#"{{"t":"cr","op":"kpid","alg":{},"pk":{},{},"id":{}}}"#,
            alg.tag(),
            arr(&pk),
            orc_json(nid_oracle(alg, &pk)),
            arr(&id.bytes)
        );
        // matches: the genuine id, a changed byte, another algorithm, another key, a wrong length
        let mut bad_bytes = id;
        bad_bytes.bytes[31] ^= 0x80;
        let other_alg = ALGS[(i + 1) % 4];
        let mut other_key = pk.clone();
        other_key[0] ^= 2;
        let mut as_other = id;
        as_other.alg = other_alg;
        let probes: Vec<(NodeId, IdentityAlg, Vec<u8>)> = vec![
            (id, alg, pk.clone()),
            (bad_bytes, alg, pk.clone()),
            (id, other_alg, pk.clone()),
            (as_other, alg, pk.clone()),
            (id, alg, other_key),
            (id, alg, pk[..pk.len() - 1].to_vec()),
        ];
        for (id, a, k) in probes {
            let _ = writeln!(
                out,
                r#"{{"t":"cr","op":"match","id":{},"alg":{},"pk":{},{},"res":{}}}"#,
                id_json(&id),
                a.tag(),
                arr(&k),
                orc_json(nid_oracle(a, &k)),
                id.matches(a, &k)
            );
        }
    }
}

/// The verdicts of the signature libraries on one (key, message, signature).
fn ed_flags(pk: &[u8], msg: &[u8], sig: &[u8]) -> [bool; 4] {
    let (Ok(pk), Ok(sig)) = (<[u8; 32]>::try_from(pk), <[u8; 64]>::try_from(sig)) else {
        return [false; 4];
    };
    let Ok(vk) = ed25519_dalek::VerifyingKey::from_bytes(&pk) else {
        return [false; 4];
    };
    let ok = vk
        .verify_strict(msg, &ed25519_dalek::Signature::from_bytes(&sig))
        .is_ok();
    [true, true, true, ok]
}

fn p256_flags(pk: &[u8], msg: &[u8], sig: &[u8]) -> [bool; 4] {
    let vk = p256::ecdsa::VerifyingKey::from_sec1_bytes(pk);
    let s = p256::ecdsa::Signature::from_slice(sig);
    let low = s.as_ref().is_ok_and(|s| s.normalize_s() == *s);
    let ok = match (&vk, &s) {
        (Ok(vk), Ok(s)) => vk.verify(msg, s).is_ok(),
        _ => false,
    };
    [vk.is_ok(), s.is_ok(), low, ok]
}

fn ml_flags(pk: &[u8], ctx: &[u8], msg: &[u8], sig: &[u8]) -> [bool; 4] {
    let Ok(pk) = <[u8; 1952]>::try_from(pk) else {
        return [false; 4];
    };
    let vk = ml_dsa::VerifyingKey::<ml_dsa::MlDsa65>::decode(&pk.into());
    let Ok(s) = ml_dsa::Signature::<ml_dsa::MlDsa65>::try_from(sig) else {
        return [true, false, true, false];
    };
    [true, true, true, ctx.len() <= 255 && vk.verify_with_context(msg, ctx, &s)]
}

fn digest(msg: &[u8]) -> [u8; 32] {
    blake3::derive_key(labels::HYBRID_SIGNATURE, msg)
}

/// The digest oracle of a hybrid signature and the message it was computed on (both empty for the other algorithms).
fn dig_json(alg: IdentityAlg, msg: &[u8]) -> String {
    if alg == IdentityAlg::Hybrid {
        format!(r#""dig":{},"dig_in":{},"hyb":true"#, arr(&digest(msg)), arr(msg))
    } else {
        r#""dig":[],"dig_in":[],"hyb":false"#.into()
    }
}

/// The flags of the two halves the model takes for `alg`.
fn all_flags(alg: IdentityAlg, pk: &[u8], msg: &[u8], sig: &[u8]) -> ([bool; 4], [bool; 4]) {
    match alg {
        IdentityAlg::Ed25519 => (ed_flags(pk, msg, sig), [false; 4]),
        IdentityAlg::EcdsaP256 => (p256_flags(pk, msg, sig), [false; 4]),
        IdentityAlg::MlDsa65 => ([false; 4], ml_flags(pk, &[], msg, sig)),
        IdentityAlg::Hybrid => {
            if pk.len() == alg.public_key_len() && sig.len() == alg.signature_len() {
                let d = digest(msg);
                (
                    ed_flags(&pk[..32], &d, &sig[..64]),
                    ml_flags(&pk[32..], &[], &d, &sig[64..]),
                )
            } else {
                ([false; 4], [false; 4])
            }
        }
    }
}

fn ver_line(out: &mut String, alg: IdentityAlg, pk: &[u8], msg: &[u8], sig: &[u8]) {
    let (fe, fm) = all_flags(alg, pk, msg, sig);
    let r = verify(alg, pk, msg, sig);
    let dig = dig_json(alg, msg);
    let _ = writeln!(
        out,
        r#"{{"t":"cr","op":"ver","alg":{},"pk":{},"msg":{},"sig":{},"fe":{},"fm":{},{dig},"res":"{}"}}"#,
        alg.tag(),
        arr(pk),
        arr(msg),
        arr(sig),
        flags(fe),
        flags(fm),
        res(&r)
    );
}

fn mutations(alg: IdentityAlg, pk: &[u8], msg: &[u8], sig: &[u8]) -> Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> {
    let mut v = vec![(pk.to_vec(), msg.to_vec(), sig.to_vec())];
    let flip = |b: &[u8], i: usize| {
        let mut c = b.to_vec();
        c[i] ^= 1;
        c
    };
    v.push((pk.to_vec(), flip(msg, 0), sig.to_vec()));
    for i in [0, 1, sig.len() / 2, sig.len() - 1] {
        v.push((pk.to_vec(), msg.to_vec(), flip(sig, i)));
    }
    for i in [0, 1, pk.len() / 2, pk.len() - 1] {
        v.push((flip(pk, i), msg.to_vec(), sig.to_vec()));
    }
    if alg == IdentityAlg::Hybrid {
        for i in [31, 32, 63, 64, 65] {
            v.push((pk.to_vec(), msg.to_vec(), flip(sig, i)));
            v.push((flip(pk, i), msg.to_vec(), sig.to_vec()));
        }
    }
    // lengths
    for d in [-1i32, 1] {
        let resize = |b: &[u8]| {
            let mut c = b.to_vec();
            if d < 0 {
                c.pop();
            } else {
                c.push(0);
            }
            c
        };
        v.push((resize(pk), msg.to_vec(), sig.to_vec()));
        v.push((pk.to_vec(), msg.to_vec(), resize(sig)));
    }
    v.push((vec![], msg.to_vec(), sig.to_vec()));
    v.push((pk.to_vec(), msg.to_vec(), vec![]));
    v.push((pk.to_vec(), vec![], sig.to_vec()));
    v
}

fn ver_trace(out: &mut String) {
    for (i, alg) in ALGS.into_iter().enumerate() {
        let kp = keypair(alg, 200 + i as u64);
        let pk = public(&kp);
        let msg = b"a message for the verifier".to_vec();
        let sig = sign(&kp, &msg);
        for (p, m, s) in mutations(alg, &pk, &msg, &sig) {
            ver_line(out, alg, &p, &m, &s);
        }
    }
    // Ed25519: a key that is not a point, found with the library, and an all-ones key and signature
    let kp = keypair(IdentityAlg::Ed25519, 300);
    let pk = public(&kp);
    let sig = sign(&kp, b"m");
    let mut found = 0;
    for y in 0..=255u8 {
        let mut bad = [0u8; 32];
        bad[0] = y;
        if ed25519_dalek::VerifyingKey::from_bytes(&bad).is_err() {
            ver_line(out, IdentityAlg::Ed25519, &bad, b"m", &sig);
            found += 1;
            if found == 3 {
                break;
            }
        }
    }
    assert!(found > 0, "no invalid Ed25519 key found");
    ver_line(out, IdentityAlg::Ed25519, &[0xFF; 32], b"m", &[0xFF; 64]);
    ver_line(out, IdentityAlg::Ed25519, &pk, b"m", &[0; 64]);
    // P-256: every first byte, the malleable form, degenerate signatures and keys that are not points
    let kp = keypair(IdentityAlg::EcdsaP256, 301);
    let pk = public(&kp);
    let sig = sign(&kp, b"m");
    for first in [0u8, 1, 2, 3, 4, 5, 6, 7, 255] {
        let mut k = pk.clone();
        k[0] = first;
        ver_line(out, IdentityAlg::EcdsaP256, &k, b"m", &sig);
    }
    let mut high = sig.clone();
    high[32..].copy_from_slice(&negate(&sig[32..]));
    ver_line(out, IdentityAlg::EcdsaP256, &pk, b"m", &high);
    // the low form of that signature verifies, the high form does not
    ver_line(out, IdentityAlg::EcdsaP256, &pk, b"m", &sig);
    for degenerate in [[0u8; 64], [0xFF; 64]] {
        ver_line(out, IdentityAlg::EcdsaP256, &pk, b"m", &degenerate);
    }
    let mut zero_s = sig.clone();
    zero_s[32..].fill(0);
    ver_line(out, IdentityAlg::EcdsaP256, &pk, b"m", &zero_s);
    let mut big_r = sig.clone();
    big_r[..32].copy_from_slice(&N);
    ver_line(out, IdentityAlg::EcdsaP256, &pk, b"m", &big_r);
    let mut found = 0;
    for x in 1..=255u8 {
        let mut k = vec![2u8];
        k.extend_from_slice(&[0; 31]);
        k.push(x);
        if p256::ecdsa::VerifyingKey::from_sec1_bytes(&k).is_err() {
            ver_line(out, IdentityAlg::EcdsaP256, &k, b"m", &sig);
            found += 1;
            if found == 3 {
                break;
            }
        }
    }
    assert!(found > 0, "no invalid P-256 key found");
    // ML-DSA with a context: the boundary of 255 bytes
    let kp = keypair(IdentityAlg::MlDsa65, 302);
    let pk = public(&kp);
    let sig = sign(&kp, b"m");
    for ctx_len in [0usize, 1, 255, 256, 300] {
        let ctx = vec![9u8; ctx_len];
        let r = verify_ml_dsa_65(&pk, &ctx, b"m", &sig);
        let _ = writeln!(
            out,
            r#"{{"t":"cr","op":"mlv","ctx":{ctx_len},"pk":{},"msg":{},"sig":{},"fm":{},"res":"{}"}}"#,
            arr(&pk),
            arr(b"m"),
            arr(&sig),
            flags(ml_flags(&pk, &ctx, b"m", &sig)),
            res(&r)
        );
    }
}

fn vnode_trace(out: &mut String) {
    for (i, alg) in ALGS.into_iter().enumerate() {
        let kp = keypair(alg, 400 + i as u64);
        let pk = public(&kp);
        let msg = b"node message".to_vec();
        let sig = sign(&kp, &msg);
        let id = kp.node_id();
        let mut bad_id = id;
        bad_id.bytes[0] ^= 1;
        let mut as_other = id;
        as_other.alg = ALGS[(i + 1) % 4];
        let mut bad_sig = sig.clone();
        bad_sig[0] ^= 1;
        let cases: Vec<(NodeId, Vec<u8>, Vec<u8>)> = vec![
            (id, pk.clone(), sig.clone()),
            (id, pk.clone(), bad_sig.clone()),
            (bad_id, pk.clone(), sig.clone()),
            (bad_id, pk.clone(), bad_sig),
            (as_other, pk.clone(), sig.clone()),
            (id, pk[..pk.len() - 1].to_vec(), sig.clone()),
            (id, pk.clone(), sig[..sig.len() - 1].to_vec()),
        ];
        for (id, p, s) in cases {
            let (fe, fm) = all_flags(id.alg, &p, &msg, &s);
            let r = verify_node(&id, &p, &msg, &s);
            let dig = dig_json(id.alg, &msg);
            let _ = writeln!(
                out,
                r#"{{"t":"cr","op":"vnode","id":{},"pk":{},"msg":{},"sig":{},{},"fe":{},"fm":{},{dig},"res":"{}"}}"#,
                id_json(&id),
                arr(&p),
                arr(&msg),
                arr(&s),
                orc_json(nid_oracle(id.alg, &p)),
                flags(fe),
                flags(fm),
                res(&r)
            );
        }
    }
}

fn kp_trace(out: &mut String) {
    let mut rng = SplitMix64::new(0x4B50);
    for alg in ALGS {
        let need = alg.seed_len();
        let mut seeds: Vec<Vec<u8>> = vec![vec![], rand(&mut rng, need - 1), rand(&mut rng, need + 1), rand(&mut rng, need)];
        seeds.push(vec![0u8; need]);
        seeds.push(vec![0xFFu8; need]);
        if alg == IdentityAlg::EcdsaP256 {
            let mut one = vec![0u8; 32];
            one[31] = 1;
            seeds.push(one);
            seeds.push(n_plus(-1).to_vec());
            seeds.push(N.to_vec());
            seeds.push(n_plus(1).to_vec());
            let mut hi = vec![0u8; 32];
            hi[0] = 0xFF;
            seeds.push(hi);
            let mut ones_low = vec![0u8; 32];
            ones_low[0] = 0x7F;
            seeds.push(ones_low);
        }
        for seed in seeds {
            let r = Keypair::from_seed(alg, &seed);
            let _ = writeln!(
                out,
                r#"{{"t":"cr","op":"kp","alg":{},"seed":{},"res":"{}"}}"#,
                alg.tag(),
                arr(&seed),
                res(&r)
            );
        }
        let kp = keypair(alg, 500 + u64::from(alg.tag()));
        let (pkl, sigl) = (alg.public_key_len(), alg.signature_len());
        for (kind, need) in [("pub", pkl), ("sig", sigl)] {
            let mut lens = vec![0, 1, 31, 32, 33, need - 1, need, need + 1, MAX_PUBLIC_KEY_LEN.max(MAX_SIGNATURE_LEN)];
            lens.sort_unstable();
            lens.dedup();
            for len in lens {
                let mut buf = vec![0u8; len];
                let r = if kind == "pub" { kp.public_key(&mut buf) } else { kp.sign(b"m", &mut buf) };
                let rs = match &r {
                    Ok(n) => format!("{n}"),
                    Err(e) => format!("\"{e:?}\""),
                };
                let _ = writeln!(
                    out,
                    r#"{{"t":"cr","op":"write","alg":{},"kind":"{kind}","out":{len},"res":{rs}}}"#,
                    alg.tag()
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// the DRBG

fn chacha_stream(key: &[u8; 32], nonce: &[u8; 12], pos: u64, n: usize) -> Vec<u8> {
    let mut c = ChaCha20::new(key.into(), nonce.into());
    c.try_seek(pos).unwrap();
    let mut buf = vec![0u8; n];
    c.try_write_keystream(&mut buf).unwrap_or_else(|e| panic!("pos {pos} n {n}: {e:?}"));
    buf
}

/// The first 5 bytes of block `counter` of the ChaCha20 stream, through the cipher core (which serves all `2^32`
/// blocks, unlike the stream wrapper).
fn chacha_block_head(key: &[u8; 32], nonce: &[u8; 12], counter: u32) -> Vec<u8> {
    use chacha20::cipher::{Block, StreamCipherCore};
    use chacha20::variants::Ietf;
    use chacha20::{ChaChaCore, R20};
    let mut core = ChaChaCore::<R20, Ietf>::new(key.into(), nonce.into());
    core.set_block_pos(counter);
    let mut block = Block::<ChaChaCore<R20, Ietf>>::default();
    core.write_keystream_block(&mut block);
    block[..5].to_vec()
}

#[derive(Clone)]
enum DOp {
    Fill(usize),
    Reseed(Vec<u8>),
}

fn drbg_run(out: &mut String, seed: [u8; 32], ops: &[DOp]) -> Vec<Vec<u8>> {
    let mut d = Drbg::new(&seed);
    let mut key = seed;
    let mut outs = Vec::new();
    let mut items = Vec::new();
    for op in ops {
        match op {
            DOp::Fill(n) => {
                let mut buf = if *n > MAX_FILL { vec![0u8; *n] } else { vec![0xA5u8; *n] };
                let r = d.fill(&mut buf);
                if *n > MAX_FILL {
                    assert_eq!(r, Err(CryptoError::InputTooLong));
                    items.push(format!(r#"{{"k":"fill","n":{n},"err":"InputTooLong"}}"#));
                } else {
                    r.unwrap();
                    let orc = chacha_stream(&key, &[0; 12], 0, 32 + n);
                    assert_eq!(buf, orc[32..]);
                    key = orc[..32].try_into().unwrap();
                    outs.push(buf.clone());
                    items.push(format!(
                        r#"{{"k":"fill","n":{n},"out":{},"orc":{}}}"#,
                        arr(&buf),
                        arr(&orc)
                    ));
                }
            }
            DOp::Reseed(e) => {
                let e32: [u8; 32] = e.clone().try_into().unwrap();
                d.reseed(&e32);
                for (k, x) in key.iter_mut().zip(e) {
                    *k ^= x;
                }
                items.push(format!(r#"{{"k":"reseed","e":{}}}"#, arr(e)));
            }
        }
    }
    let _ = writeln!(
        out,
        r#"{{"t":"cr","op":"drbg","seed":{},"max":{MAX_FILL},"ops":[{}]}}"#,
        arr(&seed),
        items.join(",")
    );
    outs
}

fn drbg_trace(out: &mut String) {
    let mut rng = SplitMix64::new(0xD2B6);
    let lens = [0usize, 1, 31, 32, 33, 63, 64, 65, 100, 1000];
    let seed: [u8; 32] = rand(&mut rng, 32).try_into().unwrap();
    let mut ops: Vec<DOp> = lens.iter().map(|&n| DOp::Fill(n)).collect();
    let a = drbg_run(out, seed, &ops);
    let b = drbg_run(&mut String::new(), seed, &ops);
    assert_eq!(a, b, "the same seed gives the same stream");
    // reseeds in between: with random entropy, with zeros (no change) and with the same entropy twice
    let e1 = rand(&mut rng, 32);
    ops = vec![
        DOp::Fill(40),
        DOp::Reseed(e1.clone()),
        DOp::Fill(40),
        DOp::Reseed(vec![0; 32]),
        DOp::Fill(40),
        DOp::Reseed(e1.clone()),
        DOp::Reseed(e1),
        DOp::Fill(40),
        DOp::Reseed(rand(&mut rng, 32)),
        DOp::Reseed(vec![0xFF; 32]),
        DOp::Fill(0),
        DOp::Fill(5),
    ];
    drbg_run(out, seed, &ops);
    // the limit: one byte over is refused with the state unchanged, the next fill is what it would have been
    ops = vec![
        DOp::Fill(10),
        DOp::Fill(MAX_FILL + 1),
        DOp::Fill(10),
        DOp::Reseed(vec![1; 32]),
        DOp::Fill(MAX_FILL + 1),
        DOp::Fill(10),
    ];
    drbg_run(out, [7; 32], &ops);
    // a run with the all-zero seed
    drbg_run(out, [0; 32], &[DOp::Fill(64), DOp::Fill(64)]);
}

// ---------------------------------------------------------------------------------------------------------------
// the provider

fn provider_trace(out: &mut String) {
    let sw = Software;
    let mut rng = SplitMix64::new(0x9807);
    for (ai, alg) in [Aead::ChaCha20Poly1305, Aead::Aes128Gcm].into_iter().enumerate() {
        for len in 0..=70usize {
            let key = rand(&mut rng, len);
            let k = sw.aead_key(alg, &key);
            let h = sw.hp_key(alg, &key);
            for (kind, r) in [("aead", res(&k.as_ref().map(|_| ()).map_err(|e| *e))), ("hp", res(&h.as_ref().map(|_| ()).map_err(|e| *e)))] {
                let _ = writeln!(
                    out,
                    r#"{{"t":"cr","op":"key","kind":"{kind}","alg":{ai},"len":{len},"keylen":{},"res":"{r}"}}"#,
                    alg.key_len()
                );
            }
        }
        // seal and open: shapes, the roundtrip and the error mapping
        let key = rand(&mut rng, alg.key_len());
        let k = sw.aead_key(alg, &key).unwrap();
        let nonce: [u8; 12] = rand(&mut rng, 12).try_into().unwrap();
        for plen in [0usize, 1, 15, 16, 17, 100, 1500] {
            let pt = rand(&mut rng, plen);
            let aad = rand(&mut rng, plen % 7);
            let mut buf = pt.clone();
            let tag = sw.seal(&k, &nonce, &aad, &mut buf).unwrap();
            let sealed_len = buf.len();
            let mut opened = buf.clone();
            let r_ok = sw.open(&k, &nonce, &aad, &mut opened, &tag);
            assert!(r_ok.is_ok() && opened == pt);
            let mut bad_tag = tag;
            bad_tag[0] ^= 1;
            let mut o2 = buf.clone();
            let r_bad = sw.open(&k, &nonce, &aad, &mut o2, &bad_tag);
            assert_eq!(o2, buf, "a failed open leaves the ciphertext");
            let mut bad_n = nonce;
            bad_n[11] ^= 1;
            let r_nonce = sw.open(&k, &bad_n, &aad, &mut buf.clone(), &tag);
            let _ = writeln!(
                out,
                r#"{{"t":"cr","op":"aead","alg":{ai},"plen":{plen},"clen":{sealed_len},"tag":{},"open":"{}","badtag":"{}","badnonce":"{}"}}"#,
                tag.len(),
                res(&r_ok),
                res(&r_bad),
                res(&r_nonce)
            );
        }
    }
    hp_trace(out);
    dh_trace(out);
    kem_trace(out);
}

fn hex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn hp_trace(out: &mut String) {
    let sw = Software;
    let mut rng = SplitMix64::new(0x4850);
    // ChaCha20: the counters around the block boundaries and the end of the 32-bit counter, and the RFC 9001 vector
    let key: [u8; 32] = rand(&mut rng, 32).try_into().unwrap();
    let hp = sw.hp_key(Aead::ChaCha20Poly1305, &key).unwrap();
    let mut cases: Vec<([u8; 32], [u8; 16])> = Vec::new();
    for counter in [0u32, 1, 2, 3, 255, 256, 65535, 65536, 1 << 24, (1 << 31) - 1, 1 << 31, u32::MAX - 1, u32::MAX] {
        let mut sample: [u8; 16] = rand(&mut rng, 16).try_into().unwrap();
        sample[..4].copy_from_slice(&counter.to_le_bytes());
        cases.push((key, sample));
    }
    cases.push((
        hex("25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4").try_into().unwrap(),
        hex("5e5cd55c41f69080575d7999c25a5bfb").try_into().unwrap(),
    ));
    for (k, sample) in cases {
        let hp = sw.hp_key(Aead::ChaCha20Poly1305, &k).unwrap_or_else(|_| unreachable!());
        let mask = sw.hp_mask(&hp, &sample);
        let counter = u32::from_le_bytes(sample[..4].try_into().unwrap());
        let off = u64::from(counter) * 64;
        let nonce: [u8; 12] = sample[4..].try_into().unwrap();
        let orc = chacha_block_head(&k, &nonce, counter);
        assert_eq!(mask.to_vec(), orc, "the mask is the stream at counter * 64");
        let _ = writeln!(
            out,
            r#"{{"t":"cr","op":"hpc","key":{},"sample":{},"mask":{},"orc_off":{},"orc":{}}}"#,
            arr(&k),
            arr(&sample),
            arr(&mask),
            limbs(off),
            arr(&orc)
        );
    }
    let _ = hp;
    let kat = sw
        .hp_mask(
            &sw.hp_key(
                Aead::ChaCha20Poly1305,
                &hex("25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4"),
            )
            .unwrap(),
            &hex("5e5cd55c41f69080575d7999c25a5bfb").try_into().unwrap(),
        )
        .to_vec();
    assert_eq!(kat, hex("aefefe7d03"));
    // AES-128: random samples and the RFC 9001 vector
    let mut aes_cases: Vec<([u8; 16], [u8; 16])> = (0..6)
        .map(|_| (rand(&mut rng, 16).try_into().unwrap(), rand(&mut rng, 16).try_into().unwrap()))
        .collect();
    aes_cases.push((
        hex("9f50449e04a0e810283a1e9933adedd2").try_into().unwrap(),
        hex("d1b1c98dd7689fb8ec11d242b123dc9b").try_into().unwrap(),
    ));
    for (k, sample) in aes_cases {
        let hp = sw.hp_key(Aead::Aes128Gcm, &k).unwrap();
        let mask = sw.hp_mask(&hp, &sample);
        let cipher = Aes128::new_from_slice(&k).unwrap();
        let mut block = sample.into();
        cipher.encrypt_block(&mut block);
        let block: [u8; 16] = block.into();
        assert_eq!(mask.to_vec(), block[..5].to_vec());
        let _ = writeln!(
            out,
            r#"{{"t":"cr","op":"hpa","key":{},"sample":{},"mask":{},"orc":{}}}"#,
            arr(&k),
            arr(&sample),
            arr(&mask),
            arr(&block)
        );
    }
    let kat = sw
        .hp_mask(
            &sw.hp_key(Aead::Aes128Gcm, &hex("9f50449e04a0e810283a1e9933adedd2")).unwrap(),
            &hex("d1b1c98dd7689fb8ec11d242b123dc9b").try_into().unwrap(),
        )
        .to_vec();
    assert_eq!(kat, hex("437b9aec36"));
}

fn dh_trace(out: &mut String) {
    let sw = Software;
    let mut rng = SplitMix64::new(0x25519);
    let mut peers: Vec<Vec<u8>> = vec![
        vec![0u8; 32],
        {
            let mut v = vec![0u8; 32];
            v[0] = 1;
            v
        },
        hex("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800"),
        hex("5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157"),
        hex("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"),
        hex("edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"),
        hex("eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"),
        x25519_dalek::X25519_BASEPOINT_BYTES.to_vec(),
    ];
    for _ in 0..4 {
        peers.push(rand(&mut rng, 32));
    }
    for peer in peers {
        let seed: [u8; 32] = rand(&mut rng, 32).try_into().unwrap();
        let sec = sw.x25519_secret(&seed);
        let p: [u8; 32] = peer.clone().try_into().unwrap();
        let orc = x25519_dalek::x25519(seed, p);
        let r = sw.x25519_dh(&sec, &p);
        let rj = match &r {
            Ok(s) => format!(r#"{{"ok":{}}}"#, arr(s.expose())),
            Err(e) => format!(r#"{{"err":"{e:?}"}}"#),
        };
        let _ = writeln!(
            out,
            r#"{{"t":"cr","op":"dh","sec":{},"peer":{},"orc":{},"res":{rj}}}"#,
            arr(&seed),
            arr(&peer),
            arr(&orc)
        );
    }
}

/// The FIPS 203 modulus check of an encapsulation key: every 12-bit coefficient below 3329.
fn modulus_ok(ek: &[u8]) -> bool {
    ek.get(..1152).is_some_and(|t| {
        t.chunks(3).all(|c| {
            let c0 = u16::from(c[0]) | (u16::from(c[1] & 0xF) << 8);
            let c1 = u16::from(c[1] >> 4) | (u16::from(c[2]) << 4);
            c0 < 3329 && c1 < 3329
        })
    })
}

fn kem_trace(out: &mut String) {
    let sw = Software;
    let (_dk, ek) = sw.kem_keygen(&[1; 32], &[2; 32]);
    let good = sw.kem_encaps_key_bytes(&ek).to_vec();
    assert_eq!(good.len(), KEM_ENCAPS_KEY_LEN);
    let mut bad_mod = good.clone();
    bad_mod[0] = 0xFF;
    bad_mod[1] = 0xFF;
    let mut cases: Vec<Vec<u8>> = vec![good.clone(), bad_mod, vec![], good[..1183].to_vec(), {
        let mut v = good.clone();
        v.push(0);
        v
    }];
    cases.push(vec![0u8; KEM_ENCAPS_KEY_LEN]);
    for c in cases {
        let r = sw.kem_encaps_key(&c);
        let _ = writeln!(
            out,
            r#"{{"t":"cr","op":"kemkey","len":{},"mod":{},"res":"{}"}}"#,
            c.len(),
            modulus_ok(&c),
            res(&r)
        );
    }
    for len in [0usize, 1, KEM_CIPHERTEXT_LEN - 1, KEM_CIPHERTEXT_LEN, KEM_CIPHERTEXT_LEN + 1] {
        let r = sw.kem_ciphertext(&vec![3u8; len]);
        let _ = writeln!(out, r#"{{"t":"cr","op":"kemct","len":{len},"res":"{}"}}"#, res(&r));
    }
}

// ---------------------------------------------------------------------------------------------------------------
// secrets

/// The bytes a `Secret<N>` holds in memory after its destructor ran.
fn bytes_after_drop<const N: usize>(fill: u8) -> Vec<u8> {
    let mut slot = MaybeUninit::new(Secret::<N>::new([fill; N]));
    // SAFETY: the value is initialised and dropped exactly once; the memory stays allocated and is read as bytes.
    unsafe {
        std::ptr::drop_in_place(slot.as_mut_ptr());
        std::slice::from_raw_parts(slot.as_ptr().cast::<u8>(), N).to_vec()
    }
}

fn secret_trace(out: &mut String) {
    let cases: Vec<(Vec<u8>, Vec<u8>)> = vec![
        (vec![], vec![]),
        (vec![1], vec![1]),
        (vec![1], vec![2]),
        (vec![1, 2, 3], vec![1, 2, 3]),
        (vec![1, 2, 3], vec![1, 2, 4]),
        (vec![1, 2, 3], vec![0, 2, 3]),
        (vec![1, 2, 3], vec![1, 2]),
        (vec![1, 2], vec![1, 2, 3]),
        (vec![], vec![0]),
        (vec![0; 32], vec![0; 32]),
        (vec![0; 32], vec![0; 31]),
    ];
    for (a, b) in cases {
        let r = ct_eq(&a, &b);
        assert_eq!(r, a == b);
        let _ = writeln!(out, r#"{{"t":"cr","op":"cteq","a":{},"b":{},"eq":{r}}}"#, arr(&a), arr(&b));
    }
    let a = Secret::<4>::new([1, 2, 3, 4]);
    let b = Secret::<4>::new([1, 2, 3, 4]);
    let c = Secret::<4>::new([1, 2, 3, 5]);
    assert!(a == b && a != c && a.clone() == a);
    assert_eq!(format!("{a:?}"), "Secret(..)");
    assert_eq!(format!("{c:?}"), format!("{a:?}"));
    let _ = writeln!(
        out,
        r#"{{"t":"cr","op":"secret","a":[1,2,3,4],"b":[1,2,3,4],"c":[1,2,3,5],"ab":true,"ac":false,"debug":"{:?}"}}"#,
        a
    );
    for (n, after) in [(16usize, bytes_after_drop::<16>(0xAB)), (32, bytes_after_drop::<32>(0xCD)), (64, bytes_after_drop::<64>(0xEF))] {
        assert!(after.iter().all(|&x| x == 0), "a dropped Secret<{n}> still holds bytes");
        let _ = writeln!(out, r#"{{"t":"cr","op":"drop","n":{n},"after":{}}}"#, arr(&after));
    }
}

#[test]
fn crypto_traces() {
    let out = big(|| {
        let mut out = String::new();
        labels_trace(&mut out);
        kdf_trace(&mut out);
        alg_trace(&mut out);
        nid_trace(&mut out);
        ver_trace(&mut out);
        vnode_trace(&mut out);
        kp_trace(&mut out);
        drbg_trace(&mut out);
        provider_trace(&mut out);
        secret_trace(&mut out);
        out
    });
    assert!(out.lines().count() > 800);
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("crypto.ndjson"), out).unwrap();
    }
}
