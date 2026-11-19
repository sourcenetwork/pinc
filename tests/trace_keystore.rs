//! Trace generation for the software key store and the key host: handles, the request and answer of every operation,
//! the sealed format, recorded as ndjson (`keystore.ndjson`) for the TLA+ trace check (`TraceKeystore.tla`) and the
//! Lean replay (`Pinc.TraceKeystore`).
//!
//! Every event is `{"t":"ks","op":...}`. A handle is named by the index of its creation in the run; the test compares
//! handles with `==` and records whether each new handle differs from every earlier one, in this store and in the
//! other. The events:
//! * `new`: `generate`, `generate_kem` or `insert`, with the new handle's index and whether it is distinct from all
//!   earlier handles;
//! * `rm`, `sign`, `pub`, `nodeid`, `dec`: one call on a handle (possibly removed, or made by the other store, or of the
//!   other kind) and its exact result; a signature is verified with `pinc_crypto::identity::verify`, a decapsulation is
//!   compared with the encapsulation;
//! * `bind`, `ans`: a `KeyHost` over a store: the binding of a handshake handle and the answer to a request;
//! * `seal`, `unseal`: the sealed blobs of two stores and what each store makes of genuine, altered, cut, extended and
//!   foreign blobs.
//!
//! The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use std::fmt::Write as _;

use pinc_crypto::identity::verify;
use pinc_crypto::provider::KEM_CIPHERTEXT_LEN;
use pinc_crypto::{IdentityAlg, Keypair, NodeId, Provider, Software};
use pinc_keystore::{KeyHandle, KeyHost, KeyStore, SoftwareStore};
use pinc_security::{KeyHandle as SecHandle, KeyRequest, KeyResponse};

const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

fn arr(b: &[u8]) -> String {
    format!("[{}]", b.iter().map(u8::to_string).collect::<Vec<_>>().join(","))
}

fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// The run: two stores, every handle ever made and the output.
struct Run {
    stores: Vec<SoftwareStore>,
    handles: Vec<KeyHandle>,
    out: String,
}

impl Run {
    fn new() -> Self {
        Self {
            stores: vec![SoftwareStore::new().unwrap(), SoftwareStore::new().unwrap()],
            handles: Vec::new(),
            out: String::new(),
        }
    }

    /// Record a new handle: its index, and whether it differs from every handle made before.
    fn record_new(&mut self, s: usize, kind: &str, alg: u8, h: KeyHandle) -> usize {
        let distinct = self.handles.iter().all(|o| *o != h);
        assert!(distinct, "a handle repeats");
        self.handles.push(h);
        let idx = self.handles.len() - 1;
        let _ = writeln!(
            self.out,
            r#"{{"t":"ks","op":"new","s":{s},"kind":"{kind}","alg":{alg},"h":{idx},"distinct":{distinct}}}"#
        );
        idx
    }

    fn generate(&mut self, s: usize, alg: IdentityAlg) -> usize {
        let h = self.stores[s].generate(alg).unwrap();
        self.record_new(s, "gen", alg.tag(), h)
    }

    fn insert(&mut self, s: usize, alg: IdentityAlg, seed: u8) -> usize {
        let kp = Keypair::from_seed(alg, &vec![seed; alg.seed_len()]).unwrap();
        let h = self.stores[s].insert(kp);
        self.record_new(s, "ins", alg.tag(), h)
    }

    fn generate_kem(&mut self, s: usize) -> (usize, Vec<u8>) {
        let (h, ek) = self.stores[s].generate_kem().unwrap();
        (self.record_new(s, "kem", 0, h), ek.to_vec())
    }

    fn remove(&mut self, s: usize, h: usize) -> bool {
        let r = self.stores[s].remove(&self.handles[h]);
        let _ = writeln!(self.out, r#"{{"t":"ks","op":"rm","s":{s},"h":{h},"res":{r}}}"#);
        r
    }

    fn sign(&mut self, s: usize, h: usize) {
        let msg = b"a message to sign".to_vec();
        let r = self.stores[s].sign(&self.handles[h], &msg);
        let tail = match &r {
            Ok(sig) => {
                let (alg, pk) = self.stores[s].public(&self.handles[h]).unwrap();
                let ver = verify(sig.alg(), &pk, &msg, sig.as_bytes()).is_ok() && sig.alg() == alg;
                format!(
                    r#""res":"ok","alg":{},"len":{},"ver":{ver}"#,
                    sig.alg().tag(),
                    sig.as_bytes().len()
                )
            }
            Err(e) => format!(r#""res":"{e:?}","alg":0,"len":0,"ver":false"#),
        };
        let _ = writeln!(self.out, r#"{{"t":"ks","op":"sign","s":{s},"h":{h},{tail}}}"#);
    }

    #[allow(clippy::many_single_char_names)]
    fn public(&mut self, s: usize, h: usize) {
        let r = self.stores[s].public(&self.handles[h]);
        let tail = match &r {
            Ok((alg, pk)) => format!(r#""res":"ok","alg":{},"len":{}"#, alg.tag(), pk.len()),
            Err(e) => format!(r#""res":"{e:?}","alg":0,"len":0"#),
        };
        let _ = writeln!(self.out, r#"{{"t":"ks","op":"pub","s":{s},"h":{h},{tail}}}"#);
        let nid = self.stores[s].node_id(&self.handles[h]);
        let (res, same) = match (&nid, &r) {
            (Ok(id), Ok((alg, pk))) => ("ok".to_string(), *id == NodeId::from_public(*alg, pk).unwrap()),
            (Err(e), Err(f)) => (format!("{e:?}"), e == f),
            _ => ("mismatch".into(), false),
        };
        let _ = writeln!(
            self.out,
            r#"{{"t":"ks","op":"nodeid","s":{s},"h":{h},"res":"{res}","same":{same}}}"#
        );
    }

    fn decap(&mut self, s: usize, h: usize, ct: &[u8], expect: Option<[u8; 32]>) {
        let r = self.stores[s].decapsulate(&self.handles[h], ct);
        let (res, agree) = match &r {
            Ok(secret) => ("ok".to_string(), expect.is_none_or(|e| *secret.expose() == e)),
            Err(e) => (format!("{e:?}"), true),
        };
        let _ = writeln!(
            self.out,
            r#"{{"t":"ks","op":"dec","s":{s},"h":{h},"ctlen":{},"res":"{res}","agree":{agree}}}"#,
            ct.len()
        );
    }
}

/// Handles of every kind in store 0, calls on them, on removed handles and on handles of the other store.
fn store_trace(run: &mut Run) {
    let mut ids = Vec::new();
    for alg in ALGS {
        ids.push(run.generate(0, alg));
    }
    ids.push(run.insert(0, IdentityAlg::Ed25519, 7));
    ids.push(run.insert(0, IdentityAlg::EcdsaP256, 9));
    let (kem, ek) = run.generate_kem(0);
    let other_id = run.generate(1, IdentityAlg::Ed25519);
    let (other_kem, _) = run.generate_kem(1);
    let ek = Software.kem_encaps_key(&ek).unwrap();
    let (ct, shared) = Software.kem_encapsulate(&ek, &[3; 32]).unwrap();
    let ct = Software.kem_ciphertext_bytes(&ct);
    assert_eq!(ct.len(), KEM_CIPHERTEXT_LEN);
    for &h in ids.iter().chain([&kem, &other_id, &other_kem]) {
        for s in [0, 1] {
            run.sign(s, h);
            run.public(s, h);
            run.decap(s, h, &ct, (h == kem && s == 0).then(|| *shared.expose()));
        }
    }
    for len in [0usize, 1, KEM_CIPHERTEXT_LEN - 1, KEM_CIPHERTEXT_LEN + 1] {
        run.decap(0, kem, &vec![5u8; len], None);
    }
    // a forged ciphertext of the right length gives a secret, not an error
    run.decap(0, kem, &vec![0u8; KEM_CIPHERTEXT_LEN], None);
    // removal: the first removal finds the key, the second does not, the other store's key is not removed here
    assert!(run.remove(0, ids[0]));
    assert!(!run.remove(0, ids[0]));
    assert!(!run.remove(0, other_id));
    assert!(!run.remove(1, ids[1]));
    for s in [0, 1] {
        run.sign(s, ids[0]);
        run.public(s, ids[0]);
    }
    run.sign(1, other_id);
    assert!(run.remove(0, kem));
    run.decap(0, kem, &ct, None);
    // handles made after removals are new
    let again = run.generate(0, IdentityAlg::Ed25519);
    run.sign(0, again);
}

/// A host over a store: the binding, the answer to each kind of request and the failures.
fn host_trace(out: &mut String) {
    let mut store = SoftwareStore::new().unwrap();
    let mut ks = Vec::new();
    for alg in ALGS {
        ks.push((alg, store.generate(alg).unwrap()));
    }
    let (kem_h, ek) = store.generate_kem().unwrap();
    let ek = Software.kem_encaps_key(&ek).unwrap();
    let (ct, shared) = Software.kem_encapsulate(&ek, &[4; 32]).unwrap();
    let ct: [u8; KEM_CIPHERTEXT_LEN] = Software.kem_ciphertext_bytes(&ct);
    let mut host = KeyHost::new(store);
    let mut bound: Vec<(u64, usize)> = Vec::new();
    let all: Vec<KeyHandle> = ks.iter().map(|(_, h)| h.clone()).chain([kem_h.clone()]).collect();
    let bind =
        |host: &mut KeyHost<SoftwareStore>, bound: &mut Vec<(u64, usize)>, out: &mut String, sec: u64, k: usize| {
            host.bind(SecHandle(sec), all[k].clone());
            bound.retain(|(s, _)| *s != sec);
            bound.push((sec, k));
            let _ = writeln!(out, r#"{{"t":"ks","op":"bind","sec":{sec},"k":{k}}}"#);
        };
    for i in 0..4 {
        bind(&mut host, &mut bound, out, 10 + i as u64, i);
    }
    bind(&mut host, &mut bound, out, 20, 4);
    let msg = b"handshake message".to_vec();
    let sign = |host: &mut KeyHost<SoftwareStore>, out: &mut String, sec: u64, alg: IdentityAlg| {
        let (kind, len, ver) = match host.answer(&KeyRequest::Sign {
            key: SecHandle(sec),
            alg,
            message: &msg,
        }) {
            KeyResponse::Signature(sig) => ("sig", sig.len(), true),
            KeyResponse::SharedSecret(_) => ("secret", 0, false),
            KeyResponse::Failed => ("failed", 0, false),
        };
        let _ = writeln!(
            out,
            r#"{{"t":"ks","op":"ans","req":"sign","sec":{sec},"alg":{},"ans":"{kind}","len":{len},"ok":{ver}}}"#,
            alg.tag()
        );
    };
    for (i, (alg, _)) in ks.iter().enumerate() {
        sign(&mut host, out, 10 + i as u64, *alg);
        // the wrong algorithm for the key
        sign(&mut host, out, 10 + i as u64, ALGS[(i + 1) % 4]);
    }
    sign(&mut host, out, 99, IdentityAlg::Ed25519);
    sign(&mut host, out, 20, IdentityAlg::Ed25519);
    let decap = |host: &mut KeyHost<SoftwareStore>, out: &mut String, sec: u64| {
        let (kind, agree) = match host.answer(&KeyRequest::Decapsulate {
            key: SecHandle(sec),
            ct: &ct,
        }) {
            KeyResponse::Signature(_) => ("sig", false),
            KeyResponse::SharedSecret(s) => ("secret", *s.expose() == *shared.expose()),
            KeyResponse::Failed => ("failed", false),
        };
        let _ = writeln!(
            out,
            r#"{{"t":"ks","op":"ans","req":"decap","sec":{sec},"alg":0,"ans":"{kind}","len":0,"ok":{agree}}}"#
        );
    };
    decap(&mut host, out, 20);
    decap(&mut host, out, 10);
    decap(&mut host, out, 99);
    // rebinding replaces: 10 now names the KEM key, then the Ed25519 key again
    bind(&mut host, &mut bound, out, 10, 4);
    decap(&mut host, out, 10);
    sign(&mut host, out, 10, IdentityAlg::Ed25519);
    bind(&mut host, &mut bound, out, 10, 0);
    sign(&mut host, out, 10, IdentityAlg::Ed25519);
    // a key removed from the store behind the binding is a failure
    assert!(host.store().remove(&all[0]));
    let _ = writeln!(out, r#"{{"t":"ks","op":"hrm","k":0}}"#);
    sign(&mut host, out, 10, IdentityAlg::Ed25519);
    // the bound table has one entry per handshake handle
    let mut secs: Vec<u64> = bound.iter().map(|(s, _)| *s).collect();
    secs.sort_unstable();
    secs.dedup();
    assert_eq!(secs.len(), bound.len());
}

/// Sealed blobs of two stores and everything done to them.
fn sealed_trace(run: &mut Run) {
    let mut sealed: Vec<(usize, Vec<u8>, Vec<u8>)> = Vec::new();
    let unseal = |run: &mut Run, s: usize, blob: &[u8], pt_of: Option<&[u8]>| {
        let r = run.stores[s].unseal(blob);
        let (res, pt) = match &r {
            Ok(p) => ("ok".to_string(), p.to_vec()),
            Err(e) => (format!("{e:?}"), vec![]),
        };
        if let (Ok(p), Some(want)) = (&r, pt_of) {
            assert_eq!(p.as_slice(), want);
        }
        let _ = writeln!(
            run.out,
            r#"{{"t":"ks","op":"unseal","s":{s},"blob":{},"res":"{res}","pt":{}}}"#,
            arr(blob),
            arr(&pt)
        );
    };
    for pt_len in [0usize, 1, 3, 16, 17, 100] {
        let pt: Vec<u8> = (0..pt_len).map(|i| i as u8 ^ 0x5a).collect();
        for s in [0, 1] {
            let blob = run.stores[s].seal(&pt).unwrap();
            assert_eq!(blob.len(), 1 + 12 + pt_len + 16);
            assert_eq!(blob[0], 1);
            assert!(sealed.iter().all(|(_, b, _)| *b != blob), "a nonce repeated");
            let _ = writeln!(
                run.out,
                r#"{{"t":"ks","op":"seal","s":{s},"pt":{},"blob":{}}}"#,
                arr(&pt),
                arr(&blob)
            );
            sealed.push((s, blob, pt.clone()));
        }
        // the same plaintext twice in one store gives two blobs
        let again = run.stores[0].seal(&pt).unwrap();
        assert!(sealed.iter().all(|(_, b, _)| *b != again));
        let _ = writeln!(
            run.out,
            r#"{{"t":"ks","op":"seal","s":0,"pt":{},"blob":{}}}"#,
            arr(&pt),
            arr(&again)
        );
        sealed.push((0, again, pt));
    }
    let all = sealed.clone();
    for (s, blob, pt) in &all {
        unseal(run, *s, blob, Some(pt));
        unseal(run, 1 - *s, blob, None);
    }
    // alterations of one short blob in store 0: every byte, every cut, an extension, other versions
    let (_, blob, pt) = all.iter().find(|(s, _, p)| *s == 0 && p.len() == 3).unwrap().clone();
    for i in 0..blob.len() {
        for bit in [0x01u8, 0x80] {
            let mut b = blob.clone();
            b[i] ^= bit;
            unseal(run, 0, &b, None);
        }
    }
    for cut in 0..blob.len() {
        unseal(run, 0, &blob[..cut], None);
    }
    let mut longer = blob.clone();
    longer.push(0);
    unseal(run, 0, &longer, None);
    for v in [0u8, 2, 255] {
        let mut b = blob.clone();
        b[0] = v;
        unseal(run, 0, &b, None);
    }
    unseal(run, 0, &[], None);
    unseal(run, 0, &[1], None);
    unseal(run, 0, &blob, Some(&pt));
}

#[test]
fn keystore_traces() {
    let out = big(|| {
        let mut run = Run::new();
        store_trace(&mut run);
        let mut host_out = String::new();
        host_trace(&mut host_out);
        run.out.push_str(&host_out);
        sealed_trace(&mut run);
        run.out
    });
    assert!(out.lines().count() > 200);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("keystore.ndjson"), out).unwrap();
    }
}
