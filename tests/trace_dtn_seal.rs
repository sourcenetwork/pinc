//! Trace generation for the one-shot encryption (`vinc-dtn` `seal.rs`, `head.rs`, `bundle.rs`): real runs of
//! `encapsulate`, `decapsulate`, the slice AEAD, `seal_bundle` and the signed head through the public API, recorded
//! as ndjson (`dtn_seal.ndjson`) for the TLA+ trace check (`TraceDtnSeal.tla`) and the Lean replay
//! (`Vinc/TraceDtnSeal.lean`).
//!
//! What is recorded is what an observer sees. A public value (a node id, a key pair, an ephemeral public key, a
//! KEM ciphertext, a bundle id), a seed and an AEAD key are ids (one id per distinct byte string per kind in a
//! run: equal bytes, equal id). An AEAD key is observed through a probe: the sealed bytes of 16 zero bytes at
//! slice index 0, so two ciphers have the same key iff their probes are equal. The checkers replay the calls on
//! symbolic terms (the ephemeral key is `epub` of the seed, the KEM ciphertext `ct` of the message seed and the
//! recipient's encapsulation key, the AEAD key is the term of the hybrid derivation, ...) and require the ids to
//! relate exactly as the terms do. So the key a recipient derives equals the sender's iff the terms are equal
//! (same recipient, epoch, key pair, ephemeral key, ciphertext and bundle id), a wrong recipient or epoch is
//! refused, a forged ciphertext derives another key, and a slice opens only under its key and its index.
//!
//! The test asserts everything itself (against facts read off the code's own outputs: equal probes iff the
//! ciphers interoperate), so it is meaningful without the proof tools. The trace is written to the directory in
//! `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
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
    clippy::needless_pass_by_value,
    clippy::type_complexity,
    clippy::struct_field_names,
    clippy::cast_lossless,
    unreachable_pub
)]

mod dtn_common;

use std::collections::HashMap;

use dtn_common::{Recipient, Sealed, keypair, make, plan, recipient};
use vinc_crypto::{IdentityAlg, NodeId, Secret, Software};
use vinc_dtn::error::DtnError;
use vinc_dtn::head::{BundleId, Envelope, Erasure, HEAD_LEN, Head, SignedHead};
use vinc_dtn::hlc::Hlc;
use vinc_dtn::seal::{Cipher, SealSeeds, decapsulate, encapsulate};

/// Dense ids for byte strings, one id per (kind, bytes).
#[derive(Default)]
struct Ids(HashMap<(char, Vec<u8>), u32>);

impl Ids {
    fn id(&mut self, kind: char, b: &[u8]) -> u32 {
        let next = u32::try_from(self.0.len()).unwrap() + 1;
        *self.0.entry((kind, b.to_vec())).or_insert(next)
    }
}

fn node_bytes(n: &NodeId) -> Vec<u8> {
    let mut v = vec![n.alg.tag()];
    v.extend_from_slice(&n.bytes);
    v
}

fn kp_bytes(r: &Recipient) -> Vec<u8> {
    let mut v = r.keys.x25519.to_vec();
    v.extend_from_slice(&r.keys.kem_ek);
    v
}

/// The probe of a cipher: its sealing of 16 zero bytes at index 0, tag included.
fn probe(c: &Cipher<Software>) -> Vec<u8> {
    let mut buf = [0u8; 16];
    let tag = c.seal_slice(&Software, 0, &mut buf).unwrap();
    buf.iter().chain(tag.iter()).copied().collect()
}

/// A head with the fields `decapsulate` reads; the rest is a placeholder.
fn head_of(id: BundleId, src: NodeId, dst: NodeId, env: &Envelope) -> Head {
    Head {
        id,
        source: src,
        destination: dst,
        created: Hlc::new(1000, 0),
        lifetime_ms: 1,
        copies: 1,
        erasure: Erasure { k: 1, m: 0 },
        slice_log: 0,
        payload_len: 1,
        root: [0; 32],
        envelope: *env,
    }
}

struct Run {
    ids: Ids,
    lines: Vec<String>,
    /// The ciphers seen, by key id.
    ciphers: Vec<(u32, Cipher<Software>)>,
}

impl Run {
    fn new() -> Self {
        Self {
            ids: Ids::default(),
            lines: vec![r#"{"t":"ds","e":"begin"}"#.to_string()],
            ciphers: vec![],
        }
    }

    fn keep(&mut self, kid: u32, c: Cipher<Software>) {
        if !self.ciphers.iter().any(|(k, _)| *k == kid) {
            self.ciphers.push((kid, c));
        }
    }

    /// Seal as `src` to `rcpt` with the seed bytes `(a, b)` at creation counter `ctr`; returns the head fields.
    fn enc(&mut self, src: &NodeId, rcpt: &Recipient, a: u8, b: u8, ctr: u32) -> Head {
        let seeds = SealSeeds {
            eph_x25519: Secret::new([a; 32]),
            kem_m: Secret::new([b; 32]),
        };
        let created = Hlc::new(1000, ctr);
        let (id, env, cipher) = encapsulate(&Software, &rcpt.keys, src, created, &seeds).unwrap();
        assert_eq!(id, BundleId::derive(src, created, &env.eph_x25519));
        let kid = self.ids.id('k', &probe(&cipher));
        let (s, d) = (
            self.ids.id('n', &node_bytes(src)),
            self.ids.id('n', &node_bytes(&rcpt.keys.node)),
        );
        let kp = self.ids.id('p', &kp_bytes(rcpt));
        let (se, sm) = (self.ids.id('S', &[a; 32]), self.ids.id('M', &[b; 32]));
        let (e, c, i) = (
            self.ids.id('e', &env.eph_x25519),
            self.ids.id('c', &env.kem_ct),
            self.ids.id('i', &id.0),
        );
        self.lines.push(format!(
            r#"{{"t":"ds","e":"enc","src":{s},"dest":{d},"ep":{},"kp":{kp},"wall":1000,"ctr":{ctr},"se":{se},"sm":{sm},"eph":{e},"ct":{c},"id":{i},"kid":{kid}}}"#,
            rcpt.keys.epoch
        ));
        self.keep(kid, cipher);
        head_of(id, *src, rcpt.keys.node, &env)
    }

    /// Decapsulate `head` with `own`; the verdict is asserted against the expectation read off the head.
    fn dec(&mut self, own: &Recipient, head: &Head, expect_ok_key_of: Option<u32>) {
        let r = decapsulate(&Software, &own.keys, &own.dk, &own.xs, head);
        let lo = head.envelope.eph_x25519 == [0; 32];
        let wrong = head.destination != own.keys.node || head.envelope.epoch != own.keys.epoch;
        let (v, kid) = match r {
            Err(DtnError::WrongRecipient) => {
                assert!(wrong);
                ("wrong", 0)
            }
            Err(DtnError::Crypto(_)) => {
                assert!(!wrong && lo);
                ("crypto", 0)
            }
            Err(e) => panic!("unexpected {e:?}"),
            Ok(c) => {
                assert!(!wrong && !lo);
                let kid = self.ids.id('k', &probe(&c));
                if let Some(want) = expect_ok_key_of {
                    assert_eq!(kid, want, "a genuine head must derive the sender's key");
                }
                self.keep(kid, c);
                ("ok", kid)
            }
        };
        let (n, kp) = (
            self.ids.id('n', &node_bytes(&own.keys.node)),
            self.ids.id('p', &kp_bytes(own)),
        );
        let (dst, e, c, i) = (
            self.ids.id('n', &node_bytes(&head.destination)),
            self.ids.id('e', &head.envelope.eph_x25519),
            self.ids.id('c', &head.envelope.kem_ct),
            self.ids.id('i', &head.id.0),
        );
        self.lines.push(format!(
            r#"{{"t":"ds","e":"dec","node":{n},"ep":{},"kp":{kp},"dst":{dst},"hep":{},"eph":{e},"ct":{c},"id":{i},"lo":{lo},"v":"{v}","kid":{kid}}}"#,
            own.keys.epoch, head.envelope.epoch
        ));
    }

    /// Seal 16 bytes at index `i` with cipher `a`, open at index `j` with cipher `b` (optionally tampered).
    fn open(&mut self, a: usize, b: usize, i: u64, j: u64, tamper: bool) {
        let (ka, ca) = &self.ciphers[a];
        let (kb, cb) = &self.ciphers[b];
        let mut buf = [9u8; 16];
        let tag = ca.seal_slice(&Software, i, &mut buf).unwrap();
        if tamper {
            buf[3] ^= 1;
        }
        let ok = cb.open_slice(&Software, j, &mut buf, &tag).is_ok();
        assert_eq!(
            ok,
            ka == kb && i == j && !tamper,
            "a slice opens only under its key and its index"
        );
        self.lines.push(format!(
            r#"{{"t":"ds","e":"open","ka":{ka},"kb":{kb},"i":{i},"j":{j},"tamper":{tamper},"ok":{ok}}}"#
        ));
    }
}

/// The names and widths of the fields of `Head::encode`, in order.
const FIELDS: [(&str, usize); 17] = [
    ("id", 32),
    ("stag", 1),
    ("src", 32),
    ("dtag", 1),
    ("dst", 32),
    ("wall", 8),
    ("ctr", 4),
    ("life", 8),
    ("copies", 2),
    ("k", 1),
    ("m", 1),
    ("log", 1),
    ("plen", 8),
    ("root", 32),
    ("epoch", 4),
    ("eph", 32),
    ("kct", 1088),
];

#[test]
fn one_shot_encryption_trace() {
    // The ML-DSA keys and ML-KEM values are large: run on a thread with room for them.
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(trace)
        .unwrap()
        .join()
        .unwrap();
}

fn trace() {
    let alg = IdentityAlg::Ed25519;
    let (s0, s1) = (keypair(alg, 1), keypair(IdentityAlg::Hybrid, 2));
    let (n0, n1) = (s0.node_id(), s1.node_id());
    let r0 = recipient(alg, 10, 1);
    let r0e2 = recipient(alg, 10, 2);
    let r1 = recipient(IdentityAlg::MlDsa65, 20, 1);
    let mut impostor = recipient(IdentityAlg::MlDsa65, 20, 1);
    impostor.keys.node = r0.keys.node;
    assert_eq!(r0.keys.node, r0e2.keys.node);
    assert_ne!(r0.keys.node, r1.keys.node);
    let mut run = Run::new();

    // Sealing: different seeds, senders, recipients, epochs and creation counters; one repeated seed pair.
    let h_a = run.enc(&n0, &r0, 1, 2, 0);
    let h_b = run.enc(&n0, &r0, 3, 4, 0);
    let h_c = run.enc(&n1, &r0, 5, 6, 0);
    let h_d = run.enc(&n0, &r1, 7, 8, 0);
    let h_e = run.enc(&n0, &r0e2, 9, 10, 0);
    // The same seeds and creation time again: the same key (the freshness assumption is what forbids this); another
    // creation counter with the same seeds: another key (the bundle id binds it).
    let _same = run.enc(&n0, &r0, 1, 2, 0);
    let _ctr = run.enc(&n0, &r0, 1, 2, 1);
    // Same ephemeral seed, another message seed and the reverse: both halves matter.
    let _half_a = run.enc(&n0, &r0, 1, 4, 0);
    let _half_b = run.enc(&n0, &r0, 3, 2, 0);
    // The same seeds to the same key pair at another epoch: the epoch is bound into the key.
    let _epoch = run.enc(&n0, &r0e2, 1, 2, 0);

    // Decapsulation: the genuine head under every recipient record, and heads changed in one field.
    let owners = [&r0, &r0e2, &r1, &impostor];
    for h in [&h_a, &h_b, &h_c, &h_d, &h_e] {
        for own in owners {
            run.dec(own, h, None);
        }
    }
    let genuine_kid = run.ids.id(
        'k',
        &probe(&decapsulate(&Software, &r0.keys, &r0.dk, &r0.xs, &h_a).unwrap()),
    );
    run.dec(&r0, &h_a, Some(genuine_kid));
    for own in [&r0, &r0e2, &impostor] {
        let mut h = h_a;
        h.envelope.kem_ct[7] ^= 1;
        run.dec(own, &h, None);
        let mut h = h_a;
        h.envelope.eph_x25519[0] ^= 1;
        run.dec(own, &h, None);
        let mut h = h_a;
        h.id.0[5] ^= 1;
        run.dec(own, &h, None);
        let mut h = h_a;
        h.envelope.eph_x25519 = [0; 32];
        run.dec(own, &h, None);
        let mut h = h_a;
        h.destination = r1.keys.node;
        run.dec(own, &h, None);
        let mut h = h_a;
        h.envelope.epoch = 2;
        run.dec(own, &h, None);
        // Another bundle's ciphertext or ephemeral key under this bundle's id.
        let mut h = h_a;
        h.envelope.kem_ct = h_b.envelope.kem_ct;
        run.dec(own, &h, None);
        let mut h = h_a;
        h.envelope.eph_x25519 = h_b.envelope.eph_x25519;
        run.dec(own, &h, None);
    }

    // Slices: every pair of ciphers seen, indices that agree and differ, with and without tampering.
    let n = run.ciphers.len();
    for a in 0..n {
        for b in 0..n {
            run.open(a, b, 0, 0, false);
        }
        run.open(a, a, 3, 3, false);
        run.open(a, a, 3, 4, false);
        run.open(a, a, 0, 2_000_000_000, false);
        run.open(a, a, 5, 5, true);
    }

    // The largest index a slice can have never opens a slice sealed at another one (not recorded: past TLC integers).
    {
        let (_, c) = &run.ciphers[0];
        let mut buf = [1u8; 16];
        let tag = c.seal_slice(&Software, 0, &mut buf).unwrap();
        assert!(c.open_slice(&Software, u64::MAX, &mut buf, &tag).is_err());
    }

    // seal_bundle seals each data index once: equal plaintext slices give pairwise different symbols.
    for (k, m, plain_slices) in [(2u8, 1u8, 5usize), (3, 2, 7), (1, 0, 4), (4, 1, 4)] {
        let sender = keypair(alg, 1);
        let to = recipient(alg, 10, 1);
        let payload = vec![0xabu8; (1024 - 16) * plain_slices];
        let s: Sealed = make(&sender, &to, plan(k, m, 0), &payload, 77);
        let layout = s.signed.head().layout().unwrap();
        let g = layout.slice_len() as usize;
        let mut seen = std::collections::HashSet::new();
        let mut bk = vec![];
        for b in 0..layout.blocks() {
            bk.push(layout.block_k(b));
            for t in 0..layout.block_k(b) {
                let sym = layout.block_start(b) as usize + t;
                assert!(
                    seen.insert(s.sealed[sym * g..(sym + 1) * g].to_vec()),
                    "a nonce was reused"
                );
            }
        }
        assert_eq!(seen.len() as u64, layout.data_symbols());
        let bks: Vec<String> = bk.iter().map(ToString::to_string).collect();
        run.lines.push(format!(
            r#"{{"t":"ds","e":"nonces","k":{k},"data":{},"bk":[{}],"distinct":true}}"#,
            layout.data_symbols(),
            bks.join(",")
        ));
    }

    // The signed head: untouched it verifies; any changed byte of the body is refused, whichever field it is in.
    let sender = keypair(alg, 1);
    let to = recipient(alg, 10, 1);
    let s = make(&sender, &to, plan(2, 1, 0), &[5u8; 3000], 5);
    let mut enc = vec![0u8; s.signed.encoded_len()];
    s.signed.encode(&mut enc).unwrap();
    assert!(SignedHead::decode(&enc).unwrap().verify().is_ok());
    assert_eq!(FIELDS.iter().map(|f| f.1).sum::<usize>(), HEAD_LEN);
    run.lines
        .push(format!(r#"{{"t":"ds","e":"hgood","len":{HEAD_LEN},"ok":true}}"#));
    let mut at = 0;
    for (name, w) in FIELDS {
        for pos in [at, at + w / 2, at + w - 1] {
            let mut bad = enc.clone();
            bad[pos] ^= 0x01;
            let rejected = SignedHead::decode(&bad).and_then(|h| h.verify()).is_err();
            assert!(rejected, "a changed byte of {name} was accepted");
            run.lines.push(format!(
                r#"{{"t":"ds","e":"hflip","pos":{pos},"f":"{name}","rej":{rejected}}}"#
            ));
        }
        at += w;
    }

    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        let mut text = run.lines.join("\n");
        text.push('\n');
        std::fs::write(std::path::Path::new(&dir).join("dtn_seal.ndjson"), text).unwrap();
    }
}
