//! Trace generation for the identifiers and parameters of the handshake (`ids.rs` of `pinc-security`): connection ids,
//! ALPNs, ALPN lists, AEAD tags and sets, and the local identity, driven through the public API and recorded as ndjson
//! (`secids.ndjson`) for the TLA+ trace check (`TraceSecIds`).
//!
//! * `cid`, `alpn`: `ConnId::new` and `Alpn::new` of every length from 0 to 40 and of 255, 256 and 1000 bytes, of two
//!   patterns, and of 200 seeded random strings; `cideq`, `alpneq`: equality of every pair of a set of edge values.
//! * `list`: `AlpnList::new` of lists of 0 to 11 items (valid ones, and ones with an item of 0 or 33 bytes) and of 100
//!   seeded random lists, with `find` of a set of ALPNs wanted.
//! * `tag`, `tagof`, `bits`, `has`, `choose`, `offer`: the AEAD tags and sets, over every input.
//! * `ident`: `LocalIdentity::new` of every algorithm with key lengths around each algorithm's, and of 50 seeded random
//!   ones, with what it gives back (the key, the algorithm, the key handle as four 16-bit limbs, the node id).
//!
//! Every result is also asserted here against an independent computation. The trace is written to the directory in
//! `PINC_TRACE_DIR` when it is set; otherwise nothing is written, the assertions still run.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::manual_is_multiple_of
)]

use std::fmt::Write as _;

use pinc_crypto::{Aead, Capabilities, IdentityAlg, NodeId};
use pinc_security::ids::{
    AeadSet, Alpn, AlpnList, ConnId, KeyHandle, LocalIdentity, MAX_ALPN_LEN, MAX_ALPNS, MAX_CID_LEN, aead_from_tag,
    aead_tag,
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

/// A list of byte strings as the model reads it.
fn lists(l: &[Vec<u8>]) -> String {
    format!("[{}]", l.iter().map(|b| bytes(b)).collect::<Vec<_>>().join(","))
}

/// `[(i * s + 3) % 256 for i in 1..=n]`.
fn pat(n: usize, s: usize) -> Vec<u8> {
    (1..=n).map(|i| ((i * s + 3) % 256) as u8).collect()
}

fn random_bytes(rng: &mut SplitMix64, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    rng.fill(&mut v);
    v
}

/// Whether some line of `op` holds `needle`.
fn has(out: &str, op: &str, needle: &str) -> bool {
    let head = format!(r#"{{"op":"{op}","#);
    out.lines().any(|l| l.starts_with(&head) && l.contains(needle))
}

fn cid_ops(out: &mut String) {
    let mut rng = SplitMix64::traced(1);
    let mut inputs: Vec<Vec<u8>> = Vec::new();
    for n in (0..=40).chain([255, 256, 1000]) {
        inputs.push(pat(n, 5));
        inputs.push(pat(n, 7));
    }
    for _ in 0..200 {
        let n = (rng.next_u64() % 48) as usize;
        inputs.push(random_bytes(&mut rng, n));
    }
    for b in &inputs {
        let c = ConnId::new(b);
        assert_eq!(c.is_some(), b.len() <= MAX_CID_LEN);
        if let Some(c) = &c {
            assert_eq!(c.as_bytes(), b.as_slice());
        }
        let _ = writeln!(
            out,
            r#"{{"op":"cid","b":{},"ok":{},"v":{}}}"#,
            bytes(b),
            c.is_some(),
            bytes(c.as_ref().map_or(&[][..], ConnId::as_bytes))
        );
        let a = Alpn::new(b);
        assert_eq!(a.is_some(), (1..=MAX_ALPN_LEN).contains(&b.len()));
        if let Some(a) = &a {
            assert_eq!(a.as_bytes(), b.as_slice());
        }
        let _ = writeln!(
            out,
            r#"{{"op":"alpn","b":{},"ok":{},"v":{}}}"#,
            bytes(b),
            a.is_some(),
            bytes(a.as_ref().map_or(&[][..], Alpn::as_bytes))
        );
    }
}

fn eq_ops(out: &mut String) {
    let mut last_changed = pat(20, 5);
    *last_changed.last_mut().unwrap() = 0;
    let cids: Vec<Vec<u8>> = vec![
        vec![],
        vec![0],
        vec![0, 0],
        vec![1],
        vec![1, 0],
        vec![0, 1],
        pat(20, 5),
        last_changed,
        pat(19, 5),
        vec![0; 20],
    ];
    for a in &cids {
        for b in &cids {
            let r = ConnId::new(a).unwrap() == ConnId::new(b).unwrap();
            assert_eq!(r, a == b);
            let _ = writeln!(out, r#"{{"op":"cideq","a":{},"b":{},"r":{r}}}"#, bytes(a), bytes(b));
        }
    }
    let mut last_zero = pat(32, 7);
    *last_zero.last_mut().unwrap() = 0;
    let alpns: Vec<Vec<u8>> = vec![
        vec![0],
        vec![0, 0],
        vec![1],
        vec![1, 0],
        pat(32, 7),
        last_zero,
        pat(31, 7),
        vec![0; 32],
    ];
    for a in &alpns {
        for b in &alpns {
            let r = Alpn::new(a).unwrap() == Alpn::new(b).unwrap();
            assert_eq!(r, a == b);
            let _ = writeln!(out, r#"{{"op":"alpneq","a":{},"b":{},"r":{r}}}"#, bytes(a), bytes(b));
        }
    }
}

fn list_op(out: &mut String, l: &[Vec<u8>], w: &[u8]) {
    let refs: Vec<&[u8]> = l.iter().map(Vec::as_slice).collect();
    let list = AlpnList::new(&refs);
    let expect_ok = (1..=MAX_ALPNS).contains(&l.len()) && l.iter().all(|a| (1..=MAX_ALPN_LEN).contains(&a.len()));
    assert_eq!(list.is_some(), expect_ok);
    let found = list.as_ref().and_then(|x| x.find(w));
    if list.is_some() {
        assert_eq!(found.is_some(), l.iter().any(|a| a == w));
        if let Some(f) = &found {
            assert_eq!(f.as_bytes(), w);
        }
    } else {
        assert!(found.is_none());
    }
    let _ = writeln!(
        out,
        r#"{{"op":"list","l":{},"w":{},"ok":{},"found":{},"v":{}}}"#,
        lists(l),
        bytes(w),
        list.is_some(),
        found.is_some(),
        bytes(found.as_ref().map_or(&[][..], Alpn::as_bytes))
    );
}

fn list_ops(out: &mut String) {
    let a = |m: usize| pat(m, 7);
    let ws = [a(1), a(2), a(3), a(32), vec![], a(33)];
    let mut all: Vec<Vec<Vec<u8>>> = Vec::new();
    for n in 0..=11usize {
        all.push((1..=n).map(|i| a(1 + i % 3)).collect());
    }
    for n in 1..=9usize {
        for j in 1..=9usize {
            for bad in [0usize, 33] {
                let mut l: Vec<Vec<u8>> = (1..=n).map(|i| a(1 + i % 3)).collect();
                if j <= n {
                    l[j - 1] = a(bad);
                }
                if !all.contains(&l) {
                    all.push(l);
                }
            }
        }
    }
    for l in &all {
        for w in &ws {
            list_op(out, l, w);
        }
    }
    let mut rng = SplitMix64::traced(2);
    for _ in 0..100 {
        let n = 1 + (rng.next_u64() % 10) as usize;
        let l: Vec<Vec<u8>> = (0..n)
            .map(|_| {
                let len = (rng.next_u64() % 34) as usize;
                random_bytes(&mut rng, len)
            })
            .collect();
        let w = if rng.next_u64() % 2 == 0 {
            l[(rng.next_u64() % n as u64) as usize].clone()
        } else {
            let len = 1 + (rng.next_u64() % 32) as usize;
            random_bytes(&mut rng, len)
        };
        list_op(out, &l, &w);
    }
}

fn aead_ops(out: &mut String) {
    for t in 0..=255u8 {
        let r = aead_from_tag(t).map_or(0, aead_tag);
        assert_eq!(r, if matches!(t, 1 | 2) { t } else { 0 });
        let _ = writeln!(out, r#"{{"op":"tag","t":{t},"r":{r}}}"#);
    }
    let (chacha, aes) = (aead_tag(Aead::ChaCha20Poly1305), aead_tag(Aead::Aes128Gcm));
    assert_eq!((chacha, aes), (1, 2));
    let _ = writeln!(out, r#"{{"op":"tagof","a":"chacha","r":{chacha}}}"#);
    let _ = writeln!(out, r#"{{"op":"tagof","a":"aes","r":{aes}}}"#);
    for b in 0..=255u8 {
        let r = AeadSet::from_bits(b).map_or(0, AeadSet::bits);
        assert_eq!(r, if (1..=3).contains(&b) { b } else { 0 });
        let _ = writeln!(out, r#"{{"op":"bits","b":{b},"r":{r}}}"#);
    }
    for s in 1..=3u8 {
        for t in 1..=2u8 {
            let r = AeadSet::from_bits(s).unwrap().contains(aead_from_tag(t).unwrap());
            assert_eq!(r, s & t != 0);
            let _ = writeln!(out, r#"{{"op":"has","s":{s},"t":{t},"r":{r}}}"#);
        }
    }
    for a in 1..=3u8 {
        for b in 1..=3u8 {
            let r = AeadSet::from_bits(a)
                .unwrap()
                .choose(AeadSet::from_bits(b).unwrap())
                .map_or(0, aead_tag);
            let expect = if a & b & 2 != 0 { 2 } else { u8::from(a & b & 1 != 0) };
            assert_eq!(r, expect);
            let _ = writeln!(out, r#"{{"op":"choose","a":{a},"b":{b},"r":{r}}}"#);
        }
    }
    for hw in [false, true] {
        for simd in [false, true] {
            let r = AeadSet::offer(Capabilities {
                aes_gcm_hw: hw,
                chacha20_simd: simd,
            })
            .bits();
            assert_eq!(r, if hw { 3 } else { 1 });
            let _ = writeln!(out, r#"{{"op":"offer","hw":{hw},"simd":{simd},"r":{r}}}"#);
        }
    }
}

fn ident_op(out: &mut String, alg: IdentityAlg, pk: &[u8], key: u64) {
    let id = LocalIdentity::new(alg, pk, KeyHandle(key));
    let ok = pk.len() == alg.public_key_len();
    assert_eq!(id.is_ok(), ok);
    let (pk2, alg2, key2, nid) = match &id {
        Ok(id) => {
            assert_eq!(id.public_key(), pk);
            assert_eq!(id.alg(), alg);
            assert_eq!(id.key(), KeyHandle(key));
            let expect = NodeId::from_public(alg, pk).unwrap();
            assert_eq!(id.node_id(), expect);
            if alg == IdentityAlg::Ed25519 {
                assert_eq!(id.node_id().bytes.as_slice(), pk);
            }
            (
                bytes(id.public_key()),
                id.alg().tag(),
                limbs(id.key().0),
                bytes(&id.node_id().bytes),
            )
        }
        Err(_) => ("[]".to_owned(), 0, "[0,0,0,0]".to_owned(), "[]".to_owned()),
    };
    let _ = writeln!(
        out,
        r#"{{"op":"ident","alg":{},"pk":{},"key":{},"ok":{ok},"pk2":{pk2},"alg2":{alg2},"key2":{key2},"nid":{nid}}}"#,
        alg.tag(),
        bytes(pk),
        limbs(key)
    );
}

fn ident_ops(out: &mut String) {
    let keys = [0u64, 1, 0xffff, 0x1_0000, u64::MAX];
    let mut k = 0usize;
    for tag in 1..=4u8 {
        let alg = IdentityAlg::from_tag(tag).unwrap();
        for n in [0usize, 1, 31, 32, 33, 34, 1951, 1952, 1953, 1983, 1984, 1985, 2600] {
            ident_op(out, alg, &pat(n, 11), keys[k % keys.len()]);
            k += 1;
        }
    }
    let mut rng = SplitMix64::traced(3);
    for i in 0..50 {
        let alg = IdentityAlg::from_tag(1 + (rng.next_u64() % 4) as u8).unwrap();
        let n = if i % 2 == 0 {
            alg.public_key_len()
        } else {
            (rng.next_u64() % 2048) as usize
        };
        let pk = random_bytes(&mut rng, n);
        ident_op(out, alg, &pk, rng.next_u64());
    }
}

#[test]
fn sec_ids_traces() {
    let mut out = String::new();
    cid_ops(&mut out);
    eq_ops(&mut out);
    list_ops(&mut out);
    aead_ops(&mut out);
    ident_ops(&mut out);
    for op in [
        "cid", "alpn", "cideq", "alpneq", "list", "tag", "tagof", "bits", "has", "choose", "offer", "ident",
    ] {
        assert!(
            pinc_tests::soaking() || out.contains(&format!(r#"{{"op":"{op}","#)),
            "the runs never produce {op}"
        );
    }
    for op in ["cid", "alpn", "list", "ident"] {
        assert!(
            has(&out, op, r#""ok":true"#) && has(&out, op, r#""ok":false"#),
            "{op}: ok is not both"
        );
    }
    assert!(has(&out, "list", r#""found":true"#) && has(&out, "list", r#""found":false"#));
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("secids.ndjson"), out).unwrap();
}
