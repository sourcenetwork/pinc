//! The DRBG, provider and secret parts of the `pinc-crypto` trace (see `trace_crypto.rs`).
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
use pinc_crypto::drbg::MAX_FILL;
use pinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use pinc_crypto::{Aead, CryptoError, Drbg, Provider, Secret, Software, ct_eq};
use pinc_tests::SplitMix64;

use super::{arr, limbs, rand, res};

// ---------------------------------------------------------------------------------------------------------------
// the DRBG

fn chacha_stream(key: &[u8; 32], nonce: &[u8; 12], pos: u64, n: usize) -> Vec<u8> {
    let mut c = ChaCha20::new(key.into(), nonce.into());
    c.try_seek(pos).unwrap();
    let mut buf = vec![0u8; n];
    c.try_write_keystream(&mut buf).unwrap();
    buf
}

/// The first 5 bytes of block `counter` of the `ChaCha20` stream, through the cipher core (which serves all `2^32`
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

pub(super) fn drbg_trace(out: &mut String) {
    let mut rng = SplitMix64::traced(0xD2B6);
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

pub(super) fn provider_trace(out: &mut String) {
    let sw = Software;
    let mut rng = SplitMix64::traced(0x9807);
    for (ai, alg) in [Aead::ChaCha20Poly1305, Aead::Aes128Gcm].into_iter().enumerate() {
        for len in 0..=70usize {
            let key = rand(&mut rng, len);
            let k = sw.aead_key(alg, &key);
            let h = sw.hp_key(alg, &key);
            for (kind, r) in [
                ("aead", res(&k.as_ref().map(|_| ()).map_err(|e| *e))),
                ("hp", res(&h.as_ref().map(|_| ()).map_err(|e| *e))),
            ] {
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
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn hp_trace(out: &mut String) {
    let sw = Software;
    let mut rng = SplitMix64::traced(0x4850);
    // ChaCha20: the counters around the block boundaries and the end of the 32-bit counter, and the RFC 9001 vector
    let key: [u8; 32] = rand(&mut rng, 32).try_into().unwrap();
    let hp = sw.hp_key(Aead::ChaCha20Poly1305, &key).unwrap();
    let mut cases: Vec<([u8; 32], [u8; 16])> = Vec::new();
    for counter in [
        0u32,
        1,
        2,
        3,
        255,
        256,
        65535,
        65536,
        1 << 24,
        (1 << 31) - 1,
        1 << 31,
        u32::MAX - 1,
        u32::MAX,
    ] {
        let mut sample: [u8; 16] = rand(&mut rng, 16).try_into().unwrap();
        sample[..4].copy_from_slice(&counter.to_le_bytes());
        cases.push((key, sample));
    }
    cases.push((
        hex("25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4")
            .try_into()
            .unwrap(),
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
        .map(|_| {
            (
                rand(&mut rng, 16).try_into().unwrap(),
                rand(&mut rng, 16).try_into().unwrap(),
            )
        })
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
            &sw.hp_key(Aead::Aes128Gcm, &hex("9f50449e04a0e810283a1e9933adedd2"))
                .unwrap(),
            &hex("d1b1c98dd7689fb8ec11d242b123dc9b").try_into().unwrap(),
        )
        .to_vec();
    assert_eq!(kat, hex("437b9aec36"));
}

fn dh_trace(out: &mut String) {
    let sw = Software;
    let mut rng = SplitMix64::traced(0x25519);
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
    for len in [
        0usize,
        1,
        KEM_CIPHERTEXT_LEN - 1,
        KEM_CIPHERTEXT_LEN,
        KEM_CIPHERTEXT_LEN + 1,
    ] {
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

pub(super) fn secret_trace(out: &mut String) {
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
        let _ = writeln!(
            out,
            r#"{{"t":"cr","op":"cteq","a":{},"b":{},"eq":{r}}}"#,
            arr(&a),
            arr(&b)
        );
    }
    let a = Secret::<4>::new([1, 2, 3, 4]);
    let b = Secret::<4>::new([1, 2, 3, 4]);
    let c = Secret::<4>::new([1, 2, 3, 5]);
    assert!(a == b && a != c && a.clone() == a);
    assert_eq!(format!("{a:?}"), "Secret(..)");
    assert_eq!(format!("{c:?}"), format!("{a:?}"));
    let _ = writeln!(
        out,
        r#"{{"t":"cr","op":"secret","a":[1,2,3,4],"b":[1,2,3,4],"c":[1,2,3,5],"ab":true,"ac":false,"debug":"{a:?}"}}"#
    );
    for (n, after) in [
        (16usize, bytes_after_drop::<16>(0xAB)),
        (32, bytes_after_drop::<32>(0xCD)),
        (64, bytes_after_drop::<64>(0xEF)),
    ] {
        assert!(after.iter().all(|&x| x == 0), "a dropped Secret<{n}> still holds bytes");
        let _ = writeln!(out, r#"{{"t":"cr","op":"drop","n":{n},"after":{}}}"#, arr(&after));
    }
}
