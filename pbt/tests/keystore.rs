//! `pinc-keystore`: the software store driven by generated operation sequences against a model, and the sealed
//! envelope under every change of its bytes.
//!
//! Where the expected behaviour comes from:
//! - crate doc: "Signatures come back in the exact form [`pinc_crypto::identity::verify`] accepts for the key's
//!   algorithm"; "Handles are unique across stores in a process; a handle presented to another store is
//!   [`KeyStoreError::UnknownKey`]";
//! - `SoftwareStore::remove`: "Drop a key ... returns whether it was present"; `KeyStore::public`, `node_id`;
//! - `sealed`: "Layout: `header || nonce (12) || ciphertext || tag (16)`. The whole header is authenticated", so
//!   `unseal` gives back exactly what `seal` took and refuses (`InvalidSealed`) any other bytes;
//! - `SoftwareStore::from_entropy`: "the same entropy gives the same keys, nonces and sealing key".
#![allow(clippy::unwrap_used, clippy::indexing_slicing, missing_docs)]

use ephyra::prelude::*;
use pinc_crypto::identity::verify;
use pinc_crypto::provider::KEM_CIPHERTEXT_LEN;
use pinc_crypto::{IdentityAlg, Provider, Software};
use pinc_keystore::{KeyHandle, KeyStore, KeyStoreError, SoftwareStore};
use pinc_pbt::bytes;

const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Op {
    Generate(#[ephyra(gen = gens::frequency(vec![(5, gens::int(0u8..=1).boxed()), (1, gens::int(2u8..=3).boxed())]))] u8),
    GenerateKem,
    Remove(#[ephyra(gen = gens::int(0u8..=15))] u8),
    Sign(#[ephyra(gen = gens::int(0u8..=15))] u8, #[ephyra(gen = bytes(64))] Vec<u8>),
    Decapsulate(#[ephyra(gen = gens::int(0u8..=15))] u8, #[ephyra(gen = gens::int(0u8..=255))] u8),
    Seal(#[ephyra(gen = bytes(200))] Vec<u8>),
    /// Unseal a sealed value as it is, or with one change: a flipped bit, a cut, bytes appended, another version byte.
    Unseal(
        #[ephyra(gen = gens::int(0u8..=15))] u8,
        #[ephyra(gen = gens::int(0u8..=4))] u8,
        #[ephyra(gen = gens::int(0usize..=400))] usize,
        #[ephyra(gen = gens::int(1u8..=255))] u8,
    ),
    Reseed(#[ephyra(gen = gens::int(0u8..=255))] u8),
    Random(#[ephyra(gen = gens::int(0usize..=100))] usize),
    /// Present a handle of this store to the other store.
    Foreign(#[ephyra(gen = gens::int(0u8..=15))] u8),
}

enum Kind {
    Identity(IdentityAlg),
    Kem([u8; pinc_crypto::provider::KEM_ENCAPS_KEY_LEN]),
}

#[ephyra::test(gen = (gens::int(0u8..=255), gens::vec(ephyra::any::<Op>()).len(0..=30)), tests = 300)]
fn software_store_against_a_model(x: (u8, Vec<Op>)) {
    let (seed, ops) = x;
    let mut st = SoftwareStore::from_entropy([seed; 32]);
    let mut other = SoftwareStore::from_entropy([seed; 32]);
    let mut keys: Vec<(KeyHandle, Kind, bool)> = Vec::new();
    let mut sealed: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    for op in &ops {
        match op {
            Op::Generate(a) => {
                let alg = ALGS[usize::from(*a)];
                let h = st.generate(alg).unwrap();
                assert!(keys.iter().all(|(k, ..)| *k != h), "a handle was issued twice");
                keys.push((h, Kind::Identity(alg), true));
            }
            Op::GenerateKem => {
                let (h, ek) = st.generate_kem().unwrap();
                keys.push((h, Kind::Kem(ek), true));
            }
            Op::Remove(i) => {
                let n = keys.len().max(1);
                if let Some((h, _, live)) = keys.get_mut(usize::from(*i) % n) {
                    assert_eq!(st.remove(h), *live, "remove did not report whether the key was there");
                    *live = false;
                }
            }
            Op::Sign(i, msg) => {
                if let Some((h, kind, live)) = keys.get(usize::from(*i) % keys.len().max(1)) {
                    let r = st.sign(h, msg);
                    match (kind, *live) {
                        (_, false) => assert_eq!(r.err(), Some(KeyStoreError::UnknownKey)),
                        (Kind::Kem(_), true) => assert_eq!(r.err(), Some(KeyStoreError::WrongKeyKind)),
                        (Kind::Identity(alg), true) => {
                            let sig = r.unwrap();
                            assert_eq!(sig.alg(), *alg);
                            let (palg, pk) = st.public(h).unwrap();
                            assert_eq!(palg, *alg);
                            assert_eq!(verify(*alg, &pk, msg, sig.as_bytes()), Ok(()), "a store signature does not verify");
                            let id = st.node_id(h).unwrap();
                            assert!(id.matches(*alg, &pk), "node_id is not the id of the public key");
                        }
                    }
                }
            }
            Op::Decapsulate(i, m) => {
                if let Some((h, kind, live)) = keys.get(usize::from(*i) % keys.len().max(1)) {
                    match (kind, *live) {
                        (Kind::Kem(ek), true) => {
                            let p = Software;
                            let ek = p.kem_encaps_key(ek).unwrap();
                            let (ct, ss) = p.kem_encapsulate(&ek, &[*m; 32]).unwrap();
                            let got = st.decapsulate(h, &p.kem_ciphertext_bytes(&ct)).unwrap();
                            assert_eq!(got, ss, "decapsulation gives another secret");
                            let short = st.decapsulate(h, &[0u8; KEM_CIPHERTEXT_LEN - 1]);
                            assert!(short.is_err(), "a short ciphertext was taken");
                        }
                        (Kind::Identity(_), true) => {
                            let r = st.decapsulate(h, &[0u8; KEM_CIPHERTEXT_LEN]);
                            assert_eq!(r.err(), Some(KeyStoreError::WrongKeyKind));
                        }
                        (_, false) => {
                            let r = st.decapsulate(h, &[0u8; KEM_CIPHERTEXT_LEN]);
                            assert_eq!(r.err(), Some(KeyStoreError::UnknownKey));
                        }
                    }
                }
            }
            Op::Seal(pt) => {
                let s = st.seal(pt).unwrap();
                assert_eq!(s.len(), 1 + 12 + pt.len() + 16, "the envelope is not header, nonce, body and tag");
                assert!(sealed.iter().all(|(_, b)| b[1..13] != s[1..13]), "a sealing nonce repeated");
                sealed.push((pt.clone(), s));
            }
            Op::Unseal(i, how, at, x) => {
                if let Some((pt, s)) = sealed.get(usize::from(*i) % sealed.len().max(1)) {
                    let mut b = s.clone();
                    match how {
                        0 => {}
                        1 => {
                            let j = at % b.len();
                            b[j] ^= x;
                        }
                        2 => b.truncate(at % b.len()),
                        3 => b.push(*x),
                        _ => b[0] = b[0].wrapping_add(*x),
                    }
                    let r = st.unseal(&b);
                    if *how == 0 {
                        assert_eq!(r.as_deref().map(|v| v.as_slice()), Ok(pt.as_slice()), "unseal did not give back");
                    } else {
                        assert_eq!(r.err(), Some(KeyStoreError::InvalidSealed), "a changed envelope was taken");
                    }
                    // A store made from the same entropy has the same sealing key, whatever was reseeded since.
                    let r2 = other.unseal(s);
                    assert_eq!(r2.as_deref().map(|v| v.as_slice()), Ok(pt.as_slice()), "the twin store cannot unseal");
                }
            }
            Op::Reseed(e) => st.reseed(&[*e; 32]),
            Op::Random(n) => {
                let mut a = vec![0u8; *n];
                st.random(&mut a).unwrap();
            }
            Op::Foreign(i) => {
                if let Some((h, ..)) = keys.get(usize::from(*i) % keys.len().max(1)) {
                    assert_eq!(other.sign(h, b"m").err(), Some(KeyStoreError::UnknownKey), "another store took a handle");
                    assert_eq!(other.public(h).err(), Some(KeyStoreError::UnknownKey));
                }
            }
        }
    }
}

#[ephyra::test(gen = (gens::int(0u8..=255), bytes(100)), tests = 300)]
fn the_same_entropy_gives_the_same_sealing_key_and_another_does_not(x: (u8, Vec<u8>)) {
    let (seed, pt) = x;
    let mut a = SoftwareStore::from_entropy([seed; 32]);
    let mut b = SoftwareStore::from_entropy([seed; 32]);
    let mut c = SoftwareStore::from_entropy([seed.wrapping_add(1); 32]);
    let s = a.seal(&pt).unwrap();
    assert_eq!(b.unseal(&s).as_deref().map(|v| v.as_slice()), Ok(pt.as_slice()));
    assert_eq!(c.unseal(&s).err(), Some(KeyStoreError::InvalidSealed), "another store opened the envelope");
}

#[ephyra::test(gen = pinc_pbt::mostly_valid(|g: &mut Source| {
    let pt = g.draw(&bytes(60));
    SoftwareStore::from_entropy([7; 32]).seal(&pt).unwrap()
}), tests = 20_000)]
fn unseal_of_hostile_bytes_never_panics_and_takes_only_genuine_envelopes(b: Vec<u8>) {
    let mut st = SoftwareStore::from_entropy([7; 32]);
    if let Ok(pt) = st.unseal(&b) {
        // A genuine envelope of this store: its length says so.
        assert_eq!(b.len(), 1 + 12 + pt.len() + 16);
    }
}
