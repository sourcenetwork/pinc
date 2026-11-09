//! Scaffolding shared by the delay-tolerant delivery tests: keys, bundles and receptions.
#![allow(
    dead_code,
    missing_docs,
    unreachable_pub,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::assert_is_empty,
    clippy::similar_names,
    clippy::trivially_copy_pass_by_ref,
    clippy::struct_field_names,
    clippy::cast_lossless,
    clippy::range_plus_one,
    clippy::many_single_char_names,
    clippy::items_after_statements,
    clippy::needless_pass_by_value
)]

use vinc_crypto::{IdentityAlg, Keypair, Provider, Secret, Software};
use vinc_dtn::bundle::{Outgoing, Plan, seal_bundle, serve, serve_len};
use vinc_dtn::head::{Erasure, SignedHead};
use vinc_dtn::hlc::Hlc;
use vinc_dtn::seal::{RecipientKeys, SealSeeds};
use vinc_tests::SplitMix64;

pub const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

pub type KemDk = <Software as Provider>::KemDecapsKey;
pub type XSecret = <Software as Provider>::X25519Secret;

pub fn bytes(seed: u64, len: usize) -> Vec<u8> {
    let mut v = vec![0; len];
    SplitMix64::new(seed).fill(&mut v);
    v
}

pub fn keypair(alg: IdentityAlg, seed: u64) -> Keypair {
    Keypair::from_seed(alg, &bytes(seed, alg.seed_len())).unwrap()
}

pub struct Recipient {
    pub id: Keypair,
    pub keys: RecipientKeys,
    pub dk: KemDk,
    pub xs: XSecret,
}

pub fn recipient(alg: IdentityAlg, seed: u64, epoch: u32) -> Recipient {
    let p = Software;
    let id = keypair(alg, seed);
    let d: [u8; 32] = bytes(seed + 1, 32).try_into().unwrap();
    let z: [u8; 32] = bytes(seed + 2, 32).try_into().unwrap();
    let (dk, ek) = p.kem_keygen(&d, &z);
    let xs = p.x25519_secret(&bytes(seed + 3, 32).try_into().unwrap());
    let keys = RecipientKeys {
        node: id.node_id(),
        epoch,
        kem_ek: p.kem_encaps_key_bytes(&ek),
        x25519: p.x25519_public(&xs),
    };
    Recipient { id, keys, dk, xs }
}

pub fn seeds(seed: u64) -> SealSeeds {
    SealSeeds {
        eph_x25519: Secret::new(bytes(seed, 32).try_into().unwrap()),
        kem_m: Secret::new(bytes(seed + 1, 32).try_into().unwrap()),
    }
}

pub fn plan(k: u8, m: u8, slice_log: u8) -> Plan {
    Plan {
        created: Hlc::new(1_000, 0),
        lifetime_ms: 60_000,
        copies: 8,
        erasure: Erasure { k, m },
        slice_log,
    }
}

/// A sealed bundle with everything a relay holds.
pub struct Sealed {
    pub signed: SignedHead,
    pub sealed: Vec<u8>,
    pub outboard: Vec<u8>,
    pub payload: Vec<u8>,
}

pub fn make(signer: &Keypair, to: &Recipient, plan: Plan, payload: &[u8], seed: u64) -> Sealed {
    let seeds = seeds(seed);
    let out = Outgoing {
        recipient: &to.keys,
        plan,
        seeds: &seeds,
    };
    let layout =
        vinc_dtn::layout::SliceLayout::new(plan.erasure.k, plan.erasure.m, plan.slice_log, payload.len() as u64)
            .unwrap();
    let mut sealed = vec![0xaa; layout.total_len() as usize];
    let mut outboard = vec![0; layout.outboard_len().unwrap() as usize];
    let signed = seal_bundle(&Software, signer, &out, payload, &mut sealed, &mut outboard).unwrap();
    Sealed {
        signed,
        sealed,
        outboard,
        payload: payload.to_vec(),
    }
}

impl Sealed {
    /// The proof stream for `symbols`.
    pub fn proof(&self, symbols: std::ops::Range<u64>) -> Vec<u8> {
        let layout = self.signed.head().layout().unwrap();
        let mut out = vec![0; serve_len(&layout, &symbols).unwrap()];
        assert_eq!(
            serve(&layout, &self.sealed, &self.outboard, &symbols, &mut out).unwrap(),
            out.len()
        );
        out
    }
}
