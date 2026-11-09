//! A signer's public key and signature over a domain-separated digest.
//!
//! Invariants: the signed message is the 32-byte transcript hash of `body` under a label from [`crate::labels`], so
//! a signature made for one kind of message never verifies as another; the public key travels with the signature
//! because a node id of every algorithm but Ed25519 is only a hash of it, and verification checks that the key
//! belongs to the claimed node id before it checks the signature; lengths are exact for the algorithm.

use vinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN, verify_node};
use vinc_crypto::{IdentityAlg, Keypair, NodeId, Transcript};
use vinc_wire::{Reader, Writer};

use crate::error::DtnError;

/// A signer's public key and the signature, both zero-padded to the longest algorithm.
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Endorsement {
    pk: [u8; MAX_PUBLIC_KEY_LEN],
    pk_len: u16,
    sig: [u8; MAX_SIGNATURE_LEN],
    sig_len: u16,
}

impl core::fmt::Debug for Endorsement {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Endorsement(..)")
    }
}

fn digest(label: &'static str, body: &[u8]) -> [u8; 32] {
    let mut t = Transcript::with_label(label);
    t.absorb(body);
    t.snapshot()
}

impl Endorsement {
    /// Sign `body` under `label` with `signer`.
    pub(crate) fn sign(signer: &Keypair, label: &'static str, body: &[u8]) -> Result<Self, DtnError> {
        let mut pk = [0u8; MAX_PUBLIC_KEY_LEN];
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let pk_len = signer.public_key(&mut pk)?;
        let sig_len = signer.sign(&digest(label, body), &mut sig)?;
        Ok(Self {
            pk,
            pk_len: u16::try_from(pk_len).map_err(|_| DtnError::Params)?,
            sig,
            sig_len: u16::try_from(sig_len).map_err(|_| DtnError::Params)?,
        })
    }

    /// Check that this is `signer`'s signature over `body` under `label`.
    pub(crate) fn verify(&self, signer: &NodeId, label: &'static str, body: &[u8]) -> Result<(), DtnError> {
        let pk = self.pk.get(..usize::from(self.pk_len)).ok_or(DtnError::Params)?;
        let sig = self.sig.get(..usize::from(self.sig_len)).ok_or(DtnError::Params)?;
        verify_node(signer, pk, &digest(label, body), sig)?;
        Ok(())
    }

    /// The encoded size for an algorithm: two `u16` lengths, the key and the signature.
    pub(crate) const fn encoded_len(alg: IdentityAlg) -> usize {
        4 + alg.public_key_len() + alg.signature_len()
    }

    pub(crate) fn encode(&self, w: &mut Writer<'_>) -> Result<(), DtnError> {
        w.put_u16(self.pk_len)?;
        w.put_slice(self.pk.get(..usize::from(self.pk_len)).ok_or(DtnError::Params)?)?;
        w.put_u16(self.sig_len)?;
        w.put_slice(self.sig.get(..usize::from(self.sig_len)).ok_or(DtnError::Params)?)?;
        Ok(())
    }

    /// Decode, requiring the exact lengths of `alg`.
    pub(crate) fn decode(alg: IdentityAlg, r: &mut Reader<'_>) -> Result<Self, DtnError> {
        let mut out = Self {
            pk: [0; MAX_PUBLIC_KEY_LEN],
            pk_len: 0,
            sig: [0; MAX_SIGNATURE_LEN],
            sig_len: 0,
        };
        let pk_len = r.read_u16()?;
        if usize::from(pk_len) != alg.public_key_len() {
            return Err(DtnError::Params);
        }
        out.pk
            .get_mut(..usize::from(pk_len))
            .ok_or(DtnError::Params)?
            .copy_from_slice(r.read_bytes(usize::from(pk_len))?);
        let sig_len = r.read_u16()?;
        if usize::from(sig_len) != alg.signature_len() {
            return Err(DtnError::Params);
        }
        out.sig
            .get_mut(..usize::from(sig_len))
            .ok_or(DtnError::Params)?
            .copy_from_slice(r.read_bytes(usize::from(sig_len))?);
        out.pk_len = pk_len;
        out.sig_len = sig_len;
        Ok(out)
    }
}
