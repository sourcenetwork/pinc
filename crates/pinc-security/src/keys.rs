//! The key-custody seam: requests the handshake cannot answer itself, and a software answerer.
//!
//! The handshake never touches a long-term key. It emits a [`KeyRequest`] (sign this message, decapsulate this
//! ciphertext) and accepts the [`KeyResponse`] whenever the host has it, so a slow device never blocks the state
//! machine. Invariants: a request is a pure description (a handle plus public bytes); a response is a signature or a
//! 32-byte secret, never a key. [`SoftKeys`] answers a request at once from software keys, so a software node pays
//! no extra round trip. A [`SoftPrekeys`] rotates its ML-KEM prekey after a lifetime or a number of uses, and the
//! rotated-out decapsulation key is dropped, which zeroizes it, so a later compromise of the node cannot open
//! handshakes of an earlier window.

use pinc_crypto::identity::MAX_SIGNATURE_LEN;
use pinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use pinc_crypto::{CryptoError, IdentityAlg, Keypair, Provider, Secret, Transcript};
use zeroize::Zeroize;

use crate::KeyHandle;
use crate::labels;
use crate::session::Env;

/// A host key operation the handshake is waiting for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeyRequest<'a> {
    /// Sign `message` with the identity key `key`, which uses `alg`.
    Sign {
        /// The identity key.
        key: KeyHandle,
        /// The signature algorithm the host must use.
        alg: IdentityAlg,
        /// The bytes to sign.
        message: &'a [u8],
    },
    /// Decapsulate `ct` with the prekey `key` and return the 32-byte shared secret.
    Decapsulate {
        /// The prekey.
        key: KeyHandle,
        /// The ML-KEM-768 ciphertext.
        ct: &'a [u8; KEM_CIPHERTEXT_LEN],
    },
}

/// The host's answer to a [`KeyRequest`].
#[derive(Debug)]
pub enum KeyResponse<'a> {
    /// The signature, for a [`KeyRequest::Sign`].
    Signature(&'a [u8]),
    /// The shared secret, for a [`KeyRequest::Decapsulate`].
    SharedSecret(Secret<32>),
    /// The host could not or would not perform the operation.
    Failed,
}

/// The hash of an encapsulation key, as the transcript and the responder's cache know it.
pub fn prekey_hash(encaps_key: &[u8]) -> [u8; 32] {
    let mut t = Transcript::with_label(labels::KEM_KEY_HASH);
    t.absorb("encaps_key", encaps_key);
    t.snapshot()
}

/// The public part of a prekey: the encapsulation key, its hash and the handle to decapsulate with.
#[derive(Clone)]
pub struct PrekeyInfo {
    pub(crate) encaps_key: [u8; KEM_ENCAPS_KEY_LEN],
    pub(crate) hash: [u8; 32],
    pub(crate) handle: KeyHandle,
}

impl core::fmt::Debug for PrekeyInfo {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PrekeyInfo")
            .field("handle", &self.handle)
            .finish_non_exhaustive()
    }
}

impl PrekeyInfo {
    /// The prekey with encapsulation key `encaps_key`, decapsulated by the host key `handle`.
    pub fn new(encaps_key: [u8; KEM_ENCAPS_KEY_LEN], handle: KeyHandle) -> Self {
        Self {
            hash: prekey_hash(&encaps_key),
            encaps_key,
            handle,
        }
    }

    /// The encapsulation key.
    pub const fn encaps_key(&self) -> &[u8; KEM_ENCAPS_KEY_LEN] {
        &self.encaps_key
    }

    /// The hash of the encapsulation key.
    pub const fn hash(&self) -> &[u8; 32] {
        &self.hash
    }

    /// The decapsulation key's handle.
    pub const fn handle(&self) -> KeyHandle {
        self.handle
    }
}

/// When a software prekey rotates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrekeyPolicy {
    /// The most nanoseconds a prekey is used for: 10 minutes by default.
    pub lifetime_ns: u64,
    /// The most handshakes one prekey serves: 64 by default.
    pub max_uses: u32,
}

impl Default for PrekeyPolicy {
    fn default() -> Self {
        Self {
            lifetime_ns: 600_000_000_000,
            max_uses: 64,
        }
    }
}

/// A semi-static ML-KEM-768 prekey held in software, rotated by [`PrekeyPolicy`].
///
/// The handle of a prekey is its generation number, so a request for a rotated-out key is refused rather than
/// answered with an unrelated secret.
pub struct SoftPrekeys<P: Provider> {
    dk: P::KemDecapsKey,
    info: PrekeyInfo,
    created_at: u64,
    uses: u32,
    policy: PrekeyPolicy,
}

impl<P: Provider> core::fmt::Debug for SoftPrekeys<P> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SoftPrekeys")
            .field("handle", &self.info.handle)
            .field("uses", &self.uses)
            .finish_non_exhaustive()
    }
}

impl<P: Provider> SoftPrekeys<P> {
    /// A first prekey, created at time `now`.
    ///
    /// # Errors
    /// [`CryptoError::InputTooLong`] if the generator refuses.
    pub fn new(env: &mut Env<'_, P>, policy: PrekeyPolicy) -> Result<Self, CryptoError> {
        let (dk, info) = Self::generate(env, 0)?;
        Ok(Self {
            dk,
            info,
            created_at: env.now,
            uses: 0,
            policy,
        })
    }

    fn generate(env: &mut Env<'_, P>, generation: u64) -> Result<(P::KemDecapsKey, PrekeyInfo), CryptoError> {
        let mut seeds = [[0u8; 32]; 2];
        for seed in &mut seeds {
            env.drbg.fill(seed)?;
        }
        let [d, z] = seeds;
        let (dk, ek) = env.provider.kem_keygen(&d, &z);
        seeds.zeroize();
        Ok((
            dk,
            PrekeyInfo::new(env.provider.kem_encaps_key_bytes(&ek), KeyHandle(generation)),
        ))
    }

    /// The prekey for one more handshake, rotating first if it is past its lifetime or its use count.
    ///
    /// # Errors
    /// [`CryptoError::InputTooLong`] if the generator refuses during a rotation.
    pub fn acquire(&mut self, env: &mut Env<'_, P>) -> Result<PrekeyInfo, CryptoError> {
        let due =
            self.uses >= self.policy.max_uses || env.now.saturating_sub(self.created_at) >= self.policy.lifetime_ns;
        if due {
            let (dk, info) = Self::generate(env, self.info.handle.0.wrapping_add(1))?;
            // Assigning drops the old decapsulation key, which zeroizes it.
            self.dk = dk;
            self.info = info;
            self.created_at = env.now;
            self.uses = 0;
        }
        self.uses = self.uses.saturating_add(1);
        Ok(self.info.clone())
    }

    /// The handle of the current prekey.
    pub const fn handle(&self) -> KeyHandle {
        self.info.handle
    }

    /// How many handshakes the current prekey served.
    pub const fn uses(&self) -> u32 {
        self.uses
    }

    /// Decapsulate `ct` with the prekey named by `handle`.
    ///
    /// # Errors
    /// [`CryptoError::InvalidSecretKey`] if `handle` names a rotated-out or unknown prekey.
    pub fn decapsulate(
        &self,
        p: &P,
        handle: KeyHandle,
        ct: &[u8; KEM_CIPHERTEXT_LEN],
    ) -> Result<Secret<32>, CryptoError> {
        if handle != self.info.handle {
            return Err(CryptoError::InvalidSecretKey);
        }
        p.kem_decapsulate(&self.dk, &p.kem_ciphertext(ct)?)
    }
}

/// Software keys that answer a [`KeyRequest`] in the same call.
#[derive(Debug)]
pub struct SoftKeys<'a, P: Provider> {
    /// The identity key pair and the handle it answers to.
    pub signer: Option<(KeyHandle, &'a Keypair)>,
    /// The prekeys.
    pub prekeys: Option<&'a SoftPrekeys<P>>,
}

impl<P: Provider> SoftKeys<'_, P> {
    /// Answer `req`. A signature is written into `sig_buf` and returned as a slice of it; a request this store
    /// cannot serve gets [`KeyResponse::Failed`].
    pub fn answer<'b>(
        &self,
        env: &mut Env<'_, P>,
        req: &KeyRequest<'_>,
        sig_buf: &'b mut [u8; MAX_SIGNATURE_LEN],
    ) -> KeyResponse<'b> {
        match *req {
            KeyRequest::Sign { key, alg, message } => {
                let Some((handle, pair)) = self.signer else {
                    return KeyResponse::Failed;
                };
                let Ok(rnd) = env.random::<32>() else {
                    return KeyResponse::Failed;
                };
                let signed = (handle == key && pair.alg() == alg)
                    .then(|| pair.sign_with_rnd(message, &rnd, sig_buf.as_mut_slice()).ok())
                    .flatten();
                match signed.and_then(|n| sig_buf.get(..n)) {
                    Some(sig) => KeyResponse::Signature(sig),
                    None => KeyResponse::Failed,
                }
            }
            KeyRequest::Decapsulate { key, ct } => self
                .prekeys
                .and_then(|k| k.decapsulate(env.provider, key, ct).ok())
                .map_or(KeyResponse::Failed, KeyResponse::SharedSecret),
        }
    }
}
