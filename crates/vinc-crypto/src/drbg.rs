//! A deterministic random bit generator: `ChaCha20` with fast key erasure.
//!
//! Invariants: the generator holds a 32-byte key and nothing else. Every [`Drbg::fill`] derives the next key and
//! the output from one `ChaCha20` stream, replaces the key and wipes the old one, so a later state compromise reveals
//! no earlier output. The crate never reads entropy itself: the host seeds and reseeds with 32 bytes, and the same
//! seed always gives the same stream.

use chacha20::ChaCha20;
use chacha20::cipher::{KeyIvInit, StreamCipher};
use zeroize::Zeroize;

use crate::{CryptoError, Secret};

/// The most bytes one [`Drbg::fill`] call produces, so the 32-bit block counter cannot wrap.
pub const MAX_FILL: usize = 1 << 30;

/// A `ChaCha20` DRBG with fast key erasure.
#[derive(Debug)]
pub struct Drbg {
    key: Secret<32>,
}

impl Drbg {
    /// A generator seeded with 32 bytes of host entropy.
    pub const fn new(seed: &[u8; 32]) -> Self {
        Self {
            key: Secret::new(*seed),
        }
    }

    /// Mix 32 more bytes of host entropy into the state.
    ///
    /// The new key is the old key combined by XOR with the entropy, so the state is at least as unpredictable as the better of
    /// the two.
    pub fn reseed(&mut self, entropy: &[u8; 32]) {
        let mut next = *self.key.expose();
        for (k, e) in next.iter_mut().zip(entropy) {
            *k ^= e;
        }
        self.key = Secret::new(next);
        next.zeroize();
    }

    /// Fill `out` with pseudo-random bytes, then re-key from the stream.
    ///
    /// # Errors
    /// [`CryptoError::InputTooLong`] if `out` is longer than [`MAX_FILL`]; the state is unchanged.
    pub fn fill(&mut self, out: &mut [u8]) -> Result<(), CryptoError> {
        if out.len() > MAX_FILL {
            return Err(CryptoError::InputTooLong);
        }
        // The key changes after every call, so a constant nonce never repeats a (key, nonce) pair.
        let mut cipher = ChaCha20::new(self.key.expose().into(), &[0u8; 12].into());
        let mut next = [0u8; 32];
        let result = cipher
            .try_write_keystream(&mut next)
            .and_then(|()| cipher.try_write_keystream(out))
            .map_err(|_| CryptoError::InputTooLong);
        if result.is_ok() {
            self.key = Secret::new(next);
        } else {
            out.zeroize();
        }
        next.zeroize();
        result
    }
}
