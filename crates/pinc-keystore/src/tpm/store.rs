//! [`TpmStore`]: a [`KeyStore`] whose identity keys and sealing key live in a TPM 2.0.

use std::collections::HashMap;
use std::net::ToSocketAddrs;
use std::vec;
use std::vec::Vec;

use p256::ecdsa::{Signature as P256Signature, VerifyingKey};
use tpm2_protocol::TpmUnmarshal;
use tpm2_protocol::data::{Tpm2bPrivate, Tpm2bPublic};
use pinc_crypto::{IdentityAlg, Provider, Secret, Software};
use zeroize::Zeroizing;

use super::client::{Blob, EccPoint, MAX_AUTH_LEN, RC_INITIALIZE, TpmClient};
use super::template;
use super::transport::{DeviceTransport, SimTransport, Transport};
use crate::{KeyHandle, KeyStore, KeyStoreError, Result, Signature, sealed};

/// The first byte of a TPM-sealed value.
const VERSION: u8 = 2;
/// Persistent handles live in `0x8100_0000..=0x81FF_FFFF` (`TPM_HT_PERSISTENT`, owner range).
const PERSISTENT: core::ops::RangeInclusive<u32> = 0x8100_0000..=0x81FF_FFFF;
const NONCE_LEN: usize = 12;

/// Auth values for a [`TpmStore`]. The defaults are empty, as on a TPM nobody has taken ownership of.
#[derive(Clone, Default)]
pub struct TpmConfig {
    owner_auth: Zeroizing<Vec<u8>>,
    key_auth: Zeroizing<Vec<u8>>,
}

impl core::fmt::Debug for TpmConfig {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("TpmConfig(..)")
    }
}

impl TpmConfig {
    fn validate(&self) -> Result<()> {
        if self.owner_auth.len() > MAX_AUTH_LEN || self.key_auth.len() > MAX_AUTH_LEN {
            return Err(KeyStoreError::InvalidAuth);
        }
        Ok(())
    }

    /// Empty auth values.
    pub fn new() -> Self {
        Self::default()
    }

    /// The owner hierarchy's auth value, used to create the storage key and to make keys persistent.
    #[must_use]
    pub fn owner_auth(mut self, auth: &[u8]) -> Self {
        self.owner_auth = Zeroizing::new(auth.to_vec());
        self
    }

    /// The auth value given to every key and sealed object this store creates, and presented to use them.
    #[must_use]
    pub fn key_auth(mut self, auth: &[u8]) -> Self {
        self.key_auth = Zeroizing::new(auth.to_vec());
        self
    }
}

struct Slot {
    handle: u32,
    persistent: bool,
    public: [u8; 33],
}

/// A [`KeyStore`] over a TPM 2.0.
///
/// It holds ECDSA P-256 identity keys (created in the TPM, never exported) and seals data under a TPM-protected
/// key. [`KeyStore::decapsulate`] and every other algorithm are [`KeyStoreError::Unsupported`]: keep those keys in a
/// [`SoftwareStore`](crate::SoftwareStore).
///
/// Dropping the store flushes its transient handles; a failure to flush then cannot be reported, and the TPM
/// reclaims the handle when its resource manager closes the session.
pub struct TpmStore<T: Transport> {
    client: TpmClient<T>,
    config: TpmConfig,
    primary: u32,
    keys: HashMap<u64, Slot>,
    /// Transient handles whose flush the TPM refused, retried before the next command that loads an object.
    stale: Vec<u32>,
}

/// The most refused-flush handles remembered; a TPM holds only a few transient objects, so more is a wedged TPM.
const MAX_STALE: usize = 8;

impl<T: Transport> core::fmt::Debug for TpmStore<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("TpmStore(..)")
    }
}

fn compress(point: &EccPoint) -> Result<[u8; 33]> {
    let mut sec1 = Vec::with_capacity(65);
    sec1.push(4);
    sec1.extend_from_slice(&point.x);
    sec1.extend_from_slice(&point.y);
    let vk = VerifyingKey::from_sec1_bytes(&sec1).map_err(|_| pinc_crypto::CryptoError::InvalidPublicKey)?;
    <[u8; 33]>::try_from(vk.to_sec1_point(true).as_bytes())
        .map_err(|_| pinc_crypto::CryptoError::InvalidPublicKey.into())
}

/// Parse `version || private || public` off the front of a sealed value; returns the blob and the header length.
fn parse_sealed(sealed: &[u8]) -> Result<(Blob, usize)> {
    let invalid = |_| KeyStoreError::InvalidSealed;
    let (&version, body) = sealed.split_first().ok_or(KeyStoreError::InvalidSealed)?;
    if version != VERSION {
        return Err(KeyStoreError::InvalidSealed);
    }
    let (_, after_private) = Tpm2bPrivate::unmarshal(body).map_err(invalid)?;
    let (_, after_public) = Tpm2bPublic::unmarshal(after_private).map_err(invalid)?;
    let private_len = body.len() - after_private.len();
    let public_len = after_private.len() - after_public.len();
    let (private, rest) = body.split_at_checked(private_len).ok_or(KeyStoreError::InvalidSealed)?;
    let (public, _) = rest.split_at_checked(public_len).ok_or(KeyStoreError::InvalidSealed)?;
    let blob = Blob {
        private: private.to_vec(),
        public: public.to_vec(),
    };
    Ok((blob, 1 + private_len + public_len))
}

impl TpmStore<DeviceTransport> {
    /// Open a store on the kernel resource manager, `/dev/tpmrm0`.
    ///
    /// # Errors
    /// [`KeyStoreError::Transport`] if the device cannot be opened; otherwise as [`TpmStore::open`].
    pub fn open_device(config: TpmConfig) -> Result<Self> {
        let device =
            DeviceTransport::open(DeviceTransport::RESOURCE_MANAGER).map_err(|e| KeyStoreError::Transport(e.kind()))?;
        Self::open(device, config)
    }
}

impl TpmStore<SimTransport> {
    /// Open a store on a TPM simulator: connect to its command port (and, if it has one, power it on through
    /// `platform`), start it with `TPM2_Startup(CLEAR)` (a simulator that is already running is fine), then
    /// [`TpmStore::open`].
    ///
    /// # Errors
    /// [`KeyStoreError::Transport`] if a port cannot be reached; otherwise as [`TpmStore::open`].
    pub fn connect_simulator<A: ToSocketAddrs>(command: A, platform: Option<A>, config: TpmConfig) -> Result<Self> {
        config.validate()?;
        let sim = match platform {
            Some(platform) => SimTransport::power_on(command, platform),
            None => SimTransport::connect(command),
        }
        .map_err(|e| KeyStoreError::Transport(e.kind()))?;
        let mut client = TpmClient::new(sim);
        match client.startup_clear() {
            Ok(()) | Err(KeyStoreError::Tpm { code: RC_INITIALIZE }) => {}
            Err(e) => return Err(e),
        }
        Self::from_client(client, config)
    }
}

impl<T: Transport> TpmStore<T> {
    /// Open a store over `transport`: validate the auth values and create the storage key.
    ///
    /// # Errors
    /// [`KeyStoreError::InvalidAuth`] for an over-long auth value; a TPM or transport failure.
    pub fn open(transport: T, config: TpmConfig) -> Result<Self> {
        config.validate()?;
        Self::from_client(TpmClient::new(transport), config)
    }

    fn from_client(mut client: TpmClient<T>, config: TpmConfig) -> Result<Self> {
        let primary = client.create_primary(&config.owner_auth)?;
        Ok(Self {
            client,
            config,
            primary,
            keys: HashMap::new(),
            stale: Vec::new(),
        })
    }

    /// The command client, for commands the store does not wrap.
    pub fn client_mut(&mut self) -> &mut TpmClient<T> {
        &mut self.client
    }

    /// The TPM handle behind `key`.
    pub fn tpm_handle(&self, key: &KeyHandle) -> Option<u32> {
        self.keys.get(&key.id()).map(|s| s.handle)
    }

    /// Flush the transient `handle`; if the TPM refuses, remember it so [`Self::reclaim`] tries again.
    fn discard(&mut self, handle: u32) -> Result<()> {
        let flushed = self.client.flush_context(handle);
        if flushed.is_err() && self.stale.len() < MAX_STALE {
            self.stale.push(handle);
        }
        flushed
    }

    /// Retry the flushes the TPM refused earlier, so a transient refusal does not strand a handle.
    fn reclaim(&mut self) {
        for handle in std::mem::take(&mut self.stale) {
            // A refusal puts the handle back on the list.
            let _ = self.discard(handle);
        }
    }

    /// Create an identity key of `alg` inside the TPM and load it.
    ///
    /// # Errors
    /// [`KeyStoreError::Unsupported`] unless `alg` is [`IdentityAlg::EcdsaP256`]; a TPM or transport failure.
    pub fn generate(&mut self, alg: IdentityAlg) -> Result<KeyHandle> {
        if alg != IdentityAlg::EcdsaP256 {
            return Err(KeyStoreError::Unsupported);
        }
        self.reclaim();
        let blob = self.client.create(
            self.primary,
            &[],
            template::p256_signing_key(),
            &self.config.key_auth,
            &[],
        )?;
        let handle = self.client.load(self.primary, &[], &blob)?;
        self.register(handle, false)
    }

    /// Load the persistent key at `handle`.
    ///
    /// # Errors
    /// [`KeyStoreError::InvalidHandle`] outside the persistent range; a TPM failure such as `TPM_RC_HANDLE` if
    /// nothing lives there.
    pub fn load_persistent(&mut self, handle: u32) -> Result<KeyHandle> {
        if !PERSISTENT.contains(&handle) {
            return Err(KeyStoreError::InvalidHandle);
        }
        self.register(handle, true)
    }

    /// Make `key` persistent at `at`, so a later run can find it with [`TpmStore::load_persistent`].
    ///
    /// # Errors
    /// [`KeyStoreError::InvalidHandle`] if `at` is outside the persistent range or `key` is already persistent;
    /// a TPM failure such as `TPM_RC_NV_DEFINED` if `at` is taken.
    pub fn persist(&mut self, key: &KeyHandle, at: u32) -> Result<()> {
        if !PERSISTENT.contains(&at) {
            return Err(KeyStoreError::InvalidHandle);
        }
        let slot = self.keys.get(&key.id()).ok_or(KeyStoreError::UnknownKey)?;
        if slot.persistent {
            return Err(KeyStoreError::InvalidHandle);
        }
        let transient = slot.handle;
        self.client.evict_control(&self.config.owner_auth, transient, at)?;
        self.client.flush_context(transient)?;
        if let Some(slot) = self.keys.get_mut(&key.id()) {
            slot.handle = at;
            slot.persistent = true;
        }
        Ok(())
    }

    /// Read the public key of the object at `handle` and record it; on failure a transient `handle` is flushed.
    fn register(&mut self, handle: u32, persistent: bool) -> Result<KeyHandle> {
        let public = self.client.read_public(handle).and_then(|p| compress(&p));
        let public = match public {
            Ok(p) => p,
            Err(e) => {
                if !persistent {
                    // The read failure is the error to report; a refused flush is remembered, not reported.
                    let _ = self.discard(handle);
                }
                return Err(e);
            }
        };
        let key = KeyHandle::next();
        self.keys.insert(
            key.id(),
            Slot {
                handle,
                persistent,
                public,
            },
        );
        Ok(key)
    }

    fn slot(&self, key: &KeyHandle) -> Result<&Slot> {
        self.keys.get(&key.id()).ok_or(KeyStoreError::UnknownKey)
    }
}

impl<T: Transport> Drop for TpmStore<T> {
    fn drop(&mut self) {
        // Best effort: a destructor cannot report, and the resource manager reclaims leftovers on close.
        for slot in self.keys.values().filter(|s| !s.persistent) {
            let _ = self.client.flush_context(slot.handle);
        }
        let _ = self.client.flush_context(self.primary);
        for handle in &self.stale {
            let _ = self.client.flush_context(*handle);
        }
    }
}

impl<T: Transport> KeyStore for TpmStore<T> {
    fn sign(&mut self, key: &KeyHandle, msg: &[u8]) -> Result<Signature> {
        let handle = self.slot(key)?.handle;
        let digest = Software.sha256(msg);
        let (r, s) = self.client.sign_p256(handle, &self.config.key_auth, &digest)?;
        let mut rs = [0u8; 64];
        let (lo, hi) = rs.split_at_mut(32);
        lo.copy_from_slice(&r);
        hi.copy_from_slice(&s);
        let sig = P256Signature::from_slice(&rs).map_err(|_| pinc_crypto::CryptoError::InvalidSignature)?;
        Ok(Signature::new(
            IdentityAlg::EcdsaP256,
            sig.normalize_s().to_bytes().as_slice().to_vec(),
        ))
    }

    fn public(&self, key: &KeyHandle) -> Result<(IdentityAlg, Vec<u8>)> {
        Ok((IdentityAlg::EcdsaP256, self.slot(key)?.public.to_vec()))
    }

    fn decapsulate(&mut self, _key: &KeyHandle, _ct: &[u8]) -> Result<Secret<32>> {
        Err(KeyStoreError::Unsupported)
    }

    fn random(&mut self, out: &mut [u8]) -> Result<()> {
        self.client.fill_random(out)
    }

    fn seal(&mut self, plaintext: &[u8]) -> Result<Vec<u8>> {
        let mut dek = Zeroizing::new([0u8; sealed::KEY_LEN]);
        self.client.fill_random(dek.as_mut_slice())?;
        let mut nonce = [0u8; NONCE_LEN];
        self.client.fill_random(&mut nonce)?;
        let blob = self.client.create(
            self.primary,
            &[],
            template::sealed_data(),
            &self.config.key_auth,
            dek.as_slice(),
        )?;
        let mut header = vec![VERSION];
        header.extend_from_slice(&blob.private);
        header.extend_from_slice(&blob.public);
        sealed::encrypt(&Secret::new(*dek), &header, nonce, plaintext)
    }

    fn unseal(&mut self, sealed: &[u8]) -> Result<Zeroizing<Vec<u8>>> {
        let (blob, header_len) = parse_sealed(sealed)?;
        self.reclaim();
        let handle = self.client.load(self.primary, &[], &blob)?;
        let dek = self.client.unseal(handle, &self.config.key_auth);
        let flushed = self.discard(handle);
        let dek = dek?;
        flushed?;
        let dek: [u8; sealed::KEY_LEN] = dek.as_slice().try_into().map_err(|_| KeyStoreError::InvalidSealed)?;
        sealed::decrypt(&Secret::new(dek), sealed, header_len)
    }
}
