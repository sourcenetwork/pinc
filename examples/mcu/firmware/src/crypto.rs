//! The chip's cryptographic processor (CRYP) and hash processor (HASH) behind the library's [`Provider`].
//!
//! AES-128-GCM, the AES header mask and SHA-256 run on the chip; every other primitive is the library's software.
//! The chip has no unit for ChaCha20-Poly1305, BLAKE3, ML-KEM or the Curve25519 operations.
//!
//! One operation runs at a time and to its end: the image calls the endpoint from its main loop only, and no
//! interrupt handler touches either unit.

use core::sync::atomic::{AtomicU32, Ordering};

use pinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use pinc_crypto::{Aead, Capabilities, CryptoError, Provider, Secret, Software, ct_eq};
use stm32_metapac as pac;

/// The length of an AES block.
const BLOCK: usize = 16;

/// Packets sealed or opened with AES-128-GCM on the chip since the image started.
pub(crate) static AES_PACKETS: AtomicU32 = AtomicU32::new(0);
/// Packets sealed or opened with ChaCha20-Poly1305 in software since the image started.
pub(crate) static CHACHA_PACKETS: AtomicU32 = AtomicU32::new(0);

/// The primitives of the library with the chip's units where it has them.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct Chip;

/// An AEAD key: the raw AES key, which the chip expands at every use, or the software's expanded `ChaCha20` key.
#[allow(
    clippy::large_enum_variant,
    reason = "a key lives in its connection, and there is no heap to box it in"
)]
pub(crate) enum AeadKey {
    Aes(Secret<16>),
    Soft(<Software as Provider>::AeadKey),
}

/// A header-protection key, as [`AeadKey`].
#[allow(clippy::large_enum_variant, reason = "as `AeadKey`")]
pub(crate) enum HpKey {
    Aes(Secret<16>),
    Soft(<Software as Provider>::HpKey),
}

impl core::fmt::Debug for AeadKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("AeadKey(..)")
    }
}

impl core::fmt::Debug for HpKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("HpKey(..)")
    }
}

/// Give both units their clock.
pub(crate) fn init() {
    pac::RCC.ahb3enr().modify(|w| {
        w.set_crypen(true);
        w.set_hashen(true);
    });
    let _ = pac::RCC.ahb3enr().read();
}

/// Up to four bytes as the word the units take them in, the first byte lowest; missing bytes are zero.
fn word(bytes: &[u8]) -> u32 {
    let mut w = [0u8; 4];
    w[..bytes.len()].copy_from_slice(bytes);
    u32::from_le_bytes(w)
}

/// Four bytes of a key or a nonce as the word its register takes, the first byte highest.
fn be(bytes: &[u8]) -> u32 {
    word(bytes).swap_bytes()
}

/// Load a 128-bit key, which the unit keeps in the upper half of its key registers.
fn load_key(key: &[u8; 16]) {
    pac::CRYP.key(2).klr().write_value(be(&key[0..4]));
    pac::CRYP.key(2).krr().write_value(be(&key[4..8]));
    pac::CRYP.key(3).klr().write_value(be(&key[8..12]));
    pac::CRYP.key(3).krr().write_value(be(&key[12..16]));
}

/// Write one block to the unit; a short one is padded with zeros.
fn put(block: &[u8]) {
    let mut padded = [0u8; BLOCK];
    padded[..block.len()].copy_from_slice(block);
    for w in padded.as_chunks::<4>().0 {
        pac::CRYP.din().write_value(u32::from_le_bytes(*w));
    }
}

/// Read one block from the unit.
fn take() -> [u8; BLOCK] {
    while !pac::CRYP.sr().read().ofne() {}
    let mut block = [0u8; BLOCK];
    for w in block.as_chunks_mut::<4>().0 {
        *w = pac::CRYP.dout().read().to_le_bytes();
    }
    block
}

/// AES-128-GCM over `buf` in place, in the unit's four phases; returns the tag.
fn gcm(
    key: &[u8; 16],
    nonce: &[u8; Aead::NONCE_LEN],
    aad: &[u8],
    buf: &mut [u8],
    decrypt: bool,
) -> [u8; Aead::TAG_LEN] {
    let cryp = pac::CRYP;
    // AES-GCM, on bytes; the phase is the first one, which makes the hash key.
    cryp.cr().write(|w| {
        w.set_algomode3(true);
        w.set_datatype(2);
    });
    load_key(key);
    cryp.init(0).ivlr().write_value(be(&nonce[0..4]));
    cryp.init(0).ivrr().write_value(be(&nonce[4..8]));
    cryp.init(1).ivlr().write_value(be(&nonce[8..12]));
    // The counter of the first block of the payload (SP 800-38D: the nonce's own block is 1).
    cryp.init(1).ivrr().write_value(2);
    cryp.cr().modify(|w| w.set_crypen(true));
    while cryp.cr().read().crypen() {}

    if !aad.is_empty() {
        cryp.cr().modify(|w| w.set_gcm_ccmph(1));
        cryp.cr().modify(|w| w.set_crypen(true));
        for block in aad.chunks(BLOCK) {
            put(block);
            while !cryp.sr().read().ifem() {}
        }
        while cryp.sr().read().busy() {}
        cryp.cr().modify(|w| w.set_crypen(false));
    }

    if !buf.is_empty() {
        cryp.cr().modify(|w| {
            w.set_gcm_ccmph(2);
            w.set_algodir(decrypt);
        });
        cryp.cr().modify(|w| w.set_crypen(true));
        for block in buf.chunks_mut(BLOCK) {
            if block.len() < BLOCK && !decrypt {
                // The tag covers the ciphertext, which here is the unit's output: it must know how much of the last
                // block is padding. Deciphering, the padding is in its input and is zero already.
                #[allow(clippy::cast_possible_truncation, reason = "below 16")]
                let padding = (BLOCK - block.len()) as u8;
                cryp.cr().modify(|w| w.set_crypen(false));
                cryp.cr().modify(|w| w.set_npblb(padding));
                cryp.cr().modify(|w| w.set_crypen(true));
            }
            put(block);
            let out = take();
            block.copy_from_slice(&out[..block.len()]);
        }
        while cryp.sr().read().busy() {}
        cryp.cr().modify(|w| w.set_crypen(false));
    }

    cryp.cr().modify(|w| {
        w.set_gcm_ccmph(3);
        w.set_algodir(false);
    });
    cryp.cr().modify(|w| w.set_crypen(true));
    // The two lengths in bits, 64 bits each as two words, the high one first; a packet's are far below 2^32. The
    // unit takes these words as numbers, whatever the order it takes the bytes of data in.
    #[allow(clippy::cast_possible_truncation, reason = "a packet is at most a datagram")]
    let (aad_bits, buf_bits) = ((aad.len() * 8) as u32, (buf.len() * 8) as u32);
    cryp.din().write_value(0);
    cryp.din().write_value(aad_bits);
    cryp.din().write_value(0);
    cryp.din().write_value(buf_bits);
    let tag = take();
    // The key stays in the unit's registers otherwise.
    cryp.cr().write(|w| w.set_iprst(true));
    cryp.cr().write(|_| {});
    tag
}

/// One block through AES-128.
fn aes_block(key: &[u8; 16], block: &[u8; BLOCK]) -> [u8; BLOCK] {
    let cryp = pac::CRYP;
    // AES-ECB, on bytes.
    cryp.cr().write(|w| {
        w.set_algomode0(4);
        w.set_datatype(2);
    });
    load_key(key);
    cryp.cr().modify(|w| w.set_fflush(true));
    cryp.cr().modify(|w| w.set_crypen(true));
    put(block);
    let out = take();
    cryp.cr().write(|w| w.set_iprst(true));
    cryp.cr().write(|_| {});
    out
}

/// SHA-256 on the hash unit.
fn sha256(data: &[u8]) -> [u8; 32] {
    let hash = pac::HASH;
    // SHA-256 (3), on bytes.
    hash.cr().write(|w| {
        w.set_algo(3);
        w.set_datatype(2);
        w.set_init(true);
    });
    for w in data.chunks(4) {
        hash.din().write_value(word(w));
    }
    #[allow(clippy::cast_possible_truncation, reason = "below 32")]
    let last_bits = ((data.len() % 4) * 8) as u8;
    hash.str().write(|w| w.set_nblw(last_bits));
    hash.str().modify(|w| w.set_dcal(true));
    while !hash.sr().read().dcis() {}
    let mut out = [0u8; 32];
    for (i, w) in out.as_chunks_mut::<4>().0.iter_mut().enumerate() {
        *w = hash.hr(i).read().to_be_bytes();
    }
    out
}

impl Provider for Chip {
    type AeadKey = AeadKey;
    type HpKey = HpKey;
    type X25519Secret = <Software as Provider>::X25519Secret;
    type KemEncapsKey = <Software as Provider>::KemEncapsKey;
    type KemDecapsKey = <Software as Provider>::KemDecapsKey;
    type KemCiphertext = <Software as Provider>::KemCiphertext;

    fn capabilities(&self) -> Capabilities {
        Capabilities {
            aes_gcm_hw: true,
            chacha20_simd: false,
        }
    }

    fn aead_key(&self, alg: Aead, key: &[u8]) -> Result<AeadKey, CryptoError> {
        match alg {
            Aead::Aes128Gcm => <[u8; 16]>::try_from(key)
                .map(|k| AeadKey::Aes(Secret::new(k)))
                .map_err(|_| CryptoError::InvalidLength),
            Aead::ChaCha20Poly1305 => Software.aead_key(alg, key).map(AeadKey::Soft),
        }
    }

    fn seal(
        &self,
        key: &AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
    ) -> Result<[u8; Aead::TAG_LEN], CryptoError> {
        match key {
            AeadKey::Aes(k) => {
                AES_PACKETS.fetch_add(1, Ordering::Relaxed);
                Ok(gcm(k.expose(), nonce, aad, buf, false))
            }
            AeadKey::Soft(k) => {
                CHACHA_PACKETS.fetch_add(1, Ordering::Relaxed);
                Software.seal(k, nonce, aad, buf)
            }
        }
    }

    fn open(
        &self,
        key: &AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
        tag: &[u8; Aead::TAG_LEN],
    ) -> Result<(), CryptoError> {
        match key {
            AeadKey::Aes(k) => {
                AES_PACKETS.fetch_add(1, Ordering::Relaxed);
                if ct_eq(&gcm(k.expose(), nonce, aad, buf, true), tag) {
                    return Ok(());
                }
                // The unit deciphers before the tag is known: cipher the bytes again, so that what is left is the
                // ciphertext, as the trait promises.
                gcm(k.expose(), nonce, aad, buf, false);
                Err(CryptoError::Authentication)
            }
            AeadKey::Soft(k) => {
                CHACHA_PACKETS.fetch_add(1, Ordering::Relaxed);
                Software.open(k, nonce, aad, buf, tag)
            }
        }
    }

    fn hp_key(&self, alg: Aead, key: &[u8]) -> Result<HpKey, CryptoError> {
        match alg {
            Aead::Aes128Gcm => <[u8; 16]>::try_from(key)
                .map(|k| HpKey::Aes(Secret::new(k)))
                .map_err(|_| CryptoError::InvalidLength),
            Aead::ChaCha20Poly1305 => Software.hp_key(alg, key).map(HpKey::Soft),
        }
    }

    fn hp_mask(&self, key: &HpKey, sample: &[u8; Aead::SAMPLE_LEN]) -> [u8; Aead::MASK_LEN] {
        match key {
            HpKey::Aes(k) => {
                let [m0, m1, m2, m3, m4, ..] = aes_block(k.expose(), sample);
                [m0, m1, m2, m3, m4]
            }
            HpKey::Soft(k) => Software.hp_mask(k, sample),
        }
    }

    fn sha256(&self, data: &[u8]) -> [u8; 32] {
        sha256(data)
    }

    fn x25519_secret(&self, seed: &[u8; 32]) -> Self::X25519Secret {
        Software.x25519_secret(seed)
    }

    fn x25519_public(&self, secret: &Self::X25519Secret) -> [u8; 32] {
        Software.x25519_public(secret)
    }

    fn x25519_dh(&self, secret: &Self::X25519Secret, peer: &[u8; 32]) -> Result<Secret<32>, CryptoError> {
        Software.x25519_dh(secret, peer)
    }

    fn kem_keygen(&self, d: &[u8; 32], z: &[u8; 32]) -> (Self::KemDecapsKey, Self::KemEncapsKey) {
        Software.kem_keygen(d, z)
    }

    fn kem_encaps_key(&self, bytes: &[u8]) -> Result<Self::KemEncapsKey, CryptoError> {
        Software.kem_encaps_key(bytes)
    }

    fn kem_encaps_key_bytes(&self, ek: &Self::KemEncapsKey) -> [u8; KEM_ENCAPS_KEY_LEN] {
        Software.kem_encaps_key_bytes(ek)
    }

    fn kem_ciphertext(&self, bytes: &[u8]) -> Result<Self::KemCiphertext, CryptoError> {
        Software.kem_ciphertext(bytes)
    }

    fn kem_ciphertext_bytes(&self, ct: &Self::KemCiphertext) -> [u8; KEM_CIPHERTEXT_LEN] {
        Software.kem_ciphertext_bytes(ct)
    }

    fn kem_encapsulate(
        &self,
        ek: &Self::KemEncapsKey,
        m: &[u8; 32],
    ) -> Result<(Self::KemCiphertext, Secret<32>), CryptoError> {
        Software.kem_encapsulate(ek, m)
    }

    fn kem_decapsulate(&self, dk: &Self::KemDecapsKey, ct: &Self::KemCiphertext) -> Result<Secret<32>, CryptoError> {
        Software.kem_decapsulate(dk, ct)
    }
}

/// What one primitive costs in software and on the chip.
#[derive(Clone, Copy, Default)]
pub(crate) struct Timing {
    pub(crate) name: &'static str,
    /// Nanoseconds in software, the least of the runs.
    pub(crate) software_ns: u32,
    /// The same on the chip, when it has the primitive.
    pub(crate) chip_ns: Option<u32>,
    /// Whether the chip gave what the software gave, on every input tried.
    pub(crate) agree: bool,
}

/// The least time of four runs of `f`, in nanoseconds.
fn time(now: fn() -> u64, mut f: impl FnMut()) -> u32 {
    let mut least = u64::MAX;
    for _ in 0..4 {
        let t = now();
        f();
        least = least.min(now() - t);
    }
    u32::try_from(least).unwrap_or(u32::MAX)
}

/// The bytes of a packet's payload for the measurement.
const PACKET: usize = 1200;

/// Whether the chip seals and opens `len` bytes as the software does, and refuses a changed tag leaving the ciphertext.
fn gcm_agrees(len: usize) -> bool {
    let (key, nonce, aad) = ([0x42u8; 16], [7u8; Aead::NONCE_LEN], [0xA5u8; 21]);
    let mut plain = [0u8; PACKET];
    for (i, b) in plain.iter_mut().enumerate() {
        #[allow(clippy::cast_possible_truncation, reason = "a pattern")]
        let v = (i * 31 + 7) as u8;
        *b = v;
    }
    let plain = &plain[..len];
    let (Ok(soft), Ok(chip)) = (
        Software.aead_key(Aead::Aes128Gcm, &key),
        Chip.aead_key(Aead::Aes128Gcm, &key),
    ) else {
        return false;
    };
    let (mut a, mut b) = ([0u8; PACKET], [0u8; PACKET]);
    let (a, b) = (&mut a[..len], &mut b[..len]);
    a.copy_from_slice(plain);
    b.copy_from_slice(plain);
    let (Ok(tag_a), Ok(tag_b)) = (Software.seal(&soft, &nonce, &aad, a), Chip.seal(&chip, &nonce, &aad, b)) else {
        return false;
    };
    if a != b || tag_a != tag_b {
        return false;
    }
    let mut wrong = tag_a;
    wrong[3] ^= 1;
    if Chip.open(&chip, &nonce, &aad, b, &wrong).is_ok() || a != b {
        return false;
    }
    Chip.open(&chip, &nonce, &aad, b, &tag_a).is_ok() && b == plain
}

/// Time the primitives of a handshake and of a packet, in software and on the chip, and check the chip against the
/// software.
pub(crate) fn measure(now: fn() -> u64) -> [Timing; 9] {
    let mut out = [Timing::default(); 9];
    measure_packet(now, &mut out);
    measure_handshake(now, &mut out);
    out
}

/// The primitives of a packet, which the chip has but for `ChaCha20-Poly1305`.
fn measure_packet(now: fn() -> u64, out: &mut [Timing; 9]) {
    let (key, nonce, aad) = ([0x42u8; 16], [7u8; Aead::NONCE_LEN], [0xA5u8; 21]);
    let mut buf = [0u8; PACKET];

    if let (Ok(soft), Ok(chip)) = (
        Software.aead_key(Aead::Aes128Gcm, &key),
        Chip.aead_key(Aead::Aes128Gcm, &key),
    ) {
        out[0] = Timing {
            name: "aes128gcm_seal_1200",
            software_ns: time(now, || {
                let _ = Software.seal(&soft, &nonce, &aad, &mut buf);
            }),
            chip_ns: Some(time(now, || {
                let _ = Chip.seal(&chip, &nonce, &aad, &mut buf);
            })),
            agree: [0, 1, 15, 16, 17, 1199, PACKET].into_iter().all(gcm_agrees),
        };
    }
    if let Ok(soft) = Software.aead_key(Aead::ChaCha20Poly1305, &[0x42; 32]) {
        out[1] = Timing {
            name: "chacha20poly1305_seal_1200",
            software_ns: time(now, || {
                let _ = Software.seal(&soft, &nonce, &aad, &mut buf);
            }),
            chip_ns: None,
            agree: true,
        };
    }
    if let (Ok(soft), Ok(chip)) = (
        Software.hp_key(Aead::Aes128Gcm, &key),
        Chip.hp_key(Aead::Aes128Gcm, &key),
    ) {
        let sample = [0x3Cu8; Aead::SAMPLE_LEN];
        out[2] = Timing {
            name: "aes_header_mask",
            software_ns: time(now, || {
                let _ = Software.hp_mask(&soft, &sample);
            }),
            chip_ns: Some(time(now, || {
                let _ = Chip.hp_mask(&chip, &sample);
            })),
            agree: Software.hp_mask(&soft, &sample) == Chip.hp_mask(&chip, &sample),
        };
    }
    out[3] = Timing {
        name: "sha256_1024",
        software_ns: time(now, || {
            let _ = Software.sha256(&buf[..1024]);
        }),
        chip_ns: Some(time(now, || {
            let _ = Chip.sha256(&buf[..1024]);
        })),
        agree: [0, 1, 3, 55, 56, 64, 1021, 1024]
            .into_iter()
            .all(|n| Software.sha256(&buf[..n]) == Chip.sha256(&buf[..n])),
    };
}

/// The primitives of a handshake, which the chip has no unit for.
fn measure_handshake(now: fn() -> u64, out: &mut [Timing; 9]) {
    let secret = Software.x25519_secret(&[9; 32]);
    let public = Software.x25519_public(&secret);
    out[4] = Timing {
        name: "x25519_public",
        software_ns: time(now, || {
            let _ = Software.x25519_public(&secret);
        }),
        chip_ns: None,
        agree: true,
    };
    out[5] = Timing {
        name: "x25519_dh",
        software_ns: time(now, || {
            let _ = Software.x25519_dh(&secret, &public);
        }),
        chip_ns: None,
        agree: true,
    };
    out[6] = Timing {
        name: "mlkem768_keygen",
        software_ns: time(now, || {
            let _ = Software.kem_keygen(&[1; 32], &[2; 32]);
        }),
        chip_ns: None,
        agree: true,
    };
    let (dk, ek) = Software.kem_keygen(&[1; 32], &[2; 32]);
    out[7] = Timing {
        name: "mlkem768_encapsulate",
        software_ns: time(now, || {
            let _ = Software.kem_encapsulate(&ek, &[3; 32]);
        }),
        chip_ns: None,
        agree: true,
    };
    if let Ok((ct, _)) = Software.kem_encapsulate(&ek, &[3; 32]) {
        out[8] = Timing {
            name: "mlkem768_decapsulate",
            software_ns: time(now, || {
                let _ = Software.kem_decapsulate(&dk, &ct);
            }),
            chip_ns: None,
            agree: true,
        };
    }
}
