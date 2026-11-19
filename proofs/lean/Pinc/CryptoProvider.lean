import Pinc.CryptoIdentity

/-!
# The provider of `pinc-crypto` (`provider.rs`, `software.rs`)

The length checks and the error of every `Provider` method, the AEAD wrappers over abstract primitives, the sampling
of the header protection mask (RFC 9001 5.4.3 and 5.4.4), the X25519 non-contributory check and the ML-KEM parsers.
The primitives (AES, `ChaCha20`, the AEADs, X25519, ML-KEM) are abstract functions; what is proved is how the code
feeds them and what it does with their answers.

The nonce of an AEAD call is a `[u8; 12]` passed through unchanged. How a protocol nonce is built from a packet
number (the IV XOR the number, below 2^62, so a key never meets the same nonce twice) is `pinc-security`'s
`record.rs`, proved in `Pinc.Record` and `Record.tla`; the other nonces under one key are the random nonces of the
sealed format (`Pinc.KeystoreSealed`) and the constant nonce of the DRBG, whose key changes after every call
(`Pinc.CryptoDrbg`).
-/

namespace Pinc.CryptoProvider
open Pinc.CryptoKdf (Bytes)
open Pinc.CryptoIdentity (Err)

/-- `Aead`. -/
inductive Aead where
  | chacha20Poly1305
  | aes128Gcm
  deriving DecidableEq, Repr

def Aead.keyLen : Aead → Nat
  | .chacha20Poly1305 => 32
  | .aes128Gcm => 16

def nonceLen : Nat := 12
def tagLen : Nat := 16
def maskLen : Nat := 5
def sampleLen : Nat := 16
def kemEncapsKeyLen : Nat := 1184
def kemCiphertextLen : Nat := 1088

/-- `aead_key` and `hp_key`: a key of any other length is an `InvalidLength`. -/
def keySetup (alg : Aead) (key : Bytes) : Except Err Bytes :=
  if key.length = alg.keyLen then .ok key else .error .invalidLength

theorem keySetup_ok_iff (alg : Aead) (key : Bytes) : (∃ k, keySetup alg key = .ok k) ↔ key.length = alg.keyLen := by
  unfold keySetup
  split <;> simp_all

theorem keySetup_err (alg : Aead) (key : Bytes) (h : key.length ≠ alg.keyLen) :
    keySetup alg key = .error .invalidLength := by simp [keySetup, h]

/-! ## AEAD wrappers -/

/-- An AEAD primitive: `seal key nonce aad plaintext` is the ciphertext and tag, or `none` beyond its input limit;
`open key nonce aad ciphertext tag` is the plaintext, or `none` when the tag does not verify. -/
structure AeadImpl where
  sealF : Bytes → Bytes → Bytes → Bytes → Option (Bytes × Bytes)
  openF : Bytes → Bytes → Bytes → Bytes → Bytes → Option Bytes

/-- `Provider::seal`: any failure of the primitive is `InputTooLong`. -/
def sealW (A : AeadImpl) (k n a p : Bytes) : Except Err (Bytes × Bytes) :=
  match A.sealF k n a p with
  | some r => .ok r
  | none => .error .inputTooLong

/-- `Provider::open`: any failure of the primitive is `Authentication`. -/
def openW (A : AeadImpl) (k n a c t : Bytes) : Except Err Bytes :=
  match A.openF k n a c t with
  | some p => .ok p
  | none => .error .authentication

/-- The primitive's correctness and shape (RFC 8439, SP 800-38D): what it seals it opens, the ciphertext is as
long as the plaintext, the tag 16 bytes. A hypothesis on the abstract primitive. -/
structure AeadSpec (A : AeadImpl) : Prop where
  roundtrip : ∀ k n a p c t, A.sealF k n a p = some (c, t) → A.openF k n a c t = some p
  shape : ∀ k n a p c t, A.sealF k n a p = some (c, t) → c.length = p.length ∧ t.length = tagLen

theorem seal_open_roundtrip {A : AeadImpl} (hs : AeadSpec A) {k n a p c t : Bytes}
    (h : sealW A k n a p = .ok (c, t)) : openW A k n a c t = .ok p := by
  unfold sealW at h
  cases hh : A.sealF k n a p with
  | none => simp [hh] at h
  | some r =>
    simp only [hh, Except.ok.injEq] at h
    subst h
    simp [openW, hs.roundtrip _ _ _ _ _ _ hh]

theorem seal_shape {A : AeadImpl} (hs : AeadSpec A) {k n a p c t : Bytes} (h : sealW A k n a p = .ok (c, t)) :
    c.length = p.length ∧ t.length = 16 := by
  unfold sealW at h
  cases hh : A.sealF k n a p with
  | none => simp [hh] at h
  | some r =>
    simp only [hh, Except.ok.injEq] at h
    subst h
    exact hs.shape _ _ _ _ _ _ hh

theorem open_err {A : AeadImpl} {k n a c t : Bytes} (h : A.openF k n a c t = none) :
    openW A k n a c t = .error .authentication := by simp [openW, h]

/-! ## Header protection masks -/

/-- `u32::from_le_bytes` of the first four bytes of a sample. -/
def le32 : Bytes → Nat
  | c0 :: c1 :: c2 :: c3 :: _ => c0 + 256 * (c1 + 256 * (c2 + 256 * c3))
  | _ => 0

theorem le32_lt {s : Bytes} (h : 4 ≤ s.length) (hb : ∀ b ∈ s, b < 256) : le32 s < 2 ^ 32 := by
  match s, h, hb with
  | c0 :: c1 :: c2 :: c3 :: _, _, hb =>
    have h0 := hb c0 (by simp)
    have h1 := hb c1 (by simp)
    have h2 := hb c2 (by simp)
    have h3 := hb c3 (by simp)
    simp only [le32]
    omega

/-- The counter determines the first four bytes (bytes below 256). -/
theorem le32_injective {s t : Bytes} (hs : s.length = 4) (ht : t.length = 4) (hbs : ∀ b ∈ s, b < 256)
    (hbt : ∀ b ∈ t, b < 256) (h : le32 s = le32 t) : s = t := by
  match s, t, hs, ht, hbs, hbt with
  | [a0, a1, a2, a3], [b0, b1, b2, b3], _, _, hbs, hbt =>
    have := hbs a0 (by simp); have := hbs a1 (by simp); have := hbs a2 (by simp); have := hbs a3 (by simp)
    have := hbt b0 (by simp); have := hbt b1 (by simp); have := hbt b2 (by simp); have := hbt b3 (by simp)
    simp only [le32] at h
    simp only [List.cons.injEq, and_true]
    omega

/-- The `ChaCha20` mask: the counter is the little-endian first four bytes of the sample, the nonce the other 12;
the stream is sought to `counter * 64` and 5 bytes are read. `stream key nonce i` is byte `i` of the stream. -/
def hpMaskChaCha (stream : Bytes → Bytes → Nat → Nat) (key sample : Bytes) : Bytes :=
  (List.range maskLen).map (fun i => stream key (sample.drop 4) (le32 sample * 64 + i))

/-- The AES mask: the first five bytes of the encryption of the sample block. -/
def hpMaskAes (enc : Bytes → Bytes → Bytes) (key sample : Bytes) : Bytes := (enc key sample).take maskLen

/-- A sample is split into a 4-byte counter and a 12-byte nonce, exactly. -/
theorem sample_split {s : Bytes} (h : s.length = sampleLen) : (s.take 4).length = 4 ∧ (s.drop 4).length = 12 := by
  simp [sampleLen] at h
  simp [h]

/-- The mask reads positions `counter * 64` to `counter * 64 + 4`, inside the `2^32` blocks of the RFC 8439 stream, for
every counter (a 32-bit value). The code makes the block through the cipher core, which serves all `2^32` blocks; the
stream wrapper serves one block fewer, which made the mask of counter `2^32 - 1` zero before the fix (the
regression test `header_protection_chacha20_counter_edges`). -/
theorem chacha_mask_in_stream {s : Bytes} (h : s.length = sampleLen) (hb : ∀ b ∈ s, b < 256) :
    le32 s * 64 ≤ 2 ^ 32 * 64 ∧ le32 s * 64 + maskLen ≤ 2 ^ 32 * 64 := by
  have h4 : 4 ≤ s.length := by simp [sampleLen] at h; omega
  have := le32_lt h4 hb
  unfold maskLen
  omega

theorem chacha_mask_length (stream : Bytes → Bytes → Nat → Nat) (key sample : Bytes) :
    (hpMaskChaCha stream key sample).length = maskLen := by simp [hpMaskChaCha]

/-- The AES mask has five bytes when the cipher gives a block of 16: the fallback to zeros is unreachable. -/
theorem aes_mask_length (enc : Bytes → Bytes → Bytes) (key sample : Bytes) (h : (enc key sample).length = 16) :
    (hpMaskAes enc key sample).length = maskLen := by
  simp [hpMaskAes, h, maskLen]

/-- Two samples with the same counter and the same nonce are the same sample: distinct samples never read the same
position of the same stream. -/
theorem sample_determined {s t : Bytes} (hs : s.length = sampleLen) (ht : t.length = sampleLen)
    (hbs : ∀ b ∈ s, b < 256) (hbt : ∀ b ∈ t, b < 256) (hc : le32 s = le32 t) (hn : s.drop 4 = t.drop 4) : s = t := by
  have h4s : (s.take 4).length = 4 := (sample_split hs).1
  have h4t : (t.take 4).length = 4 := (sample_split ht).1
  have hle : le32 s = le32 (s.take 4) := by
    match s, hs with
    | c0 :: c1 :: c2 :: c3 :: _, _ => simp [le32]
  have hle' : le32 t = le32 (t.take 4) := by
    match t, ht with
    | c0 :: c1 :: c2 :: c3 :: _, _ => simp [le32]
  have := le32_injective h4s h4t (fun b hb => hbs b (List.mem_of_mem_take hb)) (fun b hb => hbt b (List.mem_of_mem_take hb))
    (by rw [← hle, ← hle']; exact hc)
  calc s = s.take 4 ++ s.drop 4 := (List.take_append_drop 4 s).symm
    _ = t.take 4 ++ t.drop 4 := by rw [this, hn]
    _ = t := List.take_append_drop 4 t

/-! ## X25519 and ML-KEM -/

/-- `x25519_dh`: an all-zero result is `NonContributory`. -/
def dh (x : Bytes → Bytes → Bytes) (sec peer : Bytes) : Except Err Bytes :=
  if x sec peer = List.replicate 32 0 then .error .nonContributory else .ok (x sec peer)

theorem dh_ok_nonzero {x : Bytes → Bytes → Bytes} {sec peer r : Bytes} (h : dh x sec peer = .ok r) :
    r ≠ List.replicate 32 0 := by
  unfold dh at h
  split at h
  · cases h
  · cases h; assumption

theorem dh_zero_refused (x : Bytes → Bytes → Bytes) (sec peer : Bytes) (h : x sec peer = List.replicate 32 0) :
    dh x sec peer = .error .nonContributory := by simp [dh, h]

/-- `kem_encaps_key`: a wrong length and a failed modulus check are the same error. -/
def kemEncapsKey (modulusOk : Bytes → Bool) (b : Bytes) : Except Err Bytes :=
  if b.length ≠ kemEncapsKeyLen then .error .invalidEncapsulationKey
  else if ¬modulusOk b then .error .invalidEncapsulationKey
  else .ok b

theorem kemEncapsKey_ok_iff (m : Bytes → Bool) (b r : Bytes) :
    kemEncapsKey m b = .ok r ↔ b.length = kemEncapsKeyLen ∧ m b = true ∧ r = b := by
  unfold kemEncapsKey
  by_cases h1 : b.length = kemEncapsKeyLen <;> by_cases h2 : m b = true <;> simp [h1, h2, eq_comm]

/-- `kem_ciphertext`: the length is all that is checked (ML-KEM accepts every ciphertext of the right length). -/
def kemCiphertext (b : Bytes) : Except Err Bytes :=
  if b.length ≠ kemCiphertextLen then .error .invalidLength else .ok b

theorem kemCiphertext_ok_iff (b r : Bytes) : kemCiphertext b = .ok r ↔ b.length = kemCiphertextLen ∧ r = b := by
  unfold kemCiphertext
  by_cases h1 : b.length = kemCiphertextLen <;> simp [h1, eq_comm]

/-- The keygen seed is `d || z`, 64 bytes: the two halves are 32 bytes each. -/
theorem kem_seed_split (d z : Bytes) (hd : d.length = 32) (hz : z.length = 32) :
    (d ++ z).take 32 = d ∧ (d ++ z).drop 32 = z := by
  constructor
  · simpa [hd] using List.take_left' hd
  · simpa [hd] using List.drop_left' hd

end Pinc.CryptoProvider

#audit_axioms Pinc.CryptoProvider.seal_open_roundtrip
#audit_axioms Pinc.CryptoProvider.le32_injective
#audit_axioms Pinc.CryptoProvider.chacha_mask_in_stream
#audit_axioms Pinc.CryptoProvider.sample_determined
#audit_axioms Pinc.CryptoProvider.dh_ok_nonzero
#audit_axioms Pinc.CryptoProvider.kemEncapsKey_ok_iff
