import Vinc.CryptoKdf

/-!
# Identities of `vinc-crypto` (`identity.rs`)

The signature algorithms with their wire tags and lengths, node ids, the decision tables of `verify`, `verify_node`
and `verify_ml_dsa_65`, and the errors of the key pair operations. The signature primitives (dalek, `p256`, `ml-dsa`)
are abstract: `Flags` holds what they answer (does the key parse, does the signature parse, is `s` low, does the
equation hold), and the code's decision, which error is returned for which combination, is a function of those and of
the lengths. The node id uses the BLAKE3 `derive_key` primitive through `Vinc.CryptoKdf`.
-/

namespace Vinc.CryptoIdentity
open Vinc.CryptoKdf

/-- The signature algorithms, `IdentityAlg`. -/
inductive Alg where
  | ed25519
  | ecdsaP256
  | mlDsa65
  | hybrid
  deriving DecidableEq, Repr

/-- The one-byte wire tag. -/
def Alg.tag : Alg → Nat
  | .ed25519 => 1
  | .ecdsaP256 => 2
  | .mlDsa65 => 3
  | .hybrid => 4

/-- `IdentityAlg::from_tag`. -/
def Alg.ofTag : Nat → Option Alg
  | 1 => some .ed25519
  | 2 => some .ecdsaP256
  | 3 => some .mlDsa65
  | 4 => some .hybrid
  | _ => none

def Alg.pkLen : Alg → Nat
  | .ed25519 => 32
  | .ecdsaP256 => 33
  | .mlDsa65 => 1952
  | .hybrid => 32 + 1952

def Alg.sigLen : Alg → Nat
  | .ed25519 => 64
  | .ecdsaP256 => 64
  | .mlDsa65 => 3309
  | .hybrid => 64 + 3309

def Alg.seedLen : Alg → Nat
  | .hybrid => 64
  | _ => 32

def Alg.all : List Alg := [.ed25519, .ecdsaP256, .mlDsa65, .hybrid]

/-- `MAX_PUBLIC_KEY_LEN` and `MAX_SIGNATURE_LEN`. -/
def maxPk : Nat := 32 + 1952
def maxSig : Nat := 64 + 3309

/-- The tag round trips, and `from_tag` accepts exactly the four tags. -/
theorem ofTag_tag (a : Alg) : Alg.ofTag a.tag = some a := by cases a <;> rfl

theorem tag_ofTag {t : Nat} {a : Alg} (h : Alg.ofTag t = some a) : a.tag = t := by
  match t, h with
  | 1, h => cases h; rfl
  | 2, h => cases h; rfl
  | 3, h => cases h; rfl
  | 4, h => cases h; rfl
  | 0, h => cases h
  | n + 5, h => cases h

theorem ofTag_none {t : Nat} (h : t = 0 ∨ 5 ≤ t) : Alg.ofTag t = none := by
  match t, h with
  | 0, _ => rfl
  | n + 5, _ => rfl

theorem tag_injective {a b : Alg} (h : a.tag = b.tag) : a = b := by cases a <;> cases b <;> simp_all [Alg.tag]

theorem tag_range (a : Alg) : 1 ≤ a.tag ∧ a.tag ≤ 4 := by cases a <;> simp [Alg.tag]

/-- Every length used by the buffers is within the maxima, and the hybrid is the concatenation of its two halves. -/
theorem lens_le_max (a : Alg) : a.pkLen ≤ maxPk ∧ a.sigLen ≤ maxSig := by
  cases a <;> simp [Alg.pkLen, Alg.sigLen, maxPk, maxSig]

theorem hybrid_layout : Alg.hybrid.pkLen = Alg.ed25519.pkLen + Alg.mlDsa65.pkLen ∧
    Alg.hybrid.sigLen = Alg.ed25519.sigLen + Alg.mlDsa65.sigLen ∧
    Alg.hybrid.seedLen = Alg.ed25519.seedLen + Alg.mlDsa65.seedLen := by decide

/-! ## Errors -/

/-- `CryptoError`. -/
inductive Err where
  | invalidLength
  | authentication
  | inputTooLong
  | nonContributory
  | invalidEncapsulationKey
  | invalidSecretKey
  | invalidPublicKey
  | invalidSignature
  | highS
  | nodeIdMismatch
  deriving DecidableEq, Repr

/-! ## Node ids -/

/-- `NodeId`: the algorithm and 32 bytes. -/
structure NodeId where
  alg : Alg
  bytes : Bytes
  deriving DecidableEq, Repr

/-- `NodeId::from_public`, over the 32-byte output `H` of the derivation primitive for a call. -/
def fromPublic (H : Call → Bytes) (alg : Alg) (pk : Bytes) : Except Err NodeId :=
  if pk.length ≠ alg.pkLen then .error .invalidLength
  else .ok ⟨alg, if alg = .ed25519 then pk else H (nodeIdCall alg.tag pk)⟩

/-- A wrong length is refused with `InvalidLength`, and nothing else is. -/
theorem fromPublic_err (H : Call → Bytes) (alg : Alg) (pk : Bytes) :
    fromPublic H alg pk = .error .invalidLength ↔ pk.length ≠ alg.pkLen := by
  unfold fromPublic
  split <;> simp_all

theorem fromPublic_ok_len {H : Call → Bytes} (hH : ∀ c, (H c).length = 32) {alg : Alg} {pk : Bytes} {id : NodeId}
    (h : fromPublic H alg pk = .ok id) : id.alg = alg ∧ id.bytes.length = 32 := by
  unfold fromPublic at h
  split at h
  · cases h
  · cases h
    cases alg <;> simp_all [Alg.pkLen]

/-- The id is a function of the algorithm and the public key, and two different pairs never share an id, if the
primitive is collision resistant (`Injective`). -/
theorem fromPublic_injective {H : Call → Bytes} (hH : ∀ c c', H c = H c' → c = c') {a a' : Alg} {pk pk' : Bytes}
    {id : NodeId} (h : fromPublic H a pk = .ok id) (h' : fromPublic H a' pk' = .ok id) : a = a' ∧ pk = pk' := by
  have hl : pk.length = a.pkLen := by
    by_cases hc : pk.length = a.pkLen
    · exact hc
    · simp [fromPublic, hc] at h
  have hl' : pk'.length = a'.pkLen := by
    by_cases hc : pk'.length = a'.pkLen
    · exact hc
    · simp [fromPublic, hc] at h'
  simp only [fromPublic, hl, hl', ne_eq, not_true_eq_false, ite_false] at h h'
  have e : (⟨a, if a = .ed25519 then pk else H (nodeIdCall a.tag pk)⟩ : NodeId) =
      ⟨a', if a' = .ed25519 then pk' else H (nodeIdCall a'.tag pk')⟩ :=
    (Except.ok.inj h).trans (Except.ok.inj h').symm
  injection e with ea eb
  subst ea
  refine ⟨rfl, ?_⟩
  by_cases ha : a = .ed25519
  · simp only [ha, ite_true] at eb
    exact eb
  · simp only [ha, ite_false] at eb
    exact (nodeIdCall_injective (hH _ _ eb)).2

/-- `NodeId::matches`: the id of `pk` under `alg` is this id. -/
def matches' (H : Call → Bytes) (id : NodeId) (alg : Alg) (pk : Bytes) : Bool :=
  match fromPublic H alg pk with
  | .ok id' => decide (id'.alg = id.alg) && decide (id'.bytes = id.bytes)
  | .error _ => false

theorem matches_iff (H : Call → Bytes) (id : NodeId) (alg : Alg) (pk : Bytes) :
    matches' H id alg pk = true ↔ fromPublic H alg pk = .ok id := by
  unfold matches'
  cases hf : fromPublic H alg pk with
  | error e => simp
  | ok id' =>
    cases id; cases id'
    simp

/-- The wire form of an id: its tag, then its 32 bytes. -/
def encodeId (id : NodeId) : Bytes := id.alg.tag :: id.bytes

/-- Two ids with the same encoding are the same id, also across algorithms: the tag is part of the encoding. -/
theorem encodeId_injective {a b : NodeId} (h : encodeId a = encodeId b) : a = b := by
  cases a; cases b
  simp only [encodeId, List.cons.injEq] at h
  have := tag_injective h.1
  subst this
  simp [h.2]

/-- Ed25519 ids are the public key; the id of any other algorithm is an output of the derivation, never a key. -/
theorem ed25519_id_is_key (H : Call → Bytes) (pk : Bytes) (h : pk.length = 32) :
    fromPublic H .ed25519 pk = .ok ⟨.ed25519, pk⟩ := by
  simp [fromPublic, Alg.pkLen, h]

/-! ## Verification

The verdicts of the signature primitives, as functions of what they are given. They are abstract (the dalek,
`p256` and `ml-dsa` crates are assumed correct); the code's decision, which error follows which verdict, is the
subject of the theorems. -/

structure Prim where
  /-- `VerifyingKey::from_bytes` accepts the key -/
  edPk : Bytes → Bool
  /-- `verify_strict` accepts (key, message, signature) -/
  edVer : Bytes → Bytes → Bytes → Bool
  /-- `from_sec1_bytes` accepts the key -/
  pPk : Bytes → Bool
  /-- `Signature::from_slice` accepts the signature -/
  pSig : Bytes → Bool
  /-- the signature's `s` is already low (`normalize_s` is the identity) -/
  pLow : Bytes → Bool
  /-- ECDSA verification accepts (key, message, signature) -/
  pVer : Bytes → Bytes → Bytes → Bool
  /-- `MlSignature::try_from` accepts the signature -/
  mSig : Bytes → Bool
  /-- ML-DSA verification accepts (key, context, message, signature) -/
  mVer : Bytes → Bytes → Bytes → Bytes → Bool

/-- `ed_verify`. -/
def edVerify (P : Prim) (pk msg sig : Bytes) : Except Err Unit :=
  if pk.length ≠ 32 ∨ sig.length ≠ 64 then .error .invalidLength
  else if ¬P.edPk pk then .error .invalidPublicKey
  else if ¬P.edVer pk msg sig then .error .invalidSignature
  else .ok ()

/-- `p256_verify`: only the compressed form (a first byte of 2 or 3), then the point, then the signature, then low `s`. -/
def p256Verify (P : Prim) (pk msg sig : Bytes) : Except Err Unit :=
  if pk.length ≠ 33 then .error .invalidLength
  else if ¬(pk.head? = some 2 ∨ pk.head? = some 3) then .error .invalidPublicKey
  else if ¬P.pPk pk then .error .invalidPublicKey
  else if ¬P.pSig sig then .error .invalidSignature
  else if ¬P.pLow sig then .error .highS
  else if ¬P.pVer pk msg sig then .error .invalidSignature
  else .ok ()

/-- `verify_ml_dsa_65` with a context. -/
def mlVerify (P : Prim) (pk ctx msg sig : Bytes) : Except Err Unit :=
  if ctx.length > 255 ∨ sig.length ≠ 3309 then .error .invalidLength
  else if pk.length ≠ 1952 then .error .invalidLength
  else if ¬P.mSig sig then .error .invalidSignature
  else if ¬P.mVer pk ctx msg sig then .error .invalidSignature
  else .ok ()

/-- `hybrid_digest`, over the primitive. -/
def hybridDigest (H : Call → Bytes) (msg : Bytes) : Bytes := H (hybridCall msg)

/-- `Result::and`: the first error, else the second result. -/
def andR : Except Err Unit → Except Err Unit → Except Err Unit
  | .error e, _ => .error e
  | .ok (), r => r

/-- `verify`. -/
def verify (H : Call → Bytes) (P : Prim) (alg : Alg) (pk msg sig : Bytes) : Except Err Unit :=
  if pk.length ≠ alg.pkLen ∨ sig.length ≠ alg.sigLen then .error .invalidLength
  else match alg with
    | .ed25519 => edVerify P pk msg sig
    | .ecdsaP256 => p256Verify P pk msg sig
    | .mlDsa65 => mlVerify P pk [] msg sig
    | .hybrid =>
      let digest := hybridDigest H msg
      andR (edVerify P (pk.take 32) digest (sig.take 64)) (mlVerify P (pk.drop 32) [] digest (sig.drop 64))

/-- A key or signature of the wrong length is refused with `InvalidLength`, before any primitive runs. -/
theorem verify_wrong_length (H : Call → Bytes) (P : Prim) (alg : Alg) (pk msg sig : Bytes)
    (h : pk.length ≠ alg.pkLen ∨ sig.length ≠ alg.sigLen) : verify H P alg pk msg sig = .error .invalidLength := by
  simp [verify, h]

/-- An accepted signature had the right lengths. -/
theorem verify_ok_lengths {H : Call → Bytes} {P : Prim} {alg : Alg} {pk msg sig : Bytes}
    (h : verify H P alg pk msg sig = .ok ()) : pk.length = alg.pkLen ∧ sig.length = alg.sigLen := by
  unfold verify at h
  split at h
  · cases h
  · omega

theorem ed_ok_iff (P : Prim) (pk msg sig : Bytes) :
    edVerify P pk msg sig = .ok () ↔ (pk.length = 32 ∧ sig.length = 64) ∧ P.edPk pk = true ∧ P.edVer pk msg sig = true := by
  unfold edVerify
  by_cases h1 : pk.length = 32 <;> by_cases h2 : sig.length = 64 <;> by_cases h3 : P.edPk pk = true <;>
    by_cases h4 : P.edVer pk msg sig = true <;> simp [h1, h2, h3, h4]

/-- ECDSA is accepted only for a compressed key (first byte 2 or 3), with a signature that parses, is low-`s`
and verifies. -/
theorem p256_ok_iff (P : Prim) (pk msg sig : Bytes) :
    p256Verify P pk msg sig = .ok () ↔ pk.length = 33 ∧ (pk.head? = some 2 ∨ pk.head? = some 3) ∧ P.pPk pk = true ∧
      P.pSig sig = true ∧ P.pLow sig = true ∧ P.pVer pk msg sig = true := by
  unfold p256Verify
  by_cases h1 : pk.length = 33 <;> by_cases h2 : (pk.head? = some 2 ∨ pk.head? = some 3) <;>
    by_cases h3 : P.pPk pk = true <;> by_cases h4 : P.pSig sig = true <;> by_cases h5 : P.pLow sig = true <;>
    by_cases h6 : P.pVer pk msg sig = true <;> simp [h1, h2, h3, h4, h5, h6]

/-- The compact SEC1 form (first byte 5), the uncompressed tag and any other first byte of a 33-byte key are an
`InvalidPublicKey`, so a key has one encoding and so one node id. -/
theorem p256_other_form_refused (P : Prim) (pk msg sig : Bytes) (hl : pk.length = 33)
    (hf : ¬(pk.head? = some 2 ∨ pk.head? = some 3)) : p256Verify P pk msg sig = .error .invalidPublicKey := by
  simp [p256Verify, hl, hf]

/-- A well-formed but malleable signature is a `HighS`, not an `InvalidSignature`. -/
theorem p256_high_s (P : Prim) (pk msg sig : Bytes) (hl : pk.length = 33) (hf : pk.head? = some 2 ∨ pk.head? = some 3)
    (hp : P.pPk pk = true) (hs : P.pSig sig = true) (hlow : P.pLow sig = false) :
    p256Verify P pk msg sig = .error .highS := by
  simp [p256Verify, hl, hf, hp, hs, hlow]

theorem ml_ok_iff (P : Prim) (pk ctx msg sig : Bytes) :
    mlVerify P pk ctx msg sig = .ok () ↔ ctx.length ≤ 255 ∧ sig.length = 3309 ∧ pk.length = 1952 ∧
      P.mSig sig = true ∧ P.mVer pk ctx msg sig = true := by
  unfold mlVerify
  by_cases h1 : 255 < ctx.length <;> by_cases h2 : sig.length = 3309 <;> by_cases h3 : pk.length = 1952 <;>
    by_cases h4 : P.mSig sig = true <;> by_cases h5 : P.mVer pk ctx msg sig = true <;> simp [h1, h2, h3, h4, h5] <;> first | omega | simp_all

/-- A context over 255 bytes is an `InvalidLength`. -/
theorem ml_ctx_too_long (P : Prim) (pk ctx msg sig : Bytes) (h : 255 < ctx.length) :
    mlVerify P pk ctx msg sig = .error .invalidLength := by
  simp [mlVerify, h]

/-- A hybrid signature is accepted exactly when both halves verify, each over the domain-separated digest of the
message, never over the message itself. -/
theorem hybrid_ok_iff (H : Call → Bytes) (P : Prim) (pk msg sig : Bytes) :
    verify H P .hybrid pk msg sig = .ok () ↔
      (pk.length = Alg.hybrid.pkLen ∧ sig.length = Alg.hybrid.sigLen) ∧
      edVerify P (pk.take 32) (hybridDigest H msg) (sig.take 64) = .ok () ∧
      mlVerify P (pk.drop 32) [] (hybridDigest H msg) (sig.drop 64) = .ok () := by
  unfold verify
  by_cases h : pk.length ≠ Alg.hybrid.pkLen ∨ sig.length ≠ Alg.hybrid.sigLen
  · simp only [h, ite_true]
    constructor
    · intro e; cases e
    · intro ⟨hl, _⟩; omega
  · simp only [h, ite_false, andR]
    have hl : pk.length = Alg.hybrid.pkLen ∧ sig.length = Alg.hybrid.sigLen := by omega
    cases e : edVerify P (pk.take 32) (hybridDigest H msg) (sig.take 64) with
    | error x => simp [hl]
    | ok u =>
      cases u
      simp [hl]

/-- The first error reported is that of the Ed25519 half. -/
theorem hybrid_ed_error_first (H : Call → Bytes) (P : Prim) (pk msg sig : Bytes) (e : Err)
    (hl : ¬(pk.length ≠ Alg.hybrid.pkLen ∨ sig.length ≠ Alg.hybrid.sigLen))
    (h : edVerify P (pk.take 32) (hybridDigest H msg) (sig.take 64) = .error e) :
    verify H P .hybrid pk msg sig = .error e := by
  simp [verify, hl, h, andR]

/-- The digest both halves sign is 32 bytes whatever the message is (the primitive's output length). -/
theorem hybrid_digest_len {H : Call → Bytes} (hH : ∀ c, (H c).length = 32) (msg : Bytes) :
    (hybridDigest H msg).length = 32 := hH _

/-- A hybrid signature half is never a plain signature of the message: the digest is derived under the hybrid label,
a label no plain algorithm uses (`Call.label` differs). -/
theorem hybrid_domain (msg a : Bytes) :
    hybridCall msg ≠ (⟨.derive, bytes nodeIdLabel, a⟩ : Call) := by
  intro e
  simp only [hybridCall, Call.mk.injEq] at e
  exact absurd e.2.1 (by decide)

/-- `verify_node`: the id must match the key before anything is verified. -/
def verifyNode (H : Call → Bytes) (P : Prim) (id : NodeId) (pk msg sig : Bytes) : Except Err Unit :=
  if ¬ matches' H id id.alg pk then .error .nodeIdMismatch else verify H P id.alg pk msg sig

theorem verifyNode_mismatch (H : Call → Bytes) (P : Prim) (id : NodeId) (pk msg sig : Bytes)
    (h : fromPublic H id.alg pk ≠ .ok id) : verifyNode H P id pk msg sig = .error .nodeIdMismatch := by
  have : matches' H id id.alg pk = false := by
    cases hm : matches' H id id.alg pk
    · rfl
    · exact absurd ((matches_iff H id id.alg pk).mp hm) h
  simp [verifyNode, this]

theorem verifyNode_ok {H : Call → Bytes} {P : Prim} {id : NodeId} {pk msg sig : Bytes}
    (h : verifyNode H P id pk msg sig = .ok ()) :
    fromPublic H id.alg pk = .ok id ∧ verify H P id.alg pk msg sig = .ok () := by
  unfold verifyNode at h
  by_cases hm : matches' H id id.alg pk = true
  · simp only [hm] at h
    exact ⟨(matches_iff _ _ _ _).mp hm, h⟩
  · simp [hm] at h

/-! ## Key pairs -/

/-- The big-endian value of a byte string. -/
def beVal (b : Bytes) : Nat := b.foldl (fun a x => a * 256 + x) 0

/-- The order of the P-256 group. -/
def p256Order : Nat := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

/-- `P256SigningKey::from_slice` accepts a seed that is a nonzero scalar below the group order. -/
def p256SeedOk (seed : Bytes) : Bool := decide (0 < beVal seed ∧ beVal seed < p256Order)

/-- `Keypair::from_seed`: the error for a seed (the construction succeeds otherwise). -/
def fromSeed (alg : Alg) (seed : Bytes) : Except Err Unit :=
  if seed.length ≠ alg.seedLen then .error .invalidLength
  else if alg = .ecdsaP256 ∧ ¬p256SeedOk seed then .error .invalidSecretKey
  else .ok ()

theorem fromSeed_length (alg : Alg) (seed : Bytes) (h : seed.length ≠ alg.seedLen) :
    fromSeed alg seed = .error .invalidLength := by simp [fromSeed, h]

theorem fromSeed_p256 (seed : Bytes) (hl : seed.length = 32) :
    fromSeed .ecdsaP256 seed = .error .invalidSecretKey ↔ (beVal seed = 0 ∨ p256Order ≤ beVal seed) := by
  simp [fromSeed, p256SeedOk, Alg.seedLen, hl]
  omega

theorem fromSeed_other (alg : Alg) (seed : Bytes) (hl : seed.length = alg.seedLen) (h : alg ≠ .ecdsaP256) :
    fromSeed alg seed = .ok () := by simp [fromSeed, hl, h]

/-- `Keypair::public_key` and `sign`: a buffer shorter than the output is an `InvalidLength`, otherwise the length
returned is the algorithm's. (A hybrid writes its first half before it finds the second does not fit; the error is
the same.) -/
def writeOut (need : Nat) (out : Nat) : Except Err Nat := if out < need then .error .invalidLength else .ok need

theorem writeOut_iff (need out : Nat) : writeOut need out = .ok need ↔ need ≤ out := by
  unfold writeOut; split <;> simp_all

/-- `Keypair::node_id`: the buffer holds the largest key, so writing the key never fails and the id is the
`from_public` of the written key; the all-zero fallback of the code is not reachable. -/
theorem nodeId_not_fallback (H : Call → Bytes) (alg : Alg) (pk : Bytes) (h : pk.length = alg.pkLen) :
    ∃ id, fromPublic H alg pk = .ok id := by
  exact ⟨⟨alg, if alg = .ed25519 then pk else H (nodeIdCall alg.tag pk)⟩, by simp [fromPublic, h]⟩

theorem nodeId_buffer_fits (alg : Alg) : alg.pkLen ≤ maxPk := (lens_le_max alg).1

end Vinc.CryptoIdentity

#audit_axioms Vinc.CryptoIdentity.fromPublic_injective
#audit_axioms Vinc.CryptoIdentity.encodeId_injective
#audit_axioms Vinc.CryptoIdentity.matches_iff
#audit_axioms Vinc.CryptoIdentity.p256_ok_iff
#audit_axioms Vinc.CryptoIdentity.hybrid_ok_iff
#audit_axioms Vinc.CryptoIdentity.verifyNode_ok
#audit_axioms Vinc.CryptoIdentity.fromSeed_p256
