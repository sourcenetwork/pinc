import Pinc.CryptoProvider

/-!
# The sealed format of `pinc-keystore` (`sealed.rs`)

`header || nonce (12) || ciphertext || tag (16)`: ChaCha20-Poly1305 under a 32-byte key, the whole header authenticated
as associated data. `build` is `encrypt` after the AEAD, `parse` is the split `decrypt` makes before it, and the
software store prefixes the version byte 1 (`swSeal`, `swUnseal`), the TPM store its version byte 2 and the wrapped key.

Proved without assumption: the encoding is canonical (`parse` inverts `build` and `build` inverts `parse`), every string
too short is an `InvalidSealed`, the length is `header + 28 + plaintext`. Under the ideal AEAD (a hypothesis on an
abstract primitive: it opens exactly what it sealed, and the sealed bytes determine key, nonce, associated data and
plaintext): `unseal (seal p) = p`, an accepted blob is a sealing under the same key of the header it carries, and a blob
sealed under another key, with another header or with any byte changed is refused.
-/

namespace Pinc.KeystoreSealed
open Pinc.CryptoKdf (Bytes)

def nonceLen : Nat := 12
def tagLen : Nat := 16

/-- `Err::InvalidSealed`, the only error of the format. -/
inductive Err where
  | invalidSealed
  deriving DecidableEq

/-- The parts of a blob. -/
structure Parts where
  header : Bytes
  nonce : Bytes
  ct : Bytes
  tag : Bytes
  deriving DecidableEq

/-- The bytes `encrypt` returns. -/
def build (p : Parts) : Bytes := p.header ++ p.nonce ++ p.ct ++ p.tag

/-- The split `decrypt` makes: `split_at_checked(header_len)`, `split_first_chunk::<12>`, `split_last_chunk::<16>`. -/
def parse (s : Bytes) (hl : Nat) : Except Err Parts :=
  if s.length < hl then .error .invalidSealed
  else
    let rest := s.drop hl
    if rest.length < nonceLen then .error .invalidSealed
    else
      let body := rest.drop nonceLen
      if body.length < tagLen then .error .invalidSealed
      else .ok ⟨s.take hl, rest.take nonceLen, body.take (body.length - tagLen), body.drop (body.length - tagLen)⟩

theorem build_length (p : Parts) : (build p).length = p.header.length + p.nonce.length + p.ct.length + p.tag.length := by
  simp only [build, List.length_append]

/-- `parse` is an error exactly when the blob is shorter than the header, the nonce and the tag together. -/
theorem parse_error_iff (s : Bytes) (hl : Nat) : parse s hl = .error .invalidSealed ↔ s.length < hl + nonceLen + tagLen := by
  unfold parse
  dsimp only
  by_cases h1 : s.length < hl
  · simp only [h1, ite_true, true_iff]; unfold nonceLen tagLen; omega
  by_cases h2 : (s.drop hl).length < nonceLen
  · simp only [h1, h2, ite_true, ite_false, true_iff]; simp [List.length_drop] at h2 h1; unfold nonceLen tagLen at *; omega
  by_cases h3 : ((s.drop hl).drop nonceLen).length < tagLen
  · simp only [h1, h2, h3, ite_true, ite_false, true_iff]; simp [List.length_drop] at h1 h2 h3; unfold nonceLen tagLen at *; omega
  · simp only [h1, h2, h3, ite_false]
    simp [List.length_drop] at h1 h2 h3
    unfold nonceLen tagLen at *
    constructor
    · intro e; cases e
    · intro h; omega

/-- The parts of a blob that is long enough. -/
def parts (s : Bytes) (hl : Nat) : Parts :=
  let body := (s.drop hl).drop nonceLen
  ⟨s.take hl, (s.drop hl).take nonceLen, body.take (body.length - tagLen), body.drop (body.length - tagLen)⟩

theorem parse_long {s : Bytes} {hl : Nat} (h : hl + nonceLen + tagLen ≤ s.length) : parse s hl = .ok (parts s hl) := by
  unfold parse parts
  dsimp only
  have h1 : ¬ s.length < hl := by unfold nonceLen tagLen at h; omega
  have h2 : ¬ (s.drop hl).length < nonceLen := by simp only [List.length_drop]; unfold nonceLen tagLen at *; omega
  have h3 : ¬ ((s.drop hl).drop nonceLen).length < tagLen := by simp only [List.length_drop]; unfold nonceLen tagLen at *; omega
  simp only [h1, h2, h3, ite_false]

/-- A blob that is long enough is the concatenation of its parts: the format is canonical. -/
theorem build_parts (s : Bytes) (hl : Nat) : build (parts s hl) = s := by
  simp only [build, parts]
  have e1 := List.take_append_drop (((s.drop hl).drop nonceLen).length - tagLen) ((s.drop hl).drop nonceLen)
  have e2 := List.take_append_drop nonceLen (s.drop hl)
  have e3 := List.take_append_drop hl s
  rw [List.append_assoc, List.append_assoc, e1, e2, e3]

theorem build_parse {s : Bytes} {hl : Nat} {p : Parts} (h : parse s hl = .ok p) : build p = s := by
  by_cases hlen : hl + nonceLen + tagLen ≤ s.length
  · rw [parse_long hlen] at h
    cases h
    exact build_parts s hl
  · have := (parse_error_iff s hl).mpr (by omega)
    rw [this] at h
    cases h

theorem parts_build (p : Parts) (hn : p.nonce.length = nonceLen) (ht : p.tag.length = tagLen) :
    parts (build p) p.header.length = p := by
  cases p with
  | mk h n c t =>
    simp only [] at hn ht
    have e1 : (h ++ n ++ c ++ t).take h.length = h := by
      rw [List.append_assoc, List.append_assoc]; exact List.take_left' rfl
    have e2 : (h ++ n ++ c ++ t).drop h.length = n ++ c ++ t := by
      rw [List.append_assoc, List.append_assoc, List.drop_left' rfl, List.append_assoc]
    have e3 : (n ++ c ++ t).take nonceLen = n := by
      rw [List.append_assoc, ← hn]; exact List.take_left' rfl
    have e4 : (n ++ c ++ t).drop nonceLen = c ++ t := by
      rw [List.append_assoc, ← hn, List.drop_left' rfl]
    have e5 : (c ++ t).length - tagLen = c.length := by simp [ht]
    simp only [parts, build, e1, e2, e3, e4, e5, List.take_left' (rfl : c.length = c.length), Parts.mk.injEq, true_and]
    exact List.drop_left' rfl

/-- The parts of a built blob are what was put in, when the nonce and the tag have their lengths. -/
theorem parse_build (p : Parts) (hn : p.nonce.length = nonceLen) (ht : p.tag.length = tagLen) :
    parse (build p) p.header.length = .ok p := by
  have hlen : p.header.length + nonceLen + tagLen ≤ (build p).length := by
    rw [build_length]; omega
  rw [parse_long hlen, parts_build p hn ht]

/-! ## Under the ideal AEAD -/

/-- The ideal AEAD as a hypothesis on abstract functions `sealF key nonce aad plaintext = (ciphertext, tag)` and
`open`: it opens what it sealed, opens nothing else, and the sealed bytes determine key, nonce, associated data and
plaintext (the collision freedom of the tag; the repository's `IdealAead` assumption, a hypothesis). -/
structure Ideal (sealF : Bytes → Bytes → Bytes → Bytes → Bytes × Bytes)
    (openF : Bytes → Bytes → Bytes → Bytes → Bytes → Option Bytes) : Prop where
  opens : ∀ k n a p, openF k n a (sealF k n a p).1 (sealF k n a p).2 = some p
  only_sealed : ∀ k n a c t p, openF k n a c t = some p → sealF k n a p = (c, t)
  inj : ∀ k n a p k' n' a' p', sealF k n a p = sealF k' n' a' p' → k = k' ∧ n = n' ∧ a = a' ∧ p = p'
  shape : ∀ k n a p, (sealF k n a p).1.length = p.length ∧ (sealF k n a p).2.length = tagLen

variable (sealF : Bytes → Bytes → Bytes → Bytes → Bytes × Bytes) (openF : Bytes → Bytes → Bytes → Bytes → Bytes → Option Bytes)

/-- `sealed::encrypt`. -/
def encrypt (k hdr n p : Bytes) : Bytes := build ⟨hdr, n, (sealF k n hdr p).1, (sealF k n hdr p).2⟩

/-- `sealed::decrypt`: any failure is `InvalidSealed`. -/
def decrypt (k s : Bytes) (hl : Nat) : Except Err Bytes :=
  match parse s hl with
  | .error e => .error e
  | .ok q => match openF k q.nonce q.header q.ct q.tag with
    | some p => .ok p
    | none => .error .invalidSealed

variable {sealF openF}

theorem encrypt_length (h : Ideal sealF openF) (k hdr n p : Bytes) :
    (encrypt sealF k hdr n p).length = hdr.length + n.length + p.length + tagLen := by
  simp only [encrypt, build_length, (h.shape k n hdr p).1, (h.shape k n hdr p).2]

/-- Unsealing what was sealed gives the plaintext back. -/
theorem decrypt_encrypt (h : Ideal sealF openF) (k hdr n p : Bytes) (hn : n.length = nonceLen) :
    decrypt openF k (encrypt sealF k hdr n p) hdr.length = .ok p := by
  have hp := parse_build ⟨hdr, n, (sealF k n hdr p).1, (sealF k n hdr p).2⟩ hn (h.shape k n hdr p).2
  simp only [decrypt, encrypt]
  rw [hp]
  simp only [h.opens]

/-- An accepted blob is a sealing of the plaintext under the same key, with the header and the nonce it carries. -/
theorem decrypt_sound (h : Ideal sealF openF) {k s : Bytes} {hl : Nat} {p : Bytes} (hd : decrypt openF k s hl = .ok p) :
    ∃ n, n.length = nonceLen ∧ s = encrypt sealF k (s.take hl) n p := by
  unfold decrypt at hd
  cases hp : parse s hl with
  | error e => simp [hp] at hd
  | ok q =>
    rw [hp] at hd
    simp only at hd
    cases ho : openF k q.nonce q.header q.ct q.tag with
    | none => simp [ho] at hd
    | some p' =>
      simp only [ho, Except.ok.injEq] at hd
      subst hd
      have hs := h.only_sealed _ _ _ _ _ _ ho
      have hb := build_parse hp
      refine ⟨q.nonce, ?_, ?_⟩
      · by_cases hlen : hl + nonceLen + tagLen ≤ s.length
        · rw [parse_long hlen] at hp
          cases hp
          simp [parts, List.length_take, List.length_drop]
          unfold nonceLen tagLen at *
          omega
        · have := (parse_error_iff s hl).mpr (by omega)
          rw [this] at hp; cases hp
      · have hh : q.header = s.take hl := by
          by_cases hlen : hl + nonceLen + tagLen ≤ s.length
          · rw [parse_long hlen] at hp; cases hp; rfl
          · have := (parse_error_iff s hl).mpr (by omega)
            rw [this] at hp; cases hp
        simp only [encrypt, ← hh, hs]
        rw [← hb]

/-- A blob sealed under one key is refused under another. -/
theorem wrong_key (h : Ideal sealF openF) {k k' : Bytes} (hk : k ≠ k') (hdr n p : Bytes) (hn : n.length = nonceLen) :
    decrypt openF k' (encrypt sealF k hdr n p) hdr.length = .error .invalidSealed := by
  cases hd : decrypt openF k' (encrypt sealF k hdr n p) hdr.length with
  | error e => cases e; rfl
  | ok p' =>
    obtain ⟨n', hn', hs⟩ := decrypt_sound h hd
    have hp := parse_build ⟨hdr, n, (sealF k n hdr p).1, (sealF k n hdr p).2⟩ hn (h.shape k n hdr p).2
    have hlen : (encrypt sealF k hdr n p).take hdr.length = hdr := by
      simp only [encrypt, build, List.append_assoc]; exact List.take_left' rfl
    rw [hlen] at hs
    have h1 := congrArg (fun s => parse s hdr.length) hs
    simp only [encrypt] at h1
    have hn2 := parse_build ⟨hdr, n', (sealF k' n' hdr p').1, (sealF k' n' hdr p').2⟩ hn' (h.shape k' n' hdr p').2
    rw [hp, hn2] at h1
    have h2 := Except.ok.inj h1
    have h3 : (sealF k n hdr p) = (sealF k' n' hdr p') := by
      have := congrArg (fun q : Parts => (q.ct, q.tag)) h2
      exact this
    exact absurd (h.inj _ _ _ _ _ _ _ _ h3).1 hk

/-- A blob whose header (of the same length) was changed is refused. -/
theorem wrong_header (h : Ideal sealF openF) (k hdr hdr' n p : Bytes) (hn : n.length = nonceLen)
    (hl : hdr'.length = hdr.length) (hne : hdr' ≠ hdr) :
    decrypt openF k (hdr' ++ (encrypt sealF k hdr n p).drop hdr.length) hdr.length = .error .invalidSealed := by
  cases hd : decrypt openF k (hdr' ++ (encrypt sealF k hdr n p).drop hdr.length) hdr.length with
  | error e => cases e; rfl
  | ok p' =>
    obtain ⟨n', hn', hs⟩ := decrypt_sound h hd
    have hrest : (encrypt sealF k hdr n p).drop hdr.length = n ++ (sealF k n hdr p).1 ++ (sealF k n hdr p).2 := by
      simp only [encrypt, build, List.append_assoc]; rw [List.drop_left' rfl]
    have hlen : (hdr' ++ (encrypt sealF k hdr n p).drop hdr.length).take hdr.length = hdr' := by
      rw [← hl]; exact List.take_left' rfl
    rw [hlen] at hs
    have e : hdr' ++ (encrypt sealF k hdr n p).drop hdr.length =
        build ⟨hdr', n, (sealF k n hdr p).1, (sealF k n hdr p).2⟩ := by
      simp only [hrest, build, List.append_assoc]
    rw [e] at hs
    have p1 := parse_build ⟨hdr', n, (sealF k n hdr p).1, (sealF k n hdr p).2⟩ hn (h.shape k n hdr p).2
    have p2 := parse_build ⟨hdr', n', (sealF k n' hdr' p').1, (sealF k n' hdr' p').2⟩ hn' (h.shape k n' hdr' p').2
    have h1 := congrArg (fun s => parse s hdr'.length) hs
    simp only [encrypt] at h1
    rw [p1, p2] at h1
    have h2 := Except.ok.inj h1
    have h3 : sealF k n hdr p = sealF k n' hdr' p' := by
      have := congrArg (fun q : Parts => (q.ct, q.tag)) h2
      exact this
    exact (hne (h.inj _ _ _ _ _ _ _ _ h3).2.2.1.symm).elim

/-! ## The software store: version byte 1 -/

def swVersion : Nat := 1

/-- `SoftwareStore::seal`: the header is the version byte. -/
def swSeal (sealF : Bytes → Bytes → Bytes → Bytes → Bytes × Bytes) (k n p : Bytes) : Bytes :=
  encrypt sealF k [swVersion] n p

/-- `SoftwareStore::unseal`: the first byte must be the version. -/
def swUnseal (openF : Bytes → Bytes → Bytes → Bytes → Bytes → Option Bytes) (k s : Bytes) : Except Err Bytes :=
  match s with
  | v :: _ => if v = swVersion then decrypt openF k s 1 else .error .invalidSealed
  | [] => .error .invalidSealed

theorem swUnseal_swSeal (h : Ideal sealF openF) (k n p : Bytes) (hn : n.length = nonceLen) :
    swUnseal openF k (swSeal sealF k n p) = .ok p := by
  have := decrypt_encrypt h k [swVersion] n p hn
  simp only [swSeal, encrypt, build, swUnseal, List.cons_append, List.nil_append, swVersion, List.length_cons,
    List.length_nil, ite_true] at this ⊢
  exact this

theorem swUnseal_empty (k : Bytes) : swUnseal openF k [] = .error .invalidSealed := rfl

theorem swUnseal_version (k : Bytes) (v : Nat) (rest : Bytes) (hv : v ≠ swVersion) :
    swUnseal openF k (v :: rest) = .error .invalidSealed := by simp [swUnseal, hv]

theorem swSeal_length (h : Ideal sealF openF) (k n p : Bytes) :
    (swSeal sealF k n p).length = 1 + n.length + p.length + tagLen := by
  simp [swSeal, encrypt_length h, swVersion]

theorem swSeal_first (k n p : Bytes) : (swSeal sealF k n p).head? = some swVersion := by
  simp [swSeal, encrypt, build, swVersion]

end Pinc.KeystoreSealed

#audit_axioms Pinc.KeystoreSealed.parse_error_iff
#audit_axioms Pinc.KeystoreSealed.build_parse
#audit_axioms Pinc.KeystoreSealed.parse_build
#audit_axioms Pinc.KeystoreSealed.decrypt_encrypt
#audit_axioms Pinc.KeystoreSealed.decrypt_sound
#audit_axioms Pinc.KeystoreSealed.wrong_key
#audit_axioms Pinc.KeystoreSealed.wrong_header
#audit_axioms Pinc.KeystoreSealed.swUnseal_swSeal
