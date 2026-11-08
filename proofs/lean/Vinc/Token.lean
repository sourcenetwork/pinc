import Vinc.Varint

/-!
# Address-validation tokens

A model of `vinc-security/src/token.rs`. A token is `nonce(12) ++ sealed`, where `sealed` is the AEAD of
`addr ++ issued_at(8, big-endian) ++ kind(1)` under the token key, with the token label as associated data. The
AEAD is the hypothesis `IdealAead`: an ideal authenticated encryption, in which the only ciphertexts that open are the
ones `seal` produced (strict unforgeability) and `open` inverts `seal`. It is a structure of propositions that
the theorems take as an argument; it is not a postulate, and the real AEAD is not proved to satisfy it.

`validate` is modelled step for step, including the order of its checks, in `validate`; `verdict` is the part after
the AEAD opened (kind, address, then the age with `checked_sub`), which the trace replay checks on its own.
Bytes are `Nat`s; `u64` times are `Nat`s below `2^64`.
-/

namespace Vinc.Token
open Vinc.Varint

/-- The token length constants of the code. -/
def nonceLen : Nat := 12
def suffixLen : Nat := 9
def tagLen : Nat := 16
def maxAddr : Nat := 64
/-- `MAX_TOKEN_LEN`. -/
def maxToken : Nat := nonceLen + maxAddr + suffixLen + tagLen

/-- `TokenKind`. -/
inductive Kind where
  | retry
  | newToken
  deriving DecidableEq, Repr

def Kind.byte : Kind → Nat
  | .retry => 1
  | .newToken => 2

/-- `TokenKind::lifetime_ns`. -/
def Kind.lifetime : Kind → Nat
  | .retry => 10_000_000_000
  | .newToken => 86_400_000_000_000

/-- The big-endian bytes of a `u64`. -/
def be8 (v : Nat) : List Nat :=
  [v / 2 ^ 56 % 256, v / 2 ^ 48 % 256, v / 2 ^ 40 % 256, v / 2 ^ 32 % 256, v / 2 ^ 24 % 256, v / 2 ^ 16 % 256,
   v / 2 ^ 8 % 256, v % 256]

/-- `u64::from_be_bytes` on a byte list. -/
def fromBe8 (l : List Nat) : Nat := l.foldl (fun a b => a * 256 + b) 0

theorem fromBe8_be8 (v : Nat) (h : v < 2 ^ 64) : fromBe8 (be8 v) = v := by
  simp [fromBe8, be8]
  omega

theorem be8_length (v : Nat) : (be8 v).length = 8 := rfl

theorem be8_injective (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : be8 a = be8 b) : a = b := by
  have := congrArg fromBe8 h
  rwa [fromBe8_be8 a ha, fromBe8_be8 b hb] at this

private theorem list8 (l : List Nat) (h : l.length = 8) : ∃ a b c d e f g h', l = [a, b, c, d, e, f, g, h'] := by
  match l, h with
  | [a, b, c, d, e, f, g, h'], _ => exact ⟨a, b, c, d, e, f, g, h', rfl⟩

/-- Eight bytes read as a `u64` and written back are the same bytes. -/
theorem be8_fromBe8 (l : List Nat) (hl : l.length = 8) (hv : ValidBytes l) : be8 (fromBe8 l) = l := by
  obtain ⟨a, b, c, d, e, f, g, h', rfl⟩ := list8 l hl
  have ha := hv a (by simp)
  have hb := hv b (by simp)
  have hc := hv c (by simp)
  have hd := hv d (by simp)
  have he := hv e (by simp)
  have hf := hv f (by simp)
  have hg := hv g (by simp)
  have hh := hv h' (by simp)
  simp [fromBe8, be8]
  omega

theorem fromBe8_lt (l : List Nat) (hl : l.length = 8) (hv : ValidBytes l) : fromBe8 l < 2 ^ 64 := by
  obtain ⟨a, b, c, d, e, f, g, h', rfl⟩ := list8 l hl
  have ha := hv a (by simp)
  have hb := hv b (by simp)
  have hc := hv c (by simp)
  have hd := hv d (by simp)
  have he := hv e (by simp)
  have hf := hv f (by simp)
  have hg := hv g (by simp)
  have hh := hv h' (by simp)
  simp [fromBe8]
  omega

/-- The ideal authenticated encryption, as hypotheses. `enc k nonce ad m` is the ciphertext with its tag. -/
structure IdealAead (K : Type) where
  enc : K → List Nat → List Nat → List Nat → List Nat
  dec : K → List Nat → List Nat → List Nat → Option (List Nat)
  /-- Opening a sealed message gives the message back. -/
  dec_enc : ∀ k n ad m, dec k n ad (enc k n ad m) = some m
  /-- Strict unforgeability: only what `enc` produced opens, and to the message sealed. -/
  forge : ∀ k n ad c m, dec k n ad c = some m → c = enc k n ad m
  /-- The ciphertext is the message plus the 16-byte tag. -/
  length_enc : ∀ k n ad m, (enc k n ad m).length = m.length + tagLen
  /-- Plaintexts are byte strings. -/
  dec_valid : ∀ k n ad c m, dec k n ad c = some m → ValidBytes m

variable {K : Type}

/-- `TokenKey::issue`: `none` when the address is over `MAX_ADDR_LEN` (the output buffer is taken large enough). -/
def issue (A : IdealAead K) (k : K) (ad : List Nat) (addr : List Nat) (kind : Kind) (issued : Nat)
    (nonce : List Nat) : Option (List Nat) :=
  if addr.length > maxAddr then none
  else some (nonce ++ A.enc k nonce ad (addr ++ be8 issued ++ [kind.byte]))

/-- The outcome of `validate`, in the order the code checks. -/
inductive Verdict where
  | ok
  | malformed
  | auth
  | kind
  | addr
  | notYet
  | expired
  deriving DecidableEq, Repr

/-- The checks after the AEAD opened: kind, address, then `now.checked_sub(issued_at)` and the lifetime. -/
def verdict (kindOk addrOk : Bool) (issued now : Nat) (kind : Kind) : Verdict :=
  if !kindOk then .kind
  else if !addrOk then .addr
  else if now < issued then .notYet
  else if now - issued > kind.lifetime then .expired
  else .ok

/-- `TokenKey::validate`. -/
def validate (A : IdealAead K) (k : K) (ad : List Nat) (tok addr : List Nat) (kind : Kind) (now : Nat) : Verdict :=
  if tok.length < nonceLen + suffixLen + tagLen ∨ tok.length > maxToken then .malformed
  else
    match A.dec k (tok.take nonceLen) ad (tok.drop nonceLen) with
    | none => .auth
    | some body =>
      let ca := body.take (body.length - suffixLen)
      let suffix := body.drop (body.length - suffixLen)
      verdict (decide (suffix.drop 8 = [kind.byte])) (decide (ca = addr)) (fromBe8 (suffix.take 8)) now kind

theorem verdict_ok_iff (kindOk addrOk : Bool) (issued now : Nat) (kind : Kind) :
    verdict kindOk addrOk issued now kind = .ok ↔
      kindOk = true ∧ addrOk = true ∧ issued ≤ now ∧ now - issued ≤ kind.lifetime := by
  unfold verdict
  cases kindOk <;> cases addrOk <;>
    by_cases h1 : now < issued <;> by_cases h2 : now - issued > kind.lifetime <;> simp [h1, h2] <;> omega

/-- `validate` accepts exactly the tokens `issue` produced for that address and kind, whose age is within the
lifetime of the kind and which do not come from the future. -/
theorem validate_iff (A : IdealAead K) (k : K) (ad tok addr : List Nat) (kind : Kind) (now : Nat) :
    validate A k ad tok addr kind now = .ok ↔
      ∃ nonce issued, nonce.length = nonceLen ∧ issued < 2 ^ 64 ∧
        issue A k ad addr kind issued nonce = some tok ∧ issued ≤ now ∧ now - issued ≤ kind.lifetime := by
  constructor
  · intro h
    unfold validate at h
    by_cases hl : tok.length < nonceLen + suffixLen + tagLen ∨ tok.length > maxToken
    · simp [hl] at h
    simp only [hl, ite_false] at h
    cases ho : A.dec k (tok.take nonceLen) ad (tok.drop nonceLen) with
    | none => rw [ho] at h; simp at h
    | some body =>
      rw [ho] at h
      simp only at h
      obtain ⟨hk, ha, hn1, hn2⟩ := (verdict_ok_iff _ _ _ _ _).1 h
      simp only [decide_eq_true_eq] at ha hk
      have hseal := A.forge _ _ _ _ _ ho
      have hlen := A.length_enc k (tok.take nonceLen) ad body
      have hv := A.dec_valid _ _ _ _ _ ho
      have hl1 : 37 ≤ tok.length := by unfold nonceLen suffixLen tagLen at hl; omega
      have hl2 : tok.length ≤ 101 := by unfold maxToken nonceLen maxAddr suffixLen tagLen at hl; omega
      have hdrop : (tok.drop nonceLen).length = tok.length - nonceLen := by simp
      rw [hseal, hlen] at hdrop
      unfold nonceLen tagLen at hdrop
      have hb1 : 9 ≤ body.length := by omega
      have hb2 : body.length ≤ 73 := by omega
      have hsl : (body.drop (body.length - suffixLen)).length = 9 := by simp [suffixLen]; omega
      have hsv : ValidBytes ((body.drop (body.length - suffixLen)).take 8) := fun x hx =>
        hv x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
      have htm : ((body.drop (body.length - suffixLen)).take 8).length = 8 := by simp [List.length_take, hsl]
      have hrt := be8_fromBe8 _ htm hsv
      have hbody : body = addr ++ be8 (fromBe8 ((body.drop (body.length - suffixLen)).take 8)) ++ [kind.byte] := by
        rw [hrt, List.append_assoc, ← hk, List.take_append_drop, ← ha]
        exact (List.take_append_drop _ _).symm
      refine ⟨tok.take nonceLen, fromBe8 ((body.drop (body.length - suffixLen)).take 8), ?_, fromBe8_lt _ htm hsv,
        ?_, hn1, hn2⟩
      · simp [nonceLen]; omega
      · unfold issue
        have hal : addr.length ≤ maxAddr := by
          rw [← ha]; simp [suffixLen, maxAddr]; omega
        simp only [show ¬ addr.length > maxAddr by omega, ite_false]
        rw [← hbody, ← hseal, List.take_append_drop]
  · rintro ⟨nonce, issued, hn, hi, hiss, hn1, hn2⟩
    unfold issue at hiss
    by_cases hal : addr.length > maxAddr
    · simp [hal] at hiss
    simp only [hal, ite_false] at hiss
    cases hiss
    have hml : (addr ++ be8 issued ++ [kind.byte]).length = addr.length + 9 := by simp [be8_length]
    have hlen := A.length_enc k nonce ad (addr ++ be8 issued ++ [kind.byte])
    unfold validate
    have hr : ¬ ((nonce ++ A.enc k nonce ad (addr ++ be8 issued ++ [kind.byte])).length < nonceLen + suffixLen + tagLen ∨
        (nonce ++ A.enc k nonce ad (addr ++ be8 issued ++ [kind.byte])).length > maxToken) := by
      simp only [List.length_append, hlen, hml, hn]
      simp only [nonceLen, suffixLen, tagLen, maxToken, maxAddr] at *
      omega
    simp only [hr, ite_false]
    rw [List.take_left' hn, List.drop_left' hn, A.dec_enc]
    simp only [hml]
    have h1 : addr.length + 9 - suffixLen = addr.length := by unfold suffixLen; omega
    rw [h1]
    have h2 : (addr ++ be8 issued ++ [kind.byte]).take addr.length = addr := by
      rw [List.append_assoc, List.take_left']; rfl
    have h3 : (addr ++ be8 issued ++ [kind.byte]).drop addr.length = be8 issued ++ [kind.byte] := by
      rw [List.append_assoc, List.drop_left']; rfl
    rw [h2, h3]
    have h4 : (be8 issued ++ [kind.byte]).take 8 = be8 issued := by
      rw [List.take_left']; rfl
    have h5 : (be8 issued ++ [kind.byte]).drop 8 = [kind.byte] := by
      rw [List.drop_left']; rfl
    rw [h4, h5, fromBe8_be8 _ hi]
    exact (verdict_ok_iff _ _ _ _ _).2 ⟨by simp, by simp, hn1, hn2⟩

end Vinc.Token

#audit_axioms Vinc.Token.validate_iff
#audit_axioms Vinc.Token.verdict_ok_iff
#audit_axioms Vinc.Token.be8_injective
#audit_axioms Vinc.Token.be8_fromBe8
#audit_axioms Vinc.Token.fromBe8_be8
