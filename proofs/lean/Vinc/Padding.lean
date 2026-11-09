import Vinc.Amp
import Vinc.Credit

/-!
# Initial padding and message sizes

A model of the size functions of `vinc-security/src/message.rs`: `sealed_len`, `reply_len`, `min_initial_len`
and the constants `FULL_INITIAL_MIN` (1200), `SHORT_INITIAL_MIN` (464), `MIN_DATAGRAM` (1200), `MAX_ID_SIG_LEN`,
`MAX_SEALED_LEN` and `MAX_MESSAGE_LEN`. The key and signature lengths of the four identity algorithms are those of
`vinc-crypto` (`IdentityAlg::public_key_len`, `signature_len`); the KEM ciphertext is 1088 bytes, the AEAD tag 16, the
credit record 6, a connection id at most 20.

The statements: for every algorithm and both forms, three times `min_initial_len` covers the Reply plus the
overhead of its datagrams (`budget_covers_reply`), and so a responder that received a padded Initial can send its whole
Reply under the anti-amplification budget (`reply_sendable`, in terms of `Amp.canSend`, for any split of the Reply
into datagrams); `min_initial_len` is never below the floor of its form; the short Initial of a 32-byte identity is
exactly 464 bytes and 464 x 3 covers its Reply; `MAX_MESSAGE_LEN = 6529` bounds every `reply_len`; and every
`sealed_len` is at most `MAX_SEALED_LEN`.
-/

namespace Vinc.Padding

/-- `vinc_crypto::IdentityAlg`. -/
inductive Alg where
  | ed25519 | ecdsaP256 | mlDsa65 | hybrid
  deriving DecidableEq, Repr

/-- `Initial` form (`InitialForm`). -/
inductive Form where
  | full | short
  deriving DecidableEq, Repr

def Alg.all : List Alg := [.ed25519, .ecdsaP256, .mlDsa65, .hybrid]
def Form.all : List Form := [.full, .short]

theorem Alg.mem_all (a : Alg) : a ∈ Alg.all := by cases a <;> simp [Alg.all]
theorem Form.mem_all (f : Form) : f ∈ Form.all := by cases f <;> simp [Form.all]

/-- `IdentityAlg::tag`. -/
def Alg.tag : Alg → Nat
  | .ed25519 => 1 | .ecdsaP256 => 2 | .mlDsa65 => 3 | .hybrid => 4

/-- `IdentityAlg::public_key_len`: `ED_PK = 32`, `P256_PK = 33`, `ML_PK = 1952`. -/
def Alg.publicKeyLen : Alg → Nat
  | .ed25519 => 32 | .ecdsaP256 => 33 | .mlDsa65 => 1952 | .hybrid => 32 + 1952

/-- `IdentityAlg::signature_len`: `ED_SIG = 64`, `P256_SIG = 64`, `ML_SIG = 3309`. -/
def Alg.signatureLen : Alg → Nat
  | .ed25519 => 64 | .ecdsaP256 => 64 | .mlDsa65 => 3309 | .hybrid => 64 + 3309

def maxPublicKeyLen : Nat := 32 + 1952
def maxSignatureLen : Nat := 64 + 3309
/-- `KEM_CIPHERTEXT_LEN`. -/
def kemCiphertextLen : Nat := 1088
/-- `Aead::TAG_LEN`. -/
def tagLen : Nat := 16
/-- `MAX_CID_LEN`. -/
def maxCidLen : Nat := 20
/-- `FULL_INITIAL_MIN`. -/
def fullInitialMin : Nat := 1200
/-- `SHORT_INITIAL_MIN`. -/
def shortInitialMin : Nat := 464
/-- `MIN_DATAGRAM`. -/
def minDatagram : Nat := 1200

/-- `MAX_ID_SIG_LEN`. -/
def maxIdSigLen : Nat := 1 + 2 + maxPublicKeyLen + 2 + maxSignatureLen + Credit.recordLen
/-- `MAX_SEALED_LEN`. -/
def maxSealedLen : Nat := maxIdSigLen + tagLen

/-- `sealed_len`. -/
def sealedLen (a : Alg) : Nat :=
  1 + 2 + a.publicKeyLen + 2 + a.signatureLen + Credit.recordLen + tagLen

/-- `reply_len`. -/
def replyLen (a : Alg) : Nat :=
  1 + (1 + maxCidLen) + 1 + 32 + kemCiphertextLen + 2 + sealedLen a

/-- `usize::div_ceil` for a positive divisor, as the standard library writes it. -/
def divCeil (a b : Nat) : Nat := a / b + if a % b > 0 then 1 else 0

/-- `min_initial_len`. -/
def minInitialLen (f : Form) (a : Alg) : Nat :=
  let reply := replyLen a
  let datagrams := divCeil reply minDatagram
  let needed := divCeil (reply + datagrams * Amp.overhead) 3
  let floor := match f with
    | .full => fullInitialMin
    | .short => shortInitialMin
  if needed > floor then needed else floor

/-- `MAX_MESSAGE_LEN = reply_len(Hybrid)`. -/
def maxMessageLen : Nat := replyLen .hybrid

theorem divCeil_ge (a b : Nat) (hb : 0 < b) : a ≤ b * divCeil a b := by
  unfold divCeil
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.mod_lt a hb
  split <;> simp only [Nat.mul_add, Nat.mul_zero, Nat.mul_one] <;> omega

/-- The constants of the code. -/
theorem constants :
    maxIdSigLen = 5368 ∧ maxSealedLen = 5384 ∧ maxMessageLen = 6529 ∧ replyLen .ed25519 = 1268 := by decide

/-- `MAX_ID_SIG_LEN` is the sealed plaintext of the hybrid identity, `MAX_SEALED_LEN` its sealed length. -/
theorem max_is_hybrid : maxSealedLen = sealedLen .hybrid ∧ maxIdSigLen + tagLen = maxSealedLen := by decide

/-- Every sealed identity fits `MAX_SEALED_LEN`. -/
theorem sealedLen_le_max (a : Alg) : sealedLen a ≤ maxSealedLen := by
  cases a <;> decide

/-- `MAX_MESSAGE_LEN` bounds every Reply. -/
theorem replyLen_le_max (a : Alg) : replyLen a ≤ maxMessageLen := by
  cases a <;> decide

/-- The public key and signature of every algorithm fit the maxima (the buffers of the code). -/
theorem lens_le_max (a : Alg) : a.publicKeyLen ≤ maxPublicKeyLen ∧ a.signatureLen ≤ maxSignatureLen := by
  cases a <;> decide

/-- `min_initial_len` is at least the floor of its form. -/
theorem minInitialLen_ge_floor (f : Form) (a : Alg) :
    (f = .full → fullInitialMin ≤ minInitialLen f a) ∧ (f = .short → shortInitialMin ≤ minInitialLen f a) := by
  cases f <;> cases a <;> decide

/-- Three times `min_initial_len` covers the Reply and the overhead of each datagram it needs, for every
algorithm and both forms. -/
theorem budget_covers_reply (f : Form) (a : Alg) :
    replyLen a + divCeil (replyLen a) minDatagram * Amp.overhead ≤ 3 * minInitialLen f a := by
  cases f <;> cases a <;> decide

/-- The same for any Reply length, from the definition: the padding rule is correct for every reply size. -/
theorem budget_covers_any (f : Form) (reply : Nat) :
    let datagrams := divCeil reply minDatagram
    let needed := divCeil (reply + datagrams * Amp.overhead) 3
    let floor := match f with
      | .full => fullInitialMin
      | .short => shortInitialMin
    reply + datagrams * Amp.overhead ≤ 3 * (if needed > floor then needed else floor) := by
  intro datagrams needed floor
  have := divCeil_ge (reply + datagrams * Amp.overhead) 3 (by decide)
  split <;> omega

/-- The short Initial of a 32-byte identity (Ed25519) is 464 bytes, and 464 x 3 covers its Reply. -/
theorem short_ed25519 : minInitialLen .short .ed25519 = 464 ∧ replyLen .ed25519 ≤ 3 * 464 := by decide

/-- The values of every combination, as the code computes them. -/
theorem min_initial_values :
    Form.all.flatMap (fun f => Alg.all.map (fun a => minInitialLen f a)) = [1200, 1200, 2241, 2273, 464, 464, 2241, 2273] := by
  decide

/-! ## The Reply fits the budget -/

/-- Sending datagrams of the given sizes one after another is allowed at every step by `can_send`. -/
def sendable : Amp.Budget → List Nat → Bool
  | _, [] => true
  | b, n :: ns => Amp.canSend b n && sendable (Amp.onSend b n) ns

/-- Under the budget of a path that received `min_initial_len` bytes, any split of the Reply into datagrams (any
list of sizes whose sum is at most the Reply) is allowed by `can_send` at every send. -/
theorem reply_sendable (f : Form) (a : Alg) (ns : List Nat) (hs : ns.sum ≤ replyLen a) :
    sendable (Amp.onReceive Amp.Budget.new (minInitialLen f a)) ns = true := by
  have hcov := budget_covers_reply f a
  have h6529 : replyLen a ≤ 6529 := by cases a <;> decide
  have hdg : 1 ≤ divCeil (replyLen a) minDatagram := by cases a <;> decide
  have hov : Amp.overhead = 48 := rfl
  rw [hov] at hcov
  have hmin : minInitialLen f a ≤ Amp.u64max := by cases f <;> cases a <;> decide
  have hrx : (Amp.onReceive Amp.Budget.new (minInitialLen f a)).rx = minInitialLen f a := by
    show Amp.satAdd 0 (minInitialLen f a) = _
    unfold Amp.satAdd
    omega
  -- the invariant: the sum still to send plus what was sent plus the overhead stays within three times rx
  have key : ∀ (ns : List Nat) (b : Amp.Budget), b.validated = false → b.rx = minInitialLen f a →
      b.tx + ns.sum + 48 ≤ 3 * b.rx → b.tx + ns.sum ≤ Amp.u64max → sendable b ns = true := by
    intro ns
    induction ns with
    | nil => intro b _ _ _ _; rfl
    | cons n ns ih =>
      intro b hv hr hle hu
      simp only [sendable, Bool.and_eq_true]
      have hc : Amp.canSend b n = true := by
        rw [Amp.canSend_iff b n hv]
        unfold Amp.factor Amp.overhead
        simp only [List.sum_cons] at hle
        omega
      refine ⟨hc, ih _ ?_ ?_ ?_ ?_⟩
      · exact hv
      · exact hr
      · have hx : (Amp.onSend b n).tx = b.tx + n := by
          show Amp.satAdd b.tx n = _
          simp only [List.sum_cons] at hu
          exact Amp.satAdd_exact _ _ (by omega)
        have hrr : (Amp.onSend b n).rx = b.rx := rfl
        simp only [List.sum_cons] at hle
        omega
      · have hx : (Amp.onSend b n).tx = b.tx + n := by
          show Amp.satAdd b.tx n = _
          simp only [List.sum_cons] at hu
          exact Amp.satAdd_exact _ _ (by omega)
        simp only [List.sum_cons] at hu
        omega
  have htx : (Amp.onReceive Amp.Budget.new (minInitialLen f a)).tx = 0 := rfl
  apply key ns _ rfl hrx
  · rw [htx, hrx]
    omega
  · rw [htx]
    unfold Amp.u64max
    omega

end Vinc.Padding

#audit_axioms Vinc.Padding.constants
#audit_axioms Vinc.Padding.max_is_hybrid
#audit_axioms Vinc.Padding.sealedLen_le_max
#audit_axioms Vinc.Padding.replyLen_le_max
#audit_axioms Vinc.Padding.lens_le_max
#audit_axioms Vinc.Padding.minInitialLen_ge_floor
#audit_axioms Vinc.Padding.budget_covers_reply
#audit_axioms Vinc.Padding.budget_covers_any
#audit_axioms Vinc.Padding.short_ed25519
#audit_axioms Vinc.Padding.min_initial_values
#audit_axioms Vinc.Padding.reply_sendable
