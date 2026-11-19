import Pinc.Amp
import Pinc.Credit

/-!
# Initial padding and message sizes

A model of the size functions of `pinc-security/src/message.rs`: `sealed_len`, `reply_len`, `reply_datagrams`,
`min_initial_len` and the constants `FULL_INITIAL_MIN` (1200), `SHORT_INITIAL_MIN` (464), `MIN_DATAGRAM` (1200),
`FRAGMENT_HEADER` (50), `WHOLE_REPLY_MAX` (1388), `SPLIT_CID_MAX` (5), `MAX_ID_SIG_LEN`, `MAX_SEALED_LEN` and
`MAX_MESSAGE_LEN`. The key and signature lengths of the four identity algorithms are those of `pinc-crypto`
(`IdentityAlg::public_key_len`, `signature_len`); the KEM ciphertext is 1088 bytes, the AEAD tag 16, the credit
record 6, a connection id at most 20.

The statements: for every algorithm and both forms, three times `min_initial_len` covers the Reply plus the framing
and the overhead of every datagram `reply_datagrams` counts (`budget_covers_reply`); `min_initial_len` is never below
the floor of its form; the short Initial of a 32-byte identity is exactly 464 bytes and 464 x 3 covers its Reply;
`MAX_MESSAGE_LEN = 6529` bounds every `reply_len`; and every `sealed_len` is at most `MAX_SEALED_LEN`.

What the responder can send: under the budget of a path that received `min_initial_len` bytes, any split of the
Reply into datagrams is allowed by `Amp.canSend` when only the datagram sizes are recorded (`reply_sendable`); and
the transport, which records every datagram's size plus the 48-byte overhead (`finish_datagram`), can send the Reply
in at most `reply_datagrams` datagrams that carry it with their framing (`reply_sendable_charged`). The transport's
default cuts every first flight into `MIN_DATAGRAM`-byte datagrams, so a Reply counted as one datagram may take two;
with connection ids of at most `SPLIT_CID_MAX` bytes (both the transport's default and the endpoint use 4) that cut
fits too, for every algorithm and both forms (`budget_covers_split`, `split_sendable_charged`), and 6-byte ids would
not fit the short Initial of a 32-byte identity (`split_cid_max_tight`).
-/

namespace Pinc.Padding

/-- `pinc_crypto::IdentityAlg`. -/
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
/-- `FRAGMENT_HEADER`: the long header with two 20-byte ids and a two-byte length, and two two-byte varints. -/
def fragmentHeader : Nat := 1 + 1 + 2 * (1 + maxCidLen) + 2 + 2 + 2
/-- `WHOLE_REPLY_MAX`: the 1452-byte probe size less the room the transport keeps. -/
def wholeReplyMax : Nat := 1452 - 64
/-- `SPLIT_CID_MAX`. -/
def splitCidMax : Nat := 5

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

/-- `reply_datagrams`: one for a Reply a whole first flight carries, else as many `MIN_DATAGRAM`-byte datagrams as
carry it with their framing. -/
def replyDatagrams (reply : Nat) : Nat :=
  if reply ≤ wholeReplyMax then 1 else divCeil reply (minDatagram - fragmentHeader)

/-- `min_initial_len`. -/
def minInitialLen (f : Form) (a : Alg) : Nat :=
  let reply := replyLen a
  let datagrams := replyDatagrams reply
  let needed := divCeil (reply + datagrams * (Amp.overhead + fragmentHeader)) 3
  let floor := match f with
    | .full => fullInitialMin
    | .short => shortInitialMin
  if needed > floor then needed else floor

/-- `MAX_MESSAGE_LEN = reply_len(Hybrid)`. -/
def maxMessageLen : Nat := replyLen .hybrid

/-- The Reply when the responder's connection id is `c` bytes long instead of the 20 `reply_len` allows for. -/
def replyLenWith (a : Alg) (c : Nat) : Nat := replyLen a - (maxCidLen - c)

/-- The framing of a handshake datagram whose two connection ids are `c` bytes long (`write_handshake`). -/
def framingWith (c : Nat) : Nat := 1 + 1 + 2 * (1 + c) + 2 + 2 + 2

/-- The datagrams of `MIN_DATAGRAM` bytes the transport cuts a Reply of `reply` bytes into, with ids of `c` bytes. -/
def splitDatagrams (reply c : Nat) : Nat := divCeil reply (minDatagram - framingWith c)

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

/-- Three times `min_initial_len` covers the Reply and the framing and overhead of each datagram it needs, for
every algorithm and both forms. -/
theorem budget_covers_reply (f : Form) (a : Alg) :
    replyLen a + replyDatagrams (replyLen a) * (Amp.overhead + fragmentHeader) ≤ 3 * minInitialLen f a := by
  cases f <;> cases a <;> decide

/-- The same for any Reply length, from the definition: the padding rule is correct for every reply size. -/
theorem budget_covers_any (f : Form) (reply : Nat) :
    let datagrams := replyDatagrams reply
    let needed := divCeil (reply + datagrams * (Amp.overhead + fragmentHeader)) 3
    let floor := match f with
      | .full => fullInitialMin
      | .short => shortInitialMin
    reply + datagrams * (Amp.overhead + fragmentHeader) ≤ 3 * (if needed > floor then needed else floor) := by
  intro datagrams needed floor
  have := divCeil_ge (reply + datagrams * (Amp.overhead + fragmentHeader)) 3 (by decide)
  split <;> omega

/-- With connection ids of at most `SPLIT_CID_MAX` bytes, three times `min_initial_len` also covers the Reply cut
into `MIN_DATAGRAM`-byte datagrams with the framing and overhead of each, for every algorithm and both forms. -/
theorem budget_covers_split_table :
    ∀ c ∈ List.range (splitCidMax + 1), ∀ f ∈ Form.all, ∀ a ∈ Alg.all,
      replyLenWith a c + splitDatagrams (replyLenWith a c) c * (Amp.overhead + framingWith c) ≤
        3 * minInitialLen f a := by
  decide

theorem budget_covers_split (f : Form) (a : Alg) (c : Nat) (hc : c ≤ splitCidMax) :
    replyLenWith a c + splitDatagrams (replyLenWith a c) c * (Amp.overhead + framingWith c) ≤
      3 * minInitialLen f a :=
  budget_covers_split_table c (List.mem_range.2 (Nat.lt_succ_of_le hc)) f (Form.mem_all f) a (Alg.mem_all a)

/-- `SPLIT_CID_MAX` is the largest such length: with 6-byte ids the cut Reply of a 32-byte identity exceeds three
times the short Initial. -/
theorem split_cid_max_tight :
    3 * minInitialLen .short .ed25519 <
      replyLenWith .ed25519 (splitCidMax + 1) +
        splitDatagrams (replyLenWith .ed25519 (splitCidMax + 1)) (splitCidMax + 1) *
          (Amp.overhead + framingWith (splitCidMax + 1)) := by
  decide

/-- The short Initial of a 32-byte identity (Ed25519) is 464 bytes, and 464 x 3 covers its Reply. -/
theorem short_ed25519 : minInitialLen .short .ed25519 = 464 ∧ replyLen .ed25519 ≤ 3 * 464 := by decide

/-- The values of every combination, as the code computes them. -/
theorem min_initial_values :
    Form.all.flatMap (fun f => Alg.all.map (fun a => minInitialLen f a)) = [1200, 1200, 2341, 2373, 464, 464, 2341, 2373] := by
  decide

/-! ## The Reply fits the budget -/

/-- Sending datagrams of the given sizes one after another is allowed at every step by `can_send`. -/
def sendable : Amp.Budget → List Nat → Bool
  | _, [] => true
  | b, n :: ns => Amp.canSend b n && sendable (Amp.onSend b n) ns

/-- Under the budget of a path that received `min_initial_len` bytes, any split of the Reply into datagrams (any
list of sizes whose sum is at most the Reply and the framing of the datagrams that carry it) is allowed by
`can_send` at every send. -/
theorem reply_sendable (f : Form) (a : Alg)
    (ns : List Nat) (hs : ns.sum ≤ replyLen a + replyDatagrams (replyLen a) * fragmentHeader) :
    sendable (Amp.onReceive Amp.Budget.new (minInitialLen f a)) ns = true := by
  have hcov := budget_covers_reply f a
  have h6529 : replyLen a ≤ 6529 := by cases a <;> decide
  have hdg : 1 ≤ replyDatagrams (replyLen a) := by cases a <;> decide
  have hdg6 : replyDatagrams (replyLen a) ≤ 6 := by cases a <;> decide
  have hov : Amp.overhead = 48 := rfl
  have hfh : fragmentHeader = 50 := rfl
  rw [hov, hfh] at hcov
  rw [hfh] at hs
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

/-- Sending datagrams of the given sizes one after another as the transport does (`finish_datagram`): each send is
allowed by `can_send` and records the datagram's size plus the 48-byte overhead. -/
def sendableCharged : Amp.Budget → List Nat → Bool
  | _, [] => true
  | b, n :: ns => Amp.canSend b n && sendableCharged (Amp.onSend b (n + Amp.overhead)) ns

/-- From any unvalidated budget, datagrams whose sizes plus 48 bytes each fit in what is left are all sent. -/
theorem charged_from (ns : List Nat) : ∀ b : Amp.Budget, b.validated = false →
    b.tx + ns.sum + ns.length * Amp.overhead ≤ b.rx * Amp.factor → sendableCharged b ns = true := by
  induction ns with
  | nil => intro _ _ _; rfl
  | cons n ns ih =>
    intro b hv h
    simp only [sendableCharged, Bool.and_eq_true]
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at h
    refine ⟨(Amp.canSend_iff b n hv).2 (by omega), ih _ hv ?_⟩
    have hx := Amp.onSend_tx_le b (n + Amp.overhead)
    have hr : (Amp.onSend b (n + Amp.overhead)).rx = b.rx := rfl
    rw [hr]
    omega

/-- A path that received `rx` bytes lets the transport send any datagrams whose sizes plus 48 bytes each total at
most three times `rx`. -/
theorem charged_sendable (rx : Nat) (hrx : rx ≤ Amp.u64max) (ns : List Nat)
    (h : ns.sum + ns.length * Amp.overhead ≤ 3 * rx) :
    sendableCharged (Amp.onReceive Amp.Budget.new rx) ns = true := by
  apply charged_from ns _ rfl
  have hr : (Amp.onReceive Amp.Budget.new rx).rx = rx := by
    show Amp.satAdd 0 rx = rx
    unfold Amp.satAdd
    omega
  have ht : (Amp.onReceive Amp.Budget.new rx).tx = 0 := rfl
  rw [hr, ht]
  unfold Amp.factor
  omega

/-- The step shared by both cuts: `d` datagrams with `k` bytes of framing each carry a message of `q` bytes within
three times `rx`, so any at most `d` datagrams that carry the message with their framing are sent. -/
theorem cut_sendable (rx q d k : Nat) (hrx : rx ≤ Amp.u64max) (hcov : q + d * (Amp.overhead + k) ≤ 3 * rx)
    (ns : List Nat) (hlen : ns.length ≤ d) (hs : ns.sum ≤ q + ns.length * k) :
    sendableCharged (Amp.onReceive Amp.Budget.new rx) ns = true := by
  apply charged_sendable rx hrx ns
  have h1 : ns.length * (Amp.overhead + k) ≤ d * (Amp.overhead + k) := Nat.mul_le_mul_right _ hlen
  simp only [Nat.mul_add] at h1 hcov
  omega

/-- The responder sends its Reply, in at most `reply_datagrams` datagrams that carry it with their framing, under
the budget of a path that received `min_initial_len` bytes, charged as the transport charges. -/
theorem reply_sendable_charged (f : Form) (a : Alg) (ns : List Nat)
    (hlen : ns.length ≤ replyDatagrams (replyLen a)) (hs : ns.sum ≤ replyLen a + ns.length * fragmentHeader) :
    sendableCharged (Amp.onReceive Amp.Budget.new (minInitialLen f a)) ns = true :=
  cut_sendable _ _ _ _ (by cases f <;> cases a <;> decide) (budget_covers_reply f a) ns hlen hs

/-- The same for the transport's default cut into `MIN_DATAGRAM`-byte datagrams with ids of at most
`SPLIT_CID_MAX` bytes. -/
theorem split_sendable_charged (f : Form) (a : Alg) (c : Nat) (hc : c ≤ splitCidMax) (ns : List Nat)
    (hlen : ns.length ≤ splitDatagrams (replyLenWith a c) c)
    (hs : ns.sum ≤ replyLenWith a c + ns.length * framingWith c) :
    sendableCharged (Amp.onReceive Amp.Budget.new (minInitialLen f a)) ns = true :=
  cut_sendable _ _ _ _ (by cases f <;> cases a <;> decide) (budget_covers_split f a c hc) ns hlen hs

end Pinc.Padding

#audit_axioms Pinc.Padding.constants
#audit_axioms Pinc.Padding.max_is_hybrid
#audit_axioms Pinc.Padding.sealedLen_le_max
#audit_axioms Pinc.Padding.replyLen_le_max
#audit_axioms Pinc.Padding.lens_le_max
#audit_axioms Pinc.Padding.minInitialLen_ge_floor
#audit_axioms Pinc.Padding.budget_covers_reply
#audit_axioms Pinc.Padding.budget_covers_split
#audit_axioms Pinc.Padding.split_cid_max_tight
#audit_axioms Pinc.Padding.reply_sendable_charged
#audit_axioms Pinc.Padding.split_sendable_charged
#audit_axioms Pinc.Padding.budget_covers_any
#audit_axioms Pinc.Padding.short_ed25519
#audit_axioms Pinc.Padding.min_initial_values
#audit_axioms Pinc.Padding.reply_sendable
