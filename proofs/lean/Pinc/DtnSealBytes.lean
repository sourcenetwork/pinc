import Pinc.Transcript
import Pinc.Labels

/-!
# The byte layer of the one-shot encryption and the bundle head

The exact byte strings `pinc-dtn` hashes, signs and feeds to the AEAD, and the facts the symbolic model of
`Pinc.DtnSeal` needs from them. Collision resistance of the hash is a hypothesis (`HashInj`), never assumed as a
postulate.

* `be`: the big-endian bytes of a number in a fixed width (`to_be_bytes`); it is injective below `256^w`.
* `nonce` (`seal.rs::nonce`: four zero bytes and the big-endian index) and `aad` (the transcript hash and the
  big-endian index) are injective in the slice index; the nonce differs for two indices below `2^64`.
* The transcript hash of the key derivation (`transcript_hash`) absorbs eight fields; equal hashes give equal
  ephemeral key, static keys, KEM ciphertext, recipient node, epoch and bundle id (`thFields_inj`).
* `BundleId::derive` is injective in (source, creation time, ephemeral key) (`bundleId_inj`).
* The head body (`Head::encode`) is the concatenation of fixed-width fields, so it is injective (`headBody_inj`);
  the digest a signature covers is the label-separated hash of the body, so a head signature fixes every field and
  never verifies as a custody acknowledgement (`headDigest_inj`, `headDigest_ne_ack`).
* The six labels of the layer are pairwise distinct, share the prefix and are disjoint from the labels of the
  security layer and of `pinc-crypto` (`dtnLabels_nodup`, `dtnLabels_prefix`, `dtnLabels_disjoint`).
-/

namespace Pinc.DtnSeal
open Pinc.Transcript Pinc.Varint

/-! ## Fixed-width big-endian numbers -/

/-- The `w` big-endian bytes of `n` (`n.to_be_bytes()` for the width `w`). -/
def be : Nat → Nat → List Nat
  | 0, _ => []
  | w + 1, n => be w (n / 256) ++ [n % 256]

theorem be_length : ∀ w n, (be w n).length = w
  | 0, _ => rfl
  | w + 1, n => by simp [be, be_length w]

/-- Below `256^w` the bytes determine the number. -/
theorem be_inj : ∀ w n m, n < 256 ^ w → m < 256 ^ w → be w n = be w m → n = m
  | 0, n, m, hn, hm, _ => by simp at hn hm; omega
  | w + 1, n, m, hn, hm, h => by
    simp only [be] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp [be_length])
    simp only [List.cons.injEq, and_true] at h2
    rw [Nat.pow_succ] at hn hm
    have hq := be_inj w (n / 256) (m / 256) (by omega) (by omega) h1
    omega

/-- Two lists of fields whose fields have pairwise equal lengths. -/
inductive SameLens : List (List Nat) → List (List Nat) → Prop where
  | nil : SameLens [] []
  | cons {x y : List Nat} {xs ys : List (List Nat)} : x.length = y.length → SameLens xs ys → SameLens (x :: xs) (y :: ys)

/-- Concatenated fields of pairwise equal lengths determine the fields. -/
theorem flatten_inj {xs ys : List (List Nat)} (h : SameLens xs ys) (e : xs.flatten = ys.flatten) : xs = ys := by
  induction h with
  | nil => rfl
  | cons hxy _ ih =>
    simp only [List.flatten_cons] at e
    obtain ⟨h1, h2⟩ := List.append_inj e hxy
    rw [h1, ih h2]

/-! ## Nonce and associated data of a slice -/

/-- `seal.rs::nonce`: four zero bytes and the big-endian slice index. -/
def nonce (i : Nat) : List Nat := [0, 0, 0, 0] ++ be 8 i

/-- `seal.rs::aad`: the transcript hash and the big-endian slice index. -/
def aad (th : List Nat) (i : Nat) : List Nat := th ++ be 8 i

theorem nonce_length (i : Nat) : (nonce i).length = 12 := by simp [nonce, be_length]

/-- Two slice indices below `2^64` with the same nonce are the same index: a key never seals two slices under one
nonce as long as it seals each index once. -/
theorem nonce_inj (i j : Nat) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : nonce i = nonce j) : i = j := by
  simp only [nonce, List.append_cancel_left_eq] at h
  exact be_inj 8 i j (by simpa using hi) (by simpa using hj) h

theorem aad_inj (t u : List Nat) (i j : Nat) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (ht : t.length = u.length)
    (h : aad t i = aad u j) : t = u ∧ i = j := by
  obtain ⟨h1, h2⟩ := List.append_inj h ht
  exact ⟨h1, be_inj 8 i j (by simpa using hi) (by simpa using hj) h2⟩

/-- The AEAD inputs of a slice differ whenever the indices do: a slice sealed at one index opens at no other. -/
theorem slice_binding (t : List Nat) (i j : Nat) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (hne : i ≠ j) :
    nonce i ≠ nonce j ∧ aad t i ≠ aad t j := by
  refine ⟨fun h => hne (nonce_inj i j hi hj h), fun h => hne (aad_inj t t i j hi hj rfl h).2⟩

/-! ## The labels of the layer -/

def chain : String := "PINC 2026 v1 dtn chain"
def transcript : String := "PINC 2026 v1 dtn transcript"
def sliceKey : String := "PINC 2026 v1 dtn slice key"
def bundleIdL : String := "PINC 2026 v1 dtn bundle id"
def head : String := "PINC 2026 v1 dtn head"
def custodyAck : String := "PINC 2026 v1 dtn custody ack"

/-- `labels::ALL` of `pinc-dtn`. -/
def dtnLabels : List String := [chain, transcript, sliceKey, bundleIdL, head, custodyAck]

theorem dtnLabels_nodup : (dtnLabels.map Labels.bytes).Nodup := by decide

theorem dtnLabels_prefix : ∀ l ∈ dtnLabels, Labels.prefix_.toList <+: l.toList := by decide

/-- No label of this layer is a label of the security layer or of `pinc-crypto`, in bytes. -/
theorem dtnLabels_disjoint :
    ∀ l ∈ dtnLabels, Labels.bytes l ∉ (Labels.all ++ Labels.cryptoLabels).map Labels.bytes := by decide

/-! ## Transcripts of the layer -/

/-- Equal hashes of the same label over bounded field lists give the same fields. -/
theorem th_inj_fields {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (l : String)
    (fs gs : List Field) (hf : Bounded fs) (hg : Bounded gs) (h : th H l fs = th H l gs) : fs = gs := by
  have := (hH.inj _ _ _ _ h).2
  exact encode_injective fs gs hf hg this

/-- The hashes of two different labels differ. -/
theorem th_ne_of_label {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (l₁ l₂ : String)
    (hl : Labels.bytes l₁ ≠ Labels.bytes l₂) (fs : List Field) : th H l₁ fs ≠ th H l₂ fs := by
  intro h
  exact hl (hH.inj _ _ _ _ h).1

/-- The inputs of `transcript_hash`: the ephemeral key, the recipient's static X25519 and ML-KEM keys, the KEM
ciphertext, the recipient node (algorithm tag and 32 bytes), its epoch and the bundle id. -/
structure ThIn where
  eph : List Nat
  x : List Nat
  ek : List Nat
  ct : List Nat
  tag : Nat
  node : List Nat
  epoch : Nat
  id : List Nat
  deriving DecidableEq

/-- The shape the code guarantees: fixed-width keys and ids, a one-byte tag and a 32-bit epoch. -/
def ThIn.WF (a : ThIn) : Prop :=
  a.eph.length = 32 ∧ a.x.length = 32 ∧ a.ek.length = 1184 ∧ a.ct.length = 1088 ∧ a.tag < 256 ∧
  a.node.length = 32 ∧ a.epoch < 256 ^ 4 ∧ a.id.length = 32

/-- The fields `transcript_hash` absorbs, in order (the node id is two absorbs). -/
def ThIn.fields (a : ThIn) : List Field :=
  [a.eph, a.x, a.ek, a.ct, [a.tag], a.node, be 4 a.epoch, a.id]

theorem bounded_of_lengths (fs : List Field) (h : ∀ f ∈ fs, f.length ≤ 2048) : Bounded fs := by
  intro f hf
  have := h f hf
  unfold limit
  omega

theorem ThIn.bounded (a : ThIn) (h : a.WF) : Bounded a.fields := by
  obtain ⟨h1, h2, h3, h4, -, h6, -, h8⟩ := h
  apply bounded_of_lengths
  intro f hf
  simp only [ThIn.fields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [be_length, *]

/-- Equal key-derivation transcript hashes give equal inputs: the key is bound to the ephemeral key, both static
keys, the KEM ciphertext, the recipient node, its epoch and the bundle id. -/
theorem thFields_inj {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a b : ThIn) (ha : a.WF) (hb : b.WF)
    (h : th H transcript a.fields = th H transcript b.fields) : a = b := by
  have e := th_inj_fields hH _ _ _ (a.bounded ha) (b.bounded hb) h
  obtain ⟨-, -, -, -, -, -, a7, -⟩ := ha
  obtain ⟨-, -, -, -, -, -, b7, -⟩ := hb
  simp only [ThIn.fields, List.cons.injEq, and_true] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := e
  have e7' := be_inj 4 _ _ a7 b7 e7
  cases a; cases b
  simp_all

/-- The inputs of `BundleId::derive`: the source node, the creation time and the ephemeral key. -/
structure IdIn where
  tag : Nat
  node : List Nat
  wall : Nat
  counter : Nat
  eph : List Nat
  deriving DecidableEq

def IdIn.WF (a : IdIn) : Prop :=
  a.tag < 256 ∧ a.node.length = 32 ∧ a.wall < 256 ^ 8 ∧ a.counter < 256 ^ 4 ∧ a.eph.length = 32

def IdIn.fields (a : IdIn) : List Field := [[a.tag], a.node, be 8 a.wall, be 4 a.counter, a.eph]

theorem IdIn.bounded (a : IdIn) (h : a.WF) : Bounded a.fields := by
  obtain ⟨-, h2, -, -, h5⟩ := h
  apply bounded_of_lengths
  intro f hf
  simp only [IdIn.fields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> simp [be_length, *]

/-- `BundleId::derive` is injective in the source, the creation time and the ephemeral key. -/
theorem bundleId_inj {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a b : IdIn) (ha : a.WF) (hb : b.WF)
    (h : th H bundleIdL a.fields = th H bundleIdL b.fields) : a = b := by
  have e := th_inj_fields hH _ _ _ (a.bounded ha) (b.bounded hb) h
  obtain ⟨-, -, a3, a4, -⟩ := ha
  obtain ⟨-, -, b3, b4, -⟩ := hb
  simp only [IdIn.fields, List.cons.injEq, and_true] at e
  obtain ⟨e1, e2, e3, e4, e5⟩ := e
  have e3' := be_inj 8 _ _ a3 b3 e3
  have e4' := be_inj 4 _ _ a4 b4 e4
  cases a; cases b
  simp_all

/-! ## The head body and its digest -/

/-- The fields of `Head::encode`, in order. Node ids are a tag byte and 32 bytes. -/
structure HeadB where
  id : List Nat
  stag : Nat
  src : List Nat
  dtag : Nat
  dst : List Nat
  wall : Nat
  counter : Nat
  life : Nat
  copies : Nat
  k : Nat
  m : Nat
  log : Nat
  plen : Nat
  root : List Nat
  epoch : Nat
  eph : List Nat
  kct : List Nat
  deriving DecidableEq

def HeadB.WF (h : HeadB) : Prop :=
  h.id.length = 32 ∧ h.stag < 256 ∧ h.src.length = 32 ∧ h.dtag < 256 ∧ h.dst.length = 32 ∧
  h.wall < 256 ^ 8 ∧ h.counter < 256 ^ 4 ∧ h.life < 256 ^ 8 ∧ h.copies < 256 ^ 2 ∧ h.k < 256 ∧ h.m < 256 ∧
  h.log < 256 ∧ h.plen < 256 ^ 8 ∧ h.root.length = 32 ∧ h.epoch < 256 ^ 4 ∧ h.eph.length = 32 ∧ h.kct.length = 1088

def HeadB.fields (h : HeadB) : List Field :=
  [h.id, be 1 h.stag, h.src, be 1 h.dtag, h.dst, be 8 h.wall, be 4 h.counter, be 8 h.life, be 2 h.copies,
   be 1 h.k, be 1 h.m, be 1 h.log, be 8 h.plen, h.root, be 4 h.epoch, h.eph, h.kct]

/-- The encoded head: the concatenation of its fixed-width fields. -/
def HeadB.body (h : HeadB) : List Nat := h.fields.flatten

/-- `HEAD_LEN` of `head.rs`: `32 + 2 * 33 + 12 + 8 + 2 + 2 + 1 + 8 + 32 + 4 + 32 + 1088`. -/
theorem HeadB.body_length (h : HeadB) (hw : h.WF) : h.body.length = 32 + 2 * 33 + 12 + 8 + 2 + 2 + 1 + 8 + 32 + 4 + 32 + 1088 := by
  obtain ⟨h1, -, h3, -, h5, -, -, -, -, -, -, -, -, h14, -, h16, h17⟩ := hw
  simp [HeadB.body, HeadB.fields, be_length, h1, h3, h5, h14, h16, h17]

/-- The head body determines the head: the signature covers every field. -/
theorem headBody_inj (a b : HeadB) (ha : a.WF) (hb : b.WF) (h : a.body = b.body) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17⟩ := hb
  have hl : SameLens a.fields b.fields := by
    simp only [HeadB.fields]
    repeat' first | exact SameLens.nil | apply SameLens.cons (by simp [be_length, *])
  
  have e := flatten_inj hl h
  simp only [HeadB.fields, List.cons.injEq, and_true] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17⟩ := e
  have := be_inj 1 _ _ (by simpa using a2) (by simpa using b2) e2
  have := be_inj 1 _ _ (by simpa using a4) (by simpa using b4) e4
  have := be_inj 8 _ _ a6 b6 e6
  have := be_inj 4 _ _ a7 b7 e7
  have := be_inj 8 _ _ a8 b8 e8
  have := be_inj 2 _ _ a9 b9 e9
  have := be_inj 1 _ _ (by simpa using a10) (by simpa using b10) e10
  have := be_inj 1 _ _ (by simpa using a11) (by simpa using b11) e11
  have := be_inj 1 _ _ (by simpa using a12) (by simpa using b12) e12
  have := be_inj 8 _ _ a13 b13 e13
  have := be_inj 4 _ _ a15 b15 e15
  cases a; cases b
  simp_all

/-- The digest a head signature covers: the label-separated hash of the body (`Endorsement::sign`). -/
def headDigest {β : Type} (H : List Nat → List Nat → β) (h : HeadB) : β := th H head [h.body]

/-- The digest of a custody acknowledgement body, under its own label. -/
def ackDigest {β : Type} (H : List Nat → List Nat → β) (body : List Nat) : β := th H custodyAck [body]

theorem headBody_bounded (h : HeadB) (hw : h.WF) : Bounded [h.body] := by
  apply bounded_of_lengths
  intro f hf
  simp only [List.mem_singleton] at hf
  subst hf
  rw [h.body_length hw]
  omega

/-- A signature over a head digest fixes every field of the head: root, id, source, destination, times, erasure
parameters, payload length and the whole encryption envelope (epoch, ephemeral key, KEM ciphertext). -/
theorem headDigest_inj {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a b : HeadB) (ha : a.WF)
    (hb : b.WF) (h : headDigest H a = headDigest H b) : a = b := by
  have e := th_inj_fields hH _ _ _ (headBody_bounded a ha) (headBody_bounded b hb) h
  simp only [List.cons.injEq, and_true] at e
  exact headBody_inj a b ha hb e

/-- A head signature never verifies as a custody acknowledgement, whatever the bodies. -/
theorem headDigest_ne_ack {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (h : HeadB) (body : List Nat) :
    headDigest H h ≠ ackDigest H body := by
  intro e
  have := (hH.inj _ _ _ _ e).1
  revert this
  decide

end Pinc.DtnSeal

#audit_axioms Pinc.DtnSeal.be_inj
#audit_axioms Pinc.DtnSeal.nonce_inj
#audit_axioms Pinc.DtnSeal.slice_binding
#audit_axioms Pinc.DtnSeal.dtnLabels_nodup
#audit_axioms Pinc.DtnSeal.dtnLabels_prefix
#audit_axioms Pinc.DtnSeal.dtnLabels_disjoint
#audit_axioms Pinc.DtnSeal.thFields_inj
#audit_axioms Pinc.DtnSeal.bundleId_inj
#audit_axioms Pinc.DtnSeal.headBody_inj
#audit_axioms Pinc.DtnSeal.headDigest_inj
#audit_axioms Pinc.DtnSeal.headDigest_ne_ack
