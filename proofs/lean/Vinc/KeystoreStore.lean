import Vinc.CryptoIdentity

/-!
# The software store and the key host of `vinc-keystore` (`software.rs`, `host.rs`, `lib.rs`)

The store is a table from handles to keys; a handle comes from one process-wide counter (`KeyHandle::next`), so it is
fresh across all stores. A `World` holds the counter and the table of every store. `sign`, `public` and `decapsulate`
look the handle up and answer by the kind of key; `generate` draws seeds up to `SEED_RETRIES` times. `KeyHost` binds the
handshake's handles to the store's and answers a request from the binding and the store, a pure function of its state
and the request.
-/

namespace Vinc.KeystoreStore
open Vinc.CryptoKdf (Bytes)
open Vinc.CryptoIdentity (Alg)

/-- What a table entry holds. -/
inductive Kind where
  | id (alg : Alg)
  | kem
  deriving DecidableEq

/-- `KeyStoreError` (the variants a software store returns). -/
inductive KErr where
  | unknownKey
  | wrongKeyKind
  | crypto (e : Vinc.CryptoIdentity.Err)
  | entropy
  deriving DecidableEq

/-- The tables of all stores and the shared counter. -/
structure World where
  next : Nat
  tables : Nat → List (Nat × Kind)

/-- The invariant: every handle is below the counter and a table has no handle twice. -/
def Inv (w : World) : Prop :=
  ∀ s, (∀ e ∈ w.tables s, e.1 < w.next) ∧ ((w.tables s).map Prod.fst).Nodup

def World.empty : World := ⟨1, fun _ => []⟩

theorem inv_empty : Inv World.empty := by
  intro s; simp [World.empty]

/-- `add` (`insert`, `insert_kem`, a successful `generate`): a new handle from the counter. -/
def add (w : World) (s : Nat) (k : Kind) : World × Nat :=
  (⟨w.next + 1, fun t => if t = s then (w.next, k) :: w.tables t else w.tables t⟩, w.next)

/-- A handle is never given twice, also across stores: the new one is in no table. -/
theorem add_fresh {w : World} (hi : Inv w) (s t : Nat) (k : Kind) : ∀ e ∈ w.tables t, e.1 ≠ (add w s k).2 := by
  intro e he h
  have := (hi t).1 e he
  simp [add] at h
  omega

theorem add_inv {w : World} (hi : Inv w) (s : Nat) (k : Kind) : Inv (add w s k).1 := by
  intro t
  by_cases ht : t = s
  · subst ht
    simp only [add, ite_true]
    constructor
    · intro e he
      simp at he
      rcases he with rfl | he
      · simp
      · have := (hi t).1 e he; simp; omega
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, (hi t).2⟩
      intro hm
      obtain ⟨e, he, hh⟩ := List.mem_map.mp hm
      have := (hi t).1 e he
      omega
  · simp only [add, ht, ite_false]
    refine ⟨?_, (hi t).2⟩
    intro e he
    have := (hi t).1 e he
    simp; omega

/-- The counter only grows: a handle is never reused. -/
theorem add_next_lt (w : World) (s : Nat) (k : Kind) : w.next < (add w s k).1.next := by simp [add]

/-- `SoftwareStore::remove`: drop the entry, say whether it was there. -/
def remove (w : World) (s h : Nat) : World × Bool :=
  (⟨w.next, fun t => if t = s then (w.tables t).filter (fun e => e.1 != h) else w.tables t⟩,
   (w.tables s).any (fun e => e.1 == h))

def lookup (w : World) (s h : Nat) : Option Kind := ((w.tables s).find? (fun e => e.1 == h)).map Prod.snd

theorem remove_removes (w : World) (s h : Nat) : lookup (remove w s h).1 s h = none := by
  simp only [lookup, remove, ite_true]
  have : ((w.tables s).filter (fun e => e.1 != h)).find? (fun e => e.1 == h) = none := by
    rw [List.find?_eq_none]
    intro e he
    have := (List.mem_filter.mp he).2
    simpa using this
  simp [this]

/-- Removing grows nothing and changes only the one table. -/
theorem remove_length (w : World) (s h : Nat) : ((remove w s h).1.tables s).length ≤ (w.tables s).length := by
  simp only [remove, ite_true]
  exact List.length_filter_le _ _

/-- A table never holds more entries than were added. -/
theorem add_length (w : World) (s : Nat) (k : Kind) : ((add w s k).1.tables s).length = (w.tables s).length + 1 := by
  simp [add]

/-- A handle from another store is unknown here. -/
theorem foreign_unknown {w : World} (hi : Inv w) {s t h : Nat} (hs : s ≠ t) (hmem : ∃ e ∈ w.tables t, e.1 = h)
    (hdisj : ∀ e ∈ w.tables s, ∀ f ∈ w.tables t, e.1 ≠ f.1) : lookup w s h = none := by
  obtain ⟨f, hf, rfl⟩ := hmem
  simp only [lookup]
  have : (w.tables s).find? (fun e => e.1 == f.1) = none := by
    rw [List.find?_eq_none]
    intro e he
    have := hdisj e he f hf
    simpa using this
  simp [this]

/-! ## Operations on a handle -/

/-- `sign`: the algorithm of the key, so a signature of its length. -/
def sign (w : World) (s h : Nat) : Except KErr Alg :=
  match lookup w s h with
  | some (.id a) => .ok a
  | some .kem => .error .wrongKeyKind
  | none => .error .unknownKey

/-- `decapsulate`: a KEM key and a ciphertext of the right length. -/
def decapsulate (w : World) (s h : Nat) (ctLen : Nat) : Except KErr Unit :=
  match lookup w s h with
  | some .kem => if ctLen = 1088 then .ok () else .error (.crypto .invalidLength)
  | some (.id _) => .error .wrongKeyKind
  | none => .error .unknownKey

/-- `generate`: seeds are drawn up to `SEED_RETRIES` times; a draw is valid unless a P-256 seed is out of range. The
result is the number of draws used, or an error after 8. -/
def seedRetries : Nat := 8

def generateDraws (alg : Alg) (valid : Nat → Bool) : Except KErr Nat :=
  match (List.range seedRetries).find? (fun i => alg != .ecdsaP256 || valid i) with
  | some i => .ok (i + 1)
  | none => .error (.crypto .invalidSecretKey)

theorem generate_bounded (alg : Alg) (valid : Nat → Bool) (n : Nat) (h : generateDraws alg valid = .ok n) :
    1 ≤ n ∧ n ≤ seedRetries := by
  unfold generateDraws at h
  cases hf : (List.range seedRetries).find? (fun i => alg != .ecdsaP256 || valid i) with
  | none => simp [hf] at h
  | some i =>
    simp only [hf, Except.ok.injEq] at h
    subst h
    have := List.mem_of_find?_eq_some hf
    simp [List.mem_range] at this
    unfold seedRetries at *
    omega

theorem generate_first_draw (alg : Alg) (valid : Nat → Bool) (h : alg ≠ .ecdsaP256) :
    generateDraws alg valid = .ok 1 := by
  unfold generateDraws
  simp [h, seedRetries, List.range_succ]

/-! ## The key host -/

/-- The handshake's request. -/
inductive Req where
  | sign (sec : Nat) (alg : Alg) (msgLen : Nat)
  | decap (sec : Nat)

/-- The handshake's answer. -/
inductive Resp where
  | signature (alg : Alg) (len : Nat)
  | secret
  | failed
  deriving DecidableEq

/-- `KeyHost::bind`. -/
def bind (bound : List (Nat × Nat)) (sec k : Nat) : List (Nat × Nat) :=
  bound.filter (fun e => e.1 != sec) ++ [(sec, k)]

theorem bind_nodup {bound : List (Nat × Nat)} (h : (bound.map Prod.fst).Nodup) (sec k : Nat) :
    ((bind bound sec k).map Prod.fst).Nodup := by
  unfold bind
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · have : (bound.filter (fun e => e.1 != sec)).map Prod.fst = (bound.map Prod.fst).filter (· != sec) := by
      simp [List.filter_map]; rfl
    rw [this]; exact h.filter _
  · intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    have := (List.mem_filter.mp he).2
    simpa using this

theorem bind_length (bound : List (Nat × Nat)) (sec k : Nat) : (bind bound sec k).length ≤ bound.length + 1 := by
  simp only [bind, List.length_append, List.length_singleton]
  have := List.length_filter_le (fun e : Nat × Nat => e.1 != sec) bound
  omega

theorem bind_lookup (bound : List (Nat × Nat)) (sec k : Nat) : (bind bound sec k).find? (fun e => e.1 == sec) = some (sec, k) := by
  unfold bind
  rw [List.find?_append]
  have : (bound.filter (fun e => e.1 != sec)).find? (fun e => e.1 == sec) = none := by
    rw [List.find?_eq_none]
    intro e he
    have := (List.mem_filter.mp he).2
    simpa using this
  simp [this]

/-- `KeyHost::answer`: unbound, store failure and algorithm mismatch are `Failed`, nothing is guessed. -/
def answer (w : World) (s : Nat) (bound : List (Nat × Nat)) : Req → Resp
  | .sign sec alg _ =>
    match bound.find? (fun e => e.1 == sec) with
    | none => .failed
    | some (_, k) =>
      match sign w s k with
      | .error _ => .failed
      | .ok a => if a = alg then .signature a a.sigLen else .failed
  | .decap sec =>
    match bound.find? (fun e => e.1 == sec) with
    | none => .failed
    | some (_, k) =>
      match decapsulate w s k 1088 with
      | .error _ => .failed
      | .ok () => .secret

/-- A signing request is never answered with a secret, nor a decapsulation with a signature. -/
theorem answer_sign_not_secret (w : World) (s : Nat) (bound : List (Nat × Nat)) (sec : Nat) (alg : Alg) (m : Nat) :
    answer w s bound (.sign sec alg m) ≠ .secret := by
  simp only [answer]
  cases bound.find? (fun e => e.1 == sec) with
  | none => simp
  | some e =>
    cases hs : sign w s e.2 with
    | error _ => simp [hs]
    | ok a => by_cases h : a = alg <;> simp [hs, h]

theorem answer_decap_not_signature (w : World) (s : Nat) (bound : List (Nat × Nat)) (sec : Nat) (a : Alg) (n : Nat) :
    answer w s bound (.decap sec) ≠ .signature a n := by
  simp only [answer]
  cases bound.find? (fun e => e.1 == sec) with
  | none => simp
  | some e =>
    cases hs : decapsulate w s e.2 1088 with
    | error _ => simp [hs]
    | ok u => cases u; simp [hs]

/-- A signature answer carries the algorithm asked for and its length, and only a bound key whose store signs gives one. -/
theorem answer_signature_iff (w : World) (s : Nat) (bound : List (Nat × Nat)) (sec : Nat) (alg : Alg) (m : Nat) (a : Alg) (n : Nat) :
    answer w s bound (.sign sec alg m) = .signature a n ↔
      a = alg ∧ n = alg.sigLen ∧ ∃ e, bound.find? (fun e => e.1 == sec) = some e ∧ sign w s e.2 = .ok alg := by
  simp only [answer]
  cases hf : bound.find? (fun e => e.1 == sec) with
  | none => simp
  | some e =>
    cases hs : sign w s e.2 with
    | error _ => simp [hs]
    | ok b =>
      simp only [hs]
      by_cases h : b = alg
      · subst h
        simp only [ite_true, Resp.signature.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl, e, rfl, hs⟩
        · rintro ⟨rfl, rfl, e', he', he2⟩
          exact ⟨rfl, rfl⟩
      · simp only [h, ite_false]
        constructor
        · intro hh; cases hh
        · rintro ⟨_, _, e', he', he2⟩
          have : e' = e := (Option.some.inj he').symm
          subst this
          rw [hs] at he2
          cases he2
          exact absurd rfl h

theorem answer_unbound (w : World) (s : Nat) (bound : List (Nat × Nat)) (r : Req) (sec : Nat)
    (h : bound.find? (fun e => e.1 == sec) = none) :
    (r = .sign sec .ed25519 0 ∨ r = .decap sec) → answer w s bound r = .failed := by
  rintro (rfl | rfl) <;> simp [answer, h]

end Vinc.KeystoreStore

#audit_axioms Vinc.KeystoreStore.add_fresh
#audit_axioms Vinc.KeystoreStore.add_inv
#audit_axioms Vinc.KeystoreStore.remove_removes
#audit_axioms Vinc.KeystoreStore.generate_bounded
#audit_axioms Vinc.KeystoreStore.bind_nodup
#audit_axioms Vinc.KeystoreStore.bind_lookup
#audit_axioms Vinc.KeystoreStore.answer_signature_iff
