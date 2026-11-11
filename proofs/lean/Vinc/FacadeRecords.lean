import Vinc.Axioms

/-!
# Discovery by signed records in the facade: what a lookup may believe

The story, in plain words. Nodes publish records with rising sequence numbers to a store that nobody trusts. The
store may hand out the newest record of a node, an older one (a replay), a record of another node filed under this
one, or bytes that do not verify (a forgery). An endpoint that looks a node up keeps the fetched record only if it
verifies and names that node, and then only if it is newer than what it already believed.

What must never happen: the endpoint believes a record its node did not sign and publish; its belief about a node
goes back to an older record; a lookup answers with anything but what it now believes.

This is a transcription of `proofs/tla/FacadeRecords.tla` over any number of nodes, records and steps. The Rust code
is `crates/vinc/src/records.rs` (`PeerRecord::verified`, `newest`, `Records::find`) and
`crates/vinc/src/endpoint.rs` (`Endpoint::signed_record`, the rising sequence number; `Endpoint::lookup`).

Main theorems: `inv_reach` (with the sequence check every reachable state keeps the promises) and `noSeqCheck_bad`
(without it a replayed older record rolls the endpoint back).
-/

namespace Vinc.FacadeRecords

-- A record: who signed it, its sequence number (0 stands for "no record"), and whether its signature verifies.
structure Rec where
  signer : Nat
  seq : Nat
  sound : Bool
  deriving DecidableEq, Repr

-- No record.
def noRec : Rec := ⟨0, 0, false⟩

-- The endpoint's check: the signature verifies, the record names the node asked about, and it is a record at all.
abbrev verified (n : Nat) (r : Rec) : Prop := r.sound = true ∧ r.signer = n ∧ 0 < r.seq

-- `newest` in records.rs: the fetched record only if it is newer; without the check, always the fetched one.
def newest (seqCheck : Bool) (k f : Rec) : Rec := if seqCheck then (if f.seq > k.seq then f else k) else f

-- The state: what each node published last, what the store hands out, what the endpoint believes, the highest
-- sequence number it ever believed (history), and its last answer.
structure State where
  published : Nat → Nat
  store : Nat → Rec
  known : Nat → Rec
  peak : Nat → Nat
  answer : Nat × Rec

-- Change one entry of a function.
def set {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α := fun j => if j = i then v else f j

-- The changed entry reads back the new value.
theorem set_same {α : Type} (f : Nat → α) (i : Nat) (v : α) : set f i v i = v := by simp [set]

-- Every other entry is unchanged.
theorem set_other {α : Type} (f : Nat → α) (i j : Nat) (v : α) (h : j ≠ i) : set f i v j = f j := by
  simp [set, h]

-- What the endpoint believes after looking `n` up.
def best (seqCheck : Bool) (s : State) (n : Nat) : Rec :=
  if verified n (s.store n) then newest seqCheck (s.known n) (s.store n) else s.known n

-- The start: nothing published, stored or believed.
def init : State := ⟨fun _ => 0, fun _ => noRec, fun _ => noRec, fun _ => 0, (0, noRec)⟩

-- The state after each action of the TLA+ model of the same name.
-- Node `n` publishes a record above every earlier one, and the store takes it.
def publishS (s : State) (n : Nat) : State :=
  { s with published := set s.published n (s.published n + 1), store := set s.store n ⟨n, s.published n + 1, true⟩ }
-- The store hands out `r` for `n`.
def tamperS (s : State) (n : Nat) (r : Rec) : State := { s with store := set s.store n r }
-- The endpoint looks `n` up.
def lookupS (c : Bool) (s : State) (n : Nat) : State :=
  { s with known := set s.known n (best c s n), peak := set s.peak n (max (s.peak n) (best c s n).seq),
           answer := (n, best c s n) }

-- One step, with the guard of each action.
inductive Step (c : Bool) : State → State → Prop where
  | publish (s : State) (n : Nat) : Step c s (publishS s n)
  -- The store misbehaves: an older genuine record of `n`, another node's record, or bytes that do not verify.
  | tamper (s : State) (n : Nat) (r : Rec) :
      ((r.signer = n ∧ r.sound = true ∧ r.seq ≤ s.published n) ∨ r.signer ≠ n ∨ r.sound = false) →
      Step c s (tamperS s n r)
  | lookup (s : State) (n : Nat) : Step c s (lookupS c s n)

-- The states reachable from the start.
inductive Reach (c : Bool) : State → Prop where
  | init : Reach c init
  | step (s t : State) : Reach c s → Step c s t → Reach c t

-- A genuine record of a node in the store is one that node published.
abbrev StoreHonest (s : State) : Prop :=
  ∀ n, (s.store n).signer = n → (s.store n).sound = true → (s.store n).seq ≤ s.published n

-- Every believed record was signed and published by its node.
abbrev KnownGenuine (s : State) : Prop :=
  ∀ n, 0 < (s.known n).seq → (s.known n).signer = n ∧ (s.known n).sound = true ∧ (s.known n).seq ≤ s.published n

-- The belief about a node is never older than one held before.
abbrev NoRollback (s : State) : Prop := ∀ n, (s.known n).seq = s.peak n

-- The last answer is what the endpoint now believes about that node.
abbrev LookupNewest (s : State) : Prop := s.answer.2 = s.known s.answer.1

-- The promises together, with the store fact they rest on.
abbrev Inv (s : State) : Prop := StoreHonest s ∧ KnownGenuine s ∧ NoRollback s ∧ LookupNewest s

/-- The start keeps the promises. -/
theorem inv_init : Inv init := by
  refine ⟨fun n _ h => ?_, fun n h => ?_, fun n => ?_, ?_⟩
  · simp [init, noRec] at h
  · simp [init, noRec] at h
  · simp [init, noRec]
  · simp [init]

/-- With the check, a lookup never believes an older record than before. -/
theorem newest_ge (k f : Rec) : k.seq ≤ (newest true k f).seq := by
  unfold newest
  by_cases h : f.seq > k.seq
  · rw [if_pos rfl, if_pos h]; exact Nat.le_of_lt h
  · rw [if_pos rfl, if_neg h]; exact Nat.le_refl _

/-- What a lookup believes is the known record or a verified fetched one. -/
theorem best_cases (c : Bool) (s : State) (n : Nat) :
    best c s n = s.known n ∨ (best c s n = s.store n ∧ verified n (s.store n)) := by
  unfold best
  by_cases hv : verified n (s.store n)
  · rw [if_pos hv]
    unfold newest
    cases c
    · exact Or.inr ⟨by simp, hv⟩
    · by_cases h : (s.store n).seq > (s.known n).seq
      · exact Or.inr ⟨by simp [h], hv⟩
      · exact Or.inl (by simp [h])
  · rw [if_neg hv]; exact Or.inl rfl

/-- With the check, what a lookup believes is at least as new as what was known. -/
theorem best_ge (s : State) (n : Nat) : (s.known n).seq ≤ (best true s n).seq := by
  unfold best
  by_cases hv : verified n (s.store n)
  · rw [if_pos hv]; exact newest_ge _ _
  · rw [if_neg hv]; exact Nat.le_refl _

/-- With the sequence check every step keeps the promises. -/
theorem inv_step (s t : State) (hs : Inv s) (st : Step true s t) : Inv t := by
  obtain ⟨hst, hk, hn, ha⟩ := hs
  cases st with
  | publish n =>
    refine ⟨fun m h1 h2 => ?_, fun m h => ?_, hn, ha⟩
    · simp only [publishS] at h1 h2 ⊢
      by_cases hm : m = n
      · subst hm; simp [set_same]
      · rw [set_other _ _ _ _ hm] at h1 h2 ⊢
        rw [set_other _ _ _ _ hm]
        exact hst m h1 h2
    · obtain ⟨a, b, c⟩ := hk m h
      refine ⟨a, b, ?_⟩
      simp only [publishS]
      by_cases hm : m = n
      · subst hm; rw [set_same]; omega
      · rw [set_other _ _ _ _ hm]; exact c
  | tamper n r hr =>
    refine ⟨fun m h1 h2 => ?_, hk, hn, ha⟩
    simp only [tamperS] at h1 h2 ⊢
    by_cases hm : m = n
    · subst hm
      rw [set_same] at h1 h2 ⊢
      rcases hr with ⟨_, _, h⟩ | h | h
      · exact h
      · exact absurd h1 h
      · rw [h] at h2; exact absurd h2 (by decide)
    · rw [set_other _ _ _ _ hm] at h1 h2 ⊢; exact hst m h1 h2
  | lookup n =>
    refine ⟨hst, fun m h => ?_, fun m => ?_, ?_⟩
    · simp only [lookupS] at h ⊢
      by_cases hm : m = n
      · subst hm
        rw [set_same] at h ⊢
        rcases best_cases true s m with he | ⟨he, hv⟩
        · rw [he] at h ⊢; exact hk m h
        · rw [he]
          obtain ⟨h1, h2, _⟩ := hv
          exact ⟨h2, h1, hst m h2 h1⟩
      · rw [set_other _ _ _ _ hm] at h ⊢; exact hk m h
    · simp only [lookupS]
      by_cases hm : m = n
      · subst hm
        rw [set_same, set_same]
        have hge := best_ge s m
        rw [hn m] at hge
        exact (Nat.max_eq_right hge).symm
      · rw [set_other _ _ _ _ hm, set_other _ _ _ _ hm]; exact hn m
    · simp [LookupNewest, lookupS, set_same]

/-- With the sequence check every reachable state keeps the promises. -/
theorem inv_reach (s : State) (h : Reach true s) : Inv s := by
  induction h with
  | init => exact inv_init
  | step s t _ st ih => exact inv_step s t ih st

/-- Without the sequence check a replay rolls the endpoint back: node 1 publishes twice, the endpoint believes the
second record, the store hands out the first again, and the endpoint goes back to it. -/
theorem noSeqCheck_bad : ∃ s, Reach false s ∧ ¬ NoRollback s := by
  have r1 := Reach.step _ _ (Reach.init (c := false)) (Step.publish init 1)
  have r2 := Reach.step _ _ r1 (Step.publish _ 1)
  have r3 := Reach.step _ _ r2 (Step.lookup _ 1)
  have r4 := Reach.step _ _ r3 (Step.tamper _ 1 ⟨1, 1, true⟩ (Or.inl ⟨rfl, rfl, by decide⟩))
  have r5 := Reach.step _ _ r4 (Step.lookup _ 1)
  refine ⟨_, r5, fun h => ?_⟩
  exact absurd (h 1) (by decide)

end Vinc.FacadeRecords

#audit_axioms Vinc.FacadeRecords.inv_reach
#audit_axioms Vinc.FacadeRecords.noSeqCheck_bad
