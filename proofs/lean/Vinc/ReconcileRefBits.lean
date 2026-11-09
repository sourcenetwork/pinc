import Vinc.ReconcileRefIds

/-!
# Reconcile refinement, part 2f: the id lookup and the reply bitmap

`rpos` (the machine's `rposition` of an id among the 8-byte chunks) is `rposN` of the abstract system on the id values,
and the bitmap the machine builds has bit `j` set exactly when some item of ours was matched to position `j`.
-/

namespace Vinc.Reconcile

/-- The last index (from `n`) whose element satisfies `p`. -/
def lastIdx {α : Type} (p : α → Bool) : List α → Nat → Option Nat
  | [], _ => none
  | a :: l, n => match lastIdx p l (n + 1) with
    | some j => some j
    | none => if p a then some n else none

theorem lastIdx_map {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ (l : List α) (n : Nat), lastIdx p (l.map f) n = lastIdx (fun a => p (f a)) l n
  | [], _ => rfl
  | a :: l, n => by simp [lastIdx, lastIdx_map f p l (n + 1)]

theorem filter_zipIdx_getLast {α : Type} (p : α → Bool) :
    ∀ (l : List α) (n : Nat), (((l.zipIdx n).filter (fun x => p x.1)).getLast?.map (·.2)) = lastIdx p l n
  | [], _ => by simp [lastIdx]
  | a :: l, n => by
    have ih := filter_zipIdx_getLast p l (n + 1)
    rw [List.zipIdx_cons, List.filter_cons]
    generalize hG : (l.zipIdx (n + 1)).filter (fun x => p x.1) = G at ih ⊢
    cases hGl : G.getLast? with
    | none =>
      rw [hGl] at ih
      have h0 : lastIdx p l (n + 1) = none := ih.symm
      cases hp : p a
      · simp [lastIdx, h0, hp, hGl]
      · have : G = [] := by simpa using hGl
        subst this
        simp [lastIdx, h0, hp]
    | some y =>
      rw [hGl] at ih
      have h0 : lastIdx p l (n + 1) = some y.2 := ih.symm
      cases hp : p a
      · simp [lastIdx, h0, hp, hGl]
      · have : G ≠ [] := by intro h; subst h; simp at hGl
        simp [lastIdx, h0, hp, List.getLast?_cons, hGl]

theorem rposN_eq (ids : List Nat) (v : Nat) : rposN ids v = lastIdx (fun a => a == v) ids 0 := by
  unfold rposN; rw [← filter_zipIdx_getLast]

theorem rpos_eq (ids : List (List Nat)) (x : List Nat) : rpos ids x = lastIdx (fun a => a == x) ids 0 := by
  unfold rpos; rw [← filter_zipIdx_getLast]

theorem beBytes_inj (u v : Nat) (hu : u < 2 ^ 64) (hv : v < 2 ^ 64) (h : beBytes idLen u = beBytes idLen v) : u = v := by
  have h1 := fromBE_beBytes idLen u (by simpa [idLen] using hu)
  have h2 := fromBE_beBytes idLen v (by simpa [idLen] using hv)
  rw [← h1, ← h2, h]

theorem lastIdx_beBytes (v : Nat) (hv : v < 2 ^ 64) :
    ∀ (l : List Nat) (n : Nat), (∀ x ∈ l, x < 2 ^ 64) →
      lastIdx (fun a => beBytes idLen a == beBytes idLen v) l n = lastIdx (fun a => a == v) l n
  | [], _, _ => rfl
  | a :: l, n, h => by
    have ih := lastIdx_beBytes v hv l (n + 1) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha : (beBytes idLen a == beBytes idLen v) = (a == v) := by
      by_cases e : a = v
      · subst e; simp
      · have : beBytes idLen a ≠ beBytes idLen v := fun h' => e (beBytes_inj a v (h a (List.mem_cons_self ..)) hv h')
        rw [beq_false_of_ne this, beq_false_of_ne e]
    simp [lastIdx, ih, ha]

/-- The machine's lookup of an id in the chunks is the abstract `rposN` on the id values. -/
theorem rpos_map_beBytes (ids : List Nat) (v : Nat) (hids : ∀ x ∈ ids, x < 2 ^ 64) (hv : v < 2 ^ 64) :
    rpos (ids.map (beBytes idLen)) (beBytes idLen v) = rposN ids v := by
  rw [rpos_eq, rposN_eq, lastIdx_map]
  exact lastIdx_beBytes v hv ids 0 hids

/-! ## The bitmap -/

/-- Bit `j` of a bitmap of bytes, as the initiator reads it. -/
def bitAt (seen : List Nat) (j : Nat) : Bool :=
  match seen[j / 8]? with
  | some byte => decide (byte >>> (j % 8) % 2 = 1)
  | none => false

theorem shr_mod_iff (x s : Nat) : (x >>> s % 2 = 1) ↔ x.testBit s = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]; simp

theorem testBit_or_shl (x m s : Nat) (hm : m < 8) (hs : s < 8) :
    (x ||| 1 <<< m).testBit s = (x.testBit s || decide (s = m)) := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h : s = m
  · subst h; simp
  · have : ¬ (m ≤ s ∧ (1 : Nat).testBit (s - m) = true) ∨ True := Or.inr trivial
    by_cases hms : m ≤ s
    · have : s - m ≠ 0 := by omega
      simp [hms, h, Nat.testBit_one_eq_true_iff_self_eq_zero, this]
    · simp [hms, h]

theorem setBit_length (seen : List Nat) (k : Nat) : (setBit seen k).length = seen.length := by
  simp [setBit]

theorem bitAt_setBit (seen : List Nat) (k j : Nat) (hk : k / 8 < seen.length) :
    bitAt (setBit seen k) j = (bitAt seen j || decide (j = k)) := by
  unfold bitAt setBit
  rw [List.getElem?_mapIdx]
  by_cases hj : j / 8 = k / 8
  · cases hs : seen[j / 8]? with
    | none => rw [hj] at hs; simp [List.getElem?_eq_none_iff] at hs; omega
    | some byte =>
      by_cases hjk : j = k
      · subst hjk; simp [hs, shr_mod_iff, testBit_or_shl byte (j % 8) (j % 8) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))]
      · have hm : j % 8 ≠ k % 8 := by omega
        simp [hs, hj, shr_mod_iff, testBit_or_shl byte (k % 8) (j % 8) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)),
          hm, hjk]
  · have : ¬ j = k := by omega
    simp [hj, this, Ne.symm hj, Option.map]
    cases seen[j / 8]? <;> rfl

end Vinc.Reconcile