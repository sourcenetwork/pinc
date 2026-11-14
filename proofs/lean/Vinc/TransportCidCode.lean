import Vinc.Axioms
import Vinc.TransportCid

/-!
# Connection ids: the code's refill loop

`conn/cid.rs` `Cids::refill` takes, from the index after the highest one seen on, the next index until `look` of
them are held, within `2 * look` indices; an index held counts, an index whose derived id the table already accepts
(the first id, or the id of an index it holds) is passed over so that no id is listed twice, and any other is added
when a slot can be had and counts then. `refillCode` is that loop, with `idOf` the id the code derives for each index
(`idOf 0` is the first id).

The model's `refill` (the indices `hi + 1` and `hi + 2`, `look` being 2) is this loop whenever no two indices share an
id (`refillCode_eq`): an index not held then never has an id the table accepts, and once an index finds no slot none
after it does, so the indices past `hi + look` are never reached with a slot to take. So every theorem of
`Vinc.TransportCidThm`, `Vinc.TransportCidInv` and `Vinc.TransportCidCalls` holds of the code's loop when ids do not
collide. What the loop does when they do (no id listed twice, and the finding that the id of an index passed over is
lost with the older entry that holds it) is checked by TLC in `proofs/tla/Cid.tla`.
-/

namespace Vinc.TransportCid

/-- `is_local` for the id `x`: the first id, or the id of an index the table holds. -/
def idLocal (idOf : Nat → Nat) (c : C) (x : Nat) : Bool :=
  x == idOf 0 || (List.range slots).any (fun s => (c.ent s).any (fun e => idOf e.idx == x))

/-- The loop of `Cids::refill`, with `n` steps left, at index `j`, `cov` indices covered and `ev` the indices
evicted so far. -/
def refillLoop (idOf : Nat → Nat) : Nat → C → Nat → Nat → List Nat → C × List Nat
  | 0, c, _, _, ev => (c, ev)
  | n + 1, c, j, cov, ev =>
    if look ≤ cov then (c, ev)
    else if has c j then refillLoop idOf n c (j + 1) (cov + 1) ev
    else if idLocal idOf c (idOf j) then refillLoop idOf n c (j + 1) cov ev
    else
      match freeSlot c with
      | some s => refillLoop idOf n (put c s ⟨j, c.tick, false⟩) (j + 1) (cov + 1) ev
      | none =>
        match victim c with
        | some s =>
          refillLoop idOf n (put c s ⟨j, c.tick, false⟩) (j + 1) (cov + 1) (ev ++ ((c.ent s).map (·.idx)).toList)
        | none => refillLoop idOf n c (j + 1) cov ev

/-- `Cids::refill`: the indices `hi + 1` to `hi + 2 * look` at most. -/
def refillCode (idOf : Nat → Nat) (c : C) : C × List Nat :=
  if c.sec then refillLoop idOf (2 * look) c (c.hi + 1) 0 [] else (c, [])

theorem idOf_beq (idOf : Nat → Nat) (hinj : ∀ a b, idOf a = idOf b → a = b) (a b : Nat) :
    (idOf a == idOf b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have h' : idOf a ≠ idOf b := fun e => h (hinj _ _ e)
    rw [beq_false_of_ne h', beq_false_of_ne h]

/-- With no two indices sharing an id, the id of `j` is accepted exactly when `j` is index 0 or held. -/
theorem idLocal_inj (idOf : Nat → Nat) (hinj : ∀ a b, idOf a = idOf b → a = b) (c : C) (j : Nat) :
    idLocal idOf c (idOf j) = (j == 0 || has c j) := by
  unfold idLocal has
  rw [idOf_beq idOf hinj j 0]
  congr 1
  congr 1
  funext s
  cases c.ent s with
  | none => rfl
  | some e => simp only [Option.any_some]; exact idOf_beq idOf hinj e.idx j

theorem loop_done (idOf : Nat → Nat) (n : Nat) (hn : 0 < n) (c : C) (j cov : Nat) (ev : List Nat) (h : look ≤ cov) :
    refillLoop idOf n c j cov ev = (c, ev) := by
  cases n with
  | zero => omega
  | succ n => simp [refillLoop, h]

/-- With no slot to be had, the loop changes nothing, whatever it passes. -/
theorem loop_stuck (idOf : Nat → Nat) (c : C) (hf : freeSlot c = none) (hv : victim c = none) :
    ∀ n j cov ev, refillLoop idOf n c j cov ev = (c, ev) := by
  intro n
  induction n with
  | zero => intro j cov ev; rfl
  | succ n ih =>
    intro j cov ev
    simp only [refillLoop, hf, hv]
    repeat' split
    all_goals first | rfl | exact ih _ _ _

/-- One step of the loop at an index `j ≠ 0`, below `look` covered, with no two indices sharing an id: the step of
the model's `refill1`. -/
theorem loop_step (idOf : Nat → Nat) (hinj : ∀ a b, idOf a = idOf b → a = b) (n : Nat) (c : C) (j cov : Nat)
    (ev : List Nat) (hj : j ≠ 0) (hc : ¬ look ≤ cov) :
    refillLoop idOf (n + 1) c j cov ev =
      if has c j then refillLoop idOf n c (j + 1) (cov + 1) ev
      else match freeSlot c with
        | some _ => refillLoop idOf n (refill1 c j).1 (j + 1) (cov + 1) (ev ++ (refill1 c j).2.toList)
        | none =>
          match victim c with
          | some _ => refillLoop idOf n (refill1 c j).1 (j + 1) (cov + 1) (ev ++ (refill1 c j).2.toList)
          | none => refillLoop idOf n c (j + 1) cov ev := by
  have hl : idLocal idOf c (idOf j) = has c j := by
    rw [idLocal_inj idOf hinj]; simp [hj]
  simp only [refillLoop, hc, ite_false, hl]
  by_cases hh : has c j = true
  · simp [hh]
  · have hh' : has c j = false := by simpa using hh
    simp only [hh', Bool.false_eq_true, ite_false]
    cases hf : freeSlot c with
    | some s => simp [refill1, hh', hf]
    | none =>
      cases hv : victim c with
      | some s => simp [refill1, hh', hf, hv]
      | none => rfl

theorem refill1_noslot (c : C) (k : Nat) (hf : freeSlot c = none) (hv : victim c = none) : refill1 c k = (c, none) := by
  unfold refill1
  split
  · rfl
  · simp [hf, hv]

/-- The loop's second index, after one covered. -/
theorem loop_second (idOf : Nat → Nat) (hinj : ∀ a b, idOf a = idOf b → a = b) (c : C) (j cov : Nat)
    (ev : List Nat) (hj : j ≠ 0) (hcov : cov = 1) :
    refillLoop idOf 3 c j cov ev = ((refill1 c j).1, ev ++ (refill1 c j).2.toList) := by
  subst hcov
  have h1 : ¬ look ≤ 1 := by simp [look]
  have hd : ∀ c' j' ev', refillLoop idOf 2 c' j' 2 ev' = (c', ev') :=
    fun c' j' ev' => loop_done idOf 2 (by decide) c' j' 2 ev' (by simp [look])
  show refillLoop idOf (2 + 1) c j 1 ev = _
  rw [loop_step idOf hinj 2 c j 1 ev hj h1]
  by_cases hh : has c j = true
  · have : refill1 c j = (c, none) := by simp [refill1, hh]
    simp [hh, hd, this]
  · have hh' : has c j = false := by simpa using hh
    cases hf : freeSlot c with
    | some s => simp [hh', hd]
    | none =>
      cases hv : victim c with
      | some s => simp [hh', hd]
      | none =>
        have hr : ∀ k, refill1 c k = (c, none) := fun k => refill1_noslot c k hf hv
        simp [hh', loop_stuck idOf c hf hv, hr]

/-- When no two indices share an id, the code's refill loop is the model's `refill`. -/
theorem refillCode_eq (idOf : Nat → Nat) (hinj : ∀ a b, idOf a = idOf b → a = b) (c : C) :
    refillCode idOf c = refill c := by
  unfold refillCode refill
  cases hs : c.sec
  · rfl
  · show refillLoop idOf (3 + 1) c (c.hi + 1) 0 [] =
      ((refill1 (refill1 c (c.hi + 1)).1 (c.hi + 1 + 1)).1,
        (refill1 c (c.hi + 1)).2.toList ++ (refill1 (refill1 c (c.hi + 1)).1 (c.hi + 1 + 1)).2.toList)
    have h0 : ¬ look ≤ 0 := by simp [look]
    have h2 : ∀ c' j' ev', j' ≠ 0 → refillLoop idOf 3 c' j' 1 ev' = ((refill1 c' j').1, ev' ++ (refill1 c' j').2.toList) :=
      fun c' j' ev' hj => loop_second idOf hinj c' j' 1 ev' hj rfl
    rw [loop_step idOf hinj 3 c (c.hi + 1) 0 [] (by omega) h0]
    by_cases hh : has c (c.hi + 1) = true
    · have : refill1 c (c.hi + 1) = (c, none) := by simp [refill1, hh]
      simp [hh, h2, this]
    · have hh' : has c (c.hi + 1) = false := by simpa using hh
      cases hf : freeSlot c with
      | some s => simp [hh', h2]
      | none =>
        cases hv : victim c with
        | some s => simp [hh', h2]
        | none =>
          have hr : ∀ k, refill1 c k = (c, none) := fun k => refill1_noslot c k hf hv
          simp [hh', loop_stuck idOf c hf hv, hr]

#audit_axioms Vinc.TransportCid.idLocal_inj
#audit_axioms Vinc.TransportCid.loop_stuck
#audit_axioms Vinc.TransportCid.refillCode_eq

end Vinc.TransportCid
