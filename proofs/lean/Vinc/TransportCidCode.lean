import Vinc.Axioms
import Vinc.TransportCidCalls

/-!
# Connection ids: the code's calls, with any derived ids

`conn/cid.rs` `Cids::refill` takes, from the index after the highest one seen on, the next index until `look` of
them are held, within `2 * look` indices: an index held counts; an index with the first id is passed over; an index
whose derived id an entry holds is passed over and that entry stands for it too, its index becoming the newer of the
two (`bump`, the fix of #398), so no id is listed twice and the entry is kept until every index it stands for is
`look` below the highest one seen; any other index is added when a slot can be had and counts then. `refillLoop` is
that loop, with `idOf` the id the code derives for each index (`idOf 0` is the first id). `authCode` is
`on_authenticated` for the id of an index: the first slot that holds the id is used and seen, and the highest index
seen moves up to the slot's index, the newest of those its entry stands for (the code cannot tell which of them the
sender used). `installCode` is `install`. `Vinc.TraceCid` replays the recorded runs, collisions included, through
these functions.

With no two indices sharing an id they are the model's `refill`, `auth` and `install` (`refillCode_eq`,
`authCode_eq`, `installCode_eq`): an index not held then never has an id the table holds, so nothing is bumped, and
once an index finds no slot none after it does, so the indices past `hi + look` are never reached with a slot to take.
So every theorem of `Vinc.TransportCidThm`, `Vinc.TransportCidInv` and `Vinc.TransportCidCalls` holds of the code's
calls when ids do not collide. What they do when ids collide is checked by TLC in `proofs/tla/Cid.tla`: the ids of the
window of the highest index seen stay accepted, and the findings where the highest index seen runs ahead of, or stays
behind, the index the sender used.
-/

namespace Vinc.TransportCid

/-- `is_local` for the id `x`: the first id, or the id of an index the table holds. -/
def idLocal (idOf : Nat → Nat) (c : C) (x : Nat) : Bool :=
  x == idOf 0 || (List.range slots).any (fun s => (c.ent s).any (fun e => idOf e.idx == x))

/-- The slot that holds the id `x`: the first one, as the code's `find` takes it. -/
def slotOfId (idOf : Nat → Nat) (c : C) (x : Nat) : Option Nat :=
  (List.range slots).find? (fun s => (c.ent s).any (fun e => idOf e.idx == x))

/-- The entry in slot `s` stands for the index `j` too: its index becomes the newer of the two. -/
def bump (c : C) (s j : Nat) : C :=
  match c.ent s with
  | some e => put c s { e with idx := max e.idx j }
  | none => c

/-- The loop of `Cids::refill`, with `n` steps left, at index `j`, `cov` indices covered and `ev` the indices
evicted so far. -/
def refillLoop (idOf : Nat → Nat) : Nat → C → Nat → Nat → List Nat → C × List Nat
  | 0, c, _, _, ev => (c, ev)
  | n + 1, c, j, cov, ev =>
    if look ≤ cov then (c, ev)
    else if has c j then refillLoop idOf n c (j + 1) (cov + 1) ev
    else if idOf j = idOf 0 then refillLoop idOf n c (j + 1) cov ev
    else
      match slotOfId idOf c (idOf j) with
      | some s => refillLoop idOf n (bump c s j) (j + 1) cov ev
      | none =>
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

/-- `install`: start deriving; the lookahead ids become routable. -/
def installCode (idOf : Nat → Nat) (c : C) : C × List Nat := refillCode idOf { c with sec := true }

/-- The packet authenticated on the entry in slot `s`, whose index is `k`: the entry is used and seen; the highest index
moves up and the lookahead is filled when `k` is above it. -/
def authAtCode (idOf : Nat → Nat) (c1 : C) (k s : Nat) : C × List Nat :=
  let c2 := put c1 s ⟨k, c1.tick, true⟩
  if c1.hi < k then refillCode idOf { c2 with hi := k } else (c2, [])

/-- `on_authenticated` for the id of index `k`: the first slot that holds it is used, with its own index, the newest of
those its entry stands for (the first id, and an id no slot holds, only move the tick). -/
def authCode (idOf : Nat → Nat) (c : C) (k : Nat) : C × List Nat :=
  let c1 := { c with tick := c.tick + 1 }
  match slotOfId idOf c1 (idOf k) with
  | none => (c1, [])
  | some s =>
    match c.ent s with
    | none => (c1, [])
    | some e => authAtCode idOf c1 e.idx s

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

/-- With no two indices sharing an id, the slot that holds the id of `k` is the slot that holds `k`. -/
theorem slotOfId_inj (idOf : Nat → Nat) (hinj : ∀ a b, idOf a = idOf b → a = b) (c : C) (k : Nat) :
    slotOfId idOf c (idOf k) = slotOf c k := by
  unfold slotOfId slotOf
  congr 1
  funext s
  cases c.ent s with
  | none => rfl
  | some e => simp only [Option.any_some]; exact idOf_beq idOf hinj e.idx k

theorem slotOf_none (c : C) (k : Nat) (h : has c k = false) : slotOf c k = none := by
  unfold slotOf
  rw [List.find?_eq_none]
  intro s hs hp
  unfold has at h
  rw [List.any_eq_false] at h
  exact h s hs hp

/-- With no two indices sharing an id, no slot holds the id of an index the table does not hold. -/
theorem slotOfId_none (idOf : Nat → Nat) (hinj : ∀ a b, idOf a = idOf b → a = b) (c : C) (j : Nat)
    (h : has c j = false) : slotOfId idOf c (idOf j) = none := by
  rw [slotOfId_inj idOf hinj]
  exact slotOf_none c j h

theorem loop_done (idOf : Nat → Nat) (n : Nat) (hn : 0 < n) (c : C) (j cov : Nat) (ev : List Nat) (h : look ≤ cov) :
    refillLoop idOf n c j cov ev = (c, ev) := by
  cases n with
  | zero => omega
  | succ n => simp [refillLoop, h]

/-- With no two indices sharing an id and no slot to be had, the loop changes nothing, whatever it passes. -/
theorem loop_stuck (idOf : Nat → Nat) (hinj : ∀ a b, idOf a = idOf b → a = b) (c : C) (hf : freeSlot c = none)
    (hv : victim c = none) : ∀ n j cov ev, refillLoop idOf n c j cov ev = (c, ev) := by
  intro n
  induction n with
  | zero => intro j cov ev; rfl
  | succ n ih =>
    intro j cov ev
    cases hh : has c j with
    | true =>
      simp only [refillLoop, hh]
      repeat' split
      all_goals first | rfl | exact ih _ _ _ | contradiction
    | false =>
      simp only [refillLoop, hh, Bool.false_eq_true, ite_false, slotOfId_none idOf hinj c j hh, hf, hv]
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
  have h0 : ¬ idOf j = idOf 0 := fun e => hj (hinj _ _ e)
  simp only [refillLoop, hc, ite_false]
  by_cases hh : has c j = true
  · simp [hh]
  · have hh' : has c j = false := by simpa using hh
    simp only [hh', Bool.false_eq_true, ite_false, h0, slotOfId_none idOf hinj c j hh']
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
        simp [hh', loop_stuck idOf hinj c hf hv, hr]

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
          simp [hh', loop_stuck idOf hinj c hf hv, hr]

/-- When no two indices share an id, the code's `install` is the model's. -/
theorem installCode_eq (idOf : Nat → Nat) (hinj : ∀ a b, idOf a = idOf b → a = b) (c : C) :
    installCode idOf c = install c := by
  unfold installCode install
  exact refillCode_eq idOf hinj _

theorem authAtCode_eq (idOf : Nat → Nat) (hinj : ∀ a b, idOf a = idOf b → a = b) (c1 : C) (k s : Nat) :
    authAtCode idOf c1 k s = authAt c1 k s := by
  unfold authAtCode authAt
  simp only [refillCode_eq idOf hinj]

/-- When no two indices share an id, the code's `on_authenticated` is the model's `auth`, on any table of the model's
shape. -/
theorem authCode_eq (idOf : Nat → Nat) (hinj : ∀ a b, idOf a = idOf b → a = b) (c : C) (hc : Core c) (k : Nat) :
    authCode idOf c k = auth c k := by
  unfold authCode auth
  simp only [slotOfId_inj idOf hinj]
  by_cases hk : k < 1
  · have h0 : slotOf { c with tick := c.tick + 1 } k = none := by
      apply slotOf_none
      cases hh : has { c with tick := c.tick + 1 } k with
      | false => rfl
      | true =>
        obtain ⟨s, e, he, hek⟩ := (has_iff { c with tick := c.tick + 1 } hc.bound k).1 hh
        have := hc.pos s e he
        omega
    rw [if_pos hk, h0]
  · rw [if_neg hk]
    cases hs : slotOf { c with tick := c.tick + 1 } k with
    | none => rfl
    | some s =>
      obtain ⟨_, e, he, hek⟩ := slotOf_spec { c with tick := c.tick + 1 } k s hs
      have he' : c.ent s = some e := he
      simp only [he']
      rw [hek]
      exact authAtCode_eq idOf hinj _ k s

#audit_axioms Vinc.TransportCid.idLocal_inj
#audit_axioms Vinc.TransportCid.loop_stuck
#audit_axioms Vinc.TransportCid.refillCode_eq
#audit_axioms Vinc.TransportCid.installCode_eq
#audit_axioms Vinc.TransportCid.authCode_eq

end Vinc.TransportCid
