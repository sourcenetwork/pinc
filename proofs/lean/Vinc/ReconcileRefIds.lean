import Vinc.ReconcileRefMisc

/-!
# Reconcile refinement, part 2e: the IDS arm of the responder

The IDS arm of the responder, split off `tailPart` (`tailPart_ids`) as `idsArm`.
-/

namespace Vinc.Reconcile

/-- One item of the loop of the IDS arm. -/
def idStep (o : Oracle) (idl : List (List Nat)) (st : List Nat × Out × Nat) (x : Item) : List Nat × Out × Nat :=
  match rpos idl (idBytes o x) with
  | some k => (setBit st.1 k, st.2.1, st.2.2)
  | none => (st.1, st.2.1.stageItem x, st.2.2 + 1)

/-- The IDS arm of `tailPart` for the ranks `a..b`. -/
def idsArm (o : Oracle) (S : List Item) (c : Core) (lo : Item) (hi : Option Item) (a b : Nat) (r : List Nat)
    (mark : Nat) : Except Err (Core × List Nat) := do
  let lim := c.lim
  let (cc, r) ← lr (count r)
  if cc > aleaf then throw (.malformed .count)
  let (ids, r) ← lr (readBytes (cc * idLen) r)
  let narrow ← if b - a > aleaf then pure true else do pure !(← leafOk lim S lo hi a b true)
  if narrow then
    let (out, cnt) ← splitFit o lim S c.out lo hi a b mark 3
    pure (({ c with out := out }).bump cnt, r)
  else
    let xs ← readRange lim S a (b - a)
    let idl := chunks idLen cc ids
    let (seen, out, extra) := xs.foldl (idStep o idl) ([0, 0, 0, 0], c.out, 0)
    pure (({ c with out := replyPart out lo hi cc seen extra }).bump 1, r)

/-- The upper rank as `tailPart` computes it. -/
def bOf (n : Nat) (S : List Item) (hi : Option Item) : Nat := match hi with | none => n | some h => rankOf S h

theorem bOf_eq {lim S c} (I : Iv) (h : HCtx lim S c I) : bOf c.n S I.hi = rankHi S I.hi := by
  unfold bOf rankHi; cases I.hi <;> simp [h.hn]

theorem tailPart_ids (o : Oracle) (S : List Item) (c : Core) (lo : Item) (hi : Option Item) (hinit : c.init = false)
    (hab : ¬ bOf c.n S hi < rankOf S lo) (r : List Nat) (mark : Nat) :
    tailPart o S c tIDS lo hi r mark = idsArm o S c lo hi (rankOf S lo) (bOf c.n S hi) r mark := by
  cases hi <;> simp only [bOf] at hab ⊢ <;>
  (unfold tailPart idsArm
   simp (config := {decide := true}) only [hab, hinit, tFP, tIDS, bOf, ite_true, ite_false, Bool.not_false, and_true,
     Bool.false_eq_true, Nat.reduceEqDiff, bind, Except.bind, pure, Except.pure]
   rfl)

end Vinc.Reconcile
