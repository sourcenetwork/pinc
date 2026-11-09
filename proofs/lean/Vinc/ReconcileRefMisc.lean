import Vinc.ReconcileRefFp

/-!
# Reconcile refinement, part 2d: the CHECK and MISS arms

The CHECK arm (`tailPart_check`: equal whole-set fingerprint writes nothing, otherwise one MISS part) and the MISS arm
(`tailPart_miss`: the initiator records the refusal).
-/

namespace Vinc.Reconcile

theorem rankOf_nil (S : List Item) : rankOf S [] = 0 := by
  unfold rankOf
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x _; simp [lexLt_nil_right]

theorem tailPart_check (o : Oracle) (S : List Item) (c : Core) (hinit : c.init = false) (hn : c.n = S.length)
    (f : Nat) (hf : f < 2 ^ 128) (rest : List Nat) (mark : Nat) :
    tailPart o S c tCHECK [] none (fpBytes f ++ rest) mark =
      if xorH o S = f then .ok (c, rest)
      else .ok ((({ c with out := c.out.addW .miss }).bump 1), rest) := by
  have hfp : fpRange o S 0 c.n = xorH o S := by
    unfold fpRange; rw [hn]; simp
  by_cases he : xorH o S = f
  · simp [tailPart, hinit, rankOf_nil, readBytes_fp, fromBE_fpBytes f hf, hfp, he, lr, Except.mapError, tFP, tCHECK,
      tIDS, tFULL, tCOLD, tREPLY, tMISS, bind, Except.bind, pure, Except.pure]
  · have he' : ¬ f = xorH o S := fun h => he h.symm
    simp [tailPart, hinit, rankOf_nil, readBytes_fp, fromBE_fpBytes f hf, hfp, he, he', lr, Except.mapError, tFP,
      tCHECK, tIDS, tFULL, tCOLD, tREPLY, tMISS, bind, Except.bind, pure, Except.pure, Out.addW, WP.enc, Out.head]

theorem tailPart_miss (o : Oracle) (S : List Item) (c : Core) (hinit : c.init = true) (hn : c.n = S.length)
    (rest : List Nat) (mark : Nat) :
    tailPart o S c tMISS [] none rest mark = .ok ({ c with ans := { c.ans with miss := true } }, rest) := by
  simp [tailPart, hinit, rankOf_nil, hn, tFP, tCHECK, tIDS, tFULL, tCOLD, tREPLY, tMISS, bind, Except.bind, pure,
    Except.pure]

end Vinc.Reconcile
