import Pinc.ReconcileRefSplit
import Pinc.ReconcileApsAudit

/-!
# Reconcile correctness: the abstract part system instantiated with the byte machine's own rules

What is proved here, and what is not.

PROVED (unbounded, no hypothesis beyond the stated ones):
* `splitParts_spec` (ReconcileRefSplit): the index loop of the machine's split (`split` in core.rs) writes exactly the
  parts of `splitIvs` of the abstract part system, with the fingerprint of each block, and counts them;
* `fitsM_small`: the machine's `leaf_ok` (`leafOk`) accepts every range of at most one receiver item, which is the only
  property the abstract system requires of the leaf rule (`Cfg.fits_small`); `leafOk_total`: it never fails on an index
  whose items fit the item limit;
* `machineCfg`: the abstract system instantiated with the machine's leaf rule (`leafOk` of the receiver's index) and
  any narrowing fan from 2 up. Because `fits` is arbitrary in the abstract theorems, every theorem about the abstract
  system holds for this instance:
  `machine_session_exact` (the final check detects every wrong result; the first pass without an ids leaf and every
  exact pass are exact, and the exact pass passes the check), `machine_steps_bound` (a finished pass processed at most
  `17 + 17 D (2 (lg nA + lg nB) + 2)` parts), `machine_depth_bound`.

NOT PROVED (covered by TLC and by trace validation of the real code only): that the byte-level handlers
(`procPart` arms other than the split loop, `answerLoop` with its rollback, `turn` and its frames, `Initiator.handle`,
`Responder.handle`, the driver loop) are executions of the abstract `PStep` relation. The abstract theorems above
therefore state what any implementation of the part rules with the machine's leaf decisions and split computes; the
remaining link is the refinement of the byte machine to them.
-/

namespace Pinc.Reconcile

/-- The abstract system with the machine's leaf rule: a leaf fits when `leafOk` of the receiver's index says so. -/
def machineCfg (lim : Limits) (o : Oracle) (A B : List Item) (hA : Sorted A) (hB : Sorted B) : Cfg where
  o := o
  A := A
  B := B
  hA := hA
  hB := hB
  minFan := 2
  hmin := Nat.le_refl 2
  hmax := by decide
  fits := fun s it I => fitsM lim (if s then A else B) it I
  fits_small := by
    intro s it I h
    cases s
    · exact fitsM_small lim B hB it I h
    · exact fitsM_small lim A hA it I h

theorem machine_session_exact {lim : Limits} {o : Oracle} {A B : List Item} (hA : Sorted A) (hB : Sorted B)
    (hI : Indep o) :
    (∀ s, PReach (machineCfg lim o A B hA hB) s → s.exact = false → s.pend = [] →
      (CheckPasses (machineCfg lim o A B hA hB) s ↔ ExactReport A B s.here s.there) ∧
      (s.leafed = false → ExactReport A B s.here s.there)) ∧
    (∀ s, PReach (machineCfg lim o A B hA hB) s → s.exact = true → s.pend = [] →
      ExactReport A B s.here s.there ∧ CheckPasses (machineCfg lim o A B hA hB) s) :=
  aps_session_exact (c := machineCfg lim o A B hA hB) hI

theorem machine_steps_bound {lim : Limits} {o : Oracle} {A B : List Item} (hA : Sorted A) (hB : Sorted B)
    {s : St} (h : IReach (machineCfg lim o A B hA hB) s) (hp : s.pend = []) :
    s.log.length ≤ stepsBound 2 (machineCfg lim o A B hA hB).diff A.length B.length :=
  aps_steps_bound (Nat.le_refl 2) (Nat.le_refl 2) h hp

theorem machine_depth_bound {lim : Limits} {o : Oracle} {A B : List Item} (hA : Sorted A) (hB : Sorted B)
    {s : St} (h : IReach (machineCfg lim o A B hA hB) s) :
    ∀ q ∈ s.log ++ s.pend, q.d ≤ depthBound 2 A.length B.length :=
  aps_depth_bound (Nat.le_refl 2) (Nat.le_refl 2) h

#audit_axioms Pinc.Reconcile.splitParts_spec
#audit_axioms Pinc.Reconcile.fitsM_small
#audit_axioms Pinc.Reconcile.leafOk_total
#audit_axioms Pinc.Reconcile.machine_session_exact
#audit_axioms Pinc.Reconcile.machine_steps_bound
#audit_axioms Pinc.Reconcile.machine_depth_bound

end Pinc.Reconcile
