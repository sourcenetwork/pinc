import Vinc.Axioms
import Vinc.ReconcileApsIds

/-!
# Reconcile APS: axiom audit of the main theorems

The abstract part system (ReconcileApsSplit .. ReconcileApsIds) proves, for sorted sets and any choice of the code's
nondeterminism, any id function and (where stated) independent hashes:

* `splitIvs_spec`: a split is a partition into at most `fan` blocks, each holding fewer receiver items;
* `reach_inv`: safety in every reachable state (arenas safe whatever the ids, pending intervals disjoint);
* `final_exact_of_lossless`: a pass without an ids leaf, and every exact pass, reports exactly when it ends;
* `aps_session_exact`: pass 1 passes the final check exactly when it is exact; the exact pass is exact and passes;
* `aps_ids_exact_of_inj`: an injective id function makes the ids reply exact;
* `aps_progress`, `aps_finishes`: no stuck state, termination;
* `aps_depth_bound`, `aps_depth_bound_16`, `aps_steps_bound`: depth `2 (lg nA + lg nB) + 3` (67 with the 16-way split
  for sets under 2^64 items) and at most `17 + 17 D (2 (lg nA + lg nB) + 2)` parts processed, `D` the difference.
-/

#audit_axioms Vinc.Reconcile.splitIvs_spec
#audit_axioms Vinc.Reconcile.reach_inv
#audit_axioms Vinc.Reconcile.reach_cov
#audit_axioms Vinc.Reconcile.final_exact_of_lossless
#audit_axioms Vinc.Reconcile.aps_session_exact
#audit_axioms Vinc.Reconcile.aps_ids_exact_of_inj
#audit_axioms Vinc.Reconcile.aps_progress
#audit_axioms Vinc.Reconcile.aps_finishes
#audit_axioms Vinc.Reconcile.aps_depth_bound
#audit_axioms Vinc.Reconcile.aps_depth_bound_16
#audit_axioms Vinc.Reconcile.aps_steps_bound
#audit_axioms Vinc.Reconcile.Proc.cost
