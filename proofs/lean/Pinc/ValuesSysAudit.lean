import Pinc.Axioms
import Pinc.ValuesSysScen

/-! Axiom audit of the main theorems of the value fetch system. -/

#audit_axioms Pinc.ValuesSys.reach_inv
#audit_axioms Pinc.ValuesSys.only_verified
#audit_axioms Pinc.ValuesSys.readable_after_commit
#audit_axioms Pinc.ValuesSys.verified_grows
#audit_axioms Pinc.ValuesSys.one_final_event
#audit_axioms Pinc.ValuesSys.liar_only
#audit_axioms Pinc.ValuesSys.evicted_holds_nothing
#audit_axioms Pinc.ValuesSys.every_provider_lied
#audit_axioms Pinc.ValuesSys.all_lie_fails
#audit_axioms Pinc.ValuesSys.failure_reasons
#audit_axioms Pinc.ValuesSys.complete_means_all
#audit_axioms Pinc.ValuesSys.work_conserved
#audit_axioms Pinc.ValuesSys.resume_not_asked
#audit_axioms Pinc.ValuesSys.terminates
#audit_axioms Pinc.ValuesSys.completes
#audit_axioms Pinc.ValuesSys.p1_safe
#audit_axioms Pinc.ValuesSys.p2_safe
#audit_axioms Pinc.ValuesSys.p3_safe
#audit_axioms Pinc.ValuesSys.p4_safe
#audit_axioms Pinc.ValuesSys.p1_completes
#audit_axioms Pinc.ValuesSys.p2_completes
#audit_axioms Pinc.ValuesSys.p3_completes
#audit_axioms Pinc.ValuesSys.p4_completes
#audit_axioms Pinc.ValuesSys.drop_completes
#audit_axioms Pinc.ValuesSys.slow_completes
#audit_axioms Pinc.ValuesSys.liar_safe
#audit_axioms Pinc.ValuesSys.liar_honest_survives
#audit_axioms Pinc.ValuesSys.all_lie
#audit_axioms Pinc.ValuesSys.restart_safe
#audit_axioms Pinc.ValuesSys.restart_keeps_verified
#audit_axioms Pinc.ValuesSys.loss_safe
#audit_axioms Pinc.ValuesSys.edge_reasons
#audit_axioms Pinc.ValuesSys.Op.plumbOk
