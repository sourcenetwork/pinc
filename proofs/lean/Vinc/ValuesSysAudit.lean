import Vinc.Axioms
import Vinc.ValuesSysScen

/-! Axiom audit of the main theorems of the value fetch system. -/

#audit_axioms Vinc.ValuesSys.reach_inv
#audit_axioms Vinc.ValuesSys.only_verified
#audit_axioms Vinc.ValuesSys.readable_after_commit
#audit_axioms Vinc.ValuesSys.verified_grows
#audit_axioms Vinc.ValuesSys.one_final_event
#audit_axioms Vinc.ValuesSys.liar_only
#audit_axioms Vinc.ValuesSys.evicted_holds_nothing
#audit_axioms Vinc.ValuesSys.every_provider_lied
#audit_axioms Vinc.ValuesSys.all_lie_fails
#audit_axioms Vinc.ValuesSys.failure_reasons
#audit_axioms Vinc.ValuesSys.complete_means_all
#audit_axioms Vinc.ValuesSys.work_conserved
#audit_axioms Vinc.ValuesSys.resume_not_asked
#audit_axioms Vinc.ValuesSys.terminates
#audit_axioms Vinc.ValuesSys.completes
#audit_axioms Vinc.ValuesSys.p1_safe
#audit_axioms Vinc.ValuesSys.p2_safe
#audit_axioms Vinc.ValuesSys.p3_safe
#audit_axioms Vinc.ValuesSys.p4_safe
#audit_axioms Vinc.ValuesSys.p1_completes
#audit_axioms Vinc.ValuesSys.p2_completes
#audit_axioms Vinc.ValuesSys.p3_completes
#audit_axioms Vinc.ValuesSys.p4_completes
#audit_axioms Vinc.ValuesSys.drop_completes
#audit_axioms Vinc.ValuesSys.slow_completes
#audit_axioms Vinc.ValuesSys.liar_safe
#audit_axioms Vinc.ValuesSys.liar_honest_survives
#audit_axioms Vinc.ValuesSys.all_lie
#audit_axioms Vinc.ValuesSys.restart_safe
#audit_axioms Vinc.ValuesSys.restart_keeps_verified
#audit_axioms Vinc.ValuesSys.loss_safe
#audit_axioms Vinc.ValuesSys.edge_reasons
