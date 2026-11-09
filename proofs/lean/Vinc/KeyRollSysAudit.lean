import Vinc.KeyRollSysCex

/-! Axiom audit of the main theorems of the key roll system. -/

#audit_axioms Vinc.KeyRollSys.Reach.inv
#audit_axioms Vinc.KeyRollSys.genIsDepth
#audit_axioms Vinc.KeyRollSys.phaseParity
#audit_axioms Vinc.KeyRollSys.inStep
#audit_axioms Vinc.KeyRollSys.keysAgree
#audit_axioms Vinc.KeyRollSys.noKeyReuse
#audit_axioms Vinc.KeyRollSys.freshSeal
#audit_axioms Vinc.KeyRollSys.sharesOnce
#audit_axioms Vinc.KeyRollSys.holdOnePTO
#audit_axioms Vinc.KeyRollSys.agreeDh
#audit_axioms Vinc.KeyRollSys.floorHonoured
#audit_axioms Vinc.KeyRollSys.acceptIff
#audit_axioms Vinc.KeyRollSys.neverOtherKey
#audit_axioms Vinc.KeyRollSys.oldKeyOnePTO
#audit_axioms Vinc.KeyRollSys.forgedCostsOneOpen
#audit_axioms Vinc.KeyRollSys.forged_deliver
#audit_axioms Vinc.KeyRollSys.genMonotone
#audit_axioms Vinc.KeyRollSys.floorsRespected
#audit_axioms Vinc.KeyRollSys.dupRequestAnswered
#audit_axioms Vinc.KeyRollSys.dialerWins
#audit_axioms Vinc.KeyRollSys.staleAnswerNoKey
#audit_axioms Vinc.KeyRollSys.duplicate_answered_again
#audit_axioms Vinc.KeyRollSys.stale_answer_ignored
#audit_axioms Vinc.KeyRollSys.no_orphan_after_collision
