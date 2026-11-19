import Pinc.KeyRollSysCex

/-! Axiom audit of the main theorems of the key roll system. -/

#audit_axioms Pinc.KeyRollSys.Reach.inv
#audit_axioms Pinc.KeyRollSys.genIsDepth
#audit_axioms Pinc.KeyRollSys.phaseParity
#audit_axioms Pinc.KeyRollSys.inStep
#audit_axioms Pinc.KeyRollSys.keysAgree
#audit_axioms Pinc.KeyRollSys.noKeyReuse
#audit_axioms Pinc.KeyRollSys.freshSeal
#audit_axioms Pinc.KeyRollSys.sharesOnce
#audit_axioms Pinc.KeyRollSys.holdOnePTO
#audit_axioms Pinc.KeyRollSys.agreeDh
#audit_axioms Pinc.KeyRollSys.floorHonoured
#audit_axioms Pinc.KeyRollSys.acceptIff
#audit_axioms Pinc.KeyRollSys.neverOtherKey
#audit_axioms Pinc.KeyRollSys.oldKeyOnePTO
#audit_axioms Pinc.KeyRollSys.forgedCostsOneOpen
#audit_axioms Pinc.KeyRollSys.forged_deliver
#audit_axioms Pinc.KeyRollSys.genMonotone
#audit_axioms Pinc.KeyRollSys.floorsRespected
#audit_axioms Pinc.KeyRollSys.dupRequestAnswered
#audit_axioms Pinc.KeyRollSys.dialerWins
#audit_axioms Pinc.KeyRollSys.staleAnswerNoKey
#audit_axioms Pinc.KeyRollSys.duplicate_answered_again
#audit_axioms Pinc.KeyRollSys.stale_answer_ignored
#audit_axioms Pinc.KeyRollSys.no_orphan_after_collision
