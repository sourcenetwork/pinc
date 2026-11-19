import Pinc.FacadeAcpForget

/-!
# The facade's access decisions: the settings that break a promise

Each theorem gives a run of the model of `Pinc/FacadeAcpForget.lean` under one setting that is not the code's, and the
promise it breaks: the code before the unrevoke fix (`noForgetOnLift_bad`), an answer kept across a revoke
(`noForgetOnRevoke_bad`), a dial to a revoked peer that goes out (`noRefuseDial_bad`), a host that edits its hook
without telling the endpoint (`noForgetOnChange_bad`), the rule before #440 (`perPeer_bad`), the asking session's own
refusal told to the endpoint (`noAny_bad`), an answer worked out over the listed protocols only (`unlisted_bad`) and a
refusal kept across a dial the hook allows (`noDialAsk_bad`). With the code's settings none of them can happen
(`Pinc/FacadeAcpForgetThm.lean`).
-/

namespace Pinc.FacadeAcpForget

-- The witness settings: the hook allows peer 1 protocol 1 either way and nothing else; protocols 1 and 2 are listed.
def witness (lift revoke dial change each any : Bool) : Cfg :=
  { hook := fun p q => p == 1 && q.proto == 1, listed := [1, 2], dialed := [], forgetOnLift := lift,
    forgetOnRevoke := revoke, refuseDial := dial, forgetOnChange := change, askEach := each, answerAny := any,
    askHeld := true, dialAsks := true }

-- A session of protocol 1, and one of protocol 2, both inbound.
def q1 : Q := ⟨1, .inb⟩
def q2 : Q := ⟨2, .inb⟩

/-- The code before the unrevoke fix: peer 1 is revoked and dials, the deny is cached, the revocation is lifted and the
deny kept, so its next session is refused although the gate now lets it in. -/
theorem noForgetOnLift_bad : ∃ s, Reach (witness false true true true true true) s ∧ ¬ DecideFresh s := by
  let c := witness false true true true true true
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.revoke _ 1)
  have r2 := Reach.step _ _ r1 (Step.ask (c := c) _ 1 q1 q1 (by decide) (by decide) (by decide) (by decide))
  have r3 := Reach.step _ _ r2 (Step.lift (c := c) _ 1)
  have r4 := Reach.step _ _ r3 (Step.cached (c := c) _ 1 q1 (by decide) (by decide) (by decide))
  refine ⟨_, r4, fun h => ?_⟩
  exact absurd (h (by decide)) (by decide)

/-- Keeping the answers across a revoke: peer 1's allow is cached, it is revoked, and its next session goes through
the endpoint on the cached allow although the gate now refuses the peer everything. -/
theorem noForgetOnRevoke_bad : ∃ s, Reach (witness true false true true true true) s ∧ ¬ DecideFresh s := by
  let c := witness true false true true true true
  have r1 := Reach.step _ _ (Reach.init (c := c))
    (Step.ask _ 1 q1 q1 (by decide) (by decide) (by decide) (by decide))
  have r2 := Reach.step _ _ r1 (Step.revoke (c := c) _ 1)
  have r3 := Reach.step _ _ r2 (Step.cached (c := c) _ 1 q1 (by decide) (by decide) (by decide))
  refine ⟨_, r3, fun h => ?_⟩
  exact absurd (h (by decide)) (by decide)

/-- A dial that is not refused up front: peer 1 is revoked and this node's dial reaches it. -/
theorem noRefuseDial_bad : ∃ s, Reach (witness true true false true true true) s ∧ ¬ NoDialRevoked s := by
  let c := witness true true false true true true
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.revoke _ 1)
  have r2 := Reach.step _ _ r1 (Step.dial (c := c) _ 1 ⟨1, .outb⟩ (by decide) (by decide))
  refine ⟨_, r2, fun h => ?_⟩
  exact absurd (h 1 (by decide)) (by decide)

/-- A host that edits its hook without telling the endpoint: peer 2 is refused everything and the deny cached, the
host allows it protocol 1 inbound, and its next session on it is refused although the hook now admits it. -/
theorem noForgetOnChange_bad : ∃ s, Reach (witness true true true false true true) s ∧ ¬ DecideFresh s := by
  let c := witness true true true false true true
  have r1 := Reach.step _ _ (Reach.init (c := c))
    (Step.ask _ 2 q1 q1 (by decide) (by decide) (by decide) (by decide))
  have r2 := Reach.step _ _ r1 (Step.rehook (c := c) _ 2 q1)
  have r3 := Reach.step _ _ r2 (Step.cached (c := c) _ 2 q1 (by decide) (by decide) (by decide))
  refine ⟨_, r3, fun h => ?_⟩
  exact absurd (h (by decide)) (by decide)

/-- The rule before #440: peer 1 dials on protocol 1, the hook allows it and the endpoint caches the allow; its session
on protocol 2, which the hook refuses, comes up on that allow. -/
theorem perPeer_bad : ∃ s, Reach (witness true true true true false false) s ∧ ¬ NoCrossAllow s := by
  let c := witness true true true true false false
  have r1 := Reach.step _ _ (Reach.init (c := c))
    (Step.ask _ 1 q1 q1 (by decide) (by decide) (by decide) (by decide))
  have r2 := Reach.step _ _ r1 (Step.cached (c := c) _ 1 q2 (by decide) (by decide) (by decide))
  refine ⟨_, r2, fun h => ?_⟩
  exact absurd (h (by decide) (by decide)) (by decide)

/-- Telling the endpoint the asking session's own refusal: peer 1 dials first on protocol 2, which the hook refuses,
and the deny is cached although the hook allows it protocol 1. -/
theorem noAny_bad :
    ∃ s, Reach (witness true true true true true false) s ∧
      ¬ NoCrossDeny (witness true true true true true false) s := by
  let c := witness true true true true true false
  have r1 := Reach.step _ _ (Reach.init (c := c))
    (Step.ask _ 1 q2 q2 (by decide) (by decide) (by decide) (by decide))
  refine ⟨_, r1, fun h => ?_⟩
  exact absurd (h 1 (by decide) q1 (by decide)) (by decide)

-- The settings of a node that dials a protocol it does not list: protocol 1 is listed, protocol 2 is dialed without
-- being listed, and the hook allows peer 1 protocol 2 outbound and nothing else; `held` and `dial` are the two rules
-- of the fix for such a node.
def unlisted (held dial : Bool) : Cfg :=
  { hook := fun p q => p == 1 && q == ⟨2, .outb⟩, listed := [1], dialed := [2], forgetOnLift := true,
    forgetOnRevoke := true, refuseDial := true, forgetOnChange := true, askEach := true, answerAny := true,
    askHeld := held, dialAsks := dial }

/-- The answer worked out over the listed protocols only: this node dials peer 1 on protocol 2, which it does not
list; the check its dial raised asks protocol 2 outbound and the session comes up. When the endpoint asks again the
question is protocol 2 inbound, as no dial waits any more, which the hook refuses, and the other questions are the
listed protocol's, which the hook refuses too: the endpoint is told deny, which closes the session the hook allows. -/
theorem unlisted_bad : ∃ s, Reach (unlisted false true) s ∧ ¬ NoCut s := by
  let c := unlisted false true
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.dial _ 1 ⟨2, .outb⟩ (by decide) (by decide))
  have r2 := Reach.step _ _ r1
    (Step.ask (c := c) _ 1 ⟨2, .outb⟩ ⟨2, .outb⟩ (by decide) (by decide) (by decide) (by decide))
  have r3 := Reach.step _ _ r2
    (Step.recheck (c := c) _ 1 ⟨2, .outb⟩ ⟨2, .inb⟩ (by decide) (by decide) (by decide))
  refine ⟨_, r3, fun h => ?_⟩
  exact absurd h (by decide)

/-- A refusal kept across a dial: peer 1 dials this node on the listed protocol, which the hook refuses, and the
endpoint keeps the deny; this node then dials peer 1 on protocol 2, which the hook allows, and the deny stands against
that dial. -/
theorem noDialAsk_bad : ∃ s, Reach (unlisted true false) s ∧ ¬ NoCrossDeny (unlisted true false) s := by
  let c := unlisted true false
  have r1 := Reach.step _ _ (Reach.init (c := c))
    (Step.ask _ 1 ⟨1, .inb⟩ ⟨1, .inb⟩ (by decide) (by decide) (by decide) (by decide))
  have r2 := Reach.step _ _ r1 (Step.dial (c := c) _ 1 ⟨2, .outb⟩ (by decide) (by decide))
  refine ⟨_, r2, fun h => ?_⟩
  exact absurd (h 1 (by decide) ⟨2, .outb⟩ (by decide)) (by decide)

#audit_axioms Pinc.FacadeAcpForget.noForgetOnLift_bad
#audit_axioms Pinc.FacadeAcpForget.noForgetOnRevoke_bad
#audit_axioms Pinc.FacadeAcpForget.noRefuseDial_bad
#audit_axioms Pinc.FacadeAcpForget.noForgetOnChange_bad
#audit_axioms Pinc.FacadeAcpForget.perPeer_bad
#audit_axioms Pinc.FacadeAcpForget.noAny_bad
#audit_axioms Pinc.FacadeAcpForget.unlisted_bad
#audit_axioms Pinc.FacadeAcpForget.noDialAsk_bad

end Pinc.FacadeAcpForget
