import Vinc.KeyRollSysAct

/-!
# Three findings about the old code, as concrete traces of the fixed model

Each trace is a trace of `Vinc.KeyRollSys` that the model checker found a violation on in the code as first read
(`KeyRoll_gate.cfg`, `KeyRoll_stale.cfg`, `KeyRoll_orphan.cfg`, which now pass); every step is checked by
evaluation. The same steps, run against the fixed code, end differently:

* F1 (`duplicate_answered_again`): a repeated request is delivered while the answerer's next key is staged. The old
  `Keys::on_request` refused it before the duplicate check of `Roll::on_request`, so the lost answer was never sent
  again. Now the answer is queued again, the same answer, and no key changes.
* F2 (`stale_answer_ignored`): an old answer arrives while a newer request is out. The old `Roll::on_answer` took it
  and the two sides computed different Diffie-Hellman values. Now the answer echoes the identifier of its own
  request, which is not the request that is out, so it is ignored and nothing changes.
* F3 (`no_orphan_after_collision`): the request that lost a collision is still in flight when the roll finishes. The
  old code answered it as a fresh request and left keys staged that the peer never takes. Now it arrives in a packet
  opened under the previous key (a late copy of a settled roll) and is ignored.
-/

namespace Vinc.KeyRollSys
open Vinc.KeyRoll

/-! ## F1: a repeated request is answered again while the next key is staged -/

/-- One answerer, one requester, one retransmission. -/
def P1 : Params := ⟨1, fun _ => 1, 2, false⟩

def f1S1 := beginUpd Sys.init false
def f1S2 := sendUpd P1 f1S1 false true
def f1Pk0 := sendPkt P1 f1S1 false true
def f1S3 := deliverUpd P1 f1S2 true f1Pk0 false
def f1S4 := tickUpd f1S3
def f1S5 := sendUpd P1 f1S4 true true
def f1S6 := sendUpd P1 f1S5 false true
def f1Pk1 := sendPkt P1 f1S5 false true

theorem f1_reach : Reach P1 f1S6 :=
  Reach.step _ _ (Reach.step _ _ (Reach.step _ _ (Reach.step _ _ (Reach.step _ _ (Reach.step _ _
    Reach.init (Step.begin _ false (by decide))) (Step.send _ false true (by decide)))
    (Step.deliver _ true f1Pk0 false (by decide))) (Step.tick _)) (Step.send _ true true (by decide)))
    (Step.send _ false true (by decide))

/-- The repeated request is delivered, processed, is a duplicate of the request answered, the next key is staged,
and the answer is queued again: the same answer that went out before (`DupRequestAnswered` holds). -/
theorem duplicate_answered_again :
    deliverOk P1 f1S6 true f1Pk1 false = true ∧
    ((f1S6.nd true).afterRecv P1 f1Pk1 false f1S6.now).2 = true ∧
    ((f1S6.nd true).roll.isDup (Msg.req (.pub (atomOf false 0)))) = true ∧
    (f1S6.nd true).nxt.isSome = true ∧
    ((deliverUpd P1 f1S6 true f1Pk1 false).nd true).out ≠ none ∧
    ((deliverUpd P1 f1S6 true f1Pk1 false).nd true).out = (f1S6.nd true).lastAns := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## F2: a stale answer is ignored -/

def P2 : Params := ⟨1, fun _ => 2, 2, false⟩

def f2S1 := beginUpd Sys.init false
def f2S2 := sendUpd P2 f2S1 false true
def f2S3 := tickUpd f2S2
def f2S4 := sendUpd P2 f2S3 false true
def f2Pk0 := sendPkt P2 f2S1 false true
def f2Pk1 := sendPkt P2 f2S3 false true
def f2S5 := deliverUpd P2 f2S4 true f2Pk0 false
def f2S6 := sendUpd P2 f2S5 true true
def f2Pa0 := sendPkt P2 f2S5 true true
def f2S7 := deliverUpd P2 f2S6 true f2Pk1 false
def f2S8 := sendUpd P2 f2S7 true true
def f2Pa1 := sendPkt P2 f2S7 true true
def f2S9 := deliverUpd P2 f2S8 false f2Pa0 false
def f2S10 := sendUpd P2 f2S9 false false
def f2Pn0 := sendPkt P2 f2S9 false false
def f2S11 := deliverUpd P2 f2S10 true f2Pn0 false
def f2S12 := sendUpd P2 f2S11 true false
def f2Pn1 := sendPkt P2 f2S11 true false
def f2S13 := deliverUpd P2 f2S12 false f2Pn1 false
def f2S14 := beginUpd f2S13 false
def f2S15 := deliverUpd P2 f2S14 false f2Pa1 false

theorem f2_reach : Reach P2 f2S15 := by
  have s1 : Reach P2 f2S1 := Reach.step _ _ Reach.init (Step.begin _ false (by decide))
  have s2 : Reach P2 f2S2 := Reach.step _ _ s1 (Step.send _ false true (by decide))
  have s3 : Reach P2 f2S3 := Reach.step _ _ s2 (Step.tick _)
  have s4 : Reach P2 f2S4 := Reach.step _ _ s3 (Step.send _ false true (by decide))
  have s5 : Reach P2 f2S5 := Reach.step _ _ s4 (Step.deliver _ true f2Pk0 false (by decide))
  have s6 : Reach P2 f2S6 := Reach.step _ _ s5 (Step.send _ true true (by decide))
  have s7 : Reach P2 f2S7 := Reach.step _ _ s6 (Step.deliver _ true f2Pk1 false (by decide))
  have s8 : Reach P2 f2S8 := Reach.step _ _ s7 (Step.send _ true true (by decide))
  have s9 : Reach P2 f2S9 := Reach.step _ _ s8 (Step.deliver _ false f2Pa0 false (by decide))
  have s10 : Reach P2 f2S10 := Reach.step _ _ s9 (Step.send _ false false (by decide))
  have s11 : Reach P2 f2S11 := Reach.step _ _ s10 (Step.deliver _ true f2Pn0 false (by decide))
  have s12 : Reach P2 f2S12 := Reach.step _ _ s11 (Step.send _ true false (by decide))
  have s13 : Reach P2 f2S13 := Reach.step _ _ s12 (Step.deliver _ false f2Pn1 false (by decide))
  have s14 : Reach P2 f2S14 := Reach.step _ _ s13 (Step.begin _ false (by decide))
  exact Reach.step _ _ s14 (Step.deliver _ false f2Pa1 false (by decide))

/-- The old answer is delivered while the newer request is out: it is ignored. The requester's roll and the list of
completed rolls stay as they were, so no two sides disagree (`AgreeDh` holds). -/
theorem stale_answer_ignored :
    deliverOk P2 f2S14 false f2Pa1 false = true ∧
    ((deliverUpd P2 f2S14 false f2Pa1 false).nd false).roll = (f2S14.nd false).roll ∧
    (f2S14.nd false).roll.isIdle = false ∧
    (deliverUpd P2 f2S14 false f2Pa1 false).comp.length = f2S14.comp.length ∧
    ∀ c ∈ f2S15.comp, c.dh = c.gdh := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## F3: keys staged for a roll the peer never takes -/

def P3 : Params := ⟨1, fun _ => 2, 2, false⟩

/-- A node holds staged keys for a roll the peer never took and no longer can: the peer is idle with nothing staged
and on the old generation. -/
def Orphan (S : Sys) : Prop :=
  ∃ n, (S.nd n).stg.isSome = true ∧ (S.nd (!n)).roll.isIdle = true ∧ (S.nd (!n)).nxt = none ∧
    (S.nd (!n)).cur.g = (S.nd n).sk.g ∧ (S.nd (!n)).sk.g = (S.nd n).sk.g

def f3S1 := beginUpd Sys.init false
def f3S2 := sendUpd P3 f3S1 false true
def f3Pk0 := sendPkt P3 f3S1 false true
def f3S3 := beginUpd f3S2 true
def f3S4 := sendUpd P3 f3S3 true true
def f3Pk1 := sendPkt P3 f3S3 true true
def f3S5 := deliverUpd P3 f3S4 true f3Pk0 false
def f3S6 := sendUpd P3 f3S5 true true
def f3Pa := sendPkt P3 f3S5 true true
def f3S7 := deliverUpd P3 f3S6 false f3Pa false
def f3S8 := sendUpd P3 f3S7 false false
def f3Pn0 := sendPkt P3 f3S7 false false
def f3S9 := deliverUpd P3 f3S8 true f3Pn0 false
def f3S10 := sendUpd P3 f3S9 true false
def f3Pn1 := sendPkt P3 f3S9 true false
def f3S11 := deliverUpd P3 f3S10 false f3Pn1 false
def f3S12 := deliverUpd P3 f3S11 false f3Pk1 false

theorem f3_reach : Reach P3 f3S12 := by
  have s1 : Reach P3 f3S1 := Reach.step _ _ Reach.init (Step.begin _ false (by decide))
  have s2 : Reach P3 f3S2 := Reach.step _ _ s1 (Step.send _ false true (by decide))
  have s3 : Reach P3 f3S3 := Reach.step _ _ s2 (Step.begin _ true (by decide))
  have s4 : Reach P3 f3S4 := Reach.step _ _ s3 (Step.send _ true true (by decide))
  have s5 : Reach P3 f3S5 := Reach.step _ _ s4 (Step.deliver _ true f3Pk0 false (by decide))
  have s6 : Reach P3 f3S6 := Reach.step _ _ s5 (Step.send _ true true (by decide))
  have s7 : Reach P3 f3S7 := Reach.step _ _ s6 (Step.deliver _ false f3Pa false (by decide))
  have s8 : Reach P3 f3S8 := Reach.step _ _ s7 (Step.send _ false false (by decide))
  have s9 : Reach P3 f3S9 := Reach.step _ _ s8 (Step.deliver _ true f3Pn0 false (by decide))
  have s10 : Reach P3 f3S10 := Reach.step _ _ s9 (Step.send _ true false (by decide))
  have s11 : Reach P3 f3S11 := Reach.step _ _ s10 (Step.deliver _ false f3Pn1 false (by decide))
  exact Reach.step _ _ s11 (Step.deliver _ false f3Pk1 false (by decide))

/-- The request that lost the collision arrives after the roll finished, under the previous key: nothing is staged
and the state is not an orphan. -/
theorem no_orphan_after_collision : ¬ Orphan f3S12 ∧ (f3S12.nd false).stg = none ∧ (f3S12.nd false).nxt = none := by
  refine ⟨?_, by decide, by decide⟩
  rintro ⟨n, h1, _⟩
  cases n <;> revert h1 <;> decide

end Vinc.KeyRollSys
