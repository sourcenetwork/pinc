import Vinc.KeyRollSysAct

/-!
# Three findings about the code as read, as concrete traces

Each lemma is one trace of `Vinc.KeyRollSys` that the model checker also finds (`KeyRoll_gate.cfg`,
`KeyRoll_stale.cfg`, `KeyRoll_orphan.cfg`); every step is checked by evaluation, and the property that fails is
shown to fail in the last state. They are findings about `keyroll.rs` and `conn/keys.rs`, not properties.

* F1 (`gate_drops_duplicate`): with `gateFirst = true` (`Keys::on_request` refuses a request while a next key is
  staged, before the duplicate check of `Roll::on_request`) a duplicate request is dropped while the answerer's
  next key is staged: the answer is not sent again. With `gateFirst = false` the same trace answers it.
* F2 (`stale_answer_disagrees`): with `bindAnswers = false` (an answer carries no echo of the request it answers
  and `Roll::on_answer` does not check it) an old answer delivered while a newer request is out is taken, and the
  two sides compute different Diffie-Hellman values.
* F3 (`orphan_after_collision`): a request that lost a collision, still in flight, is delivered after the roll
  finished and is answered as a fresh request: the answerer stages keys the peer never takes.
-/

namespace Vinc.KeyRollSys
open Vinc.KeyRoll

/-! ## F1: the gate drops a duplicate request -/

/-- One answerer, one requester, one retransmission; `g` is `gateFirst`. -/
def P1 (g : Bool) : Params := ⟨1, fun _ => 1, 2, g, true, false⟩

def f1S1 (P : Params) := beginUpd Sys.init false
def f1S2 (P : Params) := sendUpd P (f1S1 P) false true
def f1Pk0 (P : Params) := sendPkt P (f1S1 P) false true
def f1S3 (P : Params) := deliverUpd P (f1S2 P) true (f1Pk0 P) false
def f1S4 (P : Params) := tickUpd (f1S3 P)
def f1S5 (P : Params) := sendUpd P (f1S4 P) true true
def f1S6 (P : Params) := sendUpd P (f1S5 P) false true
def f1Pk1 (P : Params) := sendPkt P (f1S5 P) false true

theorem f1_reach (g : Bool) : Reach (P1 g) (f1S6 (P1 g)) := by
  cases g <;>
  exact Reach.step _ _ (Reach.step _ _ (Reach.step _ _ (Reach.step _ _ (Reach.step _ _ (Reach.step _ _
    Reach.init (Step.begin _ false (by decide))) (Step.send _ false true (by decide)))
    (Step.deliver _ true (f1Pk0 _) false (by decide))) (Step.tick _)) (Step.send _ true true (by decide)))
    (Step.send _ false true (by decide))

/-- With `gateFirst = true` the duplicate request is delivered, processed, is a duplicate of the request answered,
and no answer is queued: `DupRequestAnswered` fails. -/
theorem gate_drops_duplicate :
    deliverOk (P1 true) (f1S6 (P1 true)) true (f1Pk1 (P1 true)) false = true ∧
    ((f1S6 (P1 true)).nd true).roll.isDup (Msg.req (.pub (atomOf false 0))) = true ∧
    (f1Pk1 (P1 true)).pl = some (Msg.req (.pub (atomOf false 0))) ∧
    (((f1S6 (P1 true)).nd true).afterRecv (P1 true) (f1Pk1 (P1 true)) false (f1S6 (P1 true)).now).2 = true ∧
    ((deliverUpd (P1 true) (f1S6 (P1 true)) true (f1Pk1 (P1 true)) false).nd true).out = none := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- ... and with `gateFirst = false` the same step queues the answer again. -/
theorem ungated_answers_duplicate :
    ((deliverUpd (P1 false) (f1S6 (P1 false)) true (f1Pk1 (P1 false)) false).nd true).out ≠ none := by decide

/-! ## F2: a stale answer is taken when answers are not bound to their request -/

def P2 : Params := ⟨1, fun _ => 2, 2, false, false, false⟩

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

/-- The two sides complete a roll with different Diffie-Hellman values: `AgreeDh` fails. -/
theorem stale_answer_disagrees : ∃ c ∈ f2S15.comp, c.dh ≠ c.gdh := by
  exact ⟨f2S15.comp.head (by decide), List.head_mem _, by decide⟩

/-! ## F3: keys staged for a roll the peer never takes -/

def P3 : Params := ⟨1, fun _ => 2, 2, false, true, false⟩

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

/-- The request that lost the collision is answered after the roll finished: the dialer stages keys the acceptor
never takes. -/
theorem orphan_after_collision : Orphan f3S12 := ⟨false, by decide, by decide, by decide, by decide, by decide⟩

end Vinc.KeyRollSys
