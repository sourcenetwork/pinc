---------------------------- MODULE LossEstimate ----------------------------
(***************************************************************************)
(* The node-wide loss estimate of pinc-transport recovery/loss_estimate.rs *)
(* (`step`, `LossEstimate::record`, `reset`, `should_send_repair`), as the *)
(* operators of LossEstimateOps.tla.                                       *)
(*                                                                         *)
(* Checked over every value 0..65536 (the ASSUMEs, which TLC evaluates in  *)
(* full), the invariant of the module doc:                                 *)
(*  - InRange: one step of either kind keeps a value of 0..65536 in it, so *)
(*    the value is always in 0..=65536 (it starts at 0, `new` and `reset`  *)
(*    set 0, and `record` only steps);                                     *)
(*  - FixedPoints: the decay stands still exactly below 32 and the growth  *)
(*    exactly above 65504;                                                 *)
(*  - FewSteps: from the farthest values the walk to either fixed point,   *)
(*    both walks together, is under 1000 steps ("a few hundred": each      *)
(*    under 400), so a batch of any size costs that at most (the fifth     *)
(*    ASSUME).                                                             *)
(* Checked for every case of a machine whose root has one successor per    *)
(* case (old values at and around 0, 32, 328, 32768, 65504, 65536; counts  *)
(* at and around 0, 32, 300, 400):                                         *)
(*  - StepOK: `step`, stopping at the fixed points, is the batch the doc   *)
(*    describes, each packet its own step, acknowledged ones first, and    *)
(*    stays in range;                                                      *)
(*  - RepairOK: `should_send_repair` is true exactly when the connection   *)
(*    is at least 2 s old, its queue drained, the path direct and the      *)
(*    estimate at least 328 (ages 0, 2 s - 1 ns, 2 s, 2 s + 1 ns).          *)
(* Not modelled: concurrent `record` calls; the compare-and-swap loop      *)
(* applies one batch at a time to the latest value (Rust core semantics,   *)
(* assumed), so each batch is a `step` from some value in range.           *)
(***************************************************************************)
EXTENDS Integers
VARIABLE c

INSTANCE LossEstimateOps

Values == 0..SCALE
ASSUME \A v \in Values : Dec(v) \in Values /\ Grow(v) \in Values
ASSUME \A v \in Values : (Dec(v) = v) <=> (v < 32)
ASSUME \A v \in Values : (Grow(v) = v) <=> (v > 65504)
ASSUME \A v \in Values : Dec(v) <= v /\ Grow(v) >= v
ASSUME WalkDec(SCALE) + WalkGrow(0) < 1000 /\ WalkDec(SCALE) < 400 /\ WalkGrow(0) < 400

Olds == {0, 1, 31, 32, 33, 63, 64, 327, 328, 329, 1000, 32768, 65503, 65504, 65505, 65535, 65536}
Counts == {0, 1, 2, 31, 32, 299, 300, 400}
Ages == {0, REPAIR_MIN_AGE - 1, REPAIR_MIN_AGE, REPAIR_MIN_AGE + 1}

Init == c = [t |-> "root"]
Next == /\ c.t = "root"
        /\ \/ \E o \in Olds, l \in Counts, a \in Counts : c' = [t |-> "step", o |-> o, l |-> l, a |-> a]
           \/ \E v \in Olds, age \in Ages, d \in BOOLEAN, p \in BOOLEAN :
                 c' = [t |-> "repair", v |-> v, age |-> age, d |-> d, p |-> p]
Spec == Init /\ [][Next]_c

StepOK == c.t = "step" => LET s == Step(c.o, c.l, c.a) IN s = Plain(c.o, c.l, c.a) /\ s \in Values
RepairOK == c.t = "repair" =>
    (Repair(c.age >= REPAIR_MIN_AGE, c.d, c.p, c.v) <=> (c.age >= 2000000000 /\ c.d /\ c.p /\ c.v >= 328))
=============================================================================
