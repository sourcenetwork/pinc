--------------------------- MODULE LossEstimateOps ---------------------------
(***************************************************************************)
(* The loss estimate of pinc-transport recovery/loss_estimate.rs: `step`   *)
(* (the two loops, each stopping at its fixed point) and                   *)
(* `LossEstimate::should_send_repair`, as operators. LossEstimate.tla      *)
(* checks them; TraceLossEstimate.tla replays the real estimate. No        *)
(* constants, no variables.                                                *)
(***************************************************************************)
EXTENDS Integers

SCALE == 65536
REPAIR_THRESHOLD == 328
REPAIR_MIN_AGE == 2000000000
GAIN == 32

\* one acknowledged packet: `v - (v >> 5)`; one lost packet: `v + ((SCALE - v) >> 5)`
Dec(v) == v - v \div GAIN
Grow(v) == v + (SCALE - v) \div GAIN

\* the loops of `step`: n steps, stopping when a step changes nothing
RECURSIVE DecN(_, _)
DecN(v, n) == IF n = 0 \/ Dec(v) = v THEN v ELSE DecN(Dec(v), n - 1)
RECURSIVE GrowN(_, _)
GrowN(v, n) == IF n = 0 \/ Grow(v) = v THEN v ELSE GrowN(Grow(v), n - 1)
\* `step(old, lost, acked)`: the acknowledged ones first, then the lost ones
Step(old, lost, acked) == GrowN(DecN(old, acked), lost)

\* the same steps written out plainly, one packet at a time and never stopping early (as the doc of `step` says:
\* "each as its own step")
RECURSIVE DecAll(_, _)
DecAll(v, n) == IF n = 0 THEN v ELSE DecAll(Dec(v), n - 1)
RECURSIVE GrowAll(_, _)
GrowAll(v, n) == IF n = 0 THEN v ELSE GrowAll(Grow(v), n - 1)
Plain(old, lost, acked) == GrowAll(DecAll(old, acked), lost)

\* the steps until the fixed point, from v
RECURSIVE WalkDec(_)
WalkDec(v) == IF Dec(v) = v THEN 0 ELSE 1 + WalkDec(Dec(v))
RECURSIVE WalkGrow(_)
WalkGrow(v) == IF Grow(v) = v THEN 0 ELSE 1 + WalkGrow(Grow(v))

\* `should_send_repair(conn_age, queue_drained, on_direct_path)`, the age already compared with REPAIR_MIN_AGE
Repair(old_enough, drained, direct, v) == drained /\ direct /\ old_enough /\ v >= REPAIR_THRESHOLD
=============================================================================
