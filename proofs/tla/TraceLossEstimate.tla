-------------------------- MODULE TraceLossEstimate --------------------------
(***************************************************************************)
(* Trace validation of the loss estimate, pinc-transport                   *)
(* recovery/loss_estimate.rs (LossEstimate).                               *)
(*                                                                         *)
(* The Rust test tests/trace_loss_estimate.rs drives real estimates        *)
(* through `new`, `record` (batches from 0 to u32::MAX packets, seeded and *)
(* at the boundaries), `reset`, `get` and `should_send_repair` (ages       *)
(* around 2 s and up to u64::MAX, both flags). Every call must be the step *)
(* LossEstimateOps.tla computes, with the answer the code gave: `get` the  *)
(* model's value, `should_send_repair` the model's decision. Counts are    *)
(* written as 2 and ages as 4 little-endian 16-bit limbs; a count of 2^16  *)
(* or more is replayed as 65536, which gives the same value because both   *)
(* walks to a fixed point are shorter (LossEstimate.tla, FewSteps).        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds loss_estimate.ndjson. *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
VARIABLES i, v
vars == <<i, v>>
INSTANCE LossEstimateOps
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/loss_estimate.ndjson")
Ev0 == Trace[i]

\* a u32 count from its 2 limbs, 65536 standing for every count at least that large
Count(l) == IF l[2] > 0 THEN 65536 ELSE l[1]
OldEnough(age) == U!Le(U!W(REPAIR_MIN_AGE), U!FromLimbs(age))

NewEv == Ev0.op = "new" /\ v' = 0 /\ Ev0.v = 0
ResetEv == Ev0.op = "reset" /\ v' = 0 /\ Ev0.v = 0
RecordEv == /\ Ev0.op = "record"
            /\ v' = Step(v, Count(Ev0.lost), Count(Ev0.acked))
            /\ Ev0.v = v'
GetEv == Ev0.op = "get" /\ Ev0.v = v /\ v' = v
RepairEv == /\ Ev0.op = "repair"
            /\ Ev0.ans = Repair(OldEnough(Ev0.age), Ev0.drained, Ev0.direct, v)
            /\ v' = v

Init == i = 1 /\ v = 0
Step1 == /\ i <= Len(Trace) /\ Ev0.t = "loss"
         /\ (NewEv \/ ResetEv \/ RecordEv \/ GetEv \/ RepairEv)
         /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step1 \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the documented range
Inv == v \in 0..SCALE
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
