-------------------------- MODULE TraceRecoveryMath --------------------------
(***************************************************************************)
(* Trace validation of pinc-transport recovery/math.rs (`sat`, `icbrt`).   *)
(*                                                                         *)
(* The Rust test tests/trace_recovery_math.rs calls the real functions     *)
(* (re-exported for the cargo feature `trace`) and records:                *)
(*  - icbrt: n below 2^30 and the root the code returned; it must be the   *)
(*    floor cube root by definition, and the root the loop of              *)
(*    RecoveryMathOps.tla computes;                                        *)
(*  - sat: the u128 argument as 8 little-endian 16-bit limbs and the u64   *)
(*    result as 4; the result must be the low 4 limbs when the high 4 are  *)
(*    zero, and every limb 65535 (u64::MAX) otherwise.                     *)
(* Each event is a successor of the root state; the invariant checks the   *)
(* event the state names. The test itself checks `icbrt` on values up to   *)
(* u128::MAX with u128 arithmetic, which TLC cannot hold.                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds recovery_math.ndjson. *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
VARIABLE c
INSTANCE RecoveryMathOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/recovery_math.ndjson")

Init == c = [t |-> "root"]
Next == c.t = "root" /\ \E j \in 1..Len(Trace) : c' = [t |-> "ev", j |-> j]
TraceSpec == Init /\ [][Next]_c

IcbrtEv(e) == /\ 0 <= e.n /\ e.n < 2 ^ 30 /\ 0 <= e.r /\ e.r < 1024
              /\ IsFloorCbrt(e.r, e.n)
              /\ e.r = Icbrt(e.n, 10, 30)
SatEv(e) == /\ Len(e.v) = 8 /\ Len(e.r) = 4
            /\ \A k \in 1..8 : 0 <= e.v[k] /\ e.v[k] <= 65535
            /\ IF \A k \in 5..8 : e.v[k] = 0
               THEN e.r = SubSeq(e.v, 1, 4)
               ELSE e.r = <<65535, 65535, 65535, 65535>>

EventsOK == c.t = "ev" =>
    LET e == Trace[c.j]
    IN /\ e.t \in {"icbrt", "sat"}
       /\ (e.t = "icbrt" => IcbrtEv(e))
       /\ (e.t = "sat" => SatEv(e))
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "ev" /\ c.j = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
