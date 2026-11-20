---------------------------- MODULE TraceTableBytes ----------------------------
(***************************************************************************)
(* Trace validation of the block sizes of pinc-table: `bytes` and `new` of *)
(* the four tables, and `Storage::zeroed` (storage.rs).                    *)
(*                                                                         *)
(* The Rust test tests/trace_table_bytes.rs runs the real `Array::bytes`,  *)
(* `Ring::bytes`, `Pool::bytes`, `SortedSlab::bytes` and each `new` on the *)
(* capacities and record sizes of the boundary sets of TableBytes.tla and  *)
(* on seeded random ones, with blocks of 0, need - 1, need and need + 1    *)
(* bytes when the need is at most 1 MiB and of 0 and 64 bytes otherwise    *)
(* (no larger block is allocated), and `Storage::zeroed` on lengths that   *)
(* are refused (above isize::MAX) or small. Numbers are u64 written as     *)
(* four 16-bit limbs. Each result must equal the operator of               *)
(* TableBytes.tla on a 64-bit usize (the width of the machine the test     *)
(* runs on; the 32-bit width is checked by TLC only) and its exact         *)
(* specification.                                                          *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds table_bytes.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

B == INSTANCE TableBytes WITH c <- 0
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/table_bytes.ndjson")

Init == c = [t |-> "root"]

Ev(ev) ==
    CASE ev.t = "tbytes" ->
            LET x == [kind |-> ev.kind, n |-> U!FromLimbs(ev.n), r |-> U!FromLimbs(ev.r),
                      k |-> U!FromLimbs(ev.k), v |-> U!FromLimbs(ev.v)]
                len == U!FromLimbs(ev.len)
                want == [e |-> ev.res, need |-> IF ev.res = "storage" THEN U!FromLimbs(ev.need) ELSE U!Zero]
            IN /\ B!Bytes(x, 64) = U!FromLimbs(ev.bytes)
               /\ B!New(x, len, 64) = want
               /\ B!SpecNew(x, len, 64) = want
      [] ev.t = "tzero" -> B!Zeroed(U!FromLimbs(ev.len), 64) = ev.res

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

(* every recorded event equals the code's operator and the specification *)
EventsOK == c.t = "event" => Ev(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
