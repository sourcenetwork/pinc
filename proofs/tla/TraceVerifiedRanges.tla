--------------------------- MODULE TraceVerifiedRanges ---------------------------
(***************************************************************************)
(* Trace validation of vinc-dag VerifiedRanges<N> and VerifiedRangesVec.   *)
(*                                                                         *)
(* The Rust test tests/trace_ranges.rs records, per insert, the request,   *)
(* whether it succeeded, the set after it (the public iter()) and the      *)
(* answers of covered_len, contains and contains_range. Each recorded      *)
(* step must be an Insert step of VerifiedRanges.tla with the capacity of  *)
(* its run, and the recorded answers must equal the specification's        *)
(* coverage semantics. A run starts from the empty set (Fresh is the Init  *)
(* of an independent execution); VecCap stands for "no capacity limit".    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds ranges.ndjson.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, RangeOps

VARIABLES items, req, res, i
vars == <<items, req, res, i>>

VR == INSTANCE VerifiedRanges WITH N <- 0, MaxOff <- 0

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/ranges.ndjson")

VecCap == 1000000
Cap(ev) == IF ev.kind = "vec" THEN VecCap ELSE ev.n

Init == i = 1 /\ VR!Init

Fresh ==
    /\ i <= Len(Trace)
    /\ Trace[i].seq = 0
    /\ items # <<>>
    /\ items' = <<>>
    /\ UNCHANGED <<req, res, i>>

Step ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
       IN /\ ev.seq = 0 => items = <<>>
          /\ VR!Insert(<<ev.s, ev.e>>, Cap(ev))
          /\ (res' = "ok") = ev.ok
          /\ items' = ev.items
          /\ Canonical(items') /\ Len(items') <= Cap(ev)
          /\ CoveredLen(items') = ev.cl
          /\ Covers(items', ev.x) = ev.cx
          /\ CoversRange(items', ev.cs, ev.ce) = ev.cr
          /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == Fresh \/ Step \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

(* the whole recorded trace is a behaviour of VerifiedRanges.tla *)
TraceAccepted == <>(i = Len(Trace) + 1)
=================================================================================
