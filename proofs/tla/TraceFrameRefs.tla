---------------------------- MODULE TraceFrameRefs ----------------------------
(***************************************************************************)
(* Trace validation of pinc-transport recovery/frame_ref.rs (FrameRefs).   *)
(*                                                                         *)
(* The Rust test tests/trace_frame_refs.rs pushes real descriptors (stream *)
(* and control, with ids, offsets and lengths at their extremes, and the   *)
(* descriptor every place holds at the start) onto fresh lists, past the   *)
(* point they are full. Each descriptor is written as a JSON array:        *)
(* ["s", id limbs, offset limbs, len limbs, fin] or ["c", kind, id limbs], *)
(* u64 as 4 and u32 as 2 little-endian 16-bit limbs. Every push must be    *)
(* the step of FrameRefsOps.tla, with the answer the code gave, and after  *)
(* it `as_slice`, `iter`, `into_iter`, `len` and `is_empty` must read the  *)
(* model's list.                                                           *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds frame_refs.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, r, max
vars == <<i, r, max>>
INSTANCE FrameRefsOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/frame_refs.ndjson")
Ev0 == Trace[i]

Same(x, v) == /\ FSlice(x) = v.slice /\ FSlice(x) = v.iter /\ FSlice(x) = v.into
              /\ x.len = v.len /\ (x.len = 0) = v.empty

InitEv == /\ Ev0.op = "init" /\ max' = Ev0.max /\ r' = FNew(Ev0.max, Ev0.d0) /\ Same(r', Ev0.v)
PushEv == LET p == FPush(r, max, Ev0.f)
          IN /\ Ev0.op = "push" /\ p.ok = Ev0.ok /\ r' = p.r /\ UNCHANGED max /\ Same(r', Ev0.v)

Init == i = 1 /\ r = [items |-> <<>>, len |-> 0] /\ max = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "frame_refs" /\ (InitEv \/ PushEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == r.len <= max
=============================================================================
