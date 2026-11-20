------------------------------ MODULE TraceLazy ------------------------------
(***************************************************************************)
(* Trace validation of pinc-transport stream/lazy.rs (Lazy<T, N>, with     *)
(* `alloc`).                                                               *)
(*                                                                         *)
(* The Rust test tests/trace_lazy.rs drives real tables through LazyProbe  *)
(* (cargo feature `trace`) at N = 1, 5 and 64: reads, writes through       *)
(* `get_mut`, `written_mut` and `prefix_mut` inside the written prefix, at *)
(* its end, past it and from N on, and `clear`. Every call must be the     *)
(* step the operators of LazyOps.tla compute, with the answer the code     *)
(* gave; after every call the written prefix and the N entries `iter`     *)
(* reads must be the model's, and the reserved room (capacity and address  *)
(* of the vector) must be the one the table was made with.                 *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds lazy.ndjson.          *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
VARIABLES i, w, n, b
vars == <<i, w, n, b>>
INSTANCE LazyOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/lazy.ndjson")
Ev0 == Trace[i]

\* the recorded table after the call: its written prefix, the N entries it reads as, and its room unchanged
Same(x, nn, bb, v) == /\ x = v.w
                      /\ LView(x, nn, bb) = v.all
                      /\ v.room = TRUE

InitEv == /\ Ev0.op = "init" /\ n' = Ev0.n /\ b' = Ev0.blank /\ w' = LNew
          /\ Same(w', Ev0.n, Ev0.blank, Ev0.v)
GetEv == /\ Ev0.op = "get"
         /\ LGet(w, n, b, Ev0.i) = [ok |-> Ev0.ok, v |-> IF Ev0.ok THEN Ev0.val ELSE b]
         /\ w' = w /\ UNCHANGED <<n, b>> /\ Same(w', n, b, Ev0.v)
SetEv == LET r == LSetMut(w, n, b, Ev0.i, Ev0.val)
         IN /\ Ev0.op = "set" /\ r.ok = Ev0.ok /\ w' = r.w
            /\ UNCHANGED <<n, b>> /\ Same(w', n, b, Ev0.v)
WSetEv == LET r == LSetWritten(w, Ev0.i, Ev0.val)
          IN /\ Ev0.op = "wset" /\ r.ok = Ev0.ok /\ w' = r.w
             /\ UNCHANGED <<n, b>> /\ Same(w', n, b, Ev0.v)
PSetEv == LET r == LSetPrefix(w, Ev0.k, Ev0.val)
          IN /\ Ev0.op = "pset" /\ r.ok = Ev0.ok /\ w' = r.w
             /\ UNCHANGED <<n, b>> /\ Same(w', n, b, Ev0.v)
ClearEv == /\ Ev0.op = "clear" /\ w' = LClear /\ UNCHANGED <<n, b>> /\ Same(w', n, b, Ev0.v)

Init == i = 1 /\ w = LNew /\ n = 1 /\ b = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "lazy"
        /\ (InitEv \/ GetEv \/ SetEv \/ WSetEv \/ PSetEv \/ ClearEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the written prefix never passes N
Inv == Len(w) <= n
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
