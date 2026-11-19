------------------------------- MODULE TraceExtIn -------------------------------
(***************************************************************************)
(* Trace validation of the ring of extension frames held for the           *)
(* application: pinc-core ext_in.rs (ExtRing).                             *)
(*                                                                         *)
(* The Rust test tests/trace_ext_in.rs drives real rings (built with the      *)
(* cargo feature `trace`) with seeded calls: puts of frames of a few       *)
(* sessions and types with bodies of every length that matters (empty,     *)
(* the limit of 1200 bytes, one over it, far over it), takes with buffers  *)
(* too small, just right and large, in mixes that keep the ring short,     *)
(* fill it, drop its oldest frame and take the head round it. Every call   *)
(* must be the step the operators of ExtInOps.tla compute, with the result   *)
(* the code returned (for a put: kept or not, and how many frames the ring *)
(* gave up for it); the head, the length and the frames held (session,     *)
(* type, length and the first byte of the body, oldest first) recorded     *)
(* after every call must be the model's. The model's frame carries the     *)
(* first byte in the slot of its place in the order of puts.               *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds ext_in.ndjson.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, r, cap, mx
vars == <<i, r, cap, mx>>
INSTANCE ExtInOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/ext_in.ndjson")
Ev0 == Trace[i]

\* a frame as the test records it: session, type, length, first byte; the model's: first byte, session, type, length
It(f) == <<f[4], f[1], f[2], f[3]>>
Rec(it) == <<it[2], it[3], it[4], it[1]>>

Same(x) ==
    /\ x.head = Ev0.v.head /\ x.len = Ev0.v.len
    /\ [k \in 1..x.len |-> Rec(x.q[k])] = Ev0.v.q

InitEv == /\ Ev0.op = "init" /\ cap' = Ev0.n /\ mx' = Ev0.mx /\ r' = Ring0 /\ Same(r')
PutEv == LET x == EPut(r, cap, mx, It(Ev0.f), FALSE)
         IN /\ Ev0.op = "put" /\ x.ok = Ev0.ok /\ x.gave = Ev0.gave
            /\ r' = x.r /\ Same(r') /\ UNCHANGED <<cap, mx>>
TakeEv == LET x == ETake(r, cap, Ev0.oc)
          IN /\ Ev0.op = "take" /\ x.res = Ev0.res
             /\ (x.res = "ok" => Rec(x.out) = Ev0.out)
             /\ (x.res = "err" => x.out = Ev0.need)
             /\ r' = x.r /\ Same(r') /\ UNCHANGED <<cap, mx>>

Init == i = 1 /\ r = Ring0 /\ cap = 1 /\ mx = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "cox"
        /\ (InitEv \/ PutEv \/ TakeEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the ring never grows, and holds no body over the limit
Inv == r.len \in 0..cap /\ \A k \in 1..r.len : r.q[k][4] <= mx
=============================================================================
