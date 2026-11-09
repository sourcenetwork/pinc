----------------------------- MODULE TraceReconcile -----------------------------
(***************************************************************************)
(* Trace validation of the set reconciliation: vinc-reconcile core.rs and  *)
(* session.rs.                                                             *)
(*                                                                         *)
(* The Rust test tests/trace_reconcile.rs runs seeded sessions of the real *)
(* Initiator and Responder (empty, equal, cold, tiny, dense, variable      *)
(* length and prefix items, differences of every size under the default    *)
(* and the smallest limits, chunked rounds, frames, narrowed splits, index *)
(* and size errors, a forced id collision, a lying answer to the final     *)
(* check, resets, and one changed message per session: a flipped bit, a    *)
(* cut, an extension, a dropped or doubled part, a changed tag or count)    *)
(* and records every handler call: who, which, the bytes delivered to it,  *)
(* and the step and bytes it wrote or the error it returned. A case line   *)
(* carries the two sets, both sides' limits, the set reference and the     *)
(* keyed hash tables, sorted by item (the real fingerprint of every item that can be       *)
(* hashed and the real id of every item of the sets), so the model runs    *)
(* with the real hash: the XOR of 16 byte values, bytewise.                *)
(*                                                                         *)
(* Every call must be the step the operators of ReconcileSess.tla (InitStart,*)
(* InitHandle, RespHandle, RespResume, the same operators the system       *)
(* model Reconcile.tla runs) compute, on the state the previous calls of   *)
(* that role left: the same step, the same bytes, or the same error. An    *)
(* error ends the session of the role that refused it (the wrappers of    *)
(* Initiator::handle and Responder::handle). A `reset` event is           *)
(* Responder::reset, and a finished session's `rep` line must be the       *)
(* initiator's report, item for item.                                      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds reconcile_tla.ndjson (the cases of reconcile.ndjson that fit TLC; the Lean replay takes them all).     *)
(* (reconcile_big.ndjson, the sessions that carry a varint of 2^31 or      *)
(* more, is replayed by the Lean replay only: TLC integers are 32 bits.)   *)
(*                                                                         *)
(* Lean counterpart: Vinc/TraceReconcile.lean (lake exe replay).           *)
(***************************************************************************)
EXTENDS ReconcileSess, Json, IOUtils

VARIABLES i, ini, rsp, cs
vars == <<i, ini, rsp, cs>>

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/reconcile_tla.ndjson")
Ev == Trace[i]

Rng(s) == {s[k] : k \in 1..Len(s)}
LimOfJ(l) == [maxItem |-> l[1], maxMessage |-> l[2], maxReport |-> l[3], maxRounds |-> l[4]]

Init ==
    /\ i = 1
    /\ ini = NewInitiator(LimOfJ(<<1, 100, 100, 100>>))
    /\ rsp = NewResponder(LimOfJ(<<1, 100, 100, 100>>))
    /\ cs = [none |-> TRUE]

CaseEv ==
    /\ Ev.e = "case"
    /\ cs' = [A |-> Ev.A, B |-> Ev.B, o |-> [H |-> Ev.H, idb |-> Ev.ID],
              ref |-> Ev.ref, lr |-> LimOfJ(Ev.limR)]
    /\ ini' = NewInitiator(LimOfJ(Ev.limI))
    /\ rsp' = NewResponder(LimOfJ(Ev.limR))

ResetEv ==
    /\ Ev.e = "reset"
    /\ rsp' = [rsp EXCEPT !.side = "fresh"]
    /\ UNCHANGED <<cs, ini>>

(* a refused message ends the session of the object that refused it (Initiator::handle, Responder::handle) *)
IniAfterErr(s) == IF s.phase \in {"open", "checking"} THEN [s EXCEPT !.phase = "idle"] ELSE s

(* the recorded outcome equals the model's: the step and the bytes, or the error *)
Agrees(r) ==
    IF Ev.ok THEN r.ok /\ r.v[1] = Ev.step /\ r.v[2] = Ev.out
    ELSE ~r.ok /\ r.err = Ev.err

IStartEv ==
    LET r == InitStart(cs.o, cs.A, ini, cs.ref)
    IN /\ Ev.who = "I" /\ Ev.call = "start"
       /\ IF Ev.ok THEN r.ok /\ r.v[2] = Ev.out /\ Ev.step = "send" ELSE ~r.ok /\ r.err = Ev.err
       /\ ini' = IF r.ok THEN r.v[1] ELSE ini
       /\ UNCHANGED <<cs, rsp>>

IHandleEv ==
    LET r == InitHandle(cs.o, cs.A, ini, Ev.in)
    IN /\ Ev.who = "I" /\ Ev.call = "handle"
       /\ Agrees(r)
       /\ ini' = IF r.ok THEN r.v[3] ELSE IniAfterErr(ini)
       /\ UNCHANGED <<cs, rsp>>

RHandleEv ==
    LET r == RespHandle(cs.o, cs.B, rsp, Ev.in)
    IN /\ Ev.who = "R" /\ Ev.call = "handle"
       /\ Agrees(r)
       /\ rsp' = IF r.ok THEN r.v[3] ELSE RespAfterErr(rsp, Ev.in)
       /\ UNCHANGED <<cs, ini>>

RResumeEv ==
    LET r == RespResume(cs.B, rsp)
    IN /\ Ev.who = "R" /\ Ev.call = "resume"
       /\ Agrees(r)
       /\ rsp' = IF r.ok THEN r.v[3] ELSE [rsp EXCEPT !.side = "done"]
       /\ UNCHANGED <<cs, ini>>

EvEv == /\ Ev.e = "ev" /\ (IStartEv \/ IHandleEv \/ RHandleEv \/ RResumeEv)

RepEv ==
    /\ Ev.e = "rep"
    /\ ini.phase = "done"
    /\ ini.core.here = Ev.here /\ ini.core.there = Ev.there
    /\ UNCHANGED <<cs, ini, rsp>>

Step ==
    /\ i <= Len(Trace)
    /\ Ev.t = "rc"
    /\ \/ CaseEv \/ ResetEv \/ EvEv \/ RepEv
    /\ i' = i + 1

Finished == i > Len(Trace) /\ UNCHANGED vars

TNext == Step \/ Finished

TraceSpec == Init /\ [][TNext]_vars

(* the model's safety facts hold on every recorded state *)
Inv ==
    /\ i <= Len(Trace) + 1
    /\ Len(ini.core.frames) <= MAX_NEST /\ Len(rsp.core.frames) <= MAX_NEST
=============================================================================
