------------------------------ MODULE TraceCoreState ------------------------------
(***************************************************************************)
(* Trace validation of the saved state of the endpoint (pinc-core          *)
(* state.rs).                                                              *)
(*                                                                         *)
(* The Rust test tests/trace_core_state.rs calls the real `restore_state`  *)
(* and `export_state` of an endpoint (three client ticket slots, the real  *)
(* bounds of 256 round trips and 256 prekey peers) with states of its own  *)
(* writer, cut, changed, extended and garbage bytes, and records for each  *)
(* call the bytes the endpoint exported before (`pre`), the input (`in`),  *)
(* the time, whether it was accepted, what the restore reported and the    *)
(* bytes the endpoint exports after (`post`); an `export` event records    *)
(* the buffer size and whether the export fitted. A trace is a behaviour   *)
(* of this spec when, for every event, the model of CoreState.tla          *)
(* (CoreStateOps.tla, the same operators) read `pre` as the tables the     *)
(* endpoint held, accepts exactly the inputs the code accepts and gives    *)
(* the counts the code reported, the tables after the restore encode to    *)
(* `post`, and a refused input leaves the tables as they were. An accepted *)
(* input must also be the encoding of the state it reads, and an export    *)
(* fits exactly when the buffer holds the state.                           *)
(*                                                                         *)
(* This check reads core_state.ndjson, whose numbers stay below 2^30 (TLC  *)
(* integers); core_state_wide.ndjson, with times and expiries up to        *)
(* 2^64 - 1, is replayed by Lean only.                                     *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR.                                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

O == INSTANCE CoreStateOps WITH CT <- 3, KR <- 256, EK <- 256, LAZY <- FALSE, LAXTAIL <- FALSE

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/core_state.ndjson")

\* the tables the endpoint held: what its own export reads as
Held(pre) == LET p == O!Parse(pre) IN p.ok /\ O!Enc(p.v) = pre

Ev(ev) ==
    LET p == O!Parse(ev.pre)
    IN /\ Held(ev.pre)
       /\ CASE ev.op = "export" ->
                 ev.ok = (ev.cap >= Len(ev.pre))
            [] ev.op = "restore" ->
                 LET r == O!Restore(p.v, ev.in, ev.now)
                     q == O!Parse(ev.in)
                 IN /\ r.ok = ev.ok /\ q.ok = ev.ok
                    /\ (q.ok => O!Enc(q.v) = ev.in)
                    /\ IF r.ok THEN r.res = ev.res /\ O!Enc(r.live) = ev.post
                       ELSE ev.res = <<>> /\ ev.post = ev.pre

(* Every event is an independent check, so the events are the states of one machine: the root state has one
   successor per block of 32 events and a block one per event, which TLC checks on all workers at once. *)
Init == c = [t |-> "root"]
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

\* every recorded verdict equals the model's
EventsOK == c.t = "event" => Ev(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
