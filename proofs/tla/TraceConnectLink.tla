---------------------------- MODULE TraceConnectLink ----------------------------
(***************************************************************************)
(* Trace validation of the client carrier state machine: pinc-connect      *)
(* client/link.rs.                                                          *)
(*                                                                         *)
(* The Rust test tests/trace_connect_link.rs drives the real Link with     *)
(* every method, at instants around every rule constant, in every context  *)
(* of the node, and records each call with its answer and the link and the *)
(* shared state read back after it. Every event must be the step the       *)
(* operators of ConnectLinkOps.tla compute: the same answer and the same   *)
(* state. Times are microseconds.                                           *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_link.ndjson.  *)
(***************************************************************************)
EXTENDS ConnectLinkOps, Json, IOUtils, TraceEnd

VARIABLES i, L, S
vars == <<i, L, S>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_link.ndjson")
Ev == Trace[i]

Init == i = 1 /\ L = NewLink /\ S = NewShared

Same(r) == /\ Ev.res = r.act /\ Ev.L = r.L /\ Ev.S = r.S /\ L' = r.L /\ S' = r.S /\ i' = i + 1
Only(newL, newS, res) == /\ Ev.res = res /\ Ev.L = newL /\ Ev.S = newS /\ L' = newL /\ S' = newS /\ i' = i + 1

NewE == /\ Ev.t = "lknew" /\ L' = NewLink /\ S' = Ev.S /\ i' = i + 1
SetE == /\ Ev.t = "lkset" /\ S' = Ev.S /\ UNCHANGED L /\ i' = i + 1

CallE ==
    /\ Ev.t = "lk"
    /\ LET c == Ev.ctx IN
       CASE Ev.c = "want_dial" -> Same(WantDial(L, S, Ev.now, c))
         [] Ev.c = "opened" -> LET o == Opened(L, Ev.now) IN Only(o.L, S, o.was)
         [] Ev.c = "closed" -> Only(Closed(L, Ev.now), S, "none")
         [] Ev.c = "heard" -> Only(Heard(L, Ev.now), S, "none")
         [] Ev.c = "wrote" -> Only(Wrote(L, Ev.now), S, "none")
         [] Ev.c = "pulse" -> LET p == Pulse(L, Ev.now, c) IN Only(p.L, S, p.p)
         [] Ev.c = "reset" -> Only(Reset(L, Ev.now), S, "close")
         [] Ev.c = "before_send" -> LET b == BeforeSend(L, S, Ev.now, c) IN Only(b.L, S, b.act)
         [] Ev.c = "check" -> LET k == Check(L, Ev.now, c, Ev.ridden) IN Only(k.L, S, k.act)
         [] Ev.c = "tick" -> Same(Tick(L, S, Ev.now, c))
         [] Ev.c = "deadline" -> Only(L, S, NextDeadline(L, S, Ev.now, c))

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (NewE \/ SetE \/ CallE)) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of ConnectLinkOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
Inv == TRUE
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
