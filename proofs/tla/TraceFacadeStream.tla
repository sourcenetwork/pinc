--------------------------- MODULE TraceFacadeStream ---------------------------
(***************************************************************************)
(* Trace validation of the stream and datagram handles of the facade:      *)
(* crates/pinc/src/stream.rs, conn.rs and engine/ops.rs, the operations of *)
(* FacadeStreamOps.tla.                                                    *)
(*                                                                         *)
(* The Rust test tests/trace_facade_stream.rs runs two real endpoints over *)
(* an in-memory wire and a virtual clock. The subject accepted one stream  *)
(* the peer opened (with `pw` chunks already sent) and calls write, finish, *)
(* reset, read, stop, recv_datagram, send_datagram, close and the drops;   *)
(* the peer sends chunks, finishes, resets, stops, sends datagrams, closes *)
(* and reads what the subject wrote. After every call the test delivers    *)
(* every packet and advances the clock until nothing is left to do, so     *)
(* each recorded call meets the transport state the calls before it made.  *)
(* Every recorded result must be the one the operations compute, from the  *)
(* state the records before it built. A call that would wait is polled     *)
(* once and dropped (r = 3): it must change nothing. A "held" record is    *)
(* the probe of whether the subject's stream still holds unread bytes, the *)
(* only way a call-level trace sees what a dropped RecvStream discarded.   *)
(*                                                                         *)
(* FILE names the ndjson under PINC_TRACE_DIR; DOC = FALSE checks the code *)
(* as written, DOC = TRUE the documented behaviour (TraceFacadeStreamDoc,  *)
(* the findings' scenarios, which pass since the facade fixes). The        *)
(* write side never runs out of room in the test (the windows are far      *)
(* larger than what is written), so room stays TRUE.                       *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR.                                                *)
(***************************************************************************)
EXTENDS FacadeStreamOps, TLC, Json, IOUtils

CONSTANT FILE

VARIABLES i, s
vars == <<i, s>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/" \o FILE)
Ev == Trace[i]
O == R(Ev.r, Ev.k, Ev.c, Ev.v)

\* a call of the subject: its recorded result is the computed one
Call(x) == x.o = O /\ s' = x.s
\* a change on the peer's side, allowed where the model allows it
Peer(ok, t) == ok /\ s' = t

Step ==
    CASE Ev.op = "init" -> s' = S0(Ev.pw)
      [] Ev.op = "write" -> ~s.dropS /\ Call(Write(s))
      [] Ev.op = "finish" -> ~s.dropS /\ Call(Finish(s))
      [] Ev.op = "reset" -> ~s.dropS /\ Call(Reset(s))
      [] Ev.op = "dsend" -> ~s.dropS /\ Call(DropSend(s))
      [] Ev.op = "read" -> ~s.dropR /\ Call(Read(s))
      [] Ev.op = "stop" -> ~s.dropR /\ ~s.hstop /\ Call(Stop(s))
      [] Ev.op = "drecv" -> ~s.dropR /\ Call(DropRecv(s))
      [] Ev.op = "rdg" -> Call(RecvDgram(s, Ev.fit))
      [] Ev.op = "sdg" -> Call(SendDgram(s, Ev.big))
      [] Ev.op = "close" -> Peer(s.live, Close(s, "local"))
      [] Ev.op = "pclose" -> Peer(s.live, Close(s, "peer"))
      [] Ev.op = "psend" -> Peer(s.live /\ ~s.pfin /\ ~s.preset, PeerSend(s))
      [] Ev.op = "pfin" -> Peer(s.live /\ ~s.pfin /\ ~s.preset, PeerFin(s))
      [] Ev.op = "preset" -> Peer(s.live /\ ~s.pfin /\ ~s.preset, PeerReset(s))
      [] Ev.op = "pstop" -> Peer(s.live /\ ~s.pstop, PeerStop(s))
      [] Ev.op = "pdg" -> Peer(s.live, PeerDgram(s))
      [] Ev.op = "pread" -> PeerRead(s) = O /\ s' = s
      \* the probe Connection::trace_held: whether the subject's stream holds unread bytes (a reset may drop them)
      [] Ev.op = "held" -> (~s.live \/ s.preset \/ Ev.v = IF s.rpos < s.pw THEN 1 ELSE 0) /\ s' = s
      [] OTHER -> FALSE

Init == i = 1 /\ s = S0(0)
TStep == /\ i <= Len(Trace) /\ Ev.t = "fst"
         /\ Step
         /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == TStep \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* on every recorded state: reads in order and once, datagrams in order, only the oldest dropped
Inv ==
    /\ s.got = [j \in 1..Len(s.got) |-> j]
    /\ \A j \in 1..(Len(s.dgot) - 1) : s.dgot[j] < s.dgot[j + 1]
    /\ \A x \in s.ddrop, y \in Range(s.dq) : x < y
    /\ Len(s.dq) <= DQ
=============================================================================
