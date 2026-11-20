--------------------------- MODULE TraceDialReport ---------------------------
(***************************************************************************)
(* Trace validation of the dial report against DialReport.tla, on the     *)
(* code's own timing: one tick is 500 ms, so the first resend delay is one *)
(* tick (handshake.rs FIRST, as `first()` gives it with a round trip of 0),*)
(* the round trip is 0 ticks (the shared world delivers at once), the      *)
(* early end comes after 4 unheard flights (EARLY_FLIGHTS) at 15 ticks     *)
(* (7.5 s), the handshake gives up past 60 ticks (CONNECT_TIMEOUT 30 s,    *)
(* the deadline one nanosecond past it fires at the next tick), and the    *)
(* doubling stays below Cap (32 ticks, CAP 16 s) within those 60 ticks.   *)
(*                                                                         *)
(* The test `tests/trace_dial_report.rs` (file dial_report.ndjson) runs A  *)
(* and a peer P in the shared world tests/facade_world.rs. It writes what  *)
(* it does and what A's application sees, one line each:                   *)
(*   tick                   the clock moved 500 ms and the world settled   *)
(*   stop, restart          P was dropped silently / built again on the    *)
(*                          same address and identity (only when A holds   *)
(*                          no session with it)                            *)
(*   cut, heal              A's datagrams to P are dropped from now / no   *)
(*                          longer                                         *)
(*   cache {allow}          A's cached access answer for P changed         *)
(*   dial                   A calls connect(P)                             *)
(*   answered {how}         "return": connect returned with the handshake  *)
(*                          done; "event": Event::Answered for a dial that *)
(*                          was handed over before (optimistic, or a       *)
(*                          sub-session over a held session)               *)
(*   closed {why}           the dial's connection closed: "early"          *)
(*                          (Unanswered) or "limit" (HandshakeTimeout)     *)
(*   failed                 connect returned the handshake timeout         *)
(*   done                   the test took the dial's result                *)
(*   drop                   A's session with P closed (by the test, or by  *)
(*                          the endpoint)                                  *)
(* What the application cannot see is a hidden step of the model, taken   *)
(* between two lines: a resend on the timer (Fire) and a reject of a       *)
(* ticket (Answer from a new incarnation). The network's choice to lose a  *)
(* flight is the test's: a flight sent while A is cut off is lost, any     *)
(* other is not. Every line the test writes of its own (all but answered,  *)
(* closed, failed, drop) comes when the world has settled, so it needs a   *)
(* model with nothing due (Quiet): no timer, answer, Limit or sub-session  *)
(* answer left to happen. A line the model cannot take deadlocks.          *)
(*                                                                         *)
(* Not traced: a thin node (the model caps its delay at CapThin, 16 ticks, *)
(* CAP_THIN 8 s, as the code does; the test never makes a thin node), the  *)
(* host's hold of resends (Hold), the first                                *)
(* fix and the planted bugs (all off), a second dial at once (over).       *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dial_report.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLES now, alive, inc, ticket, cached, held, d, steady, floor, limits, i, cut
mvars == <<now, alive, inc, ticket, cached, held, d, steady, floor, limits>>

M == INSTANCE DialReport WITH First <- 1, Rtt <- 0, Flights <- 4, Promise <- 15, Limit <- 60, Cap <- 32, CapThin <- 16,
                              MaxNow <- 100000,
                              MaxInc <- 64, Early <- TRUE, FixedBound <- 0, CountHeld <- FALSE,
                              HeardResets <- TRUE, EarlyOnThin <- FALSE, FloorEarly <- FALSE,
                              AnswerAtReport <- FALSE, AnswerEvent <- TRUE, AnswerAtKeys <- FALSE

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dial_report.ndjson")
Ev == Trace[i]
\* a flight sent now is lost exactly when A is cut off
L == IF cut THEN 1 ELSE 0

\* the hidden steps: a resend on the timer (not the early end), a reject from a new incarnation
Resend == M!Fire /\ d'.st = d.st /\ d'.lost = (IF d.hold THEN d.lost ELSE d.lost + L)
Reject == M!Answer /\ ~d'.answered /\ d'.lost = L
Hidden == (Resend \/ Reject) /\ UNCHANGED <<i, cut>>

\* nothing is due: the world has settled
Quiet == ~ENABLED (M!Fire \/ M!Answer \/ M!GiveUp \/ M!SubHeard)

Step ==
    CASE Ev.op = "tick" -> Quiet /\ M!Tick
      [] Ev.op = "stop" -> Quiet /\ M!Stop
      [] Ev.op = "restart" -> Quiet /\ ~held /\ M!Restart
      [] Ev.op \in {"cut", "heal"} -> Quiet /\ UNCHANGED mvars
      [] Ev.op = "cache" -> Quiet /\ M!Cache /\ cached' = Ev.allow
      [] Ev.op = "dial" -> Quiet /\ M!Start /\ ~d'.thin /\ ~d'.wait /\ (d'.sub \/ d'.lost = L)
      [] Ev.op = "answered" -> /\ \/ M!Answer /\ d'.answered
                                  \/ M!SubHeard
                               /\ d'.told_ans
                               /\ (Ev.how = "event") = d.told
      [] Ev.op = "closed" -> IF Ev.why = "early" THEN M!Fire /\ d'.why = "early"
                             ELSE M!GiveUp /\ d'.st = "closed"
      [] Ev.op = "failed" -> M!GiveUp /\ d'.st = "failed"
      [] Ev.op = "done" -> M!Done
      [] Ev.op = "drop" -> M!DropHeld
      [] OTHER -> FALSE

Init == M!Init /\ ticket = 0 /\ cached = FALSE /\ i = 1 /\ cut = FALSE
Next == \/ i <= Len(Trace) /\ Step /\ i' = i + 1
           /\ cut' = IF Ev.op = "cut" THEN TRUE ELSE IF Ev.op = "heal" THEN FALSE ELSE cut
        \/ i <= Len(Trace) /\ Hidden
        \* Finished: the trace was read to its end
        \/ i > Len(Trace) /\ UNCHANGED <<mvars, i, cut>>
TraceSpec == Init /\ [][Next]_<<mvars, i, cut>>

Inv == /\ M!TypeOK /\ M!NoLingering /\ M!ReachLive /\ M!ThinKeepsLimit /\ M!FloorOnLimit /\ M!SubAtOnce
       /\ M!AnsweredOnlyHeard /\ M!AnsweredWhenDone
=============================================================================
