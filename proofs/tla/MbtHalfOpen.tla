----------------------------- MODULE MbtHalfOpen -----------------------------
(***************************************************************************)
(* Model-based tests of the endpoint's half-open cap (pinc-core rx.rs,     *)
(* timers.rs): the state graph of the admission and expiry operators of    *)
(* HalfOpenOps.tla at the code's real cap (256), for a Rust test to walk.  *)
(*                                                                         *)
(* TLC enumerates every state reachable by first flights and timer calls   *)
(* and writes the graph (-dump dot,actionlabels,constrained); an edge is   *)
(* one call of the endpoint with what it decides, as the label TLC gives   *)
(* it:                                                                     *)
(*   CallFlood(t, kind, len, dec) a first flight of message type kind and  *)
(*                                length len from a source and a message   *)
(*                                id the endpoint has not seen, at time t; *)
(*                                dec is the endpoint's record of its      *)
(*                                decision (trace.rs HalfOpen admitted):   *)
(*                                1 a session is made and counted, 0       *)
(*                                refused (under the floor of its type, or *)
(*                                at the cap), 3 dropped by the screening  *)
(*                                of a short Initial or a Hello (a forgery *)
(*                                that does not parse);                    *)
(*   CallTimer(t)                 handle_timeout at time t: every          *)
(*                                unauthenticated session at or past its   *)
(*                                end is freed.                            *)
(* As in MbtOrphan.tla the result is an argument, so that the graph has    *)
(* one node per state (Complete checks that each result is in its set).    *)
(* scripts/mbt.py turns the graph into paths from the empty endpoint that  *)
(* take every edge, and tests/mbt_halfopen.rs drives a real endpoint       *)
(* (cap 256, 300 slots) along each path, comparing the decision, the count *)
(* and the sessions held, by creation time, after every call.              *)
(*                                                                         *)
(* The cap is a plain constant of the code, not a parameter of a type, so  *)
(* the graph is at the real cap, MAX = 256, and what keeps it small is     *)
(* what the state keeps: the slot a session takes is the free list's       *)
(* choice and nothing the cap or the expiry reads depends on it, so a      *)
(* state is the number of sessions made at each time, g. The calls that    *)
(* need a peer that answers are not here: a session leaves the count by    *)
(* being established (a handshake with a real peer), a resumption is       *)
(* admitted at the cap on a Hello whose ticket opens (a real earlier       *)
(* session), and a close, a stalled event queue, a missing protocol and a  *)
(* full slot table are other calls; Establish, Release and the resume flag *)
(* of HalfOpenOps are covered by the trace check and HalfOpen.tla. Every   *)
(* flight here is a forgery from a new source, so none resumes and none    *)
(* finds a session under its id; a forged short Initial or Hello is        *)
(* dropped without a session once it meets the floor of its own type (the  *)
(* short Initial's and the Hello's differ) and refused under it, so only a *)
(* full Initial of its floor or more makes one.                            *)
(*                                                                         *)
(* A model length is scaled to the code's: the real length is the real     *)
(* floor of the type plus len - Floor(kind) (40 + len for a type with no   *)
(* floor), so a flight is below, at or above its floor as in the model.    *)
(* A session is there at the end of its life and gone one tick past it.    *)
(* Model time t is an origin plus t * (30 s / LIFE). A flood at time 0 may *)
(* fill the table to the cap; the flights at later times are bounded by    *)
(* GMAX per time, which keeps the graph small, and the flights of later    *)
(* times are what the timer expires first. Two configs:                    *)
(*  - MbtHalfOpen.cfg: flights at 0 and 1, timers at 0, 1 and 2, up to 3   *)
(*    sessions made at time 1: a timer at 1 spares the sessions of time 0  *)
(*    (the limit itself) and a timer at 2 frees them, sparing those of     *)
(*    time 1;                                                              *)
(*  - MbtHalfOpen_back.cfg: flights at 0, 1 and 2, timers at 0 to 3, one   *)
(*    session per later time: sessions made out of order, and a timer at   *)
(*    a time before a session's creation (a clock that stepped back).      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS MAX, LIFE, FULL, SHORT, HELLO, HT, CT, KINDS, LENS, GMAX
VARIABLES g, count
vars == <<g, count>>

INSTANCE HalfOpenOps

\* a session made at time t: unauthenticated, counted, living the base life (a forged first flight is never answered),
\* no deadline the model reads
Born(t) == [use |-> TRUE, created |-> t, unauth |-> TRUE, counted |-> TRUE, life |-> LIFE, dl |-> NoDl]
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
\* g is a sequence: the number of sessions made at time t is g[t + 1] (TLC prints a function on 1..n as a sequence)
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN f[x + 1] + Sum(f, S \ {x})

Init == g = [i \in 1..(Max(HT) + 1) |-> 0] /\ count = 0

\* what the endpoint records of a flight: a type that starts nothing is not decided on (0); under the floor of its own
\* type it is refused (0); a forgery of a short Initial or a Hello at its floor or more is dropped by the screening (3),
\* no session; a full Initial is admitted below the cap (1) and refused at it (0)
Dec(kind, len) ==
    IF ~First(kind) \/ len < Floor(kind, FULL, SHORT, HELLO) THEN 0
    ELSE IF Forged(kind) THEN 3
    ELSE IF Admit(count, kind, len, FALSE, MAX, FULL, SHORT, HELLO) THEN 1 ELSE 0
CallFlood(t, kind, len, dec) ==
    /\ dec = Dec(kind, len)
    /\ g' = IF dec = 1 THEN [g EXCEPT ![t + 1] = @ + 1] ELSE g
    /\ count' = IF dec = 1 THEN count + 1 ELSE count
CallTimer(t) ==
    LET h == [i \in 1..Len(g) |-> IF Expired(Born(i - 1), t) THEN 0 ELSE g[i]]
    IN g' = h /\ count' = Sum(h, HT)

Next == \/ \E t \in HT, kind \in KINDS, len \in LENS, dec \in 0..3 : CallFlood(t, kind, len, dec)
        \/ \E t \in CT : CallTimer(t)
Spec == Init /\ [][Next]_vars

Bound == \A t \in HT \ {0} : g[t + 1] <= GMAX
\* the count is the number of sessions, at most the cap; every call of a state in the graph has a result in the set
\* Next ranges over
Capped == count = Sum(g, HT) /\ count <= MAX
Complete == Capped /\ \A kind \in KINDS, len \in LENS : Dec(kind, len) \in 0..3
=============================================================================
