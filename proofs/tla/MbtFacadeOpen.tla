---------------------------- MODULE MbtFacadeOpen ----------------------------
(***************************************************************************)
(* Model-based test cases for the facade's open queue (FacadeOpen.tla, the *)
(* code as built: Fifo and Handoff TRUE), four opens and a peer that lets   *)
(* the session hold two streams. One action per call the test makes, with *)
(* the call's arguments and what it returns as parameters, so TLC's state   *)
(* graph (scripts/mbt.py) has one edge per call and its result:            *)
(*   CallAsk(o, r)      the first poll of open o's `open_bi` future:       *)
(*                      r = "open" (Ready) or "wait" (Pending)             *)
(*   CallPoll(o, r, w)  a poll of a woken open o, with its answer and the  *)
(*                      opens it wakes (the hand-off)                      *)
(*   CallRelease(o, w)  open o's stream is finished and the peer's credit  *)
(*                      came back; w: the opens whose waker ran            *)
(*   CallCancel(o, w)   open o's future is dropped while it waits; w as    *)
(*                      above                                              *)
(* Opens are the integers 1..4 (scripts/mbt.py reads no model values).     *)
(* The test is tests/mbt_facade_open.rs; it compares `st` and `woken` of   *)
(* each step's state with what it observes. The list order, the clock and  *)
(* `overtaken` are the model's own; the properties of FacadeOpen.cfg are   *)
(* checked on every state of this graph.                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLES st, waits, woken, free, clock, askedAt, overtaken
vars == <<st, waits, woken, free, clock, askedAt, overtaken>>

M == INSTANCE FacadeOpen WITH Opens <- 1..4, Places <- 2, Fifo <- TRUE, Handoff <- TRUE

Init == M!Init
\* w: the opens the call wakes (their waker runs, already woken or not), as the model's actions name them
CallAsk(o, r) == M!Ask(o) /\ st'[o] = r
CallPoll(o, r, w) == M!Poll(o) /\ st'[o] = r /\ w = (IF r = "open" THEN M!Next2(waits) ELSE {})
CallRelease(o, w) == M!Release(o) /\ w = (IF waits # <<>> THEN {waits[1]} ELSE {})
CallCancel(o, w) == M!Cancel(o) /\ w = (IF waits # <<>> /\ waits[1] = o THEN M!Next2(waits) ELSE {})

Next == \/ \E o \in 1..4, r \in {"open", "wait"} : CallAsk(o, r)
        \/ \E o \in 1..4, r \in {"open", "wait"}, w \in SUBSET (1..4) : CallPoll(o, r, w)
        \/ \E o \in 1..4, w \in SUBSET (1..4) : CallRelease(o, w) \/ CallCancel(o, w)
Spec == Init /\ [][Next]_vars

Inv == M!TypeOK /\ M!PlacesKept /\ M!NoOvertake /\ M!NoStall /\ M!ListInOrder
=============================================================================
