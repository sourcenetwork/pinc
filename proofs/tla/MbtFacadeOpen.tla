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
(*                      came back; w: the opens whose waker runs: an      *)
(*                      open woken and not polled since is not armed, so  *)
(*                      a second wake does not run its waker              *)
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
\* w: the opens whose waker runs: an open woken and not polled since is not armed, so a second wake does not run
\* its waker. They are named as the model's actions name them. Every
\* parameter is fixed on the state before the call, ahead of the model's step: TLC (-dump constrained) writes a
\* successor that a conjunct after the step rejects as a state past the constraint, so a guessed r or w checked after
\* M!Ask would put a rejected state beside every call. The step still checks r: were AskAnswer or PollAnswer not the
\* model's answer, the rejected states would be back and scripts/mbt.py would fail on the count of states.
AskAnswer == IF waits # <<>> \/ free = 0 THEN "wait" ELSE "open"
PollAnswer(o) == IF waits # <<>> /\ waits[1] = o /\ free > 0 THEN "open" ELSE "wait"
CallAsk(o, r) == r = AskAnswer /\ M!Ask(o) /\ st'[o] = r
CallPoll(o, r, w) == r = PollAnswer(o) /\ w = (IF r = "open" THEN M!Next2(waits) \ woken ELSE {}) /\ M!Poll(o) /\ st'[o] = r
CallRelease(o, w) == w = (IF waits # <<>> /\ waits[1] \notin woken THEN {waits[1]} ELSE {}) /\ M!Release(o)
CallCancel(o, w) == w = (IF waits # <<>> /\ waits[1] = o THEN M!Next2(waits) \ woken ELSE {}) /\ M!Cancel(o)

Next == \/ \E o \in 1..4, r \in {"open", "wait"} : CallAsk(o, r)
        \/ \E o \in 1..4, r \in {"open", "wait"}, w \in SUBSET (1..4) : CallPoll(o, r, w)
        \/ \E o \in 1..4, w \in SUBSET (1..4) : CallRelease(o, w) \/ CallCancel(o, w)
Spec == Init /\ [][Next]_vars

Inv == M!TypeOK /\ M!PlacesKept /\ M!NoOvertake /\ M!NoStall /\ M!ListInOrder
=============================================================================
