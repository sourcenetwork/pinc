--------------------------- MODULE MbtConnectFound ---------------------------
(***************************************************************************)
(* Model-based tests of the connect client's cache of verified lookup      *)
(* answers (pinc-connect client/conn.rs, `dns_answer`, `found`,            *)
(* `found_fresh`, `forget_found`): the state graph of the operators of     *)
(* ConnectFoundOps.tla at the code's ring of FOUND = 8 slots, for          *)
(* tests/mbt_connect_found.rs to walk with a real `Connectivity`. One      *)
(* action per step:                                                        *)
(*   CallAnswer(p, q, h)  the relay's DnsReply carrying the record of peer *)
(*                        p with sequence q and home h, at the clock;      *)
(*   CallForget(p)        forget_found of peer p;                          *)
(*   CallTick             the clock moves on by one tick (no call; the     *)
(*                        next answers are at the later time).             *)
(* None of them returns anything the test reads, so the state alone is     *)
(* the node of the graph. After every step the test compares, for every    *)
(* peer, `found` with `seen` and `found_fresh` at every time 0 .. TMAX +   *)
(* TTL with `fresh` (both derived from the cache, so they add no state).   *)
(*                                                                         *)
(* The ring is kept turned so that the code's `found_next` is slot 1       *)
(* (Rot after an answer that moves it): the test cannot see a slot's index *)
(* (only `found` and `found_fresh`, which do not depend on it while a peer *)
(* has one slot, Complete), and the turned ring has N times fewer states.  *)
(* The graph is finite: no constraint.                                     *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS N, PEERS, SEQS, HOMES, TTL, TMAX

VARIABLES c, clock, seen, fresh
vars == <<c, clock, seen, fresh>>

INSTANCE ConnectFoundOps

Seen(cc) == [p \in PEERS |-> Found(cc, p)]
Fresh(cc) == [p \in PEERS |-> [i \in 1..(TMAX + TTL + 1) |-> FoundFresh(cc, i - 1, p).e]]

Init == c = C0 /\ clock = 0 /\ seen = Seen(C0) /\ fresh = Fresh(C0)

Set(cc) == c' = cc /\ seen' = Seen(cc) /\ fresh' = Fresh(cc)

CallAnswer(p, q, h) == Set(Rot(Answer(c, p, q, h, clock))) /\ UNCHANGED clock
CallForget(p) == Set(Forget(c, p)) /\ UNCHANGED clock
CallTick == clock < TMAX /\ clock' = clock + 1 /\ UNCHANGED <<c, seen, fresh>>

Next ==
    \/ \E p \in PEERS, q \in SEQS, h \in HOMES : CallAnswer(p, q, h)
    \/ \E p \in PEERS : CallForget(p)
    \/ CallTick
Spec == Init /\ [][Next]_vars

\* the turned ring is the code's up to the index of a slot: one slot per peer and found_next at slot 1
Complete == /\ c.next = 0
            /\ \A p \in PEERS : Cardinality(Held(c, p)) <= 1
=============================================================================
