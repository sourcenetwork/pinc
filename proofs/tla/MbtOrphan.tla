------------------------------ MODULE MbtOrphan ------------------------------
(***************************************************************************)
(* Model-based tests of the endpoint's table of held first-flight          *)
(* fragments (pinc-core orphan.rs): the state graph of the operators of    *)
(* OrphanOps.tla at the size of the real table, for a Rust test to walk.   *)
(*                                                                         *)
(* TLC enumerates every state reachable by hold, take and expire and       *)
(* writes the graph (-dump dot,actionlabels,constrained): a node is the    *)
(* whole table, entries and counters, and an edge is one call with what it *)
(* returns, as the label TLC gives it, the action and its arguments:       *)
(*   CallHold(t, key, len, ok)   hold a datagram of len bytes of the       *)
(*                               message key at time t; ok is the result;  *)
(*   CallTake(t, key, out)       take for the message key at time t; out   *)
(*                               is <<>> or <<loc, len, tag>> of the       *)
(*                               datagram given out;                       *)
(*   CallExpire(t)               let go of the old ones at time t.         *)
(* The result is an argument so that the graph has one node per table:     *)
(* TLC makes one action per value of every bounded \E of Next, and only    *)
(* the value the operators compute has a successor (Complete checks that   *)
(* each result is in its set, so no call is lost). scripts/mbt.py turns    *)
(* the graph into paths from the empty table that take every edge, and     *)
(* tests/mbt_orphan.rs drives a real table (OrphanProbe) along each path,  *)
(* comparing the result and the whole table after every call.              *)
(*                                                                         *)
(* N is the code's ORPHANS (4): the test drives the real table. A          *)
(* datagram's local address is the time it arrived (loc = t) and its bytes *)
(* carry its place in the order of arrival (tag = order), so the test can  *)
(* tell which one a take gave out. The test scales the rest: model time t  *)
(* is an origin plus t * (ORPHAN_LIFE / LIFE), a length of at most MAX one *)
(* of at most ORPHAN_MAX bytes and MAX + 1 one of more, and key 2 differs  *)
(* from key 1 in one of the id, the message length or the address.         *)
(* Datagrams arrive at the times HT, the other calls come at the times CT; *)
(* with LIFE = 1 and times 0..2 a datagram is seen at its arrival, one     *)
(* step later (the last moment it is fresh), two steps later (old) and     *)
(* from before its arrival (a clock that stepped back).                    *)
(* Held bounds the graph: the states past it are its leaves, reached and   *)
(* compared but not left. Two configs, since every state of the larger     *)
(* bounds is too many to walk:                                             *)
(*  - MbtOrphan.cfg: arrivals at 0 and 2, up to 6 datagrams held in all:   *)
(*    a full table evicts twice, the second time from an entry that is not *)
(*    the first (5434 states inside the bound, 92378 edges);               *)
(*  - MbtOrphan_edge.cfg: arrivals at 0, 1 and 2, up to 5 held in all: a   *)
(*    hold one step after a held datagram keeps it (and evicts from a full *)
(*    table), two steps after reuses its entry (4741 states inside the     *)
(*    bound, 99561 edges).                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS N, MAX, LIFE, HT, CT, KEYS, LENS, HMAX
VARIABLES o
vars == <<o>>

INSTANCE OrphanOps

Init == o = Orphan0(N)

HoldRes(t, key, len) == Hold(o, MAX, LIFE, t, key, t, len, o.order)
TakeRes(t, key) == Take(o, LIFE, t, key)
Out(x) == IF x.out = None THEN <<>> ELSE <<x.out[4], x.out[5], x.out[6]>>
Outs == {<<>>} \cup {<<l, n, g>> : l \in HT, n \in LENS, g \in 0..HMAX}

CallHold(t, key, len, ok) == LET x == HoldRes(t, key, len) IN ok = x.ok /\ o' = x.o
CallTake(t, key, out) == LET x == TakeRes(t, key) IN out = Out(x) /\ o' = x.o
CallExpire(t) == o' = Expire(o, LIFE, t)

Next == \/ \E t \in HT, key \in KEYS, len \in LENS, ok \in BOOLEAN : CallHold(t, key, len, ok)
        \/ \E t \in CT, key \in KEYS, out \in Outs : CallTake(t, key, out)
        \/ \E t \in CT : CallExpire(t)
Spec == Init /\ [][Next]_vars

Held == o.held <= HMAX
\* every call of a state in the graph has its result in the set Next ranges over
Complete == \A t \in CT, key \in KEYS : Out(TakeRes(t, key)) \in Outs
=============================================================================
