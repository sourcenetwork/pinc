--------------------------- MODULE MbtConnectFound ---------------------------
(***************************************************************************)
(* Model-based tests of the connect client's cache of verified lookup      *)
(* answers (pinc-connect client/conn.rs, `dns_answer`, `found`,            *)
(* `found_fresh`, `forget_found`): the state graph of the operators of     *)
(* ConnectFoundOps.tla (the rule of the code, Answer) at the code's ring   *)
(* of FOUND = 8 slots, for tests/mbt_connect_found.rs to walk with a real  *)
(* `Connectivity`.                                                         *)
(*                                                                         *)
(* Peers 1 .. NP are the peers the steps act on; peers NP + 1 .. NP + FILL *)
(* are fillers, answered once each in that order (sequence 1, home 1, time *)
(* 0) before the first step, so they hold slots 1 .. FILL; they are never  *)
(* answered or forgotten again, only evicted. With FILL = N - 2 the ring   *)
(* is full once two peers are held: then a forget and an answer for the   *)
(* third peer fill the emptied slot (the case the lowest-empty-slot rule   *)
(* fixed), and an answer for the third peer while the two are held evicts  *)
(* the filler at `next`.                                                   *)
(*                                                                         *)
(* One action per step:                                                    *)
(*   CallAnswer(p, q, h)  the relay's DnsReply carrying the record of peer *)
(*                        p with sequence q and home h, at the clock;      *)
(*   CallForget(p)        forget_found of peer p;                          *)
(*   CallTick             the clock moves on by one tick (no call; the     *)
(*                        next answers are at the later time).             *)
(* None of them returns anything the test reads, so the state alone is     *)
(* the node of the graph. After every step the test compares, for every    *)
(* peer and filler, `found` with `seen` and `found_fresh` at every time    *)
(* 0 .. TMAX + TTL with `fresh` (both derived from the cache, so they add  *)
(* no state). The ring itself is not compared: a slot's index is not       *)
(* visible through the API. The graph is finite: no constraint.            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS N, NP, FILL, SEQS, HOMES, TTL, TMAX

ASSUME FILL <= N /\ 1 \in SEQS /\ 1 \in HOMES

VARIABLES c, clock, seen, fresh
vars == <<c, clock, seen, fresh>>

INSTANCE ConnectFoundOps

PEERS == 1..NP
ALL == 1..(NP + FILL)

Seen(cc) == [p \in ALL |-> Found(cc, p)]
(* found_fresh at every time 0 .. TMAX + TTL, from what found gives (FoundFresh(cc, i - 1, p).e) *)
Fresh(s) == [p \in ALL |-> [i \in 1..(TMAX + TTL + 1) |-> FreshOf(s[p], i - 1).e]]

(* the fillers answered in order on an empty cache at time 0 *)
Filled == [ring |-> [k \in Slots |-> IF k <= FILL THEN Ent(NP + k, 1, 1, 0) ELSE NONE], next |-> 0]

Init == c = Filled /\ clock = 0 /\ seen = Seen(Filled) /\ fresh = Fresh(Seen(Filled))

Set(cc) == LET s == Seen(cc) IN c' = cc /\ seen' = s /\ fresh' = Fresh(s)

CallAnswer(p, q, h) == Set(Answer(c, p, q, h, clock)) /\ UNCHANGED clock
CallForget(p) == Set(Forget(c, p)) /\ UNCHANGED clock
CallTick == clock < TMAX /\ clock' = clock + 1 /\ UNCHANGED <<c, seen, fresh>>

Next ==
    \/ \E p \in PEERS, q \in SEQS, h \in HOMES : CallAnswer(p, q, h)
    \/ \E p \in PEERS : CallForget(p)
    \/ CallTick
Spec == Init /\ [][Next]_vars

\* Filled is what Answer makes of the fillers on an empty cache, and every peer has at most one slot
FillAnswers[k \in 0..FILL] == IF k = 0 THEN C0 ELSE Answer(FillAnswers[k - 1], NP + k, 1, 1, 0)
Complete == /\ Filled = FillAnswers[FILL]
            /\ \A p \in ALL : Cardinality(Held(c, p)) <= 1

\* witnesses that the graph has the two cases of the ring: a full ring but for the slot after the fillers (its peer
\* was forgotten, so the next answer for a new peer fills it), and a filler evicted at the next index
NotHole == Empty(c) # {FILL + 1}
FillersKept == \A f \in (NP + 1)..(NP + FILL) : Found(c, f).e
=============================================================================
