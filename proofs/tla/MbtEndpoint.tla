----------------------------- MODULE MbtEndpoint -----------------------------
(***************************************************************************)
(* Model-based tests of how the endpoint (pinc-core endpoint.rs, rx.rs,    *)
(* timers.rs, commands.rs, events.rs) uses its tables: the slot table,     *)
(* the deadline heap (DeadlineHeap), the routing table of connection ids   *)
(* (demux), the table of held fragments (Orphans) and the event queue      *)
(* (EventRing). The tables themselves are modelled elsewhere (CoreTable,   *)
(* Heap, Orphan, Queue); this is their composition, for a Rust test to     *)
(* walk on a real endpoint.                                                *)
(*                                                                         *)
(* TLC writes the state graph (-dump dot,actionlabels,constrained); an     *)
(* edge is one call of the endpoint with its result as an argument, so a   *)
(* state has one successor per call (as in MbtHalfOpen.tla):               *)
(*   CallFlood(t, id, src, dec)  handle_datagram at t of a forged full     *)
(*        Initial for message id `id` from source `src`: dec 1 a session   *)
(*        is made (accept) and takes every held part of its message from   *)
(*        its source (replay_held, Orphans::take until none, which         *)
(*        expires the old ones first), 0 the slot table is full (accept    *)
(*        finds no slot, dropped_in), 2 the event queue is stalled         *)
(*        (stalled_in, nothing kept). Only a flight that reaches unrouted  *)
(*        is a call: one whose id no session holds, or one that starts a   *)
(*        message a fresh held part belongs to (starts_held_message, fewer *)
(*        than MAX_CANDIDATES = 4 holders); a flight for an id a session   *)
(*        holds otherwise is offered to that session's connection, whose   *)
(*        answer to a forgery is the transport's (not modelled);           *)
(*   CallPart(t, id, src, len, dec)  a later part (offset 2000 of 4095)    *)
(*        of message id from src, which no session holds: dec 1 held       *)
(*        (Orphans::hold, which expires the old ones first), 0 longer than *)
(*        the largest held part (refused before anything else, dropped_in),*)
(*        2 stalled;                                                       *)
(*   CallTimer(t)        handle_timeout at t: the held parts past their    *)
(*        life go first (Orphans::expire); then, unless the queue is       *)
(*        stalled, every session at or past the end of its life is freed   *)
(*        (run_timer, free_slot);                                          *)
(*   CallStale(t)        every session command, read_datagram,             *)
(*        session_taken and the Stats query on each id that names no live  *)
(*        session (freed, never made, out of the table): all refused,      *)
(*        nothing changes;                                                 *)
(*   CallStray(t, dec)   an empty datagram, one of 9217 bytes and a short   *)
(*        header for an id nobody holds: dropped (dec 1), the third held   *)
(*        back by the stall instead (dec 2);                               *)
(*   CallSelfDial(t, res) Connect to this node's own id: res 1 refused     *)
(*        with one ConnectFailed queued, 2 EventsPending (stalled), nothing*)
(*        queued;                                                          *)
(*   CallFill(t)         dials to itself until the queue stalls;           *)
(*   CallRead, CallDrain poll_event once, or until None.                   *)
(*                                                                         *)
(* State: now (model time, ms; monotone, the calls of a host clock); live, *)
(* the sessions as <<made at, id, src>> (the slot a session takes is the   *)
(* free list's choice and nothing here reads it); o, the held parts as     *)
(* OrphanOps keeps them, a part's key <<id, src>> standing for the code's  *)
(* (dcid, total, remote) (total is 4095 for all); q, the events queued:    *)
(* 0..QB, or S - 1 and S, which stand for 2K + 960 and 2K + 961, the last  *)
(* length before the queue stalls and the first at which it does           *)
(* (EventRing::stalled with no recoverable event queued: len + 2K + 64 >   *)
(* 4K + 1024).                                                             *)
(*                                                                         *)
(* A session lives LIFE (30 s, HALF_OPEN_LIFE, the base life: a forged     *)
(* Initial is never answered and the node is not thin) and one tick: it is *)
(* there at made + LIFE and gone at made + LIFE + 1 ms, the code's end     *)
(* being made + LIFE + 1 ns (handshake_end), which no millisecond time     *)
(* tells apart. TMAX stands for u64::MAX: the end saturates there, as the  *)
(* code's does. A held part lives OLIFE (ORPHAN_LIFE, 1 s); OMAX is the    *)
(* largest held (1 stands for 200 bytes, 2 for 1501 > ORPHAN_MAX).         *)
(*                                                                         *)
(* Properties (the code's documentation):                                  *)
(*  - TableBound: no table grows (endpoint.rs invariants);                 *)
(*  - Conserved: every held part is replayed, expired, evicted or waiting  *)
(*    (orphan.rs invariants);                                              *)
(*  - Handed: a part held for a message is handed to the session its      *)
(*    start makes and is not left behind for another (replay_held);        *)
(*  - QueueBound: the queue never holds more than its stall point plus     *)
(*    what one step adds (queue.rs invariants).                            *)
(* The Rust test checks after every call what the model cannot see: each  *)
(* session in the table has one deadline in the heap, no later than its    *)
(* end, and its routing entries; a free slot has neither; after a timer    *)
(* run below u64::MAX no deadline is at or before the call's time; the     *)
(* counters, the held parts and the queue are the model's.                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS K, LIFE, OLIFE, OMAX, TMAX, KEYS, IDS, FT, PT, CT, ST, XT, DT, LENS, HMAX, QB, S
VARIABLES now, live, o, q
vars == <<now, live, o, q>>

INSTANCE OrphanOps

\* the sources of the (id, source) pairs
SRCS == {key[2] : key \in KEYS}

\* the code's saturating clock, at model scale
Sat(x) == IF x >= TMAX THEN TMAX ELSE x
End(c) == Sat(c + LIFE + 1)
Stalled == q = S
Holders(id) == {s \in live : s[2] = id}
\* a part of message key held and not past its life at t (Orphans::holds)
Fresh(t, key) == \E k \in DOMAIN o.slots : o.slots[k] # None /\ o.slots[k][3] = key /\ ~Stale(o.slots[k], OLIFE, t)

\* replay_held: take the oldest part of the message until none is left (every take expires the old ones first)
RECURSIVE TakeAll(_, _, _)
TakeAll(o1, t, key) == LET r == Take(o1, OLIFE, t, key) IN IF r.out = None THEN r.o ELSE TakeAll(r.o, t, key)

FloodDec == IF Stalled THEN 2 ELSE IF Cardinality(live) >= K THEN 0 ELSE 1

Init == now = 0 /\ live = {} /\ o = Orphan0(4) /\ q = 0

CallFlood(t, id, src, dec) ==
    /\ t >= now
    /\ <<id, src>> \in KEYS
    /\ (Holders(id) = {} \/ (Cardinality(Holders(id)) < 4 /\ Fresh(t, <<id, src>>)))
    /\ dec = FloodDec
    /\ now' = t
    /\ live' = IF dec = 1 THEN live \cup {<<t, id, src>>} ELSE live
    /\ o' = IF dec = 1 THEN TakeAll(o, t, <<id, src>>) ELSE o
    /\ UNCHANGED q

CallPart(t, id, src, len, dec) ==
    /\ t >= now
    /\ <<id, src>> \in KEYS
    /\ Holders(id) = {}
    /\ dec = (IF Stalled THEN 2 ELSE IF len > OMAX THEN 0 ELSE 1)
    /\ now' = t
    /\ o' = IF dec = 1 THEN Hold(o, OMAX, OLIFE, t, <<id, src>>, 1, len, 0).o ELSE o
    /\ UNCHANGED <<live, q>>

CallTimer(t) ==
    /\ t >= now
    /\ now' = t
    /\ o' = Expire(o, OLIFE, t)
    /\ live' = IF Stalled THEN live ELSE {s \in live : t < End(s[1])}
    /\ UNCHANGED q

CallStale(t) == t >= now /\ now' = t /\ UNCHANGED <<live, o, q>>

CallStray(t, dec) == t >= now /\ dec = (IF Stalled THEN 2 ELSE 1) /\ now' = t /\ UNCHANGED <<live, o, q>>

CallSelfDial(t, res) ==
    /\ t >= now
    /\ res = (IF Stalled THEN 2 ELSE 1)
    /\ now' = t
    /\ q' = IF Stalled THEN q ELSE q + 1
    /\ UNCHANGED <<live, o>>

CallFill(t) == t >= now /\ q <= QB /\ now' = t /\ q' = S /\ UNCHANGED <<live, o>>

CallRead == q > 0 /\ q' = q - 1 /\ UNCHANGED <<now, live, o>>

CallDrain == q > 0 /\ q' = 0 /\ UNCHANGED <<now, live, o>>

Next == \/ \E t \in FT, id \in IDS, src \in SRCS, dec \in 0..2 : CallFlood(t, id, src, dec)
        \/ \E t \in PT, id \in IDS, src \in SRCS, len \in LENS, dec \in 0..2 : CallPart(t, id, src, len, dec)
        \/ \E t \in CT : CallTimer(t)
        \/ \E t \in ST : CallStale(t)
        \/ \E t \in XT, dec \in 1..2 : CallStray(t, dec)
        \/ \E t \in DT, res \in 1..2 : CallSelfDial(t, res)
        \/ \E t \in DT : CallFill(t)
        \/ CallRead
        \/ CallDrain
Spec == Init /\ [][Next]_vars

\* the graph's bound: parts held in all, and the queue near empty or near its stall point
Bound == o.held <= HMAX /\ (q <= QB \/ q >= S - 1)

TableBound == Cardinality(live) <= K
Conserved == o.held = o.replayed + o.expired + o.evicted + Waiting(o)
Handed == \A s \in live, k \in DOMAIN o.slots : o.slots[k] = None \/ o.slots[k][3] # <<s[2], s[3]>>
QueueBound == q <= S
Made == \A s \in live : s[1] <= now /\ <<s[2], s[3]>> \in KEYS
Complete == TableBound /\ Conserved /\ Handed /\ QueueBound /\ Made

\* witnesses: each says a state is never reached; its config checks that TLC reaches it
\* two sessions under one id, the second made by a part held for it, after a part was evicted
NoTwoHolders == ~(o.evicted >= 1 /\ o.replayed >= 2 /\ \E id \in IDS : Cardinality(Holders(id)) >= 2)
\* a session made at the largest time
NoMaxSession == ~(now = TMAX /\ live # {})
\* a session past its end kept by a stalled queue
NoOverdueStalled == ~(Stalled /\ \E s \in live : now >= End(s[1]))
=============================================================================
