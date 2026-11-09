------------------------------ MODULE BroadcastLogOps ------------------------------
(***************************************************************************)
(* The hub log of vinc-broadcast log.rs (HubLog), step for step: a byte    *)
(* ring that holds the heads and bodies, the entry queue, the index from a *)
(* message id to its sequence number, and the base sequence number. A      *)
(* message is Ring cells: the model writes the id into each cell its bytes *)
(* occupy (Track; a model that does not read the bytes turns it off), so a lookup that returned another message's bytes, or bytes     *)
(* overwritten by a later message, is a violation. Sizes are small         *)
(* parameters (Ring is log_bytes, Cap is LOG_CAP, Window is LOG_WINDOW);   *)
(* time is a counter; an entry keeps the arrival time `at` and the wall     *)
(* clock `wall` the hub stamped it with (BroadcastLog uses wall = at).     *)
(* The operators are shared:      *)
(* BroadcastLog, BroadcastNode and TraceBroadcast use this module.         *)
(*                                                                         *)
(* A subtraction that would underflow (`used -= cost`) and an index slot   *)
(* that is not where the queue says stop TLC with an assertion.            *)
(*                                                                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Ring, Cap, Window, Mids, Track

None == -1
EmptyLog == [entries |-> <<>>, index |-> [m \in Mids |-> None], base |-> 0, cells |-> IF Track THEN [c \in 0..(Ring - 1) |-> 0] ELSE <<>>,
             wpos |-> 0, used |-> 0]

Sub(a, b) == IF a >= b THEN a - b ELSE 0          \* saturating_sub
Contains(L, mid) == L.index[mid] # None

\* log.rs entry(): the entry the index points at
EntryOf(L, mid) == IF L.index[mid] = None THEN None
                   ELSE IF L.index[mid] < L.base THEN None
                   ELSE IF L.index[mid] - L.base >= Len(L.entries) THEN None
                   ELSE L.index[mid] - L.base + 1

\* the bytes of a logged message (the cells of its entry)
Get(L, mid) == LET i == EntryOf(L, mid)
               IN IF i = None THEN <<>>
                  ELSE LET e == L.entries[i] IN [k \in 0..(e.len - 1) |-> L.cells[e.off + k]]

\* log.rs pop(): the oldest entry leaves
Pop(L) ==
    LET e == Head(L.entries)
        idx == IF L.index[e.mid] = L.base THEN [L.index EXCEPT ![e.mid] = None] ELSE L.index
        u == IF Assert(L.used >= e.cost, "used underflow") THEN L.used - e.cost ELSE 0
        rest == Tail(L.entries)
    IN [L EXCEPT !.entries = rest, !.index = idx, !.base = L.base + 1,
                 !.used = IF rest = <<>> THEN 0 ELSE u, !.wpos = IF rest = <<>> THEN 0 ELSE L.wpos]

Write(L, mid, at, wall, n) ==
    LET pad == IF L.wpos + n > Ring THEN Ring - L.wpos ELSE 0
        off == IF pad > 0 THEN 0 ELSE L.wpos
        seq == L.base + Len(L.entries)
        e == [mid |-> mid, at |-> at, wall |-> wall, off |-> off, len |-> n, cost |-> pad + n]
    IN [L EXCEPT !.entries = Append(@, e), !.index = [@ EXCEPT ![mid] = seq],
                 !.cells = IF Track THEN [c \in 0..(Ring - 1) |-> IF c >= off /\ c < off + n THEN mid ELSE L.cells[c]] ELSE <<>>,
                 !.used = @ + pad + n, !.wpos = (off + n) % Ring]

RECURSIVE Loop(_, _, _, _, _, _)
Loop(L, mid, at, wall, n, ev) ==
    LET pad == IF L.wpos + n > Ring THEN Ring - L.wpos ELSE 0
    IN IF Len(L.entries) < Cap /\ L.used + pad + n <= Ring
       THEN [log |-> Write(L, mid, at, wall, n), ok |-> TRUE, ev |-> ev]
       ELSE IF L.entries = <<>> THEN [log |-> L, ok |-> FALSE, ev |-> ev]
       ELSE Loop(Pop(L), mid, at, wall, n, Append(ev, Head(L.entries).mid))

\* log.rs push(): the new log, whether it was stored, and the evicted ids in order
Push(L, mid, at, wall, n) ==
    IF n > Ring \/ Contains(L, mid) THEN [log |-> L, ok |-> FALSE, ev |-> <<>>]
    ELSE Loop(L, mid, at, wall, n, <<>>)

\* log.rs expire(): drop the messages older than the window
RECURSIVE ExpireLoop(_, _, _)
ExpireLoop(L, now, ev) ==
    IF L.entries # <<>> /\ Sub(now, Head(L.entries).at) > Window
    THEN ExpireLoop(Pop(L), now, Append(ev, Head(L.entries).mid))
    ELSE [log |-> L, ev |-> ev]
Expire(L, now) == ExpireLoop(L, now, <<>>)

\* log.rs since(): the ids logged at or after `since` (the entry's wall clock), oldest first
SinceIds(L, since) == LET F(i) == L.entries[i].wall >= since
                      IN [j \in 1..Cardinality({i \in 1..Len(L.entries) : F(i)}) |->
                            L.entries[CHOOSE i \in 1..Len(L.entries) :
                                 F(i) /\ Cardinality({k \in 1..i : F(k)}) = j].mid]

\* log.rs window(): the ids logged in [now - from, now - to)
WindowIds(L, now, from, to) ==
    LET F(i) == Sub(now, from) <= L.entries[i].at /\ L.entries[i].at < Sub(now, to)
    IN [j \in 1..Cardinality({i \in 1..Len(L.entries) : F(i)}) |->
          L.entries[CHOOSE i \in 1..Len(L.entries) : F(i) /\ Cardinality({k \in 1..i : F(k)}) = j].mid]

=============================================================================
