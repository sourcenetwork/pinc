------------------------------ MODULE BroadcastLog ------------------------------
(***************************************************************************)
(* The hub log of pinc-broadcast log.rs (HubLog), step for step: a byte    *)
(* ring that holds the heads and bodies, the entry queue, the index from a *)
(* message id to its sequence number, and the base sequence number. A      *)
(* message is Ring cells: the model writes the id into each cell its bytes *)
(* occupy, so a lookup that returned another message's bytes, or bytes     *)
(* overwritten by a later message, is a violation. Sizes are small         *)
(* parameters (Ring is log_bytes, Cap is LOG_CAP, Window is LOG_WINDOW);   *)
(* time is a counter, and the entry's wall clock is its arrival time (the  *)
(* Node and Repair models keep them apart). The operators are shared:      *)
(* BroadcastNode, BroadcastRepair and TraceBroadcast INSTANCE this module. *)
(*                                                                         *)
(* A subtraction that would underflow (`used -= cost`) and an index slot   *)
(* that is not where the queue says stop TLC with an assertion.            *)
(*                                                                         *)
(* Checked in every reachable state: entries are contiguous in the ring    *)
(* with their own id in every cell and do not overlap; `used` is the sum   *)
(* of the costs and fits the ring; the index maps each logged id to base   *)
(* plus its position and maps no other; the queue holds at most Cap        *)
(* entries and each id once; an empty log is reset (wpos 0, used 0); a     *)
(* push fails only for an id already logged or a message larger than the   *)
(* ring (so with `max_body + MAX_HEAD <= log_bytes`, which Limits::valid   *)
(* demands, a push of a valid message cannot fail); the ids a push evicts  *)
(* are exactly the oldest ones, in order; expiry removes exactly the       *)
(* messages older than the window.                                         *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/BroadcastLog.lean.                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, BroadcastLogOps

CONSTANTS MaxN, MaxTime



(* ------------------------------------------------------------------ *)
\* the standalone model: any push, expiry and pop at any time
VARIABLES L, now, lastPush
vars == <<L, now, lastPush>>

Init == L = EmptyLog /\ now = 0 /\ lastPush = "none"

\* the evicted ids are the oldest ones, in order: a prefix of the queue before the push
IsPrefix(ev, entries) == Len(ev) <= Len(entries) /\ \A i \in 1..Len(ev) : ev[i] = entries[i].mid

DoPush ==
    \E mid \in Mids, n \in 1..MaxN :
        LET r == Push(L, mid, now, now, n)
        IN /\ Assert(IsPrefix(r.ev, L.entries), "evicted ids are not the oldest")
           /\ L' = r.log
           /\ lastPush' = IF r.ok THEN "none" ELSE IF Contains(L, mid) THEN "dup" ELSE IF n > Ring THEN "big" ELSE "full"
           /\ UNCHANGED now

\* expiry removes exactly the messages older than the window
DoExpire ==
    LET r == Expire(L, now)
    IN /\ Assert(IsPrefix(r.ev, L.entries) /\ \A i \in 1..Len(r.ev) : Sub(now, L.entries[i].at) > Window, "expired a live message")
       /\ Assert(r.log.entries = <<>> \/ Sub(now, Head(r.log.entries).at) <= Window, "kept an old message")
       /\ L' = r.log /\ lastPush' = "none"
       /\ UNCHANGED now

Tick == /\ now < MaxTime /\ now' = now + 1 /\ UNCHANGED <<L, lastPush>>

Next == DoPush \/ DoExpire \/ Tick
Spec == Init /\ [][Next]_vars

Ids(S) == {S.entries[i].mid : i \in 1..Len(S.entries)}
Sum(S) == LET RECURSIVE f(_) f(i) == IF i = 0 THEN 0 ELSE S.entries[i].cost + f(i - 1) IN f(Len(S.entries))

\* the cells no live entry covers hold stale bytes that nothing reads, and only the distance of an index slot
\* from the base matters: the state graph ignores both (the base counts pops for ever)
LiveCells == [c \in 0..(Ring - 1) |-> IF \E i \in 1..Len(L.entries) : c >= L.entries[i].off /\ c < L.entries[i].off + L.entries[i].len
                                       THEN L.cells[c] ELSE 0]
Rel == [m \in Mids |-> IF L.index[m] = None THEN None ELSE L.index[m] - L.base]
View == <<L.entries, Rel, LiveCells, L.wpos, L.used, now, lastPush>>

TypeOK == /\ Len(L.entries) <= Cap /\ L.used <= Ring /\ L.wpos < Ring /\ L.base >= 0

Contiguous == \A i \in 1..Len(L.entries) :
    LET e == L.entries[i] IN /\ e.off + e.len <= Ring /\ \A k \in e.off..(e.off + e.len - 1) : L.cells[k] = e.mid

Disjoint == \A i, j \in 1..Len(L.entries) : i < j =>
    (L.entries[i].off + L.entries[i].len <= L.entries[j].off \/ L.entries[j].off + L.entries[j].len <= L.entries[i].off)

UsedIsSum == L.used = Sum(L)

IndexExact == /\ \A i \in 1..Len(L.entries) : L.index[L.entries[i].mid] = L.base + i - 1
              /\ \A m \in Mids : Contains(L, m) <=> m \in Ids(L)
              /\ Cardinality(Ids(L)) = Len(L.entries)

EmptyReset == L.entries = <<>> => L.wpos = 0 /\ L.used = 0

GetExact == \A m \in Ids(L) :
    LET e == L.entries[EntryOf(L, m)]
    IN /\ DOMAIN Get(L, m) = 0..(e.len - 1) /\ \A k \in DOMAIN Get(L, m) : Get(L, m)[k] = m

\* a push fails only for a duplicate or a message larger than the ring
PushFailsOnlyDupOrBig == lastPush # "full"

Oldest == Len(L.entries) > 0 => \A i \in 1..Len(L.entries) : i > 1 => L.entries[i - 1].at <= L.entries[i].at
=============================================================================
