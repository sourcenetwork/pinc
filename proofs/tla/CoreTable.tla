------------------------------ MODULE CoreTable ------------------------------
(***************************************************************************)
(* The endpoint's connection-id table (vinc-core table.rs, Table) over     *)
(* every interleaving of insert, insert_room, insert_dup, remove,          *)
(* remove_pair, touch and clear, at small sizes, for EVERY bucket          *)
(* function (bk is chosen once, arbitrarily, so a constant function that   *)
(* sends every key to one chain is covered, and so is every other).        *)
(* CoreTableOps.tla has the operators, step for step over the array, the   *)
(* chains, the free list and the insertion-order list. The abstract table  *)
(* m is a sequence of [k, v, s] in insertion order (oldest first), s the   *)
(* order of the pushes: the holders of a key, newest push first, are its   *)
(* entries by decreasing s (a touch moves an entry in m but does not       *)
(* change s).                                                              *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the table holds at most N entries (Bound), the chains, the free list *)
(*    and the order list are well formed and agree: every live entry is in *)
(*    the chain of its key's bucket and in the order list, the free list   *)
(*    holds exactly the others, and the free list is empty exactly when    *)
(*    the table is full (WellFormed);                                      *)
(*  - the table refines m after every call: its order list is m, find and  *)
(*    get give the newest-pushed holder of a key, and matches::<M> gives   *)
(*    the first M holders in order of push, newest first, and how many     *)
(*    that is, for every M up to N + 1 (Refines): every key held is        *)
(*    found, whatever the collisions and removals;                         *)
(*  - a removal takes the newest-pushed holder of the key (remove,         *)
(*    remove_pair: the newest holding that value), and the order list is m *)
(*    without that entry, so no other entry leaves, and every other one    *)
(*    stays findable (RemoveRight with Refines);                           *)
(*  - a key's holders grow only by an insert_dup, or by an insert or an    *)
(*    insert_room of a key nobody holds, to one; without insert_dup every  *)
(*    key has at most one holder (DupRight, Unique);                       *)
(*  - an insert of a held key replaces the value of the newest-pushed      *)
(*    holder and moves nothing; of a new key, adds it as the newest and,   *)
(*    when the table is full, evicts exactly the oldest (the head of the   *)
(*    order list) and returns it; never otherwise (EvictRight);            *)
(*  - insert_dup, and insert_room of a new key, on a full table answer     *)
(*    false and change nothing, the whole structure included (RefuseRight);*)
(*  - the array position of a live entry does not change until the entry   *)
(*    is removed (StableRight).                                            *)
(* BUG_EVICT evicts the newest entry instead of the oldest: the witness    *)
(* CoreTable_evict breaks EvictRight. BUG_CHAIN leaves a removed entry in  *)
(* the middle of its chain: the witness CoreTable_chain breaks Refines.    *)
(* CoreTable_dup and CoreTable_cut are reachability witnesses: a key held  *)
(* twice (so Unique is false once insert_dup is allowed) and a key with    *)
(* more holders than M, whose oldest holders matches::<M> then leaves out. *)
(* Lean counterpart: proofs/lean/Vinc/CoreTable*.lean.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS N, KeySet, Vals, DUP, BUG_EVICT, BUG_CHAIN, CUT
VARIABLES bk, t, m, evR, refR, remR, dupR, stbR
vars == <<bk, t, m, evR, refR, remR, dupR, stbR>>

INSTANCE CoreTableOps

Slots == 0..(N - 1)
LiveSet(x) == {i \in Slots : x.en[i].live}

\* ---- the abstract table: a sequence of [k, v, s], oldest first
Hs(a, k) == {p \in 1..Len(a) : a[p].k = k}
NewestOf(a, S) == CHOOSE p \in S : \A q \in S : a[q].s <= a[p].s
RECURSIVE Desc(_)
Desc(S) == IF S = {} THEN <<>> ELSE LET x == CHOOSE x \in S : \A y \in S : y <= x IN <<x>> \o Desc(S \ {x})
Take(sq, c) == SubSeq(sq, 1, IF c < Len(sq) THEN c ELSE Len(sq))
DelP(a, p) == SubSeq(a, 1, p - 1) \o SubSeq(a, p + 1, Len(a))
ByS(a, s) == a[CHOOSE p \in 1..Len(a) : a[p].s = s]
Holders(a, k) == Desc({a[p].s : p \in Hs(a, k)})
KeysOf(a) == [p \in 1..Len(a) |-> a[p].k]
Cnt(a, x) == Cardinality(Hs(a, x))

\* the new entry of an abstract push: the stamps of m are 0..Len(m)-1 (see Rn)
Fresh(a, k, v) == [k |-> k, v |-> v, s |-> Len(a)]
AInsert(a, k, v) ==
    IF Hs(a, k) # {} THEN [a EXCEPT ![NewestOf(a, Hs(a, k))].v = v]
    ELSE IF Len(a) = N THEN Tail(a) \o <<Fresh(a, k, v)>> ELSE Append(a, Fresh(a, k, v))
ARoom(a, k, v) ==
    IF Hs(a, k) # {} THEN [a EXCEPT ![NewestOf(a, Hs(a, k))].v = v]
    ELSE IF Len(a) < N THEN Append(a, Fresh(a, k, v)) ELSE a
ADup(a, k, v) == IF Len(a) < N THEN Append(a, Fresh(a, k, v)) ELSE a
ARemove(a, k) == IF Hs(a, k) = {} THEN a ELSE DelP(a, NewestOf(a, Hs(a, k)))
PairP(a, k, v) == {p \in Hs(a, k) : a[p].v = v}
APair(a, k, v) == IF PairP(a, k, v) = {} THEN a ELSE DelP(a, NewestOf(a, PairP(a, k, v)))
ATouch(a, k) ==
    IF Hs(a, k) = {} THEN a
    ELSE LET p == NewestOf(a, Hs(a, k)) IN Append(DelP(a, p), a[p])

\* ---- the stamps are kept as ranks (only their order matters), so the state space is finite
RnS(S, x) == Cardinality({y \in S : y < x})
RnT(x) == LET S == {x.en[i].s : i \in LiveSet(x)}
          IN [x EXCEPT !.en = [i \in Slots |-> IF x.en[i].live THEN [x.en[i] EXCEPT !.s = RnS(S, x.en[i].s)] ELSE x.en[i]],
                       !.ctr = Cardinality(S)]
RnM(a) == LET S == {a[p].s : p \in 1..Len(a)} IN [p \in 1..Len(a) |-> [a[p] EXCEPT !.s = RnS(S, a[p].s)]]

\* ---- the concrete table read as a sequence, oldest first
View(x) == [p \in 1..Len(Iter(N, x)) |-> LET e == x.en[Iter(N, x)[p]] IN [k |-> e.k, v |-> e.v, s |-> e.s]]

\* a call's effect on the array positions: every live entry but those that may leave keeps its position and key
Stable(x, y, P) == \A i \in LiveSet(x) \ P : y.en[i].live /\ y.en[i].k = x.en[i].k /\ y.en[i].s = x.en[i].s

\* the evicting insert of the bugged table
InsertBug(x, k, v) ==
    IF BUG_EVICT /\ Find(N, bk, x, k) = Nil /\ x.len = N
    THEN LET p == Pop(N, bk, x, x.newest) IN [t |-> Push(N, bk, p.t, k, v).t, ev |-> <<p.k, p.v>>]
    ELSE Insert(N, bk, x, k, v)
\* the removal of the bugged table: a removed entry that is not the head of its chain stays linked
RemoveBug(x, k) ==
    LET f == Find(N, bk, x, k) IN
    IF BUG_CHAIN /\ f # Nil /\ x.heads[bk[k]] # f
    THEN LET p == Pop(N, bk, x, f)
         IN [t |-> [p.t EXCEPT !.heads = x.heads,
                               !.en = [i \in Slots |-> IF i \in LiveSet(x) /\ x.en[i].chain = f
                                                       THEN [p.t.en[i] EXCEPT !.chain = f] ELSE p.t.en[i]]],
             v |-> <<p.v>>]
    ELSE Remove(N, bk, x, k)

Init == /\ bk \in [KeySet -> 0..(N - 1)]
        /\ t = New(N) /\ m = <<>>
        /\ evR = TRUE /\ refR = TRUE /\ remR = TRUE /\ dupR = TRUE /\ stbR = TRUE

DoInsert(k, v) ==
    LET r == InsertBug(t, k, v)
        w == View(r.t)
        held == Hs(m, k) # {}
        full == Len(m) = N
    IN /\ t' = RnT(r.t) /\ m' = RnM(AInsert(m, k, v))
       /\ evR' = (evR /\ r.ev = (IF ~held /\ full THEN <<m[1].k, m[1].v>> ELSE <<>>)
                      /\ KeysOf(w) = (IF held THEN KeysOf(m)
                                      ELSE IF full THEN Tail(KeysOf(m)) \o <<k>> ELSE Append(KeysOf(m), k)))
       /\ dupR' = (dupR /\ \A x \in KeySet : Cnt(w, x) > Cnt(m, x) => x = k /\ Cnt(m, x) = 0 /\ Cnt(w, x) = 1)
       /\ stbR' = (stbR /\ Stable(t, r.t, IF ~held /\ full THEN {t.oldest} ELSE {}))
       /\ UNCHANGED <<bk, refR, remR>>

DoRoom(k, v) ==
    LET r == InsertRoom(N, bk, t, k, v)
        w == View(r.t)
        held == Hs(m, k) # {}
    IN /\ t' = RnT(r.t) /\ m' = RnM(ARoom(m, k, v))
       /\ refR' = (refR /\ r.ok = (held \/ Len(m) < N)
                       /\ (~r.ok => r.t = t)
                       /\ (r.ok /\ ~held => KeysOf(w) = Append(KeysOf(m), k)))
       /\ dupR' = (dupR /\ \A x \in KeySet : Cnt(w, x) > Cnt(m, x) => x = k /\ Cnt(m, x) = 0 /\ Cnt(w, x) = 1)
       /\ stbR' = (stbR /\ Stable(t, r.t, {}))
       /\ UNCHANGED <<bk, evR, remR>>

DoDup(k, v) ==
    LET r == InsertDup(N, bk, t, k, v)
        w == View(r.t)
    IN /\ DUP
       /\ t' = RnT(r.t) /\ m' = RnM(ADup(m, k, v))
       /\ refR' = (refR /\ r.ok = (Len(m) < N)
                       /\ (~r.ok => r.t = t)
                       /\ (r.ok => KeysOf(w) = Append(KeysOf(m), k)))
       /\ dupR' = (dupR /\ \A x \in KeySet : Cnt(w, x) > Cnt(m, x) => x = k /\ Cnt(w, x) = Cnt(m, x) + 1)
       /\ stbR' = (stbR /\ Stable(t, r.t, {}))
       /\ UNCHANGED <<bk, evR, remR>>

DoRemove(k) ==
    LET r == RemoveBug(t, k)
        w == View(r.t)
        hs == Hs(m, k)
        f == Find(N, bk, t, k)
    IN /\ t' = RnT(r.t) /\ m' = RnM(ARemove(m, k))
       /\ remR' = (remR /\ (IF hs = {} THEN r.v = <<>> /\ w = m
                            ELSE LET p == NewestOf(m, hs) IN r.v = <<m[p].v>> /\ w = DelP(m, p)))
       /\ dupR' = (dupR /\ \A x \in KeySet : Cnt(w, x) <= Cnt(m, x))
       /\ stbR' = (stbR /\ Stable(t, r.t, IF f = Nil THEN {} ELSE {f}))
       /\ UNCHANGED <<bk, evR, refR>>

DoPair(k, v) ==
    LET r == RemovePair(N, bk, t, k, v)
        w == View(r.t)
        ps == PairP(m, k, v)
        f == PairFrom(N, t, t.heads[bk[k]], k, v, N)
    IN /\ t' = RnT(r.t) /\ m' = RnM(APair(m, k, v))
       /\ remR' = (remR /\ r.ok = (ps # {})
                       /\ (IF ps = {} THEN w = m ELSE w = DelP(m, NewestOf(m, ps))))
       /\ dupR' = (dupR /\ \A x \in KeySet : Cnt(w, x) <= Cnt(m, x))
       /\ stbR' = (stbR /\ Stable(t, r.t, IF f = Nil THEN {} ELSE {f}))
       /\ UNCHANGED <<bk, evR, refR>>

DoTouch(k) ==
    LET r == Touch(N, bk, t, k)
        w == View(r)
    IN /\ t' = RnT(r) /\ m' = RnM(ATouch(m, k))
       /\ evR' = (evR /\ Len(w) = Len(m))
       /\ dupR' = (dupR /\ \A x \in KeySet : Cnt(w, x) <= Cnt(m, x))
       /\ stbR' = (stbR /\ Stable(t, r, {}))
       /\ UNCHANGED <<bk, refR, remR>>

DoClear == /\ t' = Clear(N) /\ m' = <<>> /\ UNCHANGED <<bk, evR, refR, remR, dupR, stbR>>

Next == \/ \E k \in KeySet, v \in Vals : DoInsert(k, v) \/ DoRoom(k, v) \/ DoDup(k, v) \/ DoPair(k, v)
        \/ \E k \in KeySet : DoRemove(k) \/ DoTouch(k)
        \/ DoClear
Spec == Init /\ [][Next]_vars

\* ---- the invariants
Bound == t.len <= N /\ t.len = Cardinality(LiveSet(t)) /\ t.len = Len(m)

RECURSIVE CWalk(_, _, _)
CWalk(x, i, fuel) == IF fuel = 0 \/ ~At(N, i) THEN <<>> ELSE <<i>> \o CWalk(x, x.en[i].chain, fuel - 1)
RECURSIVE OWalk(_, _, _)
OWalk(x, i, fuel) == IF fuel = 0 \/ ~At(N, i) THEN <<>> ELSE <<i>> \o OWalk(x, x.en[i].newer, fuel - 1)
Rng(w) == {w[p] : p \in 1..Len(w)}
Distinct(w) == Len(w) <= N /\ Cardinality(Rng(w)) = Len(w)

WellFormed ==
    /\ \A b \in 0..(N - 1) :
         LET w == CWalk(t, t.heads[b], N + 1)
         IN Distinct(w) /\ \A i \in Rng(w) : t.en[i].live /\ bk[t.en[i].k] = b
    /\ \A i \in LiveSet(t) : Cardinality({b \in 0..(N - 1) : i \in Rng(CWalk(t, t.heads[b], N + 1))}) = 1
    /\ LET w == CWalk(t, t.free, N + 1)
       IN Distinct(w) /\ Rng(w) = Slots \ LiveSet(t) /\ \A i \in Rng(w) : t.en[i].older = Nil /\ t.en[i].newer = Nil
    /\ LET w == OWalk(t, t.oldest, N + 1)
       IN /\ Distinct(w) /\ Rng(w) = LiveSet(t) /\ Len(w) = t.len
          /\ t.newest = IF w = <<>> THEN Nil ELSE w[Len(w)]
          /\ \A p \in 1..Len(w) : /\ t.en[w[p]].older = IF p = 1 THEN Nil ELSE w[p - 1]
                                  /\ t.en[w[p]].newer = IF p = Len(w) THEN Nil ELSE w[p + 1]
    /\ (t.free = Nil) = (t.len = N)

Refines ==
    /\ View(t) = m
    /\ \A k \in KeySet :
         LET f == Find(N, bk, t, k)
             hs == Hs(m, k)
         IN /\ (f = Nil) = (hs = {})
            /\ f # Nil => t.en[f].s = m[NewestOf(m, hs)].s /\ t.en[f].v = m[NewestOf(m, hs)].v
            /\ \A c \in 0..(N + 1) :
                 LET ix == Matches(N, bk, t, k, c)
                     want == Take(Holders(m, k), c)
                 IN /\ Len(ix) = Len(want)
                    /\ \A q \in 1..Len(ix) : t.en[ix[q]].s = want[q] /\ t.en[ix[q]].v = ByS(m, want[q]).v

Unique == \A k \in KeySet : Cnt(m, k) <= 1
EvictRight == evR
RefuseRight == refR
RemoveRight == remR
DupRight == dupR
StableRight == stbR
Inv == Bound /\ WellFormed /\ Refines /\ EvictRight /\ RefuseRight /\ RemoveRight /\ DupRight /\ StableRight
        /\ (~DUP => Unique)

\* reachability witnesses: a key held twice; a key with more holders than CUT
NoDouble == ~(\E k \in KeySet : Cnt(m, k) >= 2)
NoOverflow == ~(\E k \in KeySet : Cnt(m, k) > CUT)
=============================================================================
