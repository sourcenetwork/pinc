------------------------------ MODULE TableRing ------------------------------
(***************************************************************************)
(* The ring of pinc-table (ring.rs, `Ring`: new, push, pop, peek, get,     *)
(* iter, clear, is_full) over every sequence of calls, for every capacity  *)
(* in CAPS (0 among them), records 1..V and a record of the wrong length.  *)
(* TableRingOps.tla has the operators of the code.                         *)
(*                                                                         *)
(* The specification beside the code is `q`, the sequence of records      *)
(* pushed and not popped: push appends when there is room, pop takes the   *)
(* first, clear empties it.                                                *)
(*                                                                         *)
(* Checked, in every state reached (ring.rs module comment):               *)
(*  - Bounded: len <= capacity; HeadOK: head < capacity (0 for a ring of   *)
(*    capacity 0), which ring.rs relies on for `cap - head`;               *)
(*  - FifoOK, GetOK, PeekOK: the records held, oldest first, are `q`, so   *)
(*    records pop in the order they were pushed;                           *)
(*  - NextAt: the next push goes to (head + len) % capacity;               *)
(*  - NoOverwrite: the place of the next push holds no record held; with   *)
(*    AtInRange, `at` maps 0..capacity-1 one to one into the block, and    *)
(*    head + i is computed only below capacity, so it cannot overflow a    *)
(*    usize of any width;                                                  *)
(*  - FullOK: is_full exactly when `q` holds capacity records;             *)
(*  - ResultOK: every call returns what the specification says (Length     *)
(*    before Full, the record popped, none on an empty ring, never the     *)
(*    Position refusal);                                                   *)
(* and in every step:                                                      *)
(*  - RefusedUnchanged: a refused push and a pop of an empty ring change   *)
(*    nothing.                                                             *)
(* TableRing_wrap is a reachability witness: the ring is full with its     *)
(* oldest record past place 0, so its records wrap around the block end.   *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS CAPS, V
VARIABLES s, q, res, want
vars == <<s, q, res, want>>

INSTANCE TableRingOps

Init == /\ \E c \in CAPS : s = Ring0(c)
        /\ q = <<>>
        /\ res = <<"init", "ok", 0>>
        /\ want = <<"init", "ok", 0>>

DoPush(good, v) ==
    LET x == Push(s, good, v)
    IN /\ s' = x.s
       /\ res' = x.r
       /\ want' = <<"push", IF ~good THEN "length" ELSE IF Len(q) = s.cap THEN "full" ELSE "ok", 0>>
       /\ q' = IF good /\ Len(q) < s.cap THEN Append(q, v) ELSE q

DoPop ==
    LET x == Pop(s)
    IN /\ s' = x.s
       /\ res' = x.r
       /\ want' = IF q = <<>> THEN <<"pop", "none", 0>> ELSE <<"pop", "some", Head(q)>>
       /\ q' = IF q = <<>> THEN q ELSE Tail(q)

DoClear ==
    LET x == Clear(s)
    IN /\ s' = x.s /\ res' = x.r /\ want' = <<"clear", "ok", 0>> /\ q' = <<>>

Next == \/ \E good \in BOOLEAN, v \in 1..V : (good \/ v = 1) /\ DoPush(good, v)
        \/ DoPop
        \/ DoClear
Spec == Init /\ [][Next]_vars

TypeOK == /\ s.len \in 0..s.cap
          /\ s.buf \in [0..(s.cap - 1) -> 0..V]
          /\ q \in Seq(1..V)
Bounded == s.len <= s.cap
HeadOK == IF s.cap > 0 THEN s.head \in 0..(s.cap - 1) ELSE s.head = 0
FifoOK == /\ Len(Items(s)) = Len(q)
          /\ \A k \in 1..Len(q) : Items(s)[k] = q[k]
GetOK == \A i \in 0..s.cap : GetAt(s, i) = IF i < Len(q) THEN <<q[i + 1]>> ELSE <<>>
PeekOK == GetAt(s, 0) = IF q = <<>> THEN <<>> ELSE <<Head(q)>>
NextAt == s.len < s.cap => At(s, s.len) = (s.head + s.len) % s.cap
NoOverwrite == s.len < s.cap => \A i \in 0..(s.len - 1) : At(s, i) # At(s, s.len)
AtInRange == /\ \A i \in 0..(s.cap - 1) : At(s, i) \in 0..(s.cap - 1)
             /\ \A i, j \in 0..(s.cap - 1) : i # j => At(s, i) # At(s, j)
             /\ \A i \in 0..(s.cap - 1) : i < s.cap - s.head => s.head + i < s.cap
FullOK == (s.len = s.cap) = (Len(q) = s.cap)
ResultOK == res = want

RefusedUnchanged == [][res'[2] \in {"length", "full", "position", "none"} => UNCHANGED <<s, q>>]_vars

\* a reachability witness: full, with the oldest record past place 0
NotWrappedFull == ~(s.len = s.cap /\ s.head > 0)
=============================================================================
