------------------------------ MODULE TableArray ------------------------------
(***************************************************************************)
(* The array by position of pinc-table (array.rs, `Array`: new, set,       *)
(* remove, get, set_order, order, iter) over every sequence of calls at    *)
(* small sizes: P places, record values 1..V, a record of the wrong        *)
(* length, a position past the end, and every walk order key vector over   *)
(* 0..KEYS-1 (few, so that many are equal) and one of the wrong length.    *)
(* TableArrayOps.tla has the operators of the code.                        *)
(*                                                                         *)
(* The specification beside the code is `g`, the record each place holds  *)
(* or 0 when absent, changed by set and remove as the documentation says,  *)
(* and `gk`, the last key vector accepted (all keys 0 at the start, whose  *)
(* stable sort is the identity).                                           *)
(*                                                                         *)
(* Checked, in every state reached (array.rs module comment):              *)
(*  - PresentOK: a place is present exactly when it was set and not       *)
(*    removed, with the record last set; a position past the end reads    *)
(*    nothing;                                                             *)
(*  - CountOK: `len` is the number of present places;                      *)
(*  - OrderPerm: the order is always a permutation of 0..places;           *)
(*  - OrderOK: the order is the positions sorted by the last keys set,     *)
(*    equal keys in position order, the identity until set;               *)
(*  - IterOK: `iter` gives the present places in walk order, each once,    *)
(*    with its record;                                                     *)
(*  - ResultOK: every call returns what the specification says (whether   *)
(*    the place was present, Position before Length);                      *)
(* and in every step:                                                      *)
(*  - RefusedUnchanged: a refused call (Position, Length) and a remove of  *)
(*    a place not present change nothing (error.rs: "The table is          *)
(*    unchanged after any of them").                                       *)
(* TableArray_full is a reachability witness: every place is present.      *)
(* The refusals of `Array::new` are in TableBytes.tla.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS P, V, KEYS
VARIABLES s, g, gk, res, want
vars == <<s, g, gk, res, want>>

INSTANCE TableArrayOps

Init == /\ s = Array0(P)
        /\ g = [q \in 0..(P - 1) |-> 0]
        /\ gk = [k \in 1..P |-> 0]
        /\ res = <<"init", "ok">>
        /\ want = <<"init", "ok">>

KeySeqs == [1..P -> 0..(KEYS - 1)] \cup {[k \in 1..(P + 1) |-> 0]}

DoSet(pos, good, v) ==
    LET x == Set(s, pos, good, v)
    IN /\ s' = x.s
       /\ res' = <<"set", x.r>>
       /\ want' = <<"set", IF pos >= P THEN "position" ELSE IF ~good THEN "length"
                           ELSE IF g[pos] # 0 THEN "true" ELSE "false">>
       /\ g' = IF pos < P /\ good THEN [g EXCEPT ![pos] = v] ELSE g
       /\ UNCHANGED gk

DoRemove(pos) ==
    LET x == Remove(s, pos)
    IN /\ s' = x.s
       /\ res' = <<"remove", x.r>>
       /\ want' = <<"remove", IF pos < P /\ g[pos] # 0 THEN "true" ELSE "false">>
       /\ g' = IF pos < P THEN [g EXCEPT ![pos] = 0] ELSE g
       /\ UNCHANGED gk

DoOrder(ks) ==
    LET x == SetOrder(s, ks)
    IN /\ s' = x.s
       /\ res' = <<"order", x.r>>
       /\ want' = <<"order", IF Len(ks) = P THEN "ok" ELSE "length">>
       /\ gk' = IF Len(ks) = P THEN ks ELSE gk
       /\ UNCHANGED g

Next == \/ \E pos \in 0..P, good \in BOOLEAN, v \in 1..V : (good \/ v = 1) /\ DoSet(pos, good, v)
        \/ \E pos \in 0..P : DoRemove(pos)
        \/ \E ks \in KeySeqs : DoOrder(ks)
Spec == Init /\ [][Next]_vars

Present == {q \in 0..(P - 1) : g[q] # 0}
(* the place of position q in the walk *)
WalkAt(q) == CHOOSE i \in 0..(P - 1) : s.ord[i] = q
Key(q) == gk[q + 1]

TypeOK == /\ s.cnt \in 0..P
          /\ s.ord \in [0..(P - 1) -> 0..(P - 1)]
          /\ g \in [0..(P - 1) -> 0..V]
PresentOK == /\ \A q \in 0..(P - 1) : Get(s, q) = IF g[q] = 0 THEN <<>> ELSE <<g[q]>>
             /\ Get(s, P) = <<>>
CountOK == s.cnt = Cardinality(Present)
OrderPerm == {s.ord[i] : i \in 0..(P - 1)} = 0..(P - 1)
OrderOK == \A i, j \in 0..(P - 1) :
              i < j => (Key(s.ord[i]) < Key(s.ord[j]) \/ (Key(s.ord[i]) = Key(s.ord[j]) /\ s.ord[i] < s.ord[j]))
IterOK == LET it == Iter(s)
          IN /\ Len(it) = Cardinality(Present)
             /\ {it[k][1] : k \in 1..Len(it)} = Present
             /\ \A k \in 1..Len(it) : it[k][2] = g[it[k][1]]
             /\ \A k \in 1..(Len(it) - 1) : WalkAt(it[k][1]) < WalkAt(it[k + 1][1])
ResultOK == res = want

RefusedUnchanged == [][(res'[2] \in {"position", "length"} \/ res' = <<"remove", "false">>)
                       => UNCHANGED <<s, g, gk>>]_vars

\* a reachability witness: every place is present
NotFull == s.cnt < P
=============================================================================
