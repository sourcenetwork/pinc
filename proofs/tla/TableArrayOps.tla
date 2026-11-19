---------------------------- MODULE TableArrayOps ----------------------------
(***************************************************************************)
(* The operators of the array by position, pinc-table array.rs (`Array`), *)
(* step for step, shared by TableArray.tla (the model check) and           *)
(* TraceTableArray.tla (the trace check).                                  *)
(*                                                                         *)
(* A state is the array's block as the code reads it: `fl` the presence    *)
(* byte of each place, `rec` the record bytes of each place (a value; 0 is *)
(* the block's bytes before any set), `ord` the 2-byte walk order, `cnt`   *)
(* the count of present places, `p` the number of places. A record of the  *)
(* wrong length is the argument `good = FALSE`. A plain `-` that would     *)
(* underflow stops TLC with an error.                                      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

(* Array::new(mem, n, record) once accepted (TableBytes.tla has the refusals): the order is the identity, every
   presence byte 0, the count 0 *)
Array0(n) == [p |-> n, fl |-> [q \in 0..(n - 1) |-> FALSE], rec |-> [q \in 0..(n - 1) |-> 0],
              ord |-> [q \in 0..(n - 1) |-> q], cnt |-> 0]

(* Array::get: the record at pos, or none when absent or past the end *)
Get(s, pos) == IF pos < s.p /\ s.fl[pos] THEN <<s.rec[pos]>> ELSE <<>>

(* Array::set: Position before Length, then the record, the presence byte and the count; the result is whether
   the place was present before *)
Set(s, pos, good, v) ==
    IF pos >= s.p THEN [s |-> s, r |-> "position"]
    ELSE IF ~good THEN [s |-> s, r |-> "length"]
    ELSE [s |-> [s EXCEPT !.rec[pos] = v, !.fl[pos] = TRUE, !.cnt = @ + (IF s.fl[pos] THEN 0 ELSE 1)],
          r |-> IF s.fl[pos] THEN "true" ELSE "false"]

(* Array::remove: false for a place past the end or absent; otherwise the presence byte cleared, `count -= 1` *)
Remove(s, pos) ==
    IF pos >= s.p \/ ~s.fl[pos] THEN [s |-> s, r |-> "false"]
    ELSE IF s.cnt = 0
         THEN IF Assert(FALSE, "the count of present places underflows") THEN [s |-> s, r |-> "false"]
              ELSE [s |-> s, r |-> "false"]
    ELSE [s |-> [s EXCEPT !.fl[pos] = FALSE, !.cnt = @ - 1], r |-> "true"]

(* the inner loop of the insertion sort of Array::set_order: the entry x moves down from j past every entry whose
   key is greater (`keys[prev] <= keys[x]` stops it); keys is the sequence of keys, so keys[q + 1] is the key of
   position q *)
RECURSIVE Sink(_, _, _, _)
Sink(ks, o, j, x) ==
    IF j > 0 /\ ks[o[j - 1] + 1] > ks[x + 1] THEN Sink(ks, [o EXCEPT ![j] = o[j - 1]], j - 1, x)
    ELSE [o EXCEPT ![j] = x]

(* the outer loop: i from 1 to n - 1, x read from entry i before the inner loop *)
RECURSIVE ISort(_, _, _, _)
ISort(ks, o, i, n) == IF i >= n THEN o ELSE ISort(ks, Sink(ks, o, i, o[i]), i + 1, n)

(* Array::set_order: Length for a key slice that is not one key a place; else the order is reset to the identity
   and sorted *)
SetOrder(s, ks) ==
    IF Len(ks) # s.p THEN [s |-> s, r |-> "length"]
    ELSE [s |-> [s EXCEPT !.ord = ISort(ks, [q \in 0..(s.p - 1) |-> q], 1, s.p)], r |-> "ok"]

(* Array::iter: the present places in walk order (`order` is `ord`) with their records *)
RECURSIVE IterFrom(_, _)
IterFrom(s, k) ==
    IF k >= s.p THEN <<>>
    ELSE (IF s.fl[s.ord[k]] THEN << <<s.ord[k], s.rec[s.ord[k]]>> >> ELSE <<>>) \o IterFrom(s, k + 1)
Iter(s) == IterFrom(s, 0)
=============================================================================
