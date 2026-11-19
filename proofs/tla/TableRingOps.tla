---------------------------- MODULE TableRingOps ----------------------------
(***************************************************************************)
(* The operators of the ring, pinc-table ring.rs (`Ring`), step for step,  *)
(* shared by TableRing.tla (the model check) and TraceTableRing.tla (the   *)
(* trace check).                                                           *)
(*                                                                         *)
(* A state is the ring as the code holds it: `buf` the record of each of   *)
(* the `cap` places of the block (a value; 0 is the block's bytes before   *)
(* any push), `head`, `len`. A record of the wrong length is the argument  *)
(* `good = FALSE`. A result is <<call, outcome, record>>, the record 0     *)
(* when the call returns none.                                             *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

(* Ring::new(mem, c, record) once accepted (TableBytes.tla has the refusals) *)
Ring0(c) == [cap |-> c, buf |-> [k \in 0..(c - 1) |-> 0], head |-> 0, len |-> 0]

(* Ring::at: room = cap - head; head + i before the wrap, i - room after it *)
At(s, i) == LET room == s.cap - s.head IN IF i < room THEN s.head + i ELSE i - room

(* Ring::push: Length before Full; the record goes to at(len); a place past the block (`rec_mut` none) is the
   Position refusal of the code, which the model check shows unreachable *)
Push(s, good, v) ==
    IF ~good THEN [s |-> s, r |-> <<"push", "length", 0>>]
    ELSE IF s.len = s.cap THEN [s |-> s, r |-> <<"push", "full", 0>>]
    ELSE LET at == At(s, s.len)
         IN IF at >= s.cap THEN [s |-> s, r |-> <<"push", "position", 0>>]
            ELSE [s |-> [s EXCEPT !.buf[at] = v, !.len = @ + 1], r |-> <<"push", "ok", 0>>]

(* Ring::pop: the record at head; head moves on, to 0 after the last place *)
Pop(s) ==
    IF s.len = 0 THEN [s |-> s, r |-> <<"pop", "none", 0>>]
    ELSE LET old == s.head
         IN [s |-> [s EXCEPT !.head = IF old + 1 = s.cap THEN 0 ELSE old + 1, !.len = @ - 1],
             r |-> <<"pop", "some", s.buf[old]>>]

(* Ring::clear *)
Clear(s) == [s |-> [s EXCEPT !.head = 0, !.len = 0], r |-> <<"clear", "ok", 0>>]

(* Ring::get (peek is GetAt(s, 0)) and Ring::iter *)
GetAt(s, i) == IF i < s.len THEN <<s.buf[At(s, i)]>> ELSE <<>>
Items(s) == [k \in 1..s.len |-> s.buf[At(s, k - 1)]]
=============================================================================
