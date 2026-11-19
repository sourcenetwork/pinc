------------------------------ MODULE LazyOps ------------------------------
(***************************************************************************)
(* The operations of pinc-transport stream/lazy.rs (Lazy<T, N>) as built  *)
(* with the `alloc` feature, which the trace feature implies and every     *)
(* connection of a node uses. Lazy.tla checks them over every sequence of  *)
(* calls; EvQueueOps.tla builds the event queue on them; TraceLazy.tla     *)
(* replays the recorded calls of the real code.                            *)
(*                                                                         *)
(* The state is w, the written prefix (the code's `written` vector, whose  *)
(* capacity is N from the start); n is N and b is T::BLANK. A write        *)
(* through a returned reference is the call followed by the write, so each *)
(* operator takes the value written and returns the new prefix and whether *)
(* the call returned an entry (`ok`).                                      *)
(***************************************************************************)
EXTENDS Integers, Sequences

\* `new()`: nothing written
LNew == <<>>

\* `get(i)`: nothing from N on; an entry of the written prefix, or the blank beyond it
LGet(w, n, b, i) ==
    IF i >= n THEN [ok |-> FALSE, v |-> b]
    ELSE [ok |-> TRUE, v |-> IF i < Len(w) THEN w[i + 1] ELSE b]

\* the `while written.len() <= i { push(BLANK) }` loop of `get_mut`
LGrow(w, b, i) == IF i < Len(w) THEN w ELSE w \o [k \in 1..(i + 1 - Len(w)) |-> b]

\* `get_mut(i)` and a write of v through it: entry i and every entry before it are written first
LSetMut(w, n, b, i, v) ==
    IF i >= n THEN [ok |-> FALSE, w |-> w]
    ELSE [ok |-> TRUE, w |-> [LGrow(w, b, i) EXCEPT ![i + 1] = v]]

\* `written_mut(i)` and a write of v: only an entry already written; a blank one is not written by asking
LSetWritten(w, i, v) ==
    IF i < Len(w) THEN [ok |-> TRUE, w |-> [w EXCEPT ![i + 1] = v]]
    ELSE [ok |-> FALSE, w |-> w]

\* `written_mut(i).and_then(Option::take)` on a table of options whose blank b is None: the entry, None left behind
LTake(w, i, b) ==
    IF i < Len(w) THEN [ok |-> TRUE, v |-> w[i + 1], w |-> [w EXCEPT ![i + 1] = b]]
    ELSE [ok |-> FALSE, v |-> b, w |-> w]

\* `prefix_mut(k)` and a write of v to every entry of the slice: only when all k entries were written
LSetPrefix(w, k, v) ==
    IF k <= Len(w) THEN [ok |-> TRUE, w |-> [j \in 1..Len(w) |-> IF j <= k THEN v ELSE w[j]]]
    ELSE [ok |-> FALSE, w |-> w]

\* `clear()`: every entry blank again, the room kept
LClear == <<>>

\* `iter()`: the N entries in order, the written ones and then the blank
LView(w, n, b) == [j \in 1..n |-> IF j <= Len(w) THEN w[j] ELSE b]
=============================================================================
