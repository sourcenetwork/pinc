-------------------------------- MODULE Lazy --------------------------------
(***************************************************************************)
(* pinc-transport stream/lazy.rs, Lazy<T, N> with `alloc` (LazyOps.tla),   *)
(* over every sequence of `get_mut`, `written_mut`, `prefix_mut` (each     *)
(* followed by a write through what it returned) and `clear`, with the     *)
(* indices 0..N and prefix lengths 0..N+1, so the refused calls are among  *)
(* them. tab is the table the module doc describes: N entries, blank until *)
(* written.                                                                *)
(*                                                                         *)
(* Checked, the invariants of the module doc:                              *)
(*  - Room: the written prefix never passes N, so the room reserved at the *)
(*    start (`Vec::with_capacity(N)`) never grows and no write allocates;  *)
(*  - Reads, View: the table always reads as N entries (`get` and `iter`), *)
(*    an entry not written reads exactly as the blank, nothing from N on;  *)
(*  - Beyond: past the written prefix every entry is blank;                *)
(*  - RefusedKeeps: a call that returns nothing changes nothing (an entry  *)
(*    that still reads as blank is not written by `written_mut`).          *)
(* Lazy_full is a reachability witness: the whole room gets written.       *)
(* Without `alloc` the table is a plain array; not modelled (no state).    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS N, VALS, BLANK
ASSUME N >= 1 /\ BLANK \notin VALS
VARIABLES w, tab, last
vars == <<w, tab, last>>

INSTANCE LazyOps

Blank == [j \in 0..(N - 1) |-> BLANK]
Init == w = LNew /\ tab = Blank /\ last = "init"

Outcome(r) == IF r.ok THEN "set" ELSE "refused"
GetMut == \E i \in 0..N, v \in VALS :
    LET r == LSetMut(w, N, BLANK, i, v)
    IN /\ w' = r.w
       /\ tab' = IF r.ok THEN [tab EXCEPT ![i] = v] ELSE tab
       /\ last' = Outcome(r)
WrittenMut == \E i \in 0..N, v \in VALS :
    LET r == LSetWritten(w, i, v)
    IN /\ w' = r.w
       /\ tab' = IF r.ok THEN [tab EXCEPT ![i] = v] ELSE tab
       /\ last' = Outcome(r)
PrefixMut == \E k \in 0..(N + 1), v \in VALS :
    LET r == LSetPrefix(w, k, v)
    IN /\ w' = r.w
       /\ tab' = IF r.ok THEN [j \in 0..(N - 1) |-> IF j < k THEN v ELSE tab[j]] ELSE tab
       /\ last' = Outcome(r)
Clear == w' = LClear /\ tab' = Blank /\ last' = "clear"

Next == GetMut \/ WrittenMut \/ PrefixMut \/ Clear
Spec == Init /\ [][Next]_vars

TypeOK == /\ w \in Seq(VALS \cup {BLANK})
          /\ last \in {"init", "set", "refused", "clear"}
Room == Len(w) <= N
Reads == \A i \in 0..N :
            LGet(w, N, BLANK, i) = IF i < N THEN [ok |-> TRUE, v |-> tab[i]] ELSE [ok |-> FALSE, v |-> BLANK]
View == LView(w, N, BLANK) = [j \in 1..N |-> tab[j - 1]]
Beyond == \A j \in 0..(N - 1) : j >= Len(w) => tab[j] = BLANK
RefusedKeeps == [][last' = "refused" => (w' = w /\ tab' = tab)]_vars

\* a reachability witness: the written prefix reaches N
NotFull == Len(w) < N
=============================================================================
