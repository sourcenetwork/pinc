-------------------------------- MODULE Heap --------------------------------
(***************************************************************************)
(* The endpoint's deadline heap (pinc-core heap.rs, DeadlineHeap) over     *)
(* every sequence of `set` calls at small sizes: N ids, deadlines 0..T     *)
(* (few, so that many are equal), and an id outside the heap among the     *)
(* calls (HeapOps.tla has the operators).                                  *)
(*                                                                         *)
(* Checked, in every state reached:                                        *)
(*  - Typed, Bounded: the heap never holds more than N items, and as many  *)
(*    as there are ids with a deadline;                                    *)
(*  - Inverse: the position index and the heap are inverse on the ids      *)
(*    present; Once: an id is in the heap at most once;                    *)
(*  - Order: each element is not earlier than its parent, ties broken by   *)
(*    the lower id (the order is stated here on its own, with the lower id *)
(*    first, not through the operators' key);                              *)
(*  - MinRoot: the root is the earliest deadline, and among equal ones the *)
(*    lowest id;                                                           *)
(*  - DrainOK: removing the root over and over (a peek and a `set` with no *)
(*    deadline) gives the deadlines held in strictly increasing order of   *)
(*    <<deadline, id>>, each once, and no other;                           *)
(* and in every step:                                                      *)
(*  - SetExact: a call changes exactly the entry it names: every other id  *)
(*    keeps its presence, its deadline and the deadline stored for it; the *)
(*    id asked about has the deadline given, or none; the size changes by  *)
(*    one only when an id comes or goes; an id outside the heap changes    *)
(*    nothing.                                                             *)
(* TIEHI is the tie rule of the operators: FALSE as the code has it. The   *)
(* witness Heap_hi sets it TRUE (the higher id wins a tie) and Order       *)
(* fails. Heap_full is a reachability witness: the heap fills.             *)
(* Lean counterpart: proofs/lean/Pinc/CoreHeap*.lean.                      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS N, T, TIEHI
VARIABLES s, op
vars == <<s, op>>

INSTANCE HeapOps

Init == s = Heap0(N) /\ op = <<>>
Next == \E id \in 0..N, has \in BOOLEAN, t \in 0..T :
    /\ (has \/ t = 0)
    /\ s' = Set(s, id, has, t)
    /\ op' = <<id, has, t>>
Spec == Init /\ [][Next]_vars

Present(x) == {id \in 0..(N - 1) : x.pos[id] # NONE}
LowKey(x, id) == <<x.at[id], id>>
Dl(x, j) == IF x.pos[j] = NONE THEN <<>> ELSE <<x.at[j]>>

Typed == /\ s.hp \in Seq(0..(N - 1))
         /\ s.pos \in [0..(N - 1) -> (-1)..(N - 1)]
         /\ s.at \in [0..(N - 1) -> 0..T]
Bounded == /\ Len(s.hp) <= N
           /\ Len(s.hp) = Cardinality(Present(s))
Inverse == /\ \A i \in 0..(Len(s.hp) - 1) : s.pos[H(s.hp, i)] = i
           /\ \A id \in 0..(N - 1) : s.pos[id] # NONE => (s.pos[id] < Len(s.hp) /\ H(s.hp, s.pos[id]) = id)
Once == \A i, j \in 0..(Len(s.hp) - 1) : H(s.hp, i) = H(s.hp, j) => i = j
Order == \A j \in 1..(Len(s.hp) - 1) :
            LexLE(LowKey(s, H(s.hp, (j - 1) \div 2)), LowKey(s, H(s.hp, j)))
MinRoot == Peek(s) = IF Present(s) = {} THEN <<>>
                     ELSE LET m == CHOOSE id \in Present(s) : \A q \in Present(s) : LexLE(LowKey(s, id), LowKey(s, q))
                          IN <<s.at[m], m>>

\* what a run of pops gives out
RECURSIVE Drain(_)
Drain(x) == IF Len(x.hp) = 0 THEN <<>>
            ELSE LET pk == Peek(x) IN <<pk>> \o Drain(Set(x, pk[2], FALSE, 0))
DrainOK == LET d == Drain(s)
           IN /\ Len(d) = Len(s.hp)
              /\ \A i \in 1..(Len(d) - 1) : d[i][1] < d[i + 1][1] \/ (d[i][1] = d[i + 1][1] /\ d[i][2] < d[i + 1][2])
              /\ {d[i] : i \in 1..Len(d)} = {<<s.at[id], id>> : id \in Present(s)}

SetExact == [][LET id == op'[1] has == op'[2] t == op'[3]
               IN /\ \A j \in 0..(N - 1) : j # id => (Dl(s, j) = Dl(s', j) /\ s'.at[j] = s.at[j])
                  /\ IF id \in 0..(N - 1)
                     THEN /\ Dl(s', id) = IF has THEN <<t>> ELSE <<>>
                          /\ Len(s'.hp) = Len(s.hp) + (IF Dl(s, id) = <<>> /\ has THEN 1
                                                       ELSE IF Dl(s, id) # <<>> /\ ~has THEN -1 ELSE 0)
                     ELSE s' = s]_vars

\* a reachability witness: the heap fills
NotFull == Len(s.hp) < N
=============================================================================
