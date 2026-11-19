------------------------------ MODULE HeapOps -------------------------------
(***************************************************************************)
(* The operations of pinc-core heap.rs (DeadlineHeap), step for step: the  *)
(* indexed binary min-heap that orders the deadlines of the endpoint's     *)
(* sessions. Heap.tla checks them over every sequence of calls at small    *)
(* sizes; TraceHeap.tla replays the recorded calls of the real code.       *)
(*                                                                         *)
(* The state s: hp, the heap as a sequence of ids (the code's `heap` array *)
(* up to `len`; the code's cells beyond it are stale and never read), pos, *)
(* the position of each id in the heap or -1 (the code's NONE), and at, the *)
(* deadline of each id (kept after the id is removed, as the code keeps    *)
(* it). Heap indices are the code's, from 0: H(hp, i) is hp[i + 1].        *)
(*                                                                         *)
(* The key of an id is <<deadline, id>>, compared as a pair: the earlier   *)
(* deadline first, the lower id on a tie. TIEHI = TRUE is the witness of a *)
(* wrong rule (the higher id wins a tie); the code has TIEHI = FALSE.      *)
(* The sifts keep the code's shape: the element that moves is `id`, with   *)
(* key `k`, and the cell it leaves is overwritten by the next one that     *)
(* moves into it (the code's `put`); the element is put at the end.        *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT TIEHI

NONE == -1
H(hp, i) == hp[i + 1]
Heap0(n) == [hp |-> <<>>, pos |-> [id \in 0..(n - 1) |-> NONE], at |-> [id \in 0..(n - 1) |-> 0]]

Key(s, id) == IF TIEHI THEN <<s.at[id], -id>> ELSE <<s.at[id], id>>
KeyAt(s, i) == Key(s, H(s.hp, i))
LexLT(a, b) == a[1] < b[1] \/ (a[1] = b[1] /\ a[2] < b[2])
LexLE(a, b) == a[1] < b[1] \/ (a[1] = b[1] /\ a[2] <= b[2])

\* put(i, id): heap[i] = id, pos[id] = i (index len is the cell the heap has just grown into)
Put(s, i, id) ==
    [s EXCEPT !.hp = IF i = Len(s.hp) THEN Append(s.hp, id) ELSE [s.hp EXCEPT ![i + 1] = id],
              !.pos = [s.pos EXCEPT ![id] = i]]

\* up(i): while the parent's key is later than k, the parent moves down into the hole
RECURSIVE UpL(_, _, _, _)
UpL(s, i, id, k) ==
    IF i > 0 /\ ~LexLE(KeyAt(s, (i - 1) \div 2), k)
    THEN UpL(Put(s, i, H(s.hp, (i - 1) \div 2)), (i - 1) \div 2, id, k)
    ELSE Put(s, i, id)
Up(s, i) == LET id == H(s.hp, i) IN UpL(s, i, id, Key(s, id))

\* down(i): while the earlier child's key is earlier than k, that child moves up into the hole
RECURSIVE DownL(_, _, _, _)
DownL(s, i, id, k) ==
    LET l == 2 * i + 1
        r == l + 1
        c == IF r < Len(s.hp) /\ LexLT(KeyAt(s, r), KeyAt(s, l)) THEN r ELSE l
    IN IF l >= Len(s.hp) THEN Put(s, i, id)
       ELSE IF LexLE(k, KeyAt(s, c)) THEN Put(s, i, id)
       ELSE DownL(Put(s, i, H(s.hp, c)), c, id, k)
Down(s, i) == LET id == H(s.hp, i) IN DownL(s, i, id, Key(s, id))

\* set(id, at): an id outside 0..N is ignored; a new id joins at the end and goes up; a held id moves up or down
\* when its deadline is earlier or later, and stays when it is the same; the removal of a held id puts the last
\* element in its place and sifts it up and then down from where it is
Set(s, id, has, t) ==
    IF id \notin DOMAIN s.pos THEN s
    ELSE LET p == s.pos[id] IN
      IF p = NONE THEN
          IF ~has THEN s
          ELSE LET s1 == [s EXCEPT !.at[id] = t]
                   i == Len(s.hp)
               IN Up(Put(s1, i, id), i)
      ELSE IF has THEN
          LET old == s.at[id]
              s1 == [s EXCEPT !.at[id] = t]
          IN IF t < old THEN Up(s1, p) ELSE IF t > old THEN Down(s1, p) ELSE s1
      ELSE
          LET n1 == Len(s.hp) - 1
              last == H(s.hp, n1)
              s1 == [hp |-> SubSeq(s.hp, 1, n1), pos |-> [s.pos EXCEPT ![id] = NONE], at |-> s.at]
          IN IF last = id THEN s1
             ELSE LET s3 == Up(Put(s1, p, last), p)
                  IN Down(s3, s3.pos[last])

\* peek: the root with its deadline, or nothing
Peek(s) == IF Len(s.hp) = 0 THEN <<>> ELSE <<s.at[H(s.hp, 0)], H(s.hp, 0)>>
=============================================================================
