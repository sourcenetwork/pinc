------------------------- MODULE ConnectHeldQueueOps -------------------------
(***************************************************************************)
(* The packets a relay's carrier holds while it is not open (pinc-connect  *)
(* client/queue.rs, HeldQueue) as pure operators, at a count Q (QUEUED,    *)
(* 512 in the code), a byte budget B (QUEUE_BYTES, 48 KiB) and a longest   *)
(* packet M (MAX_PACKET_LEN, 1452). ConnectHeldQueue.tla (the model check, *)
(* small Q, B, M) and TraceConnectHeldQueue.tla (the trace validation, the *)
(* code's sizes) use them.                                                 *)
(*                                                                         *)
(* Two levels:                                                             *)
(*  - the code: the slot array `ents` (Q slots, each empty or an entry     *)
(*    with its destination, its offset and its length), `head`, `n` and    *)
(*    the byte buffer `data` (B cells), with push, pop, retain, compact    *)
(*    and drop_front step for step, every Option fallback of the code      *)
(*    included; a cell of `data` holds the destination of the packet whose *)
(*    byte it is, so that a move that loses or mixes bytes shows;          *)
(*  - the documented queue: a sequence of <<dst, len>> pairs, oldest       *)
(*    first; a push drops the oldest packets while the count is at Q or    *)
(*    the bytes would pass B, then appends; a packet over M is refused and *)
(*    counts as one drop; pop takes the oldest; retain keeps the chosen    *)
(*    positions in order.                                                  *)
(* A plain usize subtraction that would underflow and a copy_within out of *)
(* bounds stop TLC with an error, as they panic in the code.               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Q, B, M

NONE == [e |-> FALSE, d |-> 0, off |-> 0, len |-> 0]
Mk(d, off, len) == [e |-> TRUE, d |-> d, off |-> off, len |-> len]

Init0 == [ents |-> [k \in 0..(Q - 1) |-> NONE], head |-> 0, n |-> 0, data |-> [j \in 0..(B - 1) |-> 0]]

Sub(a, b) == IF Assert(a >= b, "usize subtraction underflows") THEN a - b ELSE 0
SatSub(a, b) == IF a < b THEN 0 ELSE a - b

(* HeldQueue::ent: ents.get(head + i).flatten() *)
Ent(s, i) == IF s.head + i < Q THEN s.ents[s.head + i] ELSE NONE

(* HeldQueue::used: the end of the last live packet, 0 when empty or when the last slot is empty *)
Used(s) == IF s.n = 0 THEN 0 ELSE LET e == Ent(s, s.n - 1) IN IF e.e THEN e.off + e.len ELSE 0

FirstOff(s) == LET e == Ent(s, 0) IN IF e.e THEN e.off ELSE 0

(* data.copy_within(from..to, dst): a memmove; out of bounds panics *)
CopyW(d, from, to, dst) ==
    IF Assert(from <= to /\ to <= B /\ dst + (to - from) <= B, "copy_within out of bounds")
    THEN [j \in 0..(B - 1) |-> IF j >= dst /\ j < dst + (to - from) THEN d[from + (j - dst)] ELSE d[j]]
    ELSE d

(* HeldQueue::compact: move the live packets to the start; the loop reads ent(i) at head + i >= i, which no earlier
   iteration wrote, so it reads the array as it was *)
Compact(s) ==
    LET first == Ent(s, 0)
    IN IF ~first.e THEN [s EXCEPT !.head = 0]
       ELSE LET end == Used(s)
                d1 == CopyW(s.data, first.off, end, 0)
                Shift(e) == IF e.e THEN [e EXCEPT !.off = Sub(e.off, first.off)] ELSE NONE
                e1 == [k \in 0..(Q - 1) |-> IF k < s.n THEN Shift(Ent(s, k)) ELSE NONE]
            IN [s EXCEPT !.data = d1, !.ents = e1, !.head = 0]

(* HeldQueue::drop_front *)
DropFront(s) ==
    IF s.n = 0 THEN s
    ELSE LET s1 == [s EXCEPT !.ents = IF s.head < Q THEN [s.ents EXCEPT ![s.head] = NONE] ELSE s.ents,
                             !.head = s.head + 1, !.n = s.n - 1]
         IN IF s1.n = 0 THEN [s1 EXCEPT !.head = 0] ELSE s1

(* the drop loop of push: k is the number dropped, cnt whether the count bound made a drop *)
RECURSIVE DropLoop(_, _, _, _)
DropLoop(s, len, k, cnt) ==
    IF s.n > 0 /\ (s.n >= Q \/ SatSub(Used(s), FirstOff(s)) + len > B)
    THEN DropLoop(DropFront(s), len, k + 1, cnt \/ s.n >= Q)
    ELSE [s |-> s, k |-> k, cnt |-> cnt]

(* HeldQueue::push. dropped: what the code returns; stored: whether the `if let` stored the packet (its else branch
   drops it silently); comp: whether it compacted with live packets *)
Push(s, d, len) ==
    IF len > M THEN [s |-> s, dropped |-> 1, stored |-> FALSE, comp |-> FALSE, cnt |-> FALSE]
    ELSE LET r == DropLoop(s, len, 0, FALSE)
             s1 == r.s
             c == s1.head + s1.n >= Q \/ Used(s1) + len > B
             s2 == IF c THEN Compact(s1) ELSE s1
             off == Used(s2)
             slot == s2.head + s2.n
             fits == off + len <= B /\ slot < Q
             s3 == [s2 EXCEPT !.data = [j \in 0..(B - 1) |-> IF j >= off /\ j < off + len THEN d ELSE s2.data[j]],
                              !.ents = [s2.ents EXCEPT ![slot] = Mk(d, off, len)],
                              !.n = s2.n + 1]
         IN [s |-> IF fits THEN s3 ELSE s2, dropped |-> r.k, stored |-> fits, comp |-> c /\ s1.n > 0, cnt |-> r.cnt]

(* HeldQueue::pop: none when the first slot is empty, its bytes are out of range or it is longer than M; got is the
   destination and length, cells the destinations found in its bytes *)
Pop(s) ==
    LET e == Ent(s, 0)
    IN IF ~e.e \/ e.off + e.len > B \/ e.len > M THEN [s |-> s, some |-> FALSE, d |-> 0, len |-> 0, cells |-> {}]
       ELSE [s |-> DropFront(s), some |-> TRUE, d |-> e.d, len |-> e.len,
             cells |-> {s.data[j] : j \in e.off..(e.off + e.len - 1)}]

(* HeldQueue::get(i).is_none_or(keep): a position whose packet cannot be read is kept *)
GetOk(s, i) == LET e == Ent(s, i) IN e.e /\ i < s.n /\ e.off + e.len <= B

(* the copy loop of HeldQueue::retain, over the array as it is being rewritten *)
RECURSIVE RetainLoop(_, _, _, _, _, _)
RetainLoop(s, flags, i, w, off, n0) ==
    IF i >= n0 THEN [s |-> s, w |-> w]
    ELSE LET e == Ent(s, i)
         IN IF ~e.e \/ ~flags[i] THEN RetainLoop(s, flags, i + 1, w, off, n0)
            ELSE LET s1 == [s EXCEPT !.data = CopyW(s.data, e.off, e.off + e.len, off),
                                     !.ents = IF s.head + w < Q THEN [s.ents EXCEPT ![s.head + w] = [e EXCEPT !.off = off]]
                                              ELSE s.ents]
                 IN RetainLoop(s1, flags, i + 1, w + 1, off + e.len, n0)

(* HeldQueue::retain with keep answering TRUE exactly at the positions in keep *)
Retain(s, keep) ==
    LET flags == [i \in 0..(Q - 1) |-> IF i < s.n THEN (~GetOk(s, i) \/ i \in keep) ELSE TRUE]
        r == RetainLoop(s, flags, 0, 0, 0, s.n)
        s1 == r.s
        lo == s1.head + r.w
        hi == s1.head + s.n
        e2 == [k \in 0..(Q - 1) |-> IF k >= lo /\ k < hi THEN NONE ELSE s1.ents[k]]
        s2 == [s1 EXCEPT !.ents = e2, !.n = r.w]
    IN IF r.w = 0 THEN [s2 EXCEPT !.head = 0] ELSE s2

(* ---- the documented queue ---- *)
RECURSIVE SumLen(_)
SumLen(q) == IF q = <<>> THEN 0 ELSE Head(q)[2] + SumLen(Tail(q))

(* sum is SumLen(q), carried along so that the trace at the code's sizes stays linear *)
RECURSIVE AbsDrop(_, _, _, _)
AbsDrop(q, len, k, sum) ==
    IF q # <<>> /\ (Len(q) >= Q \/ sum + len > B) THEN AbsDrop(Tail(q), len, k + 1, sum - Head(q)[2])
    ELSE [q |-> q, k |-> k]

AbsPush(q, d, len) ==
    IF len > M THEN [q |-> q, k |-> 1]
    ELSE LET r == AbsDrop(q, len, 0, SumLen(q)) IN [q |-> Append(r.q, <<d, len>>), k |-> r.k]

RECURSIVE AbsKeep(_, _, _)
AbsKeep(q, keep, i) == IF i > Len(q) THEN <<>>
                       ELSE IF (i - 1) \in keep THEN <<q[i]>> \o AbsKeep(q, keep, i + 1) ELSE AbsKeep(q, keep, i + 1)

(* keep holds positions counted from 0, as the code's *)
AbsRetain(q, keep) == AbsKeep(q, keep, 1)

(* the code's queue read as the documented one *)
View(s) == [k \in 1..s.n |-> <<Ent(s, k - 1).d, Ent(s, k - 1).len>>]
=============================================================================
