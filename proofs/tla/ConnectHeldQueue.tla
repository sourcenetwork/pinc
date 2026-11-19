--------------------------- MODULE ConnectHeldQueue ---------------------------
(***************************************************************************)
(* Model check of the packets a relay's carrier holds while it is not      *)
(* open: pinc-connect client/queue.rs, HeldQueue (push, pop, retain, and   *)
(* the private compact and drop_front), over every interleaving of pushes  *)
(* of every length in LENS (one past M included), pops and retains of      *)
(* every subset, at a small count Q, byte budget B and longest packet M    *)
(* (the code's are 512, 48 KiB and 1452: module constants, not parameters, *)
(* so the trace runs those). Each push carries a new destination 1, 2, ... *)
(* which also marks its bytes; PMAX pushes at most (refused ones count).   *)
(*                                                                         *)
(* Checked, in every state reached (the module doc's invariants and the    *)
(* docs of push, pop and retain):                                          *)
(*  - Bounded: never more than Q packets, never more than B bytes held;    *)
(*  - Layout: the live slots are exactly head .. head + n - 1, the packets *)
(*    are contiguous in `data` in queue order, the last one ends within    *)
(*    B, and every byte of a packet is still that packet's;                *)
(*  - Refines: the code's queue, read oldest first, is the documented      *)
(*    queue: a push drops the oldest packets while the count is at Q or    *)
(*    the bytes would pass B and appends the packet, a pop takes the       *)
(*    oldest, a retain keeps the chosen packets in order;                  *)
(*  - PushOK: the count a push returns is the number the documented queue  *)
(*    drops (1 for a refused packet), and a packet that is not refused is  *)
(*    always stored (the else branch of the code's `if let`, which would   *)
(*    lose it silently, is never taken);                                   *)
(*  - PopOK: pop returns the oldest packet with its destination, its       *)
(*    length and its own bytes, and nothing on an empty queue;             *)
(* and in every step:                                                      *)
(*  - RefusedUnchanged: a packet over M changes nothing.                   *)
(* Witnesses (TLC must violate them, so the cases are reached):            *)
(*  NotDropTwo (one push drops two packets for bytes), NotCountDrop (a     *)
(*  push drops because the count is at Q), NotCompactLive (a push moves    *)
(*  live packets to the start of the buffers).                             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Q, B, M, PMAX, LENS

ASSUME M <= B /\ Q >= 1

VARIABLES s, aq, nid, ev
vars == <<s, aq, nid, ev>>

INSTANCE ConnectHeldQueueOps

Ev0 == [op |-> "init", big |-> FALSE, k |-> 0, ak |-> 0, stored |-> TRUE, comp |-> FALSE, cnt |-> FALSE, pok |-> TRUE]

Init == s = Init0 /\ aq = <<>> /\ nid = 0 /\ ev = Ev0

PushA == /\ nid < PMAX
         /\ \E len \in LENS :
              LET d == nid + 1
                  r == Push(s, d, len)
                  a == AbsPush(aq, d, len)
              IN /\ s' = r.s
                 /\ aq' = a.q
                 /\ nid' = d
                 /\ ev' = [op |-> "push", big |-> len > M, k |-> r.dropped, ak |-> a.k, stored |-> r.stored,
                           comp |-> r.comp, cnt |-> r.cnt, pok |-> TRUE]

PopA == LET r == Pop(s)
            ok == IF aq = <<>> THEN ~r.some
                  ELSE r.some /\ <<r.d, r.len>> = Head(aq) /\ r.cells \subseteq {r.d}
        IN /\ s' = r.s
           /\ aq' = IF aq = <<>> THEN aq ELSE Tail(aq)
           /\ nid' = nid
           /\ ev' = [Ev0 EXCEPT !.op = "pop", !.pok = ok]

RetainA == \E keep \in SUBSET (0..(s.n - 1)) :
              /\ s' = Retain(s, keep)
              /\ aq' = AbsRetain(aq, keep)
              /\ nid' = nid
              /\ ev' = [Ev0 EXCEPT !.op = "retain"]

Next == PushA \/ PopA \/ RetainA
Spec == Init /\ [][Next]_vars

Live(i) == Ent(s, i)

Bounded == /\ s.n <= Q
           /\ SatSub(Used(s), FirstOff(s)) <= B

Layout == /\ s.head + s.n <= Q
          /\ s.n = 0 => s.head = 0
          /\ \A k \in 0..(Q - 1) : s.ents[k].e = (k >= s.head /\ k < s.head + s.n)
          /\ \A i \in 0..(s.n - 2) : Live(i + 1).off = Live(i).off + Live(i).len
          /\ Used(s) <= B
          /\ \A i \in 0..(s.n - 1) : \A j \in Live(i).off..(Live(i).off + Live(i).len - 1) : s.data[j] = Live(i).d

Refines == View(s) = aq

PushOK == ev.op = "push" => (ev.k = ev.ak /\ (ev.big \/ ev.stored))

PopOK == ev.op = "pop" => ev.pok

RefusedUnchanged == [][(ev'.op = "push" /\ ev'.big) => s' = s]_vars

\* reachability witnesses
NotDropTwo == ~(ev.op = "push" /\ ev.k >= 2 /\ ~ev.big)
NotCountDrop == ~(ev.op = "push" /\ ev.cnt)
NotCompactLive == ~(ev.op = "push" /\ ev.comp)
=============================================================================
