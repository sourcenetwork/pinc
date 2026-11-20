------------------------------ MODULE DgramQueue ------------------------------
(***************************************************************************)
(* One datagram queue of pinc-transport stream/datagram.rs (the send half  *)
(* of Datagrams when SIDE = "send", the receive half when "recv"), over    *)
(* the operators of DgramQueueOps.tla, with a pool shared with other users *)
(* (they take and give back chunks) whose budget the application may lower *)
(* below what is charged (BufferPool::set_budget_bytes, public). Every     *)
(* sequence of datagrams offered (lengths LENS, some longer than a chunk), *)
(* datagrams taken by the connection or the application, `clear`, and the  *)
(* pool's other users and budget. CS is the chunk size, scaled from 16384. *)
(*                                                                         *)
(* Checked, the invariants of the module doc:                              *)
(*  - NoStraddle, BackToBack: entries are stored back to back in a ring of *)
(*    chunks and never straddle a chunk;                                   *)
(*  - EveryChunkUsed: a chunk is returned as soon as its last entry is     *)
(*    removed; EmptyHoldsNoChunk: an empty queue holds no chunk;           *)
(*  - Bounded, PoolKept: at most QN entries in at most C chunks, each      *)
(*    charged to the pool once, so memory stays within the pool charge;    *)
(*  - DropsOldest: a full queue drops its oldest entries, only those, and  *)
(*    the rest keep their order;                                           *)
(*  - Counted: the drop counter counts every datagram offered and dropped  *)
(*    or not stored, as the docs of `send_dropped` ("dropped from the send *)
(*    queue to make room (or refused by an empty pool)") and              *)
(*    `recv_dropped` ("dropped to make room (or that could not be          *)
(*    stored)") say. A datagram refused as too large for the send queue is *)
(*    an error to the caller, not a drop.                                  *)
(* DOC = TRUE counts as the docs say, which is the code with fix T2        *)
(* (`push_drop_oldest` adds to the caller's counter at each drop, and a    *)
(* refused datagram is counted); DOC = FALSE is the code before T2.        *)
(* DgramQueue_sendcount and DgramQueue_recvcount check Counted at DMAX 3   *)
(* (the pool budget lowered below what the queue holds); before T2 they    *)
(* ran DOC = FALSE and TLC found Counted violated (the findings).          *)
(* DgramQueue_drop is a reachability witness: a push drops entries.        *)
(* Not modelled: the early-data buffer of the same file.                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS SIDE, DOC, QN, C, CS, P, LENS, MAXSZ, DMAX
ASSUME SIDE \in {"send", "recv"} /\ DOC \in BOOLEAN /\ QN >= 1 /\ C >= 1 /\ C <= 255 /\ CS >= 1 /\ P >= 0
VARIABLES q, pl, oth, cnt, gone, last
vars == <<q, pl, oth, cnt, gone, last>>

INSTANCE DgramQueueOps

Held == {s \in 0..(C - 1) : q.ch[s]}

Init == /\ q = QNew(C) /\ pl = PNew(P) /\ oth = 0 /\ cnt = 0 /\ gone = 0
        /\ last = [op |-> "init", res |-> "", k |-> 0]

Offer == \E l \in LENS :
    LET d == [len |-> l, tag |-> 0]
        r == IF SIDE = "send" THEN Send(q, pl, cnt, d, MAXSZ, QN, C, CS, P, DOC)
             ELSE Recv(q, pl, cnt, d, QN, C, CS, P, DOC)
    IN /\ q' = r.q /\ pl' = r.pl /\ cnt' = r.cnt /\ oth' = oth
       /\ gone' = gone + (IF SIDE = "send" /\ r.res = "toolarge" THEN 0 ELSE Len(q.es) + 1 - Len(r.q.es))
       /\ last' = [op |-> "offer", res |-> r.res, k |-> r.k]
\* `pop_send` or `release`
Take == LET r == Pop(q, pl, C)
        IN /\ q' = r.q /\ pl' = r.pl /\ UNCHANGED <<oth, cnt, gone>>
           /\ last' = [op |-> "take", res |-> "", k |-> 0]
\* `Datagrams::clear`: the connection is going away
ClearQ == LET r == Clear(q, pl, C)
          IN /\ q' = r.q /\ pl' = r.pl /\ UNCHANGED <<oth, cnt, gone>>
             /\ last' = [op |-> "clear", res |-> "", k |-> 0]
OtherTake == LET a == Alloc(pl, P)
             IN /\ a.ok /\ pl' = a.pl /\ oth' = oth + 1 /\ UNCHANGED <<q, cnt, gone>>
                /\ last' = [op |-> "env", res |-> "", k |-> 0]
OtherGive == /\ oth > 0 /\ pl' = Free(pl) /\ oth' = oth - 1 /\ UNCHANGED <<q, cnt, gone>>
             /\ last' = [op |-> "env", res |-> "", k |-> 0]
SetBudget == \E b \in 0..P : /\ pl' = [pl EXCEPT !.budget = b] /\ UNCHANGED <<q, oth, cnt, gone>>
                             /\ last' = [op |-> "env", res |-> "", k |-> 0]

Next == Offer \/ Take \/ ClearQ \/ OtherTake \/ OtherGive \/ SetBudget
Spec == Init /\ [][Next]_vars
Bound == cnt <= DMAX /\ gone <= DMAX

TypeOK == /\ q.chead \in 0..(C - 1) /\ q.tail \in 0..CS /\ pl.used \in 0..P /\ oth \in 0..P
          /\ \A j \in 1..Len(q.es) : q.es[j].slot \in 0..(C - 1)
Bounded == Len(q.es) <= QN /\ q.clen <= C /\ q.clen = Cardinality(Held)
Contiguous == Held = {(q.chead + j) % C : j \in 0..(q.clen - 1)}
PoolKept == pl.used = q.clen + oth
NoStraddle == \A j \in 1..Len(q.es) : q.es[j].at + q.es[j].len <= CS
InHeldChunk == \A j \in 1..Len(q.es) : q.ch[q.es[j].slot]
BackToBack ==
    q.es # <<>> =>
        /\ q.es[1].slot = q.chead
        /\ \A j \in 1..(Len(q.es) - 1) :
              LET a == q.es[j]
                  b == q.es[j + 1]
              IN \/ (b.slot = a.slot /\ b.at = a.at + a.len)
                 \/ (b.slot = (a.slot + 1) % C /\ b.at = 0)
        /\ q.es[Len(q.es)].slot = (q.chead + q.clen - 1) % C
        /\ q.tail = q.es[Len(q.es)].at + q.es[Len(q.es)].len
EveryChunkUsed == \A s \in Held : \E j \in 1..Len(q.es) : q.es[j].slot = s
EmptyHoldsNoChunk == q.es = <<>> => (q.clen = 0 /\ Held = {})
Counted == cnt = gone
DropsOldest ==
    [][last'.op = "offer" =>
         LET k == last'.k
         IN /\ k <= Len(q.es)
            /\ IF last'.res = "ok"
               THEN /\ Len(q'.es) = Len(q.es) - k + 1
                    /\ SubSeq(q'.es, 1, Len(q'.es) - 1) = SubSeq(q.es, k + 1, Len(q.es))
               ELSE q'.es = SubSeq(q.es, k + 1, Len(q.es))]_vars

\* a reachability witness: a push drops queued entries
NoDrop == last.k = 0
=============================================================================
