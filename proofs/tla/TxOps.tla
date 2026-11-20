-------------------------------- MODULE TxOps --------------------------------
(***************************************************************************)
(* The operators of pinc-core tx.rs (Endpoint::poll_transmit, gate,        *)
(* send_stash, batch) and of the two send queues it serves (endpoint.rs    *)
(* mark_dirty, dirty_front, dirty_pop, dirty_rotate), shared by Tx.tla     *)
(* (the model check) and TraceTx.tla (the recorded calls of the code).     *)
(*                                                                         *)
(* The queues are qs = <<ordinary, broadcast>>, sequences of session       *)
(* slots, served front first, the ordinary queue before the broadcast one. *)
(* A transmit of a connection is [d, len, seg]: d the destination (0 when  *)
(* the path has no address any more), len the bytes it wrote, seg the size *)
(* of each datagram, a run of Segs(len, seg) datagrams of seg bytes, the   *)
(* last one shorter or equal (pinc-transport send.rs builds it). A buffer  *)
(* being filled is [d, seg, segs, charged]: segs the datagrams in it, each *)
(* [d, n], and charged the bytes the ledger charged for them.              *)
(*                                                                         *)
(* Rotate is the module doc's: the session just served goes to the back    *)
(* of the queue its class names now (its open has left, so a broadcast     *)
(* session counts as broadcast again). dirty_rotate (fix C2) keeps a       *)
(* session alone in its queue in place only when its class still names    *)
(* that queue; a lone session whose class changed goes to the queue of    *)
(* its class (before C2 it stayed, and the trace check failed on such a   *)
(* call). mark_dirty puts a session that is not waiting at the back of    *)
(* the queue its class names (Meta::send_queue) and leaves a waiting one  *)
(* where it is. Promote is dirty_promote (fix C2): an open queued in a     *)
(* waiting broadcast session, or its broadcast flag cleared, moves it from *)
(* the broadcast queue to the back of the ordinary one at once; a session *)
(* whose flag is set while it waits in the ordinary queue moves at its    *)
(* next turn (Rotate).                                                     *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT OVH

Min(a, b) == IF a <= b THEN a ELSE b

InQ(q, i) == \E k \in 1..Len(q) : q[k] = i
Waits(qs, i) == InQ(qs[1], i) \/ InQ(qs[2], i)

(* dirty_front: <<queue, slot>> of the first session waiting, or <<>> *)
Front(qs) == IF qs[1] # <<>> THEN <<1, Head(qs[1])>> ELSE IF qs[2] # <<>> THEN <<2, Head(qs[2])>> ELSE <<>>

(* dirty_pop *)
Pop(qs, qi) == [qs EXCEPT ![qi] = Tail(@)]

(* mark_dirty: a session not waiting goes to the back of queue c; a waiting one is left as it is *)
Enq(qs, i, c) == IF Waits(qs, i) THEN qs ELSE [qs EXCEPT ![c] = Append(@, i)]

(* the class of a session: 2 (broadcast) for a broadcast session with no open still to leave, 1 otherwise *)
Cls(gossip, ctrl) == IF gossip /\ ~ctrl THEN 2 ELSE 1

(* dirty_rotate as the module doc states it: the session served goes to the back of the queue of class c *)
Rotate(qs, qi, c) == Enq(Pop(qs, qi), Head(qs[qi]), c)

Remove(qs, i) == <<SelectSeq(qs[1], LAMBDA x : x # i), SelectSeq(qs[2], LAMBDA x : x # i)>>
(* dirty_promote: a session of class c waiting in the broadcast queue goes to the back of the ordinary one when c is
   ordinary; anything else is left as it is *)
Promote(qs, i, c) == IF c = 1 /\ InQ(qs[2], i) THEN Enq(Remove(qs, i), i, 1) ELSE qs

(* len.div_ceil(seg.max(1)) *)
Segs(len, seg) == IF seg <= 1 THEN len ELSE (len + seg - 1) \div seg

(* the datagrams of a transmit *)
Sizes(dst, len, seg) ==
    LET m == Segs(len, seg)
    IN [k \in 1..m |-> [d |-> dst, n |-> IF k < m THEN seg ELSE len - seg * (m - 1)]]

(* gate: the size the ledger is asked for, len + OVH * segments.saturating_sub(1) *)
GateN(len, segs) == len + OVH * (IF segs > 0 THEN segs - 1 ELSE 0)
(* what the ledger charges for it: the gate's size plus its own OVH (no saturation at these sizes) *)
Charged(len, segs) == GateN(len, segs) + OVH

RECURSIVE SumN(_)
SumN(s) == IF s = <<>> THEN 0 ELSE Head(s).n + SumN(Tail(s))
BLen(b) == SumN(b.segs)

NoBuf == [d |-> 0, seg |-> 0, segs |-> <<>>, charged |-> 0]
NewBuf(tx) == [d |-> tx.d, seg |-> tx.seg, segs |-> Sizes(tx.d, tx.len, tx.seg),
               charged |-> Charged(tx.len, Segs(tx.len, tx.seg))]

(* batch: the loop goes on while the buffer is a run of full datagrams under the limit with room left *)
Cont(b, lim, out) == Len(b.segs) < lim /\ BLen(b) = b.seg * Len(b.segs) /\ out > BLen(b)
(* the window offered to the next connection *)
Room(b, out, md) == Min(out - BLen(b), md)

(* a run of datagrams of the buffer's size, or one shorter datagram that ends the run *)
Full(b, tx) == tx.seg = b.seg /\ tx.len % b.seg = 0
Last(b, tx) == tx.seg = tx.len /\ tx.len < b.seg
Joins(b, tx, lim) ==
    /\ tx.d = b.d
    /\ Len(b.segs) + Segs(tx.len, tx.seg) <= lim
    /\ (Full(b, tx) \/ Last(b, tx) \/ tx.seg = b.seg)
Join(b, tx) == [b EXCEPT !.segs = @ \o Sizes(tx.d, tx.len, tx.seg),
                         !.charged = @ + Charged(tx.len, Segs(tx.len, tx.seg))]

(* what poll_transmit returns for a buffer *)
BufRes(b) == [d |-> b.d, len |-> BLen(b), seg |-> b.seg]
=============================================================================
