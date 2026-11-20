---------------------------- MODULE DgramQueueOps ----------------------------
(***************************************************************************)
(* The datagram queues of pinc-transport stream/datagram.rs, step for     *)
(* step: PackedQueue (`push`, `push_drop_oldest`, `pop`, `clear`) and the  *)
(* send and receive halves of Datagrams with their drop counters, over the *)
(* chunk budget of stream/pool.rs BufferPool (`alloc_chunk` fails when the *)
(* chunks charged reach the budget or the slab; `free_chunk` lowers the    *)
(* charge, saturating at 0). DgramQueue.tla checks them at small sizes;    *)
(* TraceDgramQueue.tla replays the real queues.                            *)
(*                                                                         *)
(* A queue q is [es, ch, chead, clen, tail]: es the queued entries oldest  *)
(* first, each [slot, at, len, tag] (the chunk slot, offset and length of  *)
(* `Entry`, and tag the datagram it holds, for the replay); ch the chunk   *)
(* slots that hold a chunk; chead, clen and tail are `chunk_head`,         *)
(* `chunk_len` and `tail_at`. The ring of `entries` is kept as its live    *)
(* window: `push`, `pop` and `front` read an entry only inside the window  *)
(* (`entries[head]` when len > 0, `entries[(head + len) % Q]` written), so *)
(* where in the ring a window sits changes nothing they compute. A pool pl *)
(* is [used, budget] in chunks, of a slab of p chunks. A datagram d is     *)
(* [len, tag]. The u8 and u16 narrowings of `push` cannot fail (C <= 255,  *)
(* offsets and lengths at most CHUNK_SIZE = 16384) and are not modelled.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

PNew(p) == [used |-> 0, budget |-> p]
\* `alloc_chunk`
Alloc(pl, p) == IF pl.used >= pl.budget \/ pl.used >= p THEN [ok |-> FALSE, pl |-> pl]
                ELSE [ok |-> TRUE, pl |-> [pl EXCEPT !.used = pl.used + 1]]
\* `free_chunk`
Free(pl) == [pl EXCEPT !.used = IF pl.used > 0 THEN pl.used - 1 ELSE 0]
FreeN(pl, n) == [pl EXCEPT !.used = IF pl.used > n THEN pl.used - n ELSE 0]

QNew(c) == [es |-> <<>>, ch |-> [s \in 0..(c - 1) |-> FALSE], chead |-> 0, clen |-> 0, tail |-> 0]

\* `clear`: every chunk back to the pool, everything reset
Clear(q, pl, c) ==
    [q |-> QNew(c), pl |-> FreeN(pl, Cardinality({s \in 0..(c - 1) : q.ch[s]}))]

\* `pop`: the oldest entry out; the queue cleared when it was the last, else its chunk freed when the next entry is
\* in another one
Pop(q, pl, c) ==
    IF q.es = <<>> THEN [ok |-> FALSE, q |-> q, pl |-> pl]
    ELSE LET e == Head(q.es)
             rest == Tail(q.es)
         IN IF rest = <<>> THEN LET r == Clear([q EXCEPT !.es = rest], pl, c) IN [ok |-> TRUE, q |-> r.q, pl |-> r.pl]
            ELSE IF Head(rest).slot # e.slot /\ q.ch[q.chead]
                 THEN [ok |-> TRUE,
                       q |-> [q EXCEPT !.es = rest, !.ch[q.chead] = FALSE, !.chead = (q.chead + 1) % c,
                                       !.clen = q.clen - 1],
                       pl |-> Free(pl)]
                 ELSE [ok |-> TRUE, q |-> [q EXCEPT !.es = rest], pl |-> pl]

\* the write of `push` once the queue has a chunk with room: the entry at the tail of the last chunk
Write(q, pl, d, c, cs) ==
    LET s == (q.chead + q.clen + c - 1) % c
    IN IF ~q.ch[s] \/ q.tail + d.len > cs
       THEN [res |-> "exhausted", q |-> q, pl |-> pl]
       ELSE [res |-> "ok",
             q |-> [q EXCEPT !.es = Append(q.es, [slot |-> s, at |-> q.tail, len |-> d.len, tag |-> d.tag]),
                             !.tail = q.tail + d.len],
             pl |-> pl]

\* `push`
Push(q, pl, d, qn, c, cs, p) ==
    IF d.len > cs THEN [res |-> "toolarge", q |-> q, pl |-> pl]
    ELSE IF Len(q.es) = qn THEN [res |-> "full", q |-> q, pl |-> pl]
    ELSE IF q.clen = 0 \/ q.tail + d.len > cs
         THEN IF q.clen = c THEN [res |-> "full", q |-> q, pl |-> pl]
              ELSE LET a == Alloc(pl, p)
                       s == (q.chead + q.clen) % c
                   IN IF ~a.ok THEN [res |-> "exhausted", q |-> q, pl |-> pl]
                      ELSE Write([q EXCEPT !.ch[s] = TRUE, !.clen = q.clen + 1, !.tail = 0], a.pl, d, c, cs)
         ELSE Write(q, pl, d, c, cs)

\* `push_drop_oldest`: push, dropping the oldest entry after each refusal but TooLarge, until it fits or the queue is
\* empty; k counts the entries dropped
RECURSIVE PushDrop(_, _, _, _, _, _, _, _)
PushDrop(q, pl, d, k, qn, c, cs, p) ==
    LET r == Push(q, pl, d, qn, c, cs, p)
    IN IF r.res = "ok" THEN [res |-> "ok", q |-> r.q, pl |-> r.pl, k |-> k]
       ELSE IF r.res = "toolarge" THEN [res |-> "toolarge", q |-> r.q, pl |-> r.pl, k |-> k]
       ELSE IF r.q.es = <<>> THEN [res |-> r.res, q |-> r.q, pl |-> r.pl, k |-> k]
       ELSE LET o == Pop(r.q, r.pl, c) IN PushDrop(o.q, o.pl, d, k + 1, qn, c, cs, p)

\* `send_datagram(pool, data, max_size)` and its counter `send_dropped` (cnt). With doc, the counter follows its doc:
\* the datagrams dropped to make room and the one refused by an empty pool (the code with fix T2); without, the code
\* before T2: only the drops of a push that succeeded.
Send(q, pl, cnt, d, maxsz, qn, c, cs, p, doc) ==
    IF d.len > maxsz THEN [res |-> "toolarge", q |-> q, pl |-> pl, cnt |-> cnt, k |-> 0]
    ELSE LET r == PushDrop(q, pl, d, 0, qn, c, cs, p)
         IN [res |-> IF r.res \in {"ok", "toolarge"} THEN r.res ELSE "exhausted",
             q |-> r.q, pl |-> r.pl, k |-> r.k,
             cnt |-> CASE r.res = "ok" -> cnt + r.k
                       [] r.res = "toolarge" -> cnt
                       [] OTHER -> IF doc THEN cnt + r.k + 1 ELSE cnt]

\* `on_datagram_frame(pool, data)` and `recv_dropped` (cnt). With doc (the code with fix T2): the drops and the
\* datagram not stored; without, the code before T2: the drops of a push that succeeded, else 1.
Recv(q, pl, cnt, d, qn, c, cs, p, doc) ==
    LET r == PushDrop(q, pl, d, 0, qn, c, cs, p)
    IN [res |-> r.res, q |-> r.q, pl |-> r.pl, k |-> r.k,
        cnt |-> IF r.res = "ok" THEN cnt + r.k ELSE IF doc THEN cnt + r.k + 1 ELSE cnt + 1]

\* `front` (`peek_send`, `recv_datagram`): the oldest datagram's length and tag, or <<>>
Front(q) == IF q.es = <<>> THEN <<>> ELSE <<Head(q.es).len, Head(q.es).tag>>
=============================================================================
