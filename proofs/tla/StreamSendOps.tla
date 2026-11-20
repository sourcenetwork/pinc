---------------------------- MODULE StreamSendOps ----------------------------
(***************************************************************************)
(* The send half of a stream, pinc-transport stream/send.rs (Send<S, C>),  *)
(* call for call, over the ring of chunks (pool.rs Ring) and the range     *)
(* sets (ranges.rs RangeSet) it keeps its queues in. StreamSend.tla checks *)
(* every interleaving at small sizes; TraceStreamSend.tla replays the      *)
(* recorded calls of the real code through the same operators.             *)
(*                                                                         *)
(* One operator per call of Send: Open (init), Write (write), Finish       *)
(* (finish), OpenSource (open_source), Reset (reset: the application's     *)
(* reset, and the reset a stop request from the peer makes through         *)
(* Streams::on_stop_sending), RaiseLimit (raise_limit), NextFrame          *)
(* (next_frame), CopyOut (copy_out), OnLost (on_lost), OnAcked (on_acked), *)
(* TakeControl (take_control), ControlLost (control_lost), ResetAcked      *)
(* (reset_acked), IsAcked (is_acked), Clip (clip), and the queries         *)
(* Buffered, Wants, Flushed, IsDone, CanStop, CtlPending, ViewLost.        *)
(* ExtTo is the other users of the pool (other streams, datagram queues),  *)
(* which take and give back chunks of the same pool.                       *)
(*                                                                         *)
(* The state s: open, src (is_source), srcon (the source is held), av (the *)
(* bytes the source holds: read_at returns fewer past them), ring (slot -> *)
(* the chunk number written into it, -1 empty), wr (written), smax         *)
(* (sent_max), limit, lost and acked (sorted, disjoint, non-adjacent       *)
(* intervals <<start, end>>, at most LR and AR), ap (acked_prefix), fs     *)
(* (final_size, -1 none), fin (Fin), rst (Reset: 0 none, 1 pending, 2      *)
(* sent, 3 acknowledged) with rcode and rfs (its code and final size, -1   *)
(* none), cut (cap_cut), ext (pool chunks the other users hold). Two       *)
(* ghosts the code does not keep: rel, the chunk numbers ever released to  *)
(* the pool, and told, the final size the peer was told first (by a frame  *)
(* with the end marker or by a reset frame), -1 none.                      *)
(*                                                                         *)
(* The ring holds chunk numbers where the code holds pool handles: a slot  *)
(* is k % RING for chunk number k, as in Ring::write, and a write into an  *)
(* occupied slot writes into whatever chunk it holds, as the code does, so *)
(* a slot that holds another chunk than the one an offset names is visible *)
(* (alias, and the pairs CopyOut reads). The pool is exact: available      *)
(* chunks are B minus the chunks held (BufferPool::available_chunks with a *)
(* slab of B chunks); the 16-bit handle limit of Ring (a pool past 65535   *)
(* chunks) is not modelled.                                                *)
(*                                                                         *)
(* Scaling. The real constants are CH = 16384 (CHUNK_SIZE), LR = 16        *)
(* (RANGES), AR = 64 (ACKED_RANGES), MAXOFF = 2^62 - 1 (MAX_OFFSET), RING  *)
(* the const generic C; TLC runs them small. Bytes are not in the state:   *)
(* a written byte lives in the chunk its slot holds, so a copy returns the *)
(* bytes written at its offsets exactly when every slot it reads holds the *)
(* chunk its offsets name.                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CH, RING, B, LR, AR, MAXOFF

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b
SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y

(* ---- the range set (ranges.rs), at capacity cap; InsertR is StreamsOps' InsertR with the capacity a parameter ---- *)
InsertR(rs, s, e, cap) ==
    IF s >= e THEN [ok |-> TRUE, rs |-> rs]
    ELSE LET n == Len(rs)
             from == Cardinality({k \in 1..n : rs[k][2] < s})
             to == Cardinality({k \in 1..n : rs[k][1] <= e})
             merged == IF from < to THEN <<Min(rs[from + 1][1], s), Max(rs[to][2], e)>> ELSE <<s, e>>
             newlen == n - (to - from) + 1
         IN IF newlen > cap THEN [ok |-> FALSE, rs |-> rs]
            ELSE [ok |-> TRUE, rs |-> SubSeq(rs, 1, from) \o <<merged>> \o SubSeq(rs, to + 1, n)]

\* insert_widening: when the set is full, widen the range to swallow its nearest interval (the first that starts at or
\* after it, else the last); w says it widened. The widened insert always fits; a failure would leave the set unchanged.
InsertWidening(rs, s, e, cap) ==
    LET r == InsertR(rs, s, e, cap)
    IN IF r.ok THEN [rs |-> r.rs, w |-> FALSE]
       ELSE LET at == Cardinality({k \in 1..Len(rs) : rs[k][1] < s})
                near == IF at < Len(rs) THEN rs[at + 1] ELSE rs[Len(rs)]
                r2 == InsertR(rs, Min(near[1], s), Max(near[2], e), cap)
            IN [rs |-> IF r2.ok THEN r2.rs ELSE rs, w |-> TRUE]

\* remove: cut s..e out; fails (unchanged) when the cut splits an interval of a full set
RemoveR(rs, s, e, cap) ==
    IF s >= e THEN [ok |-> TRUE, rs |-> rs]
    ELSE LET n == Len(rs)
             from == Cardinality({k \in 1..n : rs[k][2] <= s})
             to == Cardinality({k \in 1..n : rs[k][1] < e})
         IN IF from >= to THEN [ok |-> TRUE, rs |-> rs]
            ELSE LET left == IF rs[from + 1][1] < s THEN << <<rs[from + 1][1], s>> >> ELSE <<>>
                     right == IF rs[to][2] > e THEN << <<e, rs[to][2]>> >> ELSE <<>>
                     newlen == n - (to - from) + Len(left) + Len(right)
                 IN IF newlen > cap THEN [ok |-> FALSE, rs |-> rs]
                    ELSE [ok |-> TRUE, rs |-> SubSeq(rs, 1, from) \o left \o right \o SubSeq(rs, to + 1, n)]

\* take_front, for a set that is not empty and max > 0: up to max offsets from the lowest interval
TakeFront(rs, max) ==
    LET st == rs[1][1]
        en == rs[1][2]
        stop == Min(en, st + max)
    IN [s |-> st, e |-> stop, rs |-> IF stop = en THEN Tail(rs) ELSE [rs EXCEPT ![1] = <<stop, en>>]]

\* the Gaps iterator: the parts of at..e that no interval covers, ascending
RECURSIVE GapsFrom(_, _, _)
GapsFrom(rs, at, e) ==
    IF at >= e THEN <<>>
    ELSE LET nx == Cardinality({k \in 1..Len(rs) : rs[k][2] <= at})
         IN IF nx = Len(rs) THEN << <<at, e>> >>
            ELSE LET iv == rs[nx + 1]
                 IN IF iv[1] <= at THEN GapsFrom(rs, iv[2], e)
                    ELSE << <<at, Min(iv[1], e)>> >> \o GapsFrom(rs, iv[2], e)

First0(rs) == IF Len(rs) > 0 /\ rs[1][1] = 0 THEN rs[1][2] ELSE 0
Sorted(rs, cap) == /\ Len(rs) <= cap
                   /\ \A k \in 1..Len(rs) : rs[k][1] < rs[k][2]
                   /\ \A k \in 1..(Len(rs) - 1) : rs[k][2] < rs[k + 1][1]

\* each gap inserted into lost with widening, in order; w counts the widenings
RECURSIVE InsertAllW(_, _)
InsertAllW(rs, gs) ==
    IF gs = <<>> THEN [rs |-> rs, w |-> 0]
    ELSE LET r == InsertWidening(rs, Head(gs)[1], Head(gs)[2], LR)
             rest == InsertAllW(r.rs, Tail(gs))
         IN [rs |-> rest.rs, w |-> rest.w + (IF r.w THEN 1 ELSE 0)]

(* ---- the half ---- *)
Fins == {"none", "pend", "sent", "acked"}
EmptyRing == [j \in 0..(RING - 1) |-> -1]
New == [open |-> FALSE, src |-> FALSE, srcon |-> FALSE, av |-> 0, ring |-> EmptyRing, wr |-> 0, smax |-> 0,
        limit |-> 0, lost |-> <<>>, acked |-> <<>>, ap |-> 0, fs |-> -1, fin |-> "none", rst |-> 0, rcode |-> -1,
        rfs |-> -1, cut |-> FALSE, ext |-> 0, rel |-> {}, told |-> -1]
Open(s, limit) == [s EXCEPT !.open = TRUE, !.limit = limit]

Slot(k) == k % RING
Holds(s, k) == s.ring[Slot(k)] = k
HeldSlots(s) == {j \in 0..(RING - 1) : s.ring[j] # -1}
HeldSet(s) == {s.ring[j] : j \in HeldSlots(s)}
\* Ring::numbers(acked_prefix / CH): the chunk numbers of the window the ring can hold whose slot is not empty
WindowHeld(s) == {k \in (s.ap \div CH)..(s.ap \div CH + RING - 1) : s.ring[Slot(k)] # -1}
AvailC(s) == Max(B - Cardinality(HeldSlots(s)) - s.ext, 0)
\* the chunks that hold the bytes a..w-1 (none when w <= a), and the chunks from the one holding a to the one holding w-1
ChunksOf(a, w) == IF w <= a THEN {} ELSE (a \div CH)..((w - 1) \div CH)
ChunksFrom(a, w) == IF w = 0 THEN {} ELSE (a \div CH)..((w - 1) \div CH)

Used(s) == IF s.src THEN s.smax ELSE s.wr                 \* credit spent
Live(s) == s.open /\ s.rst = 0
Buffered(s) == IF s.src \/ ~s.open \/ s.rst # 0 THEN 0 ELSE s.wr - s.ap
Unsent(s) == IF s.src THEN Max((IF s.fs = -1 THEN 0 ELSE s.fs) - s.smax, 0) ELSE Max(s.wr - s.smax, 0)
IsDone(s) == ~s.open \/ s.rst = 3 \/ (s.fin = "acked" /\ s.fs = s.ap)
\* trace_state's first answer: closed, or its end and every byte acknowledged
FinDone(s) == ~s.open \/ (s.fin = "acked" /\ s.fs = s.ap)
Wants(s) ==
    IF ~Live(s) THEN <<FALSE, FALSE>>
    ELSE LET finOnly == s.fin = "pend" /\ s.fs = s.smax
             credit == ~s.src \/ s.limit > s.smax
         IN <<s.lost # <<>> \/ finOnly, Unsent(s) > 0 /\ credit>>
Flushed(s) == ~s.open \/ s.rst \in {2, 3} \/ (s.fin \in {"sent", "acked"} /\ ~Wants(s)[1])
CanStop(s) == s.open /\ s.rst = 0 /\ ~IsDone(s)
CtlPending(s) == s.rst = 1
ViewLost(s) == IF s.lost = <<>> THEN -1 ELSE s.lost[1][1]
IsAcked(s, off, len) == IF len = 0 THEN s.fin = "acked" ELSE GapsFrom(s.acked, off, off + len) = <<>>
Clip(s, off) == Max(off, s.ap)
RaiseLimit(s, l) == [s EXCEPT !.limit = Max(@, l)]
\* the other users of the pool move their hold to n, taking only chunks that are free
ExtTo(s, n) == [s EXCEPT !.ext = IF n > s.ext THEN Min(n, s.ext + AvailC(s)) ELSE n]

ReleaseAll(s) == [s EXCEPT !.ring = EmptyRing, !.rel = @ \cup HeldSet(s)]
\* Ring::release for k in lo..hi-1: the slot k % RING is emptied, whatever chunk it holds
ReleaseChunks(s, lo, hi) ==
    LET J == {Slot(k) : k \in lo..(hi - 1)}
    IN [s EXCEPT !.ring = [j \in 0..(RING - 1) |-> IF j \in J THEN -1 ELSE s.ring[j]],
                 !.rel = @ \cup {s.ring[j] : j \in {x \in J : s.ring[x] # -1}}]

(* ---- write (and Ring::write) ---- *)
\* Ring::write over chunks k..last: an empty slot takes a pool chunk (av left), or the write fails there with the chunks
\* taken so far kept; an occupied slot is written whatever chunk it holds (alias: it held another chunk)
RECURSIVE RingWriteFrom(_, _, _, _)
RingWriteFrom(r, k, last, av) ==
    IF k > last THEN r
    ELSE IF r.ring[Slot(k)] = -1
         THEN IF av = 0 THEN [r EXCEPT !.ok = FALSE]
              ELSE RingWriteFrom([r EXCEPT !.ring[Slot(k)] = k], k + 1, last, av - 1)
         ELSE RingWriteFrom([r EXCEPT !.alias = r.alias \/ r.ring[Slot(k)] # k], k + 1, last, av)

Credit(s) == Max(s.limit - s.wr, 0)
RingRoom(s) == Max((s.ap \div CH) * CH + RING * CH - s.wr, 0)
TailRoom(s) == IF s.wr % CH = 0 THEN 0 ELSE CH - (s.wr % CH)
PoolRoom(s) == AvailC(s) * CH + TailRoom(s)

Write(s, want, room) ==
    IF ~s.open THEN [s |-> s, err |-> "StreamState", n |-> 0, alias |-> FALSE]
    ELSE IF s.src THEN [s |-> s, err |-> "WrongKind", n |-> 0, alias |-> FALSE]
    ELSE IF s.fs # -1 \/ s.rst # 0 THEN [s |-> s, err |-> "Finished", n |-> 0, alias |-> FALSE]
    ELSE LET n == Min(Min(Min(Min(want, Credit(s)), room), RingRoom(s)), PoolRoom(s))
             s1 == [s EXCEPT !.cut = @ \/ (room <= n /\ room < want)]
             r0 == [ring |-> s.ring, ok |-> TRUE, alias |-> FALSE]
             w == IF n = 0 THEN r0 ELSE RingWriteFrom(r0, s.wr \div CH, (s.wr + n - 1) \div CH, AvailC(s))
         IN IF ~w.ok THEN [s |-> [s1 EXCEPT !.ring = w.ring], err |-> "Exhausted", n |-> 0, alias |-> w.alias]
            ELSE [s |-> [s1 EXCEPT !.ring = w.ring, !.wr = s.wr + n], err |-> "ok", n |-> n, alias |-> w.alias]

Finish(s) ==
    IF ~s.open THEN [s |-> s, err |-> "StreamState"]
    ELSE IF s.src THEN [s |-> s, err |-> "WrongKind"]
    ELSE IF s.rst # 0 THEN [s |-> s, err |-> "Finished"]
    ELSE [s |-> IF s.fs = -1 THEN [s EXCEPT !.fs = s.wr, !.fin = "pend"] ELSE s, err |-> "ok"]

\* open_source: av is the bytes the source holds (the test's source returns fewer past them)
OpenSource(s, len, av) ==
    IF ~s.open THEN [s |-> s, err |-> "StreamState"]
    ELSE IF s.src THEN [s |-> s, err |-> "WrongKind"]
    \* a reset half refuses a source as finished (send.rs open_source)
    ELSE IF s.rst # 0 THEN [s |-> s, err |-> "Finished"]
    ELSE IF s.wr > 0 \/ s.fs # -1 THEN [s |-> s, err |-> "WrongKind"]
    ELSE IF len > MAXOFF THEN [s |-> s, err |-> "FlowControl"]
    ELSE [s |-> [s EXCEPT !.src = TRUE, !.srcon = TRUE, !.av = av, !.fs = len, !.fin = "pend"], err |-> "ok"]

Reset(s, code) ==
    IF ~s.open THEN [s |-> s, err |-> "StreamState"]
    ELSE IF s.rst # 0 \/ IsDone(s) THEN [s |-> s, err |-> "ok"]
    ELSE [s |-> ReleaseAll([s EXCEPT !.rst = 1, !.rcode = code, !.rfs = Used(s), !.srcon = FALSE,
                                     !.lost = <<>>, !.acked = <<>>]),
          err |-> "ok"]

(* ---- next_frame ---- *)
Tell(s, fin, e) == IF fin /\ s.told = -1 THEN [s EXCEPT !.told = e] ELSE s
NoFrame(s) == [s |-> s, some |-> FALSE, off |-> 0, len |-> 0, fin |-> FALSE]
Frm(s, o, l, f) == [s |-> Tell(s, f, o + l), some |-> TRUE, off |-> o, len |-> l, fin |-> f]

\* after the retransmission loop: the end marker alone, when nothing is queued and every byte has gone
FinOnly(s) == IF s.lost = <<>> /\ s.fin = "pend" /\ s.fs = s.smax
              THEN Frm([s EXCEPT !.fin = "sent"], s.smax, 0, TRUE) ELSE NoFrame(s)
\* the retransmission pass: the lowest lost range, cut to start at the acknowledged prefix; a range wholly inside the
\* prefix is dropped and the next one taken
RECURSIVE Retx(_, _)
Retx(s, b) ==
    IF s.lost = <<>> \/ b = 0 THEN FinOnly(s)
    ELSE LET r == TakeFront(s.lost, b)
             s1 == [s EXCEPT !.lost = r.rs]
             fin == s.fin = "pend" /\ s.fs = r.e
             st == Min(Max(r.s, s.ap), r.e)
         IN IF st = r.e /\ ~fin THEN Retx(s1, b)
            ELSE Frm(IF fin THEN [s1 EXCEPT !.fin = "sent"] ELSE s1, st, r.e - st, fin)
\* fresh data: a source-backed stream spends credit here, a buffered one spent it at the write
Fresh(s, b) ==
    LET n0 == Min(Unsent(s), b)
        n == IF s.src THEN Min(n0, Max(s.limit - s.smax, 0)) ELSE n0
        s1 == [s EXCEPT !.smax = s.smax + n]
        fin == s.fin = "pend" /\ s.fs = s.smax + n
    IN IF n = 0 THEN NoFrame(s)
       ELSE Frm(IF fin THEN [s1 EXCEPT !.fin = "sent"] ELSE s1, s.smax, n, fin)
NextFrame(s, retx, b) == IF ~Live(s) THEN NoFrame(s) ELSE IF retx THEN Retx(s, b) ELSE Fresh(s, b)

(* ---- loss, copy, acknowledgement ---- *)
\* requeue: the parts of the range below sent_max that are not acknowledged go back to lost (w: widenings)
Requeue(s, off, len, fin) ==
    IF ~Live(s) THEN [s |-> s, w |-> 0]
    ELSE LET s1 == IF fin /\ s.fin # "acked" THEN [s EXCEPT !.fin = "pend"] ELSE s
             r == InsertAllW(s.lost, GapsFrom(s.acked, off, Min(off + len, s.smax)))
         IN [s |-> [s1 EXCEPT !.lost = r.rs], w |-> r.w]
OnLost(s, off, len, fin) == Requeue(s, off, len, fin)

\* Ring::read: chunk by chunk, stopping at the first empty slot; reads are the pairs <<chunk number named by the
\* offsets, chunk number the slot holds>> of the chunks whose bytes were copied
RingRead(s, off, len) ==
    IF len = 0 THEN [got |-> 0, reads |-> {}]
    ELSE LET empty == {k \in (off \div CH)..((off + len - 1) \div CH) : s.ring[Slot(k)] = -1}
             stop == IF empty = {} THEN (off + len - 1) \div CH + 1 ELSE SetMin(empty)
         IN [got |-> IF empty = {} THEN len ELSE Max(stop * CH - off, 0),
             reads |-> {<<k, s.ring[Slot(k)]>> : k \in (off \div CH)..(stop - 1)}]
\* copy_out of the frame off, len, fin into a destination that fits it or not
CopyOut(s, off, len, fin, fits) ==
    IF ~fits THEN [s |-> s, err |-> "BufferTooSmall", got |-> 0, reads |-> {}]
    ELSE IF ~s.srcon /\ off \div CH < s.ap \div CH
         THEN [s |-> Requeue(s, off, len, fin).s, err |-> "DataUnavailable", got |-> 0, reads |-> {}]
    ELSE LET rd == IF s.srcon THEN [got |-> Min(len, Max(s.av - off, 0)), reads |-> {}] ELSE RingRead(s, off, len)
         IN IF rd.got = len THEN [s |-> s, err |-> "ok", got |-> len, reads |-> rd.reads]
            ELSE [s |-> Requeue(s, off, len, fin).s, err |-> "DataUnavailable", got |-> rd.got, reads |-> rd.reads]

\* on_acked: w counts the range-map overflows absorbed
OnAcked(s, off, len, fin) ==
    IF ~Live(s) THEN [s |-> s, w |-> 0]
    ELSE LET s0 == IF fin THEN [s EXCEPT !.fin = "acked"] ELSE s
             e == Min(off + len, s.smax)
             ins == InsertR(s.acked, off, e, AR)
             wid == InsertWidening(s.lost, off, e, LR)
             rem == RemoveR(s.lost, off, e, LR)
             s1 == IF off >= e THEN s0
                   ELSE IF ~ins.ok THEN [s0 EXCEPT !.lost = wid.rs]
                   ELSE [s0 EXCEPT !.acked = ins.rs, !.lost = rem.rs]
             w == IF off >= e THEN 0 ELSE IF ~ins.ok \/ ~rem.ok THEN 1 ELSE 0
             prefix == First0(s1.acked)
             s2 == IF ~s.src THEN ReleaseChunks(s1, s.ap \div CH, prefix \div CH) ELSE s1
             s3 == [s2 EXCEPT !.ap = prefix]
         IN [s |-> IF IsDone(s3) THEN ReleaseAll(s3) ELSE s3, w |-> w]

(* ---- the reset frame ---- *)
TakeControl(s) ==
    IF s.rst = 1 THEN [s |-> Tell([s EXCEPT !.rst = 2], TRUE, s.rfs), some |-> TRUE, code |-> s.rcode, fs |-> s.rfs]
    ELSE [s |-> s, some |-> FALSE, code |-> -1, fs |-> -1]
ControlLost(s, code, fs) == IF s.rst = 2 THEN [s EXCEPT !.rst = 1, !.rcode = code, !.rfs = fs] ELSE s
ResetAcked(s) == IF s.rst \in {1, 2} THEN [s EXCEPT !.rst = 3, !.rcode = -1, !.rfs = -1] ELSE s

(* ---- the stated invariants, as predicates of a state (StreamSend.tla and the trace check share them) ---- *)
\* the module doc of send.rs: lost below sent_max, acked_prefix the end of the acknowledged prefix
WellFormedOf(s) == /\ Sorted(s.lost, LR) /\ Sorted(s.acked, AR)
                   /\ s.fin \in Fins /\ s.rst \in 0..3
                   /\ 0 <= s.ap /\ s.ap <= s.smax /\ (~s.src => s.smax <= s.wr)
                   /\ \A k \in 1..Len(s.acked) : s.acked[k][2] <= s.smax
LostBelowSentOf(s) == \A k \in 1..Len(s.lost) : s.lost[k][2] <= s.smax
ApIsPrefixOf(s) == Live(s) => s.ap = First0(s.acked)
\* send credit: what is spent, and what is sent, stays within the peer's window
CreditSpentOf(s) == Used(s) <= s.limit
SentInWindowOf(s) == s.smax <= s.limit
\* a reset the peer accepts: its final size is not below a byte sent and not above the credit
ResetInWindowOf(s) == s.rst \in {1, 2} => (s.smax <= s.rfs /\ s.rfs <= s.limit)
\* nothing is sent past the final size; a buffered stream's final size is what was written
EndWithinFinalOf(s) == s.fs # -1 => (s.smax <= s.fs /\ (~s.src => s.wr = s.fs))
\* a buffered stream holds chunks only from the one containing acked_prefix, each in its own slot, and every byte
\* written and not acknowledged is held
HeldFromPrefixOf(s) == HeldSet(s) \subseteq ChunksFrom(s.ap, s.wr) /\ \A j \in HeldSlots(s) : Slot(s.ring[j]) = j
BytesHeldOf(s) == (Live(s) /\ ~s.src) => \A k \in ChunksOf(s.ap, s.wr) : Holds(s, k)
PoolOf(s) == Cardinality(HeldSlots(s)) + s.ext <= B
\* a copy reads only slots that hold the chunk its offsets name, and never a chunk released to the pool
ReadsOwnOf(s, R) == \A p \in R.reads : p[2] = p[1] /\ p[1] \notin s.rel
=============================================================================
