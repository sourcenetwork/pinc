------------------------------ MODULE StreamsOps ------------------------------
(***************************************************************************)
(* The operations of pinc-transport stream/table.rs, recv.rs, flow.rs,     *)
(* ranges.rs and pool.rs on the receive and credit path, step for step.    *)
(* Streams.tla checks them over every interleaving at small sizes;         *)
(* TraceStreams.tla replays the recorded calls of the real code through    *)
(* the same operators.                                                     *)
(*                                                                         *)
(* One operator per public call of Streams: Frame (on_stream_frame),       *)
(* Reset (on_reset_stream), Consume, Pending (pending_control), CtlLostMsd *)
(* CtlLostReset and CtlLostStop (on_control_lost), CtlAckedReset and       *)
(* CtlAckedStop (on_control_acked), StopReq (stop_sending), OnStop         *)
(* (on_stop_sending), OpenLocal (open_stream, bidirectional), RecvMaxStreams *)
(* (on_max_streams) and CtlLostMsts (on_control_lost, MAX_STREAMS), AppReset *)
(* (reset), Finish (the                                                    *)
(* send half completing), ExtTo (the other users of the pool: send         *)
(* buffers, datagram queues, the early-data buffer, which the code charges *)
(* to the same pool), CloseAll. The state T holds the table: slots, the    *)
(* peer-opened and locally opened counters and the pool use of the         *)
(* others. The pool use of the streams is the chunks their rings hold.     *)
(*                                                                         *)
(* Scaling. The real constants are CH = 16384, RING = 1025, RR = 96,       *)
(* N = 100, B = the pool in chunks; the model is parameterised by *)
(* them and TLC runs them small. Offsets are bounded by MAXOFF (the real   *)
(* bound is 2^62 - 1); the model never produces a larger one.              *)
(*                                                                         *)
(* Retry. The code retries a deferred window grant after every release of *)
(* pool chunks (the end of settle, and Streams::regrant after the other    *)
(* users released); an earlier version retried it only after a consume,    *)
(* which stalled a stream when the application had nothing left to read.   *)
(* RETRY = FALSE is that earlier behaviour (a witness config).             *)
(*                                                                         *)
(* Meter. Each receive half measures what its own reader drains per       *)
(* round trip (r.m, MeterStep) and its window grows toward twice that      *)
(* (Target). Before #159 one meter measured the whole connection and every *)
(* stream took twice that rate as its window, so many streams together     *)
(* asked the pool for far more credit than it holds and their grants were  *)
(* deferred. PERSTREAM = FALSE sizes a stream from the connection's rate   *)
(* (the sum of the streams' rates), that earlier behaviour (a witness).    *)
(*                                                                         *)
(* The ledger (Unreceived, GU). A receive half counts the chunks its credit *)
(* may still claim: the first FIRSTK chunks of its window while the stream *)
(* has carried no data (Charged, FIRST_CHARGE in the code), its whole      *)
(* window from its first byte on. A window grant is made only while the   *)
(* ledger with it fits the pool. Admitting one more stream (a raise of the *)
(* stream credit, a peer stream beyond the credit, a local stream) asks    *)
(* less (8abd9451): that its first charge fits beside one first charge for *)
(* each open stream (AdmCharge: what each still claims, at most FirstW),   *)
(* so streams that carry data and stay open do not shut out new ones for   *)
(* the size of their windows. The ledger can so pass the pool by an        *)
(* admission, and when a stream first carries data (its first byte is      *)
(* never refused for the ledger); the pool itself never: a frame takes     *)
(* free chunks or is held back.                                            *)
(*                                                                         *)
(* Local streams. A bidirectional stream this endpoint opens has the receive *)
(* window the connection advertised, which cannot be smaller, so OpenLocal *)
(* opens it only when its first charge fits beside the credit granted       *)
(* (Streams_local.cfg is the finding this closed, now a passing check).    *)
(*                                                                         *)
(* Stream credit. The receiver tells the opener how many streams it admits *)
(* in all (T.ad.adv: the handshake value, raised by MAX_STREAMS), keeps the *)
(* first charges of the streams the opener has not opened yet in the pool  *)
(* (Resv), and the opener never opens beyond the limit it was given        *)
(* (T.ad.lim). The room is counted beside AdmCharge, like WindowsFit. A    *)
(* raise with no room catches the credit up with a peer that opened past  *)
(* it and reserves nothing. A raise is sent whenever the room grew: the   *)
(* cannot see streams the opener opened and has not written on, so a raise *)
(* held back for size could strand an opener that used all its credit     *)
(* (RefreshAdmitOld, the eighth rule before it, is for the witness         *)
(* Streams_raise_w.cfg only). A peer                                       *)
(* stream inside the credit is admitted with no pool test, however many    *)
(* lower ids its frame opens with it. The held-back rule below stays as    *)
(* the net for a peer that ignores the credit and for a full pool.         *)
(*                                                                         *)
(* Early opens (an optimistic dial). Before the peer's record is known    *)
(* the dialer may open streams past the limit it was given (T.ad.early,     *)
(* set by SetEarly: Streams::set_early; OpenLocal skips the limit while it  *)
(* is on). Each stream we open keeps its ordinal (Slot::ordinal: how many   *)
(* we had opened in all, itself included; 0 for a peer stream), and its     *)
(* data and its control frames (a reset, a stop request, a window update)  *)
(* wait until the limit covers that ordinal (CanSend: the test of           *)
(* Streams::refresh, so SendOut sends nothing for it and Pending gives none *)
(* of its control frames, CtlGate; before #432 only its data waited,        *)
(* CtlUngated). The establishment raises the limit to the peer's record    *)
(* and turns early off.                                                    *)
(*                                                                         *)
(* Held back streams. A peer stream the table has no room for yet is      *)
(* stored nowhere, answered with nothing and never acknowledged: Locate    *)
(* answers "Exhausted" and returns the table unchanged, so the opener's    *)
(* retransmission on the same id meets the table as the first arrival did  *)
(* and the stream is admitted once Admits holds. There is no refused queue. *)
(*                                                                         *)
(* Data bytes are not part of the state here; a frame carries `diff`, whether *)
(* its bytes differ from the bytes already stored where they overlap. The *)
(* content theorems are in Pinc/TransportStreams.lean.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CH, RING, RR, N, MAXREM, B, SWC, MSWC, PM, MAXOFF, RETRY, RemIds, LocIds, FIRSTK, RELEASE, PERSTREAM
\* the table's max_remote is config.max_streams.min(N), and Streams::adopt only lowers it: never more than the slots
ASSUME MAXREM \in 0..N

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

IsUni(id) == (id \div 2) % 2 = 1
IsLocal(id) == id % 2 = 1            \* this endpoint is the server
Class(id) == IF IsUni(id) THEN 1 ELSE 0
Idx(id) == id \div 4

HalfPool == (((B * CH) \div 2) \div CH) * CH
MaxStream == Min(MSWC, Min((RING - 1) * CH, HalfPool))
SW == Min(SWC, MaxStream)           \* the initial window; the ceiling is MaxStream

NewSlot == [id |-> -1, open |-> FALSE, held |-> {}, rs |-> <<>>, read |-> 0, hi |-> 0, contig |-> 0, fin |-> -1,
            limit |-> 0, size |-> 0, pend |-> FALSE, defer |-> FALSE, rst |-> -1, obs |-> FALSE,
            sdone |-> TRUE, srst |-> 0,
            stop |-> 0, qcode |-> -1, scode |-> -1, cnt |-> FALSE, sfl |-> FALSE, ord |-> 0,
            m |-> [start |-> -1, bytes |-> 0, rate |-> 0]]

WinC == ((SW + CH - 1) \div CH) * CH        \* the initial window in whole chunks
\* what the ledger counts for a stream that has carried no data, and keeps for each stream inside the credit
\* (FIRST_CHARGE: FIRSTK chunks, 4 in the code): the initial window or that, whichever is less
FirstW == Min(WinC, FIRSTK * CH)
\* how far into a window the ledger counts it (Recv::charged_demand): the first FIRSTK chunks while the stream has
\* carried no data, the whole window from its first byte on
Charged(r, l) == IF r.hi = 0 THEN Min(l, FIRSTK * CH) ELSE l
AdmitFit(f) == Max(Min(Max(f - 3, 0), f \div 2), Min(f, 1))   \* half of f windows, three left free, one at least when one fits
\* MAXREM is the limit the connection gives the peer: Streams::adopt, called by Connection::advertise with the
\* credit record's max_streams (Limits::streams at the facade), lowers the table's max_remote to it
CapLive == Min(MAXREM, Max(N \div 2, 1))     \* the live peer streams: at most half the slots
\* the earlier cap, which never saw the configured limit (only the table's own default of 100), for Streams_cap_w.cfg
CapIgnoringLimit == Max(N \div 2, 1)
Adv0 == Min(CapLive, AdmitFit((B * CH) \div FirstW))

\* hw is the mark of the slots (Streams::used in the code): the highest slot a stream holds, 0 with none. The scans a
\* connection makes for each packet (next_hot, pending_control, poll_writable, grant, granted_unreceived, find) stop
\* at it, so a slot above it must be new: it has nothing to send, no control frame and no credit outstanding. Taking a slot raises the mark to it; freeing the top
\* slot walks it down to the highest slot still held (MarkOnFree), freeing a lower one leaves it.
\* Streams_mark_w.cfg plants a free that lowers it below a slot still held (MarkOnFreeLow).
TopHeld(S) == IF \E k \in 1..N : S[k].id # -1
              THEN CHOOSE k \in 1..N : S[k].id # -1 /\ \A j \in (k + 1)..N : S[j].id = -1
              ELSE 0
MarkOnFree(S, hw, i) == IF i = hw THEN TopHeld(S) ELSE hw
MarkOnFreeLow(S, hw, i) == Min(hw, i - 1)
Init0 == [slots |-> [i \in 1..N |-> NewSlot], rn |-> [c \in 0..1 |-> 0], lo |-> [c \in 0..1 |-> 0],
          rl |-> 0, ll |-> 0, ext |-> 0, hw |-> 0,
          ad |-> [lim |-> PM, adv |-> Adv0, pend |-> FALSE, early |-> FALSE]]

(* ---- the range set (ranges.rs): sorted, disjoint, non-adjacent intervals, at most RR ---- *)
InsertR(rs, s, e) ==
    IF s >= e THEN [ok |-> TRUE, rs |-> rs]
    ELSE LET n == Len(rs)
             from == Cardinality({k \in 1..n : rs[k][2] < s})
             to == Cardinality({k \in 1..n : rs[k][1] <= e})
             merged == IF from < to THEN <<Min(rs[from + 1][1], s), Max(rs[to][2], e)>> ELSE <<s, e>>
             newlen == n - (to - from) + 1
         IN IF newlen > RR THEN [ok |-> FALSE, rs |-> rs]
            ELSE [ok |-> TRUE, rs |-> SubSeq(rs, 1, from) \o <<merged>> \o SubSeq(rs, to + 1, n)]

Overlaps(rs, lo, e) == \E k \in 1..Len(rs) : rs[k][1] < e /\ rs[k][2] > lo
First0(rs) == IF Len(rs) > 0 /\ rs[1][1] = 0 THEN rs[1][2] ELSE 0

(* ---- the receive half (recv.rs, flow.rs) ---- *)
Status(r) == IF r.rst # -1 THEN "reset" ELSE IF r.fin # -1 /\ r.fin = r.read THEN "fin" ELSE "open"
Readable(r) == IF r.rst # -1 THEN 0 ELSE Max(r.contig - r.read, 0)
RecvDone(r) == ~r.open \/ (r.obs /\ Status(r) # "open")
SendDone(r) == r.sdone \/ r.srst = 3

(* pool_demand: the pool bytes credit up to l may still claim: the chunks of the span from the read position to l not yet held *)
PoolDemand(r, l) ==
    LET reach == IF r.fin = -1 THEN l ELSE Min(r.fin, l)
    IN IF ~r.open \/ reach <= r.read THEN 0
       ELSE LET span == (reach - 1) \div CH - r.read \div CH + 1
            IN Max(span - Cardinality(r.held), 0) * CH
Unreceived(r) == PoolDemand(r, Charged(r, r.limit))

\* the limit the window is due to move to, once an eighth of the window was freed, whether or not the stream was asked
\* to stop: the rule before c3ea10e1 (the witness Streams_stop_raise_w.cfg)
DueOld(r) ==
    IF ~r.open THEN -1
    ELSE LET cap == IF r.fin = -1 THEN MAXOFF ELSE r.fin
             cand == Min(r.read + r.size, cap)
         IN IF cand > r.limit /\ cand >= r.limit + r.size \div 8 THEN cand ELSE -1
(* due: the limit the window is due to move to; none for a stream asked to stop (c3ea10e1): its sender was told to
   reset and needs no credit for that, and what it still sends is dropped *)
Due(r) == IF r.stop # 0 THEN -1 ELSE DueOld(r)

(* ---- the pool ---- *)
HeldTotal(T) == LET f[i \in 0..N] == IF i = 0 THEN 0 ELSE f[i - 1] + Cardinality(T.slots[i].held) IN f[N]
Used(T) == HeldTotal(T) + T.ext
AvailC(T) == B - Used(T)
Avail(T) == AvailC(T) * CH
GU(T) == LET f[i \in 0..N] == IF i = 0 THEN 0 ELSE f[i - 1] + Unreceived(T.slots[i]) IN f[N]
AdmittedN(T) == T.rn[0] + T.rn[1]                    \* the peer streams admitted in all
CreditLeft(T) == Max(T.ad.adv - AdmittedN(T), 0)     \* the streams the peer may still open inside the credit
Resv(T) == CreditLeft(T) * FirstW                     \* the pool bytes kept for them

SetSlot(T, i, r) == [T EXCEPT !.slots[i] = r]
FindSlot(T, id) == IF \E i \in 1..N : T.slots[i].id = id THEN CHOOSE i \in 1..N : T.slots[i].id = id ELSE 0
Hot(r) == (r.pend /\ r.open) \/ r.srst = 1 \/ r.stop = 1
\* Streams::refresh: the data and the control frames of a stream we opened wait until the limit covers its ordinal
\* (always covered for a peer stream, whose ordinal is 0)
CanSend(T, i) == T.slots[i].ord <= T.ad.lim
\* the gate on a slot's control frames (#432); CtlUngated is the rule before it, for the witness Streams_early_ctl_w.cfg
CtlGate(T, i) == CanSend(T, i)
CtlUngated(T, i) == TRUE
\* the slot may give a control frame now
CtlDue(T, i) == Hot(T.slots[i]) /\ CtlGate(T, i)
AnyDefer(T) == \E i \in 1..N : T.slots[i].defer

(* ---- the window grant (Streams::grant) ---- *)
GrantOne(T, i, first) ==
    LET r == T.slots[i] IN
    IF ~r.open \/ ~(i = first \/ r.defer) THEN T
    ELSE LET r1 == r   \* the window size moved when its own reader consumed (Consume)
             c == Due(r1)
         IN IF c = -1 THEN SetSlot(T, i, [r1 EXCEPT !.defer = FALSE])
            ELSE LET demand == GU(T) - Unreceived(r) + PoolDemand(r1, Charged(r1, c))
                 IN IF demand + Resv(T) <= Avail(T)
                       THEN SetSlot(T, i, [r1 EXCEPT !.limit = c, !.pend = TRUE, !.defer = FALSE])
                       ELSE SetSlot(T, i, [r1 EXCEPT !.defer = TRUE])
GrantFrom(T, i, first) ==
    LET f[k \in 0..N] == IF k = 0 THEN T ELSE GrantOne(f[k - 1], k, first) IN f[N]
GrantRun(T, first) == GrantFrom(T, 1, first)
(* admit_room / refresh_admit (Streams): the streams that could be admitted now, and the raise to queue *)
FreeSlots(T) == Cardinality({i \in 1..N : T.slots[i].id = -1})
(* Streams::admitted_charge: what the open streams count for when one more stream is admitted, for each the credit it
   may still claim but at most one first charge (8abd9451). A window grant counts the whole ledger GU *)
AdmCharge(T) == LET f[i \in 0..N] == IF i = 0 THEN 0 ELSE f[i - 1] + Min(Unreceived(T.slots[i]), FirstW) IN f[N]
AdmitRoom(T) == LET fit == Max(Avail(T) - AdmCharge(T), 0) \div FirstW
                IN Min(Min(Max(CapLive - T.rl, 0), FreeSlots(T)), AdmitFit(fit))
\* The room is at most the cap left and the free slots, so when those cannot take the credit past what was advertised
\* nothing is raised and the pool sums are not taken (the same result, fewer evaluations: the model checker spends most
\* of a step in them)
RoomBound(T) == Min(Max(CapLive - T.rl, 0), FreeSlots(T))
RefreshAdmit(T) ==
    IF AdmittedN(T) + RoomBound(T) <= T.ad.adv THEN T
    ELSE LET now == AdmittedN(T) + AdmitRoom(T)
         IN IF now > T.ad.adv THEN [T EXCEPT !.ad.adv = now, !.ad.pend = TRUE] ELSE T
\* the rule before 0d36b306: a raise waited until the room grew by an eighth of the credit last given (one stream at
\* least) unless the opener had used all of it. The table no longer keeps adv_at (the streams admitted when adv was
\* set), so it is taken as 0, its value until the first raise: exact up to the first raise, where Streams_raise_w.cfg
\* finds the hold
RefreshAdmitOld(T) ==
    LET now == AdmittedN(T) + AdmitRoom(T)
        usedUp == T.ad.adv <= AdmittedN(T)
        step == Max(T.ad.adv \div 8, 1)
    IN IF now > T.ad.adv /\ (usedUp \/ now - T.ad.adv >= step)
          THEN [T EXCEPT !.ad.adv = now, !.ad.pend = TRUE]
          ELSE T
Regrant(T) == LET T1 == RefreshAdmit(T) IN IF RETRY /\ AnyDefer(T1) THEN GrantRun(T1, 0) ELSE T1

(* ---- slots ---- *)
\* A peer stream stops counting against the peer's limit (T.rl) once what it sent is whole and read (RecvDone) and our
\* answer has left with nothing queued to be sent again (Flushed): Streams::release_limit, called at the end of settle
\* and after a stream frame left (SendOut). Its slot is kept until both halves are done. cnt says the stream counts
\* (Slot::counted); sfl says the send half's end has left with no lost range queued (the part of Send::flushed that
\* sdone and srst do not show). Neither is on the wire: the trace check carries them as hidden state.
\* RELEASE = FALSE turns the release off (ReleaseLimit and SendOut change nothing, so every live peer stream counts and
\* cnt is always TRUE): the earlier table, whose state space the large Streams configs keep at the size they were cut
\* to. The rule is checked with RELEASE = TRUE in the small configs (Streams_release, Streams_cap, Streams_mark,
\* Streams_local_ctl and the witnesses) and by the trace, which runs the code with it on. With it on a stream whose
\* reset was sent stops counting too, so the peer may open more streams and the state space grows several times over.
Flushed(r) == r.sdone \/ r.srst >= 2 \/ r.sfl
ReleaseLimit(T, i) ==
    LET r == T.slots[i]
    IN IF ~RELEASE \/ r.id = -1 \/ IsLocal(r.id) \/ ~r.cnt \/ ~RecvDone(r) \/ ~Flushed(r) THEN T
       ELSE [SetSlot(T, i, [r EXCEPT !.cnt = FALSE]) EXCEPT !.rl = Max(@ - 1, 0)]
FreeSlot(T, i) ==
    LET id == T.slots[i].id
        S1 == [T.slots EXCEPT ![i] = NewSlot]
        T1 == [T EXCEPT !.slots = S1, !.hw = MarkOnFree(S1, T.hw, i)]
    IN IF id = -1 THEN T1
       ELSE IF IsLocal(id) THEN [T1 EXCEPT !.ll = Max(@ - 1, 0)]
       ELSE IF T.slots[i].cnt THEN [T1 EXCEPT !.rl = Max(@ - 1, 0)]   \* a released stream is not counted again
       ELSE T1
Settle(T, i) ==
    LET r == T.slots[i]
    IN Regrant(IF RecvDone(r) /\ SendDone(r) THEN FreeSlot(T, i) ELSE ReleaseLimit(T, i))

FirstFree(T) == IF \E i \in 1..N : T.slots[i].id = -1 THEN CHOOSE i \in 1..N : (T.slots[i].id = -1 /\ \A j \in 1..(i - 1) : T.slots[j].id # -1) ELSE 0
AllocSlot(T, id) ==
    LET i == FirstFree(T)
        local == IsLocal(id)
        recvOn == ~IsUni(id) \/ ~local
        sendOn == ~IsUni(id) \/ local
        r == [NewSlot EXCEPT !.id = id, !.open = recvOn, !.limit = IF recvOn THEN SW ELSE 0,
                              !.size = IF recvOn THEN SW ELSE 0, !.sdone = ~sendOn, !.cnt = TRUE,
                              !.ord = IF local THEN T.lo[0] + T.lo[1] + 1 ELSE 0]
        T1 == [SetSlot(T, i, r) EXCEPT !.hw = Max(@, i)]   \* taking a slot writes it: the mark rises to it
    IN IF local THEN [T1 EXCEPT !.ll = @ + 1] ELSE [T1 EXCEPT !.rl = @ + 1]

(* ---- admission of peer streams (Streams::admits, locate) ---- *)
(* the first charges of k new streams fit beside one first charge for each open stream (Streams::windows_fit): the one
   test for a peer stream beyond the credit and for a local one *)
WindowsFit(T, k) == AdmCharge(T) + k * FirstW <= Avail(T)
(* inside the credit no pool test is made: the new streams take no chunk and the credit kept their first charges *)
Admits(T, c, next, count) ==
    LET free == Cardinality({i \in 1..N : T.slots[i].id = -1})
    IN T.rl + count <= MAXREM /\ free >= count
       /\ (AdmittedN(T) + count <= T.ad.adv \/ WindowsFit(T, Max(count, CreditLeft(T))))

(* Locate: the new table, the slot (0 = none), the error ("ok" when none) *)
Locate(T, id) ==
    LET c == Class(id)
        ix == Idx(id)
        next == T.rn[c]
    IN IF IsLocal(id)
          THEN IF ix >= T.lo[c] THEN [t |-> T, i |-> 0, err |-> "StreamState"]
               ELSE [t |-> T, i |-> FindSlot(T, id), err |-> "ok"]
       ELSE IF ix < next THEN [t |-> T, i |-> FindSlot(T, id), err |-> "ok"]
       ELSE IF ix >= next + MAXREM THEN [t |-> T, i |-> 0, err |-> "StreamLimit"]
       ELSE IF ~Admits(T, c, next, ix - next + 1) THEN [t |-> T, i |-> 0, err |-> "Exhausted"]
       ELSE LET f[k \in next..ix] ==
                    IF k = next THEN AllocSlot(T, k * 4 + (id % 4)) ELSE AllocSlot(f[k - 1], k * 4 + (id % 4))
                T2 == [f[ix] EXCEPT !.rn[c] = ix + 1]
            IN [t |-> T2, i |-> FindSlot(T2, id), err |-> "ok"]

(* ---- on_data (recv.rs) ---- *)
(* recv.rs discard: a stream given up whose end is known drops every byte held and counts as read to its end, as a
   reset does but without one *)
Discard(r) == IF r.fin # -1 /\ r.rst = -1
              THEN [r EXCEPT !.read = r.fin, !.contig = r.fin, !.held = {}, !.rs = <<>>, !.obs = TRUE]
              ELSE r

(* the receive of a stream frame; End is the rule for the end arriving on a stream asked to stop *)
OnDataWith(T, r, off, len, fin, diff, End(_)) ==
    LET e == off + len
        lo == Max(off, r.read)
        first == lo \div CH
        last == (e - 1) \div CH
        missing == {k \in first..last : k \notin r.held}
        ins == InsertR(r.rs, lo, e)
        stored == [r EXCEPT !.held = r.held \cup (first..last), !.rs = ins.rs, !.contig = First0(ins.rs)]
        store == IF lo >= e THEN [r |-> r, err |-> "ok"]
                 ELSE IF last - r.read \div CH >= RING THEN [r |-> r, err |-> "FlowControl"]
                 ELSE IF lo < r.hi /\ diff /\ Overlaps(r.rs, lo, e) THEN [r |-> r, err |-> "Conflict"]
                 ELSE IF Cardinality(missing) > AvailC(T) THEN [r |-> r, err |-> "Exhausted"]
                 ELSE IF ~ins.ok THEN [r |-> r, err |-> "Fragmented"]
                 ELSE [r |-> stored, err |-> "ok"]
        done0 == [store.r EXCEPT !.hi = Max(@, e), !.fin = IF fin THEN e ELSE @]
        done == IF fin /\ r.stop # 0 THEN End(done0) ELSE done0
    IN IF e > MAXOFF THEN [r |-> r, err |-> "FlowControl"]
       ELSE IF r.fin # -1 /\ (e > r.fin \/ (fin /\ e # r.fin)) THEN [r |-> r, err |-> "FinalSize"]
       ELSE IF r.fin = -1 /\ fin /\ e < r.hi THEN [r |-> r, err |-> "FinalSize"]
       ELSE IF e > r.limit THEN [r |-> r, err |-> "FlowControl"]
       ELSE IF r.rst = -1 /\ store.err # "ok" THEN [r |-> r, err |-> store.err]
       ELSE IF r.rst = -1 THEN [r |-> done, err |-> "ok"]
       ELSE [r |-> [r EXCEPT !.hi = Max(@, e), !.fin = IF fin THEN e ELSE @], err |-> "ok"]

\* the end arriving on a stream asked to stop discards it (ff7ad474): nothing else would end it; every byte arrived, so
\* the request is over (710afb61): one not yet sent is never sent and a lost one is not sent again
EndStop(d) == [Discard(d) EXCEPT !.stop = 3, !.qcode = -1]
OnData(T, r, off, len, fin, diff) == OnDataWith(T, r, off, len, fin, diff, EndStop)
\* the rule before 710afb61 (the witness Streams_stop_end_w.cfg): the stream is discarded and its request stays
OnDataStopOld(T, r, off, len, fin, diff) == OnDataWith(T, r, off, len, fin, diff, Discard)
\* the rule before ff7ad474 (the witness Streams_stop_w.cfg): the end arriving on a stream asked to stop is kept
EndKept(d) == d
OnDataOld(T, r, off, len, fin, diff) == OnDataWith(T, r, off, len, fin, diff, EndKept)

(* Frame: Streams::on_stream_frame, the new table and the error *)
Frame(T, id, off, len, fin, diff) ==
    LET L == Locate(T, id)
    IN IF L.err # "ok" \/ L.i = 0 THEN [t |-> L.t, err |-> L.err]
       ELSE LET D == OnData(L.t, L.t.slots[L.i], off, len, fin, diff)
            IN [t |-> Settle(SetSlot(L.t, L.i, D.r), L.i), err |-> D.err]

(* ---- on_reset (recv.rs) ---- *)
(* the peer's reset; ack says whether an accepted reset ends a stop request that waits or was sent *)
OnResetRWith(r, code, fs, ack) ==
    IF fs > MAXOFF \/ (r.fin # -1 /\ r.fin # fs) \/ fs < r.hi THEN [r |-> r, err |-> "FinalSize"]
    ELSE IF fs > r.limit THEN [r |-> r, err |-> "FlowControl"]
    ELSE IF r.rst # -1 THEN [r |-> r, err |-> "ok"]
    ELSE LET d == [r EXCEPT !.hi = fs, !.fin = fs, !.rst = code, !.read = fs, !.contig = fs, !.held = {}, !.rs = <<>>]
         IN [r |-> IF ack /\ r.stop \in {1, 2} THEN [d EXCEPT !.stop = 3, !.qcode = -1] ELSE d, err |-> "ok"]
\* the sender ended the stream: a stop request that waits or was sent is over (29fb6aa7), so one not yet sent is never
\* sent and a lost one is not sent again
OnResetR(r, code, fs) == OnResetRWith(r, code, fs, TRUE)
\* the rule before 29fb6aa7 (the witnesses Streams_stop_frame.cfg, Streams_stop_reset_w.cfg): the stop state is left
OnResetROld(r, code, fs) == OnResetRWith(r, code, fs, FALSE)
Reset(T, id, code, fs) ==
    LET L == Locate(T, id)
    IN IF L.err # "ok" \/ L.i = 0 THEN [t |-> L.t, err |-> L.err]
       ELSE LET D == OnResetR(L.t.slots[L.i], code, fs)
            IN [t |-> Settle(SetSlot(L.t, L.i, D.r), L.i), err |-> D.err]

(* ---- consume (recv.rs, flow.rs Meter, Streams::consume) ---- *)
MeterStep(m, n, now, srtt) ==
    LET st == IF m.start = -1 THEN now ELSE m.start
        by == m.bytes + n
        el == IF now >= st THEN now - st ELSE 0
    IN IF srtt > 0 /\ el >= srtt THEN [start |-> now, bytes |-> 0, rate |-> (by * srtt) \div el]
       ELSE [start |-> st, bytes |-> by, rate |-> m.rate]

\* The rate a window is sized from. With PERSTREAM (the code) it is what this stream's own reader drained per round
\* trip; PERSTREAM = FALSE is the connection's rate, the sum over the streams with this one's new rate in place, as one
\* meter of the whole connection measured it before #159 (the witness config Streams_meter_w).
ConnRate(T, i, rate) == LET f[k \in 0..N] == IF k = 0 THEN 0
                                             ELSE f[k - 1] + (IF k = i THEN rate ELSE T.slots[k].m.rate)
                        IN f[N]
SizeRate(T, i, rate) == IF PERSTREAM THEN rate ELSE ConnRate(T, i, rate)
\* Streams::consume: the window size a rate asks for, twice the rate, never below the initial window nor above the
\* ceiling
Target(rate) == Min(Max(rate * 2, SW), MaxStream)

Consume(T, id, n, now, srtt) ==
    LET i == FindSlot(T, id)
        r == IF i = 0 THEN NewSlot ELSE T.slots[i]
        nr == r.read + n
        cut == r.fin # -1 /\ r.fin = nr
        \* the stream's own meter takes the bytes read
        m2 == MeterStep(r.m, n, now, srtt)
        r1 == [r EXCEPT !.read = nr,
                        !.held = IF cut THEN {} ELSE r.held \ (r.read \div CH..(nr \div CH - 1)),
                        !.rs = IF cut THEN <<>> ELSE r.rs,
                        !.m = m2,
                        !.size = Max(r.size, Target(SizeRate(T, i, m2.rate)))]
        r2 == [r1 EXCEPT !.obs = r1.obs \/ Status(r1) # "open"]
        T1 == SetSlot(T, i, r2)
    IN IF i = 0 THEN [t |-> T, err |-> "UnknownStream"]
       ELSE IF n > Readable(r) THEN [t |-> T, err |-> "InvalidConsume"]
       ELSE [t |-> Settle(GrantRun(T1, i), i), err |-> "ok"]

(* ---- control frames ---- *)
(* Pending: pending_control; the table after, the frame (kind "none", "reset", "stop" or "msd") and its number:
   the limit of an msd, the error code of a reset or a stop. The first slot with a frame to send whose stream the
   peer's limit covers (CtlDue) gives one: its stream reset first, then its stop request, then its limit. *)
PendingSlot(T) == IF \E i \in 1..N : CtlDue(T, i) THEN CHOOSE i \in 1..N : (CtlDue(T, i) /\ \A j \in 1..(i - 1) : ~CtlDue(T, j)) ELSE 0
Pending(T) ==
    IF T.ad.pend THEN [t |-> [T EXCEPT !.ad.pend = FALSE], kind |-> "msts", id |-> -1, max |-> T.ad.adv]
    ELSE LET i == PendingSlot(T)
        r == IF i = 0 THEN NewSlot ELSE T.slots[i]
    IN IF i = 0 THEN [t |-> T, kind |-> "none", id |-> -1, max |-> 0]
       ELSE IF r.srst = 1 THEN [t |-> SetSlot(T, i, [r EXCEPT !.srst = 2]), kind |-> "reset", id |-> r.id, max |-> r.scode]
       ELSE IF r.stop = 1 THEN [t |-> SetSlot(T, i, [r EXCEPT !.stop = 2]), kind |-> "stop", id |-> r.id, max |-> r.qcode]
       ELSE [t |-> SetSlot(T, i, [r EXCEPT !.pend = FALSE]), kind |-> "msd", id |-> r.id, max |-> r.limit]

CtlLostMsd(T, id, max) ==
    LET i == FindSlot(T, id)
    IN IF i = 0 THEN T
       ELSE IF max >= T.slots[i].limit THEN SetSlot(T, i, [T.slots[i] EXCEPT !.pend = TRUE]) ELSE T
CtlLostReset(T, id) ==
    LET i == FindSlot(T, id)
    IN IF i = 0 THEN T
       ELSE IF T.slots[i].srst = 2 THEN SetSlot(T, i, [T.slots[i] EXCEPT !.srst = 1]) ELSE T
CtlAckedReset(T, id) ==
    LET i == FindSlot(T, id)
    IN IF i = 0 THEN T
       ELSE LET acked == T.slots[i].srst \in {1, 2}
            IN Settle(SetSlot(T, i, [T.slots[i] EXCEPT !.srst = IF acked THEN 3 ELSE @, !.scode = IF acked THEN -1 ELSE @]), i)
\* a lost stop request is sent again unless the sender ended the stream meanwhile
CtlLostStop(T, id) ==
    LET i == FindSlot(T, id)
    IN IF i = 0 THEN T
       ELSE IF T.slots[i].stop = 2 /\ T.slots[i].rst = -1 /\ T.slots[i].fin = -1
               THEN SetSlot(T, i, [T.slots[i] EXCEPT !.stop = 1]) ELSE T
CtlAckedStop(T, id) ==
    LET i == FindSlot(T, id)
    IN IF i = 0 THEN T
       ELSE IF T.slots[i].stop \in {1, 2} THEN SetSlot(T, i, [T.slots[i] EXCEPT !.stop = 3, !.qcode = -1]) ELSE T

(* ---- the send half, as far as the receive side sees it ---- *)
\* the opener: a stream opens only inside the credit the peer gave (T.ad.lim, in all), unless opens are early (the
\* peer's limit is not known yet), and with its slot and its window in the pool beside the slots and windows kept for
\* the peer's credit
OpenLocal(T) ==
    LET c == 0
        id == T.lo[c] * 4 + 1
    IN IF (~T.ad.early /\ T.lo[0] + T.lo[1] >= T.ad.lim) \/ FirstFree(T) = 0 \/ FreeSlots(T) <= CreditLeft(T)
          \/ ~WindowsFit(T, CreditLeft(T) + 1) THEN T
       ELSE [AllocSlot(T, id) EXCEPT !.lo[c] = @ + 1]
\* a MAX_STREAMS frame arrived: the limit on the streams we may open only grows
RecvMaxStreams(T, l) == [T EXCEPT !.ad.lim = Max(@, l)]
\* Streams::set_early: opens may pass the limit (on), or no longer
SetEarly(T, on) == [T EXCEPT !.ad.early = on]
\* the establishment of an optimistic dial: the peer's record raises the limit (set_peer_limits), then early ends
Establish(T, l) == SetEarly(RecvMaxStreams(T, l), FALSE)
\* a MAX_STREAMS frame was lost: send the current limit again unless a later one superseded it
CtlLostMsts(T, l) == IF l >= T.ad.adv THEN [T EXCEPT !.ad.pend = TRUE] ELSE T
SendOpen(r) == ~(IsUni(r.id) /\ ~IsLocal(r.id))
(* A stream frame left on slot i (pick.rs, next_hot): the send half's end has gone with nothing queued again (f), or
   not yet, or a lost range waits to be sent again (not f); then release_limit. Only a send half that can still send a
   stream frame is touched, and a stream we opened past the limit sends nothing (CanSend; its control frames wait the
   same way, CtlGate in Pending). *)
SendOut(T, i, f) ==
    LET r == T.slots[i]
    IN IF ~RELEASE \/ r.id = -1 \/ ~SendOpen(r) \/ r.sdone \/ r.srst # 0 \/ ~CanSend(T, i) THEN T
       ELSE ReleaseLimit(SetSlot(T, i, [r EXCEPT !.sfl = f]), i)
(* Streams::reset: queue a stream reset on the send half, the send buffers released (ext2 <= ext) *)
AppReset(T, id, code, ext2) ==
    LET i == FindSlot(T, id)
        r == IF i = 0 THEN NewSlot ELSE T.slots[i]
        change == SendOpen(r) /\ r.srst = 0 /\ ~r.sdone
        T1 == IF change THEN [SetSlot(T, i, [r EXCEPT !.srst = 1, !.scode = code]) EXCEPT !.ext = ext2] ELSE T
    IN IF i = 0 THEN T ELSE Settle(T1, i)
(* Streams::stop_sending (table/giving_up.rs) and recv.rs request_stop: ask the peer to stop sending on a stream we
   receive on, queued once; nothing if the sender reset the stream. A stream whose end already arrived is not asked: it
   is discarded and settled, so it leaves the table once its send half is done and its place in the peer's limit is
   given back (ff7ad474) *)
StopReq(T, id, code) ==
    LET i == FindSlot(T, id)
        r == IF i = 0 THEN NewSlot ELSE T.slots[i]
    IN IF i = 0 THEN [t |-> T, err |-> "UnknownStream"]
       ELSE IF ~r.open THEN [t |-> T, err |-> "StreamState"]
       ELSE IF r.rst # -1 THEN [t |-> T, err |-> "ok"]
       ELSE IF r.fin # -1 THEN [t |-> Settle(SetSlot(T, i, Discard(r)), i), err |-> "ok"]
       ELSE IF r.stop = 0 THEN [t |-> SetSlot(T, i, [r EXCEPT !.stop = 1, !.qcode = code]), err |-> "ok"]
       ELSE [t |-> T, err |-> "ok"]
\* the rule before ff7ad474 (the witness Streams_stop_w.cfg): a stream whose end arrived is left as it is
StopReqOld(T, id, code) ==
    LET i == FindSlot(T, id)
        r == IF i = 0 THEN NewSlot ELSE T.slots[i]
    IN IF i = 0 THEN [t |-> T, err |-> "UnknownStream"]
       ELSE IF ~r.open THEN [t |-> T, err |-> "StreamState"]
       ELSE IF r.rst = -1 /\ r.fin = -1 /\ r.stop = 0
               THEN [t |-> SetSlot(T, i, [r EXCEPT !.stop = 1, !.qcode = code]), err |-> "ok"]
       ELSE [t |-> T, err |-> "ok"]
(* Streams::on_stop_sending: a stop request arrived for a stream we send on. The peer stream is located (opened
   implicitly if new) and, if its send half can still be stopped, reset with the peer's code; fresh says it was. *)
OnStop(T, id, code, ext2) ==
    IF IsUni(id) /\ ~IsLocal(id) THEN [t |-> T, err |-> "StreamState", fresh |-> FALSE]
    ELSE LET L == Locate(T, id)
         IN IF L.err # "ok" THEN [t |-> L.t, err |-> L.err, fresh |-> FALSE]
            ELSE IF L.i = 0 THEN [t |-> L.t, err |-> "ok", fresh |-> FALSE]
            ELSE LET r == L.t.slots[L.i]
                     fresh == SendOpen(r) /\ r.srst = 0 /\ ~r.sdone
                     T1 == IF fresh THEN [SetSlot(L.t, L.i, [r EXCEPT !.srst = 1, !.scode = code]) EXCEPT !.ext = ext2]
                                    ELSE L.t
                 IN [t |-> Settle(T1, L.i), err |-> "ok", fresh |-> fresh]
(* acknowledgements free send buffers (ext2 <= ext); done: the whole send half is acknowledged, the end too *)
Finish(T, id, ext2, done) ==
    LET i == FindSlot(T, id)
    IN IF i = 0 THEN T
       ELSE Settle([SetSlot(T, i, [T.slots[i] EXCEPT !.sdone = @ \/ (done /\ T.slots[i].srst = 0)]) EXCEPT !.ext = ext2], i)
(* the other users of the pool change their hold to ext2; a release lets the deferred grants go *)
ExtTo(T, ext2) ==
    IF ext2 > T.ext /\ ext2 - T.ext > AvailC(T) THEN T
    ELSE IF ext2 >= T.ext THEN [T EXCEPT !.ext = ext2]
    ELSE Regrant([T EXCEPT !.ext = ext2])
CloseAll(T, ext2) == [Init0 EXCEPT !.ext = ext2, !.lo = T.lo, !.rn = T.rn, !.ad = T.ad]
=============================================================================
