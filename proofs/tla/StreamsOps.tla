------------------------------ MODULE StreamsOps ------------------------------
(***************************************************************************)
(* The operations of vinc-transport stream/table.rs, recv.rs, flow.rs,     *)
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
(* peer-opened and locally opened counters, the pool use                  *)
(* of the others, the window target and the delivery meter. The pool use   *)
(* of the streams is the number of chunks their rings hold.                *)
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
(* The ledger (Unreceived, GU). A receive half counts the chunks its credit *)
(* may still claim: the first FIRSTK chunks of its window while the stream *)
(* has carried no data (Charged, FIRST_CHARGE in the code), its whole      *)
(* window from its first byte on. A window grant, a raise of the stream    *)
(* credit and a local stream are made only while the ledger with them fits *)
(* the pool; the first byte of a stream is never refused for the ledger,   *)
(* so the ledger can pass the pool then (the pool itself never: a frame    *)
(* takes free chunks or is held back). With FIRSTK at or above the windows *)
(* this is the rule that charged the whole window at admission.            *)
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
(* (T.ad.lim). A raise is sent when the room grew by an eighth of the      *)
(* credit last given, or at once when the opener used all of it. A peer    *)
(* stream inside the credit is admitted with no pool test, however many    *)
(* lower ids its frame opens with it. The held-back rule below stays as    *)
(* the net for a peer that ignores the credit and for a full pool.         *)
(*                                                                         *)
(* Held back streams. A peer stream the table has no room for yet is      *)
(* stored nowhere, answered with nothing and never acknowledged: Locate    *)
(* answers "Exhausted" and returns the table unchanged, so the opener's    *)
(* retransmission on the same id meets the table as the first arrival did  *)
(* and the stream is admitted once Admits holds. There is no refused queue. *)
(*                                                                         *)
(* Data bytes are not part of the state here; a frame carries `diff`, whether *)
(* its bytes differ from the bytes already stored where they overlap. The *)
(* content theorems are in Vinc/TransportStreams.lean.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CH, RING, RR, N, MAXREM, B, SWC, MSWC, PM, MAXOFF, RETRY, RemIds, LocIds, FIRSTK

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
            stop |-> 0, qcode |-> -1, scode |-> -1]

WinC == ((SW + CH - 1) \div CH) * CH        \* the initial window in whole chunks
\* what the ledger counts for a stream that has carried no data, and keeps for each stream inside the credit
\* (FIRST_CHARGE: FIRSTK chunks, 4 in the code): the initial window or that, whichever is less
FirstW == Min(WinC, FIRSTK * CH)
\* how far into a window the ledger counts it (Recv::charged_demand): the first FIRSTK chunks while the stream has
\* carried no data, the whole window from its first byte on
Charged(r, l) == IF r.hi = 0 THEN Min(l, FIRSTK * CH) ELSE l
AdmitFit(f) == Max(Min(Max(f - 3, 0), f \div 2), Min(f, 1))   \* half of f windows, three left free, one at least when one fits
\* MAXREM is the limit the connection gives the peer: Streams::limit_remote, called by Connection::base with the
\* credit record's max_streams (Limits::streams at the facade), lowers the table's max_remote to it
CapLive == Min(MAXREM, Max(N \div 2, 1))     \* the live peer streams: at most half the slots
\* the earlier cap, which never saw the configured limit (only the table's own default of 100), for Streams_cap_w.cfg
CapIgnoringLimit == Max(N \div 2, 1)
Adv0 == Min(CapLive, AdmitFit((B * CH) \div FirstW))

Init0 == [slots |-> [i \in 1..N |-> NewSlot], rn |-> [c \in 0..1 |-> 0], lo |-> [c \in 0..1 |-> 0],
          rl |-> 0, ll |-> 0, ext |-> 0, tgt |-> SW,
          m |-> [start |-> -1, bytes |-> 0, rate |-> 0],
          ad |-> [lim |-> PM, adv |-> Adv0, at |-> 0, pend |-> FALSE]]

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

(* due: the limit the window is due to move to, once an eighth of the window was freed *)
Due(r) ==
    IF ~r.open THEN -1
    ELSE LET cap == IF r.fin = -1 THEN MAXOFF ELSE r.fin
             cand == Min(r.read + r.size, cap)
         IN IF cand > r.limit /\ cand >= r.limit + r.size \div 8 THEN cand ELSE -1

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
AnyDefer(T) == \E i \in 1..N : T.slots[i].defer

(* ---- the window grant (Streams::grant) ---- *)
GrantOne(T, i, first) ==
    LET r == T.slots[i] IN
    IF ~r.open \/ ~(i = first \/ r.defer) THEN T
    ELSE LET r1 == [r EXCEPT !.size = Max(r.size, T.tgt)]
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
AdmitRoom(T) == LET fit == Max(Avail(T) - GU(T), 0) \div FirstW
                IN Min(Min(Max(CapLive - T.rl, 0), FreeSlots(T)), AdmitFit(fit))
RefreshAdmit(T) ==
    LET now == AdmittedN(T) + AdmitRoom(T)
        usedUp == T.ad.adv <= AdmittedN(T)
        step == Max((T.ad.adv - T.ad.at) \div 8, 1)
    IN IF now > T.ad.adv /\ (usedUp \/ now - T.ad.adv >= step)
          THEN [T EXCEPT !.ad.adv = now, !.ad.at = AdmittedN(T), !.ad.pend = TRUE]
          ELSE T
Regrant(T) == LET T1 == RefreshAdmit(T) IN IF RETRY /\ AnyDefer(T1) THEN GrantRun(T1, 0) ELSE T1

(* ---- slots ---- *)
FreeSlot(T, i) ==
    LET id == T.slots[i].id
        T1 == [T EXCEPT !.slots[i] = NewSlot]
    IN IF id = -1 THEN T1
       ELSE IF IsLocal(id) THEN [T1 EXCEPT !.ll = Max(@ - 1, 0)] ELSE [T1 EXCEPT !.rl = Max(@ - 1, 0)]
Settle(T, i) ==
    LET r == T.slots[i]
    IN Regrant(IF RecvDone(r) /\ SendDone(r) THEN FreeSlot(T, i) ELSE T)

FirstFree(T) == IF \E i \in 1..N : T.slots[i].id = -1 THEN CHOOSE i \in 1..N : (T.slots[i].id = -1 /\ \A j \in 1..(i - 1) : T.slots[j].id # -1) ELSE 0
AllocSlot(T, id) ==
    LET i == FirstFree(T)
        local == IsLocal(id)
        recvOn == ~IsUni(id) \/ ~local
        sendOn == ~IsUni(id) \/ local
        r == [NewSlot EXCEPT !.id = id, !.open = recvOn, !.limit = IF recvOn THEN SW ELSE 0,
                              !.size = IF recvOn THEN SW ELSE 0, !.sdone = ~sendOn]
        T1 == SetSlot(T, i, r)
    IN IF local THEN [T1 EXCEPT !.ll = @ + 1] ELSE [T1 EXCEPT !.rl = @ + 1]

(* ---- admission of peer streams (Streams::admits, locate) ---- *)
(* the first charges of k new streams fit beside the credit granted (Streams::windows_fit): the one test for a peer
   stream beyond the credit and for a local one *)
WindowsFit(T, k) == GU(T) + k * FirstW <= Avail(T)
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
OnData(T, r, off, len, fin, diff) ==
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
        done == [store.r EXCEPT !.hi = Max(@, e), !.fin = IF fin THEN e ELSE @]
    IN IF e > MAXOFF THEN [r |-> r, err |-> "FlowControl"]
       ELSE IF r.fin # -1 /\ (e > r.fin \/ (fin /\ e # r.fin)) THEN [r |-> r, err |-> "FinalSize"]
       ELSE IF r.fin = -1 /\ fin /\ e < r.hi THEN [r |-> r, err |-> "FinalSize"]
       ELSE IF e > r.limit THEN [r |-> r, err |-> "FlowControl"]
       ELSE IF r.rst = -1 /\ store.err # "ok" THEN [r |-> r, err |-> store.err]
       ELSE IF r.rst = -1 THEN [r |-> done, err |-> "ok"]
       ELSE [r |-> [r EXCEPT !.hi = Max(@, e), !.fin = IF fin THEN e ELSE @], err |-> "ok"]

(* Frame: Streams::on_stream_frame, the new table and the error *)
Frame(T, id, off, len, fin, diff) ==
    LET L == Locate(T, id)
    IN IF L.err # "ok" \/ L.i = 0 THEN [t |-> L.t, err |-> L.err]
       ELSE LET D == OnData(L.t, L.t.slots[L.i], off, len, fin, diff)
            IN [t |-> Settle(SetSlot(L.t, L.i, D.r), L.i), err |-> D.err]

(* ---- on_reset (recv.rs) ---- *)
OnResetR(r, code, fs) ==
    IF fs > MAXOFF \/ (r.fin # -1 /\ r.fin # fs) \/ fs < r.hi THEN [r |-> r, err |-> "FinalSize"]
    ELSE IF fs > r.limit THEN [r |-> r, err |-> "FlowControl"]
    ELSE IF r.rst # -1 THEN [r |-> r, err |-> "ok"]
    ELSE [r |-> [r EXCEPT !.hi = fs, !.fin = fs, !.rst = code, !.read = fs, !.contig = fs, !.held = {}, !.rs = <<>>],
          err |-> "ok"]
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

Consume(T, id, n, now, srtt) ==
    LET i == FindSlot(T, id)
        r == IF i = 0 THEN NewSlot ELSE T.slots[i]
        nr == r.read + n
        cut == r.fin # -1 /\ r.fin = nr
        r1 == [r EXCEPT !.read = nr,
                        !.held = IF cut THEN {} ELSE r.held \ (r.read \div CH..(nr \div CH - 1)),
                        !.rs = IF cut THEN <<>> ELSE r.rs]
        r2 == [r1 EXCEPT !.obs = r1.obs \/ Status(r1) # "open"]
        m2 == MeterStep(T.m, n, now, srtt)
        T1 == [SetSlot(T, i, r2) EXCEPT !.m = m2, !.tgt = Min(Max(m2.rate * 2, SW), MaxStream)]
    IN IF i = 0 THEN [t |-> T, err |-> "UnknownStream"]
       ELSE IF n > Readable(r) THEN [t |-> T, err |-> "InvalidConsume"]
       ELSE [t |-> Settle(GrantRun(T1, i), i), err |-> "ok"]

(* ---- control frames ---- *)
(* Pending: pending_control; the table after, the frame (kind "none", "reset", "stop" or "msd") and its number:
   the limit of an msd, the error code of a reset or a stop. The first slot with a frame to send gives one: its stream
   reset first, then its stop request, then its limit. *)
PendingSlot(T) == IF \E i \in 1..N : Hot(T.slots[i]) THEN CHOOSE i \in 1..N : (Hot(T.slots[i]) /\ \A j \in 1..(i - 1) : ~Hot(T.slots[j])) ELSE 0
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
\* the opener: a stream opens only inside the credit the peer gave (T.ad.lim, in all), and with its slot and its window
\* in the pool beside the slots and windows kept for the peer's credit
OpenLocal(T) ==
    LET c == 0
        id == T.lo[c] * 4 + 1
    IN IF T.lo[0] + T.lo[1] >= T.ad.lim \/ FirstFree(T) = 0 \/ FreeSlots(T) <= CreditLeft(T)
          \/ ~WindowsFit(T, CreditLeft(T) + 1) THEN T
       ELSE [AllocSlot(T, id) EXCEPT !.lo[c] = @ + 1]
\* a MAX_STREAMS frame arrived: the limit on the streams we may open only grows
RecvMaxStreams(T, l) == [T EXCEPT !.ad.lim = Max(@, l)]
\* a MAX_STREAMS frame was lost: send the current limit again unless a later one superseded it
CtlLostMsts(T, l) == IF l >= T.ad.adv THEN [T EXCEPT !.ad.pend = TRUE] ELSE T
SendOpen(r) == ~(IsUni(r.id) /\ ~IsLocal(r.id))
(* Streams::reset: queue a stream reset on the send half, the send buffers released (ext2 <= ext) *)
AppReset(T, id, code, ext2) ==
    LET i == FindSlot(T, id)
        r == IF i = 0 THEN NewSlot ELSE T.slots[i]
        change == SendOpen(r) /\ r.srst = 0 /\ ~r.sdone
        T1 == IF change THEN [SetSlot(T, i, [r EXCEPT !.srst = 1, !.scode = code]) EXCEPT !.ext = ext2] ELSE T
    IN IF i = 0 THEN T ELSE Settle(T1, i)
(* Streams::stop_sending: ask the peer to stop sending on a stream we receive on; queued once, nothing if the sender
   already ended the stream *)
StopReq(T, id, code) ==
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
CloseAll(T, ext2) == [Init0 EXCEPT !.ext = ext2, !.m = T.m, !.tgt = T.tgt, !.lo = T.lo, !.rn = T.rn, !.ad = T.ad]
=============================================================================
