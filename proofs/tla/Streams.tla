------------------------------- MODULE Streams -------------------------------
(***************************************************************************)
(* The receive, credit and admission path of the stream layer of           *)
(* vinc-transport (stream/table.rs, recv.rs, flow.rs, ranges.rs, pool.rs)  *)
(* over every interleaving of the calls the connection makes on it, at     *)
(* small sizes (StreamsOps.tla has the operators and the scaling).         *)
(*                                                                         *)
(* Checked, per concern (all over the same state space):                   *)
(*  - in-order delivery: a slot never reads past the prefix that is stored *)
(*    without holes (read <= contig, the readable bytes are held in the    *)
(*    pool), the read position never moves back, the stored ranges are     *)
(*    sorted, disjoint, non-adjacent and at most RR;                       *)
(*  - POOL_GRANT: the pool is never over its budget; a limit is raised,   *)
(*    the stream credit raised and a local stream opened only when the     *)
(*    ledger (the credit granted and not yet received, as Charged counts   *)
(*    it, with the first charges kept for the credit) fits in the bytes    *)
(*    the pool has left with them (LedgerOnGrant); an admission inside the *)
(*    credit never adds to the ledger, one beyond it only within the pool  *)
(*    (LedgerOnAdmit); the ledger passes the pool, or goes further past    *)
(*    it, only when a stream carries its first data or another user takes  *)
(*    chunks (OverOnlyByFirstData); the held chunks lie inside the span    *)
(*    the credit covers, so a frame inside the counted span never needs    *)
(*    more chunks than the ledger counted (HeldInSpan, NeedCovered); when  *)
(*    the pool has no other user and FIRSTK covers the windows the ledger  *)
(*    holds in every state (LedgerAlways, Streams_ledger, Streams_two,     *)
(*    Streams_local); a peer stream inside the credit is never held back,  *)
(*    whatever the pool holds (NoHeldWithinCredit), and the Streams_lazy   *)
(*    configs check all of it with a window larger than FIRSTK;            *)
(*  - RATE_WINDOW: the window size stays between the initial window *)
(*    and the ceiling, which is at most half the pool; the limit stays     *)
(*    within one window of the read position;                              *)
(*  - flow-control updates: a limit moves only by at least 1/8 of   *)
(*    the window, never down, and a window due to move is moved or         *)
(*    deferred (NoMissedGrant); a deferred grant is retried after every     *)
(*    release of pool chunks (NoStuckGrant; the witness Streams_stall is   *)
(*    the earlier behaviour, retry only on a consume, which stalls);       *)
(*  - STREAM_CAP: live peer streams never exceed the cap; a peer stream    *)
(*    that does not fit is held back: the call answers Exhausted and the   *)
(*    table is unchanged (LocatePure: no slot, no pool charge, no counter  *)
(*    moved), so the retransmission meets the table as the first arrival   *)
(*    did and the stream is admitted once it fits; an arriving stream      *)
(*    opens every lower id of its kind and initiator (ImplicitOpens); the  *)
(*    final size, once fixed, never changes;                               *)
(*  - STOP_SENDING: a stop request is queued once, sent as a control frame *)
(*    and sent again if lost unless the sender ended the stream; a stop    *)
(*    that arrives resets the send half with the peer's code (StopEndsWithCode), *)
(*    and the code of a reset never changes (CodeKept);                    *)
(*  - RESET: a reset fixes the final size, frees the buffered bytes and    *)
(*    leaves the stream readable to its end (nothing more is readable).    *)
(* Streams_local (a pool with no other user, a peer stream and a local    *)
(* one) holds LedgerAlways: the initial window of a stream this endpoint   *)
(* opens is counted in the ledger like a peer stream's (WindowsFit).       *)
(* Lean counterpart: proofs/lean/Vinc/TransportStreams.lean.               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS CH, RING, RR, N, MAXREM, B, SWC, MSWC, PM, MAXOFF, RETRY, RemIds, LocIds, FIRSTK
CONSTANTS HOR, LMAX, EXTMAX, SRTTS, DT
\* STOPS = FALSE leaves out the stop requests and our own resets (configs that check the credit only)
CONSTANT STOPS
VARIABLES T, clock
vars == <<T, clock>>

INSTANCE StreamsOps

Init == T = Init0 /\ clock = 0

Ids == RemIds \cup LocIds
FrameOp == \E id \in Ids, off \in 0..HOR, len \in 0..LMAX, fin \in BOOLEAN, diff \in BOOLEAN :
    /\ off + len <= HOR
    /\ T' = Frame(T, id, off, len, fin, diff).t /\ UNCHANGED clock
ResetOp == \E id \in Ids, fs \in 0..HOR : T' = Reset(T, id, 1, fs).t /\ UNCHANGED clock
ConsumeOp == \E id \in Ids, n \in 0..HOR, d \in 0..DT, srtt \in SRTTS :
    /\ clock + d <= HOR
    /\ T' = Consume(T, id, n, clock + d, srtt).t /\ clock' = clock + d
PendingOp == T' = Pending(T).t /\ UNCHANGED clock
LostMsdOp == \E id \in Ids, mx \in 0..HOR : T' = CtlLostMsd(T, id, mx) /\ UNCHANGED clock
LostResetOp == \E id \in Ids : T' = CtlLostReset(T, id) /\ UNCHANGED clock
AckedResetOp == \E id \in Ids : T' = CtlAckedReset(T, id) /\ UNCHANGED clock
OpenOp == T' = OpenLocal(T) /\ UNCHANGED clock
MaxStreamsOp == /\ LocIds # {} /\ PM >= 2 /\ \E l \in 0..(PM + 2) : T' = RecvMaxStreams(T, l) /\ UNCHANGED clock
LostMstsOp == T' = CtlLostMsts(T, T.ad.adv) /\ UNCHANGED clock   \* the latest frame lost; an older one is a no-op
AppResetOp == \E id \in Ids, e2 \in 0..T.ext : T' = AppReset(T, id, 9, e2) /\ UNCHANGED clock
LostStopOp == \E id \in Ids : T' = CtlLostStop(T, id) /\ UNCHANGED clock
AckedStopOp == \E id \in Ids : T' = CtlAckedStop(T, id) /\ UNCHANGED clock
StopReqOp == \E id \in Ids : T' = StopReq(T, id, 7).t /\ UNCHANGED clock
OnStopOp == \E id \in Ids, e2 \in 0..T.ext : T' = OnStop(T, id, 7, e2).t /\ UNCHANGED clock
FinishOp == \E id \in Ids, e2 \in 0..T.ext, dn \in BOOLEAN : T' = Finish(T, id, e2, dn) /\ UNCHANGED clock
ExtOp == \E e2 \in 0..EXTMAX : T' = ExtTo(T, e2) /\ UNCHANGED clock
CloseOp == \E e2 \in 0..T.ext : T' = CloseAll(T, e2) /\ UNCHANGED clock

Next == FrameOp \/ ResetOp \/ ConsumeOp \/ PendingOp \/ LostMsdOp \/ OpenOp \/ FinishOp \/ ExtOp \/ CloseOp
        \/ MaxStreamsOp \/ LostMstsOp
        \/ (STOPS /\ (LostResetOp \/ AckedResetOp \/ AppResetOp \/ LostStopOp \/ AckedStopOp \/ StopReqOp \/ OnStopOp))
Spec == Init /\ [][Next]_vars

\* the other users of the pool eventually let go (the liveness config only)
ExtRelease == T.ext > 0 /\ T' = ExtTo(T, 0) /\ UNCHANGED clock
LSpec == Spec /\ WF_vars(ExtRelease)

(* ---- state invariants ---- *)
Live == {i \in 1..N : T.slots[i].id # -1}
Sorted(rs) == /\ Len(rs) <= RR
              /\ \A k \in 1..Len(rs) : rs[k][1] < rs[k][2]
              /\ \A k \in 1..(Len(rs) - 1) : rs[k][2] < rs[k + 1][1]
rs_in(iv, o) == iv[1] <= o /\ o < iv[2]
Covered(r, o) == \E k \in 1..Len(r.rs) : rs_in(r.rs[k], o)
Reach(r) == IF r.fin = -1 THEN r.limit ELSE Min(r.fin, r.limit)
SpanChunks(r) == (r.read \div CH)..((Reach(r) - 1) \div CH)

SlotInv(r) ==
    /\ r.open =>
        /\ r.read <= r.contig /\ r.contig <= r.hi /\ r.hi <= r.limit
        /\ (r.fin # -1 => r.hi = r.fin)
        /\ Sorted(r.rs)
        /\ (r.rs # <<>> => r.contig = First0(r.rs) /\ r.rs[Len(r.rs)][2] <= r.hi)
        \* the bytes still to be read are stored, and held in the pool (in-order delivery reads only held bytes)
        /\ \A o \in r.read..(r.contig - 1) : r.rs # <<>> => Covered(r, o)
        /\ \A o \in r.read..(r.hi - 1) : Covered(r, o) => (o \div CH) \in r.held
        /\ \A k \in r.held : \E o \in (k * CH)..(k * CH + CH - 1) : Covered(r, o)
        /\ (Reach(r) > r.read => r.held \subseteq SpanChunks(r))
        /\ r.size >= SW /\ r.size <= MaxStream
        /\ r.limit <= Max(r.read + r.size, SW)
        /\ (r.rst # -1 => r.read = r.fin /\ r.held = {} /\ r.rs = <<>>)
    /\ ~r.open => r.held = {} /\ r.rs = <<>>

TypeOK == /\ T.ext \in 0..B /\ clock \in 0..HOR /\ T.tgt \in SW..MaxStream
          /\ \A i \in 1..N : SlotInv(T.slots[i])
Pool == Used(T) <= B
Unique == \A i, j \in 1..N : (i # j /\ T.slots[i].id # -1) => T.slots[i].id # T.slots[j].id
FreeIsNew == \A i \in 1..N : T.slots[i].id = -1 => T.slots[i] = NewSlot
Counters == /\ T.rl = Cardinality({i \in Live : ~IsLocal(T.slots[i].id)})
            /\ T.ll = Cardinality({i \in Live : IsLocal(T.slots[i].id)})
            /\ T.rl <= MAXREM /\ T.ll <= T.lo[0] + T.lo[1]
Admitted == \A i \in Live : ~IsLocal(T.slots[i].id) => Idx(T.slots[i].id) < T.rn[Class(T.slots[i].id)]
\* a peer stream that does not fit is held back: any error answer of locate leaves the table as it was
LocatePure == \A id \in Ids : Locate(T, id).err # "ok" => Locate(T, id).t = T
\* an arriving stream opens every lower id of its kind and initiator, one slot and one count each
ImplicitOpens == \A id \in Ids : LET L == Locate(T, id) IN
    (~IsLocal(id) /\ Idx(id) >= T.rn[Class(id)] /\ L.err = "ok") =>
        /\ L.t.rn[Class(id)] = Idx(id) + 1
        /\ L.t.rl = T.rl + (Idx(id) - T.rn[Class(id)] + 1)
        /\ \A k \in T.rn[Class(id)]..Idx(id) : FindSlot(L.t, k * 4 + (id % 4)) # 0
\* reachability witnesses (the configs *_w must find a violation): a stream is held back with the table full and is
\* admitted later through steps; one arriving frame opens a lower id as well
Held4 == T.rn[0] = 1 /\ Locate(T, 4).err = "Exhausted"
NoHeldAdmit == [](Held4 => [](FindSlot(T, 4) = 0))
NoJump == [][~(T.rn[0] = 0 /\ T'.rn[0] >= 2)]_vars
\* a stop that resets the send half leaves the peer's code on it
StopEndsWithCode == \A id \in Ids, c \in 0..1, e2 \in 0..T.ext : LET R == OnStop(T, id, c, e2) IN
    R.fresh => (FindSlot(R.t, id) # 0 /\ R.t.slots[FindSlot(R.t, id)].scode = c)
\* a queued stop or reset carries a code
CodesSet == \A i \in Live : (T.slots[i].stop \in {1, 2} => T.slots[i].qcode # -1) /\ (T.slots[i].srst \in {1, 2} => T.slots[i].scode # -1)
\* a window due to move was moved or deferred (credit follows consumption)
NoMissedGrant == \A i \in Live : T.slots[i].open => (Due(T.slots[i]) = -1 \/ T.slots[i].defer)
GrantFits(i) == LET r == T.slots[i]
                    r1 == [r EXCEPT !.size = Max(r.size, T.tgt)]
                    c == Due(r1)
                IN c # -1 /\ GU(T) - Unreceived(r) + PoolDemand(r1, Charged(r1, c)) + Resv(T) <= Avail(T)
\* a deferred grant that now fits is never left waiting for a consume
NoStuckGrant == \A i \in Live : T.slots[i].defer => ~GrantFits(i)
\* the ledger in every state: holds when no other user shares the pool and every window fits when its stream first
\* carries data (FIRSTK covers the windows); the first charges kept for the credit given to the peer count as granted
LedgerAlways == GU(T) + Resv(T) <= Avail(T)
\* the opener never has more streams open in all than the peer gave credit for
OpenerInside == T.lo[0] + T.lo[1] <= T.ad.lim
\* the credit given never lets a peer that keeps to it have more streams live than the configured limit MAXREM: the
\* streams it may still open plus those live are at most MAXREM (Streams_cap_w.cfg plants the cap that ignored it)
CreditInLimit == T.ad.adv > AdmittedN(T) => T.ad.adv - AdmittedN(T) + T.rl <= MAXREM
\* a peer stream that arrives inside the credit it was given is never held back, whatever the pool holds, however many
\* lower ids its frame opens with it
NoHeldWithinCredit == \A id \in RemIds : LET L == Locate(T, id) IN
    (Idx(id) >= T.rn[Class(id)] /\ AdmittedN(T) + (Idx(id) - T.rn[Class(id)] + 1) <= T.ad.adv) => L.err # "Exhausted"
\* an admission (the streams a frame opens, before its data) never takes the ledger past the pool, nor further past it:
\* inside the credit it adds nothing, beyond it the first charges must fit
LedgerOnAdmit == \A id \in RemIds : LET L == Locate(T, id) IN
    (L.err = "ok" /\ L.t.rl > T.rl) => GU(L.t) + Resv(L.t) <= Max(GU(T) + Resv(T), Avail(T))
\* a frame inside the span the ledger counts (the whole window of a stream that carried data, the first FIRSTK chunks
\* of one that has not) needs no more chunks than the ledger counted for its stream
NeedCovered == \A i \in Live : T.slots[i].open =>
    \A e \in (T.slots[i].read + 1)..Charged(T.slots[i], Reach(T.slots[i])) :
        Cardinality({k \in (T.slots[i].read \div CH)..((e - 1) \div CH) : k \notin T.slots[i].held}) * CH
            <= Unreceived(T.slots[i])

(* ---- liveness: a stream whose peer is blocked at its limit, all of it read, gets a new limit once the *)
(* other users of the pool let go: no deadlock, and the grant is not waiting for a read that cannot come     *)
Blocked(i) == LET r == T.slots[i] IN
    r.id # -1 /\ r.open /\ r.fin = -1 /\ r.rst = -1 /\ r.read = r.limit /\ r.limit < MAXOFF
Progress == \A i \in 1..N : [](Blocked(i) => <>~Blocked(i))

(* ---- transition properties ---- *)
SameInc(i) == T.slots[i].id # -1 /\ T'.slots[i].id = T.slots[i].id
LimitsMonotone == [][\A i \in 1..N : SameInc(i) => T'.slots[i].limit >= T.slots[i].limit]_vars
ReadMonotone == [][\A i \in 1..N : SameInc(i) => T'.slots[i].read >= T.slots[i].read]_vars
FinalFixed == [][\A i \in 1..N : (SameInc(i) /\ T.slots[i].fin # -1) => T'.slots[i].fin = T.slots[i].fin]_vars
\* a limit moves only by at least an eighth of the window
EighthRule == [][\A i \in 1..N : (SameInc(i) /\ T'.slots[i].limit > T.slots[i].limit) =>
                    T'.slots[i].limit >= T.slots[i].limit + T'.slots[i].size \div 8]_vars
\* a grant, a raise of the stream credit or a local stream leaves the ledger within the pool
LedgerOnGrant == [][((\E i \in 1..N : SameInc(i) /\ T'.slots[i].limit > T.slots[i].limit)
                     \/ T'.ad.adv > T.ad.adv \/ T'.ll > T.ll)
                    => GU(T') + Resv(T') <= Avail(T')]_vars
\* the ledger passes the pool, or goes further past it, only when a stream carries its first data or another user of
\* the pool takes chunks
Excess(S) == GU(S) + Resv(S) - Avail(S)
FirstData == \E i \in 1..N : T'.slots[i].hi > 0 /\ (T.slots[i].hi = 0 \/ T.slots[i].id # T'.slots[i].id)
OverOnlyByFirstData == [][Excess(T') > Max(Excess(T), 0) => (FirstData \/ T'.ext > T.ext)]_vars
\* the credit and the limit on what we may open only grow
CreditMonotone == [][T'.ad.adv >= T.ad.adv /\ T'.ad.lim >= T.ad.lim]_vars
\* a pool charge happens only within the budget
PoolOnAlloc == [][Used(T') > Used(T) => Used(T') <= B]_vars
\* the limits never exceed the pool a stream may hold
ReadFollowsContig == [][\A i \in 1..N : SameInc(i) => T'.slots[i].read <= T'.slots[i].contig]_vars
\* the code of a reset, once set, never changes (the acknowledgement of the reset forgets it)
CodeKept == [][\A i \in 1..N : (SameInc(i) /\ T.slots[i].scode # -1 /\ T'.slots[i].srst # 3) => T'.slots[i].scode = T.slots[i].scode]_vars
=============================================================================
