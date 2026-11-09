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
(*  - POOL_GRANT: the pool is never over its budget; a limit is     *)
(*    raised and a peer stream admitted only when the credit granted and   *)
(*    not yet received, with the new grant, fits in the bytes the pool     *)
(*    has left (LedgerOnGrant); the held chunks lie inside the span the    *)
(*    credit covers, so a frame inside the credit never needs more chunks  *)
(*    than the ledger counted (HeldInSpan, NeedCovered); when the pool has *)
(*    no other user the ledger holds in every state (LedgerAlways, config  *)
(*    Streams_ledger, with NeedCovered);                                   *)
(*  - RATE_WINDOW: the window size stays between the initial window *)
(*    and the ceiling, which is at most half the pool; the limit stays     *)
(*    within one window of the read position;                              *)
(*  - flow-control updates: a limit moves only by at least 1/8 of   *)
(*    the window, never down, and a window due to move is moved or         *)
(*    deferred (NoMissedGrant); a deferred grant is retried after every     *)
(*    release of pool chunks (NoStuckGrant; the witness Streams_stall is   *)
(*    the earlier behaviour, retry only on a consume, which stalls);       *)
(*  - STREAM_CAP: live peer streams never exceed the cap, a refused *)
(*    stream is remembered and answered with a reset (RefusedOk: it has no *)
(*    slot and its index is not below the next one admitted), never stored, *)
(*    and is forgotten only when its reset is acknowledged; the final size, *)
(*    once fixed, never changes;                                           *)
(*  - RESET: a reset fixes the final size, frees the buffered bytes and    *)
(*    leaves the stream readable to its end (nothing more is readable).    *)
(* The local-stream witness Streams_local shows that the initial window of *)
(* a stream this endpoint opens is not in the ledger.                      *)
(* Lean counterpart: proofs/lean/Vinc/TransportStreams.lean.               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS CH, RING, RR, N, MAXREM, B, SWC, MSWC, PM, RF, MAXOFF, RETRY, RemIds, LocIds
CONSTANTS HOR, LMAX, EXTMAX, SRTTS, DT
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
AppResetOp == \E id \in Ids, e2 \in 0..T.ext : T' = AppReset(T, id, e2) /\ UNCHANGED clock
FinishOp == \E id \in Ids, e2 \in 0..T.ext, dn \in BOOLEAN : T' = Finish(T, id, e2, dn) /\ UNCHANGED clock
ExtOp == \E e2 \in 0..EXTMAX : T' = ExtTo(T, e2) /\ UNCHANGED clock
CloseOp == \E e2 \in 0..T.ext : T' = CloseAll(T, e2) /\ UNCHANGED clock

Next == FrameOp \/ ResetOp \/ ConsumeOp \/ PendingOp \/ LostMsdOp \/ LostResetOp \/ AckedResetOp \/ OpenOp
        \/ AppResetOp \/ FinishOp \/ ExtOp \/ CloseOp
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
            /\ T.rl <= MAXREM /\ T.ll <= PM
Admitted == \A i \in Live : ~IsLocal(T.slots[i].id) => Idx(T.slots[i].id) < T.rn[Class(T.slots[i].id)]
RefusedOk == \A j \in 1..RF : T.ref[j].id # -1 =>
                /\ Idx(T.ref[j].id) >= T.rn[Class(T.ref[j].id)]
                /\ FindSlot(T, T.ref[j].id) = 0
                /\ \A k \in 1..RF : (k # j) => T.ref[k].id # T.ref[j].id
\* a window due to move was moved or deferred (credit follows consumption)
NoMissedGrant == \A i \in Live : T.slots[i].open => (Due(T.slots[i]) = -1 \/ T.slots[i].defer)
GrantFits(i) == LET r == T.slots[i]
                    r1 == [r EXCEPT !.size = Max(r.size, T.tgt)]
                    c == Due(r1)
                IN c # -1 /\ GU(T) - Unreceived(r) + PoolDemand(r1, c) <= Avail(T)
\* a deferred grant that now fits is never left waiting for a consume
NoStuckGrant == \A i \in Live : T.slots[i].defer => ~GrantFits(i)
\* the ledger in every state: holds when no other user shares the pool and every stream was admitted
LedgerAlways == GU(T) <= Avail(T)
\* a frame inside the credit needs no more chunks than the ledger counted for its stream
NeedCovered == \A i \in Live : T.slots[i].open =>
    \A e \in (T.slots[i].read + 1)..Reach(T.slots[i]) :
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
\* a grant or an admission leaves the credit within the pool
LedgerOnGrant == [][((\E i \in 1..N : SameInc(i) /\ T'.slots[i].limit > T.slots[i].limit) \/ T'.rl > T.rl)
                    => GU(T') <= Avail(T')]_vars
\* a pool charge happens only within the budget
PoolOnAlloc == [][Used(T') > Used(T) => Used(T') <= B]_vars
\* the limits never exceed the pool a stream may hold
ReadFollowsContig == [][\A i \in 1..N : SameInc(i) => T'.slots[i].read <= T'.slots[i].contig]_vars
=============================================================================
