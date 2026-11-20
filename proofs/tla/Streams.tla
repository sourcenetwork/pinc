------------------------------- MODULE Streams -------------------------------
(***************************************************************************)
(* The receive, credit and admission path of the stream layer of           *)
(* pinc-transport (stream/table.rs, recv.rs, flow.rs, ranges.rs, pool.rs)  *)
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
(*    within one window of the read position; a window grows only to      *)
(*    twice what its own reader drained per round trip                     *)
(*    (SizeFollowsOwnRate; Streams_meter, and the witness Streams_meter_w, *)
(*    the connection-wide meter before #159, which breaks it);             *)
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
(*  - EARLY (an optimistic dial, the Streams_early configs): the table      *)
(*    starts with early opens on and a limit of 0, and the establishment    *)
(*    (Establish) raises the limit and ends them. The opener passes the     *)
(*    limit only while early (OpenPastOnlyEarly), so it never has more      *)
(*    streams open than the limit or than it opened while early             *)
(*    (OpenerInsideOrEarly; the earlier OpenerInside is a witness there,    *)
(*    Streams_early_w); each stream we open keeps its ordinal, the order of *)
(*    its open (Ordinals); a stream frame leaves only for a stream whose    *)
(*    ordinal the limit covers (SendOnlyInLimit), and so does a stream      *)
(*    control frame, a reset, a stop request or a window update            *)
(*    (CtlOnlyInLimit, #432), so the peer never receives a frame for a      *)
(*    stream its limit does not cover (PeerNeverRefuses), and a control     *)
(*    frame held for the limit leaves once it covers the stream             *)
(*    (CtlReleased); once allowed a stream stays allowed, and the streams   *)
(*    allowed are the first ones opened (GateMonotone, GatePrefix);         *)
(*    Streams_early_rel is the reachability witness of a stream opened past *)
(*    the limit that a raise lets send, and Streams_early_ctl_w the rule    *)
(*    before #432 (control frames not held: PeerNeverRefuses fails on a     *)
(*    stream reset at once after an early open).                            *)
(* Lean counterpart: proofs/lean/Pinc/TransportStreams.lean.               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS CH, RING, RR, N, MAXREM, B, SWC, MSWC, PM, MAXOFF, RETRY, RemIds, LocIds, FIRSTK, RELEASE, PERSTREAM
CONSTANTS HOR, LMAX, EXTMAX, SRTTS, DT
\* STOPS = FALSE leaves out the stop requests and our own resets (configs that check the credit only)
CONSTANT STOPS
\* EARLY = TRUE starts the table of an optimistic dial: early opens on, until the establishment
CONSTANT EARLY
\* elo: a ghost, how many streams we had opened in all at the last open made while early
VARIABLES T, clock, elo
vars == <<T, clock, elo>>

INSTANCE StreamsOps

Init == T = (IF EARLY THEN SetEarly(Init0, TRUE) ELSE Init0) /\ clock = 0 /\ elo = 0

Ids == RemIds \cup LocIds
FrameOp == \E id \in Ids, off \in 0..HOR, len \in 0..LMAX, fin \in BOOLEAN, diff \in BOOLEAN :
    /\ off + len <= HOR
    /\ T' = Frame(T, id, off, len, fin, diff).t /\ UNCHANGED clock
ResetOp == \E id \in Ids, fs \in 0..HOR : T' = Reset(T, id, 1, fs).t /\ UNCHANGED clock
ConsumeOp == \E id \in Ids, n \in 0..HOR, d \in 0..DT, srtt \in SRTTS :
    /\ clock + d <= HOR
    /\ T' = Consume(T, id, n, clock + d, srtt).t /\ clock' = clock + d
PendingOp == T' = Pending(T).t /\ UNCHANGED clock
\* a MAX_STREAM_DATA frame is lost: the one with the slot's limit (sent again) or an older one (nothing to do); the
\* max is read from the slot, since a fixed range (0..HOR) sat below every limit in some configs (SW 4 > HOR 3 in
\* Streams.cfg), where the loss changed nothing
LostMsdOp == \E id \in Ids, latest \in BOOLEAN :
    LET i == FindSlot(T, id)
        lim == IF i = 0 THEN 0 ELSE T.slots[i].limit
    IN T' = CtlLostMsd(T, id, IF latest THEN lim ELSE lim - 1) /\ UNCHANGED clock
LostResetOp == \E id \in Ids : T' = CtlLostReset(T, id) /\ UNCHANGED clock
AckedResetOp == \E id \in Ids : T' = CtlAckedReset(T, id) /\ UNCHANGED clock
OpenOp == /\ T' = OpenLocal(T) /\ UNCHANGED clock
          /\ elo' = IF T.ad.early /\ T' # T THEN T'.lo[0] + T'.lo[1] ELSE elo
MaxStreamsOp == /\ LocIds # {} /\ (PM >= 2 \/ EARLY) /\ \E l \in 0..(PM + 2) : T' = RecvMaxStreams(T, l) /\ UNCHANGED clock
EstablishOp == EARLY /\ T.ad.early /\ \E l \in 0..(PM + 2) : T' = Establish(T, l) /\ UNCHANGED <<clock, elo>>
LostMstsOp == T' = CtlLostMsts(T, T.ad.adv) /\ UNCHANGED clock   \* the latest frame lost; an older one is a no-op
AppResetOp == \E id \in Ids, e2 \in 0..T.ext : T' = AppReset(T, id, 9, e2) /\ UNCHANGED clock
LostStopOp == \E id \in Ids : T' = CtlLostStop(T, id) /\ UNCHANGED clock
AckedStopOp == \E id \in Ids : T' = CtlAckedStop(T, id) /\ UNCHANGED clock
StopReqOp == \E id \in Ids : T' = StopReq(T, id, 7).t /\ UNCHANGED clock
OnStopOp == \E id \in Ids, e2 \in 0..T.ext : T' = OnStop(T, id, 7, e2).t /\ UNCHANGED clock
FinishOp == \E id \in Ids, e2 \in 0..T.ext, dn \in BOOLEAN : T' = Finish(T, id, e2, dn) /\ UNCHANGED clock
SendOutOp == RELEASE /\ \E i \in 1..N, f \in BOOLEAN : T' = SendOut(T, i, f) /\ UNCHANGED clock
ExtOp == \E e2 \in 0..EXTMAX : T' = ExtTo(T, e2) /\ UNCHANGED clock
CloseOp == \E e2 \in 0..T.ext : T' = CloseAll(T, e2) /\ UNCHANGED clock

Calls == FrameOp \/ ResetOp \/ ConsumeOp \/ PendingOp \/ LostMsdOp \/ FinishOp \/ SendOutOp \/ ExtOp \/ CloseOp
         \/ MaxStreamsOp \/ LostMstsOp
         \/ (STOPS /\ (LostResetOp \/ AckedResetOp \/ AppResetOp \/ LostStopOp \/ AckedStopOp \/ StopReqOp \/ OnStopOp))
Next == (Calls /\ UNCHANGED elo) \/ OpenOp \/ EstablishOp
\* The quick profile's Next (proofs/tla/quick, Next <- NextQuick): Next without its stuttering steps. [][NextQuick]_vars
\* is the same formula as [][Next]_vars (a step that changes nothing satisfies both), so the same behaviours are checked,
\* but TLC no longer generates the many calls that leave the table as it was and checks the step properties on each.
NextQuick == ((Calls /\ UNCHANGED elo) \/ OpenOp \/ EstablishOp) /\ vars' # vars
Spec == Init /\ [][Next]_vars
\* The bound of the EARLY configs (a CONSTRAINT): while early opens are on, a close frees the slots and keeps the
\* counters, so opens past the limit go on without end; the configs stop at one round of the slots and one more.
OpenBound == T.lo[0] + T.lo[1] <= N + 1

\* the other users of the pool eventually let go (the liveness config only)
ExtRelease == T.ext > 0 /\ T' = ExtTo(T, 0) /\ UNCHANGED <<clock, elo>>
LSpec == Spec /\ WF_vars(ExtRelease)

\* The state without the meters, for configs whose clock never moves (DT = 0, VIEW MeterFree). There a meter's epoch
\* never closes (no consume is ever a round trip after the epoch's start), so its rate stays 0 and no window grows from
\* it: two states that differ only in their meters behave alike, and fingerprinting them as one keeps the per-stream
\* meters from multiplying the state space. The configs that check the meter (Streams_meter, DT = 1) keep it.
MeterFree == <<[T EXCEPT !.slots = [k \in 1..N |-> [T.slots[k] EXCEPT !.m = [start |-> -1, bytes |-> 0, rate |-> 0]]]],
               clock, elo>>
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

TypeOK == /\ T.ext \in 0..B /\ clock \in 0..HOR
          /\ \A i \in 1..N : SlotInv(T.slots[i])
Pool == Used(T) <= B
Unique == \A i, j \in 1..N : (i # j /\ T.slots[i].id # -1) => T.slots[i].id # T.slots[j].id
FreeIsNew == \A i \in 1..N : T.slots[i].id = -1 => T.slots[i] = NewSlot
\* the peer streams that count against the limit are the live peer slots that have not been released (a stream whose
\* data is whole and read and whose answer has left stops counting, though its slot is held until the answer is acked)
Counters == /\ T.rl = Cardinality({i \in Live : ~IsLocal(T.slots[i].id) /\ T.slots[i].cnt})
            /\ T.ll = Cardinality({i \in Live : IsLocal(T.slots[i].id)})
            /\ T.rl <= MAXREM /\ T.ll <= T.lo[0] + T.lo[1]
\* only a peer stream is ever released from the count
ReleasedArePeer == \A i \in Live : ~T.slots[i].cnt => ~IsLocal(T.slots[i].id)
\* the earlier statement of Counters, before a peer stream's place was free when its answer left: every live peer slot
\* counts (Streams_released_w.cfg shows it false of the code)
CountersEveryLive == T.rl = Cardinality({i \in Live : ~IsLocal(T.slots[i].id)})
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
\* a stream given up (stop_sending) after its end arrived, and one asked to stop whose end then arrives, is discarded
\* (c0706819): it holds no bytes and counts as read to its end, so its receive half is done
StoppedEndDiscarded == \A i \in Live : LET r == T.slots[i] IN
    (r.open /\ r.stop # 0 /\ r.fin # -1 /\ r.rst = -1) => r.held = {} /\ r.rs = <<>> /\ r.read = r.fin /\ RecvDone(r)
GiveUp(id) == LET i == FindSlot(T, id) IN i # 0 /\ T.slots[i].open /\ T.slots[i].rst = -1 /\ T.slots[i].fin # -1
\* the stop request on such a stream: no bytes held, read to its end; the slot leaves at once exactly when the send half
\* is done; the peer's limit gets back one place exactly when a counted peer stream is freed or released
GiveUpDiscards == \A id \in Ids : GiveUp(id) =>
    LET i == FindSlot(T, id)
        R == StopReq(T, id, 7).t
        j == FindSlot(R, id)
        back == ~IsLocal(id) /\ T.slots[i].cnt /\ (j = 0 \/ ~R.slots[j].cnt)
    IN /\ (j = 0) = SendDone(T.slots[i])
       /\ j # 0 => /\ R.slots[j].held = {} /\ R.slots[j].rs = <<>> /\ R.slots[j].read = R.slots[j].fin
                   /\ RecvDone(R.slots[j])
       /\ R.rl = T.rl - (IF back THEN 1 ELSE 0)
\* a stream done on both halves is not left in the table
DoneFreed == \A i \in Live : ~(RecvDone(T.slots[i]) /\ SendDone(T.slots[i]))
\* witness (Streams_stop_w.cfg, the rule before c0706819, must violate it): a stream whose end arrived with a hole and
\* that is given up keeps its place: it is never read to its end, so it stays until the connection closes
GiveUpHoleDiscards == \A id \in Ids :
    (GiveUp(id) /\ T.slots[FindSlot(T, id)].contig < T.slots[FindSlot(T, id)].fin) =>
        LET R == StopReq(T, id, 7).t
            j == FindSlot(R, id)
        IN j = 0 \/ RecvDone(R.slots[j])
\* a window due to move was moved or deferred (credit follows consumption)
NoMissedGrant == \A i \in Live : T.slots[i].open => (Due(T.slots[i]) = -1 \/ T.slots[i].defer)
GrantFits(i) == LET r == T.slots[i]
                    r1 == r
                    c == Due(r1)
                IN c # -1 /\ GU(T) - Unreceived(r) + PoolDemand(r1, Charged(r1, c)) + Resv(T) <= Avail(T)
\* a deferred grant that now fits is never left waiting for a consume
NoStuckGrant == \A i \in Live : T.slots[i].defer => ~GrantFits(i)
\* the ledger in every state: holds when no other user shares the pool and every window fits when its stream first
\* carries data (FIRSTK covers the windows); the first charges kept for the credit given to the peer count as granted
LedgerAlways == GU(T) + Resv(T) <= Avail(T)
\* the opener never has more streams open in all than the peer gave credit for: true without early opens; an optimistic
\* dial passes it (Streams_early_w.cfg)
OpenerInside == T.lo[0] + T.lo[1] <= T.ad.lim
\* restated for early opens: the opener has more streams open than the limit only by the ones it opened while early
OpenerInsideOrEarly == T.lo[0] + T.lo[1] <= Max(T.ad.lim, elo)
\* each stream we open keeps its ordinal, the order of its open: they are 1, 2, ... in the order of the ids (one kind
\* of stream here), and a peer stream has none
Ordinals == \A i \in Live : IF IsLocal(T.slots[i].id) THEN T.slots[i].ord = Idx(T.slots[i].id) + 1
                                                       /\ T.slots[i].ord <= T.lo[0] + T.lo[1]
                                                  ELSE T.slots[i].ord = 0
\* a stream frame leaves only for a stream whose ordinal the limit covers: on any other slot SendOut changes nothing
SendOnlyInLimit == \A i \in 1..N, f \in BOOLEAN : ~CanSend(T, i) => SendOut(T, i, f) = T
\* a stream control frame (a reset, a stop request, a window update) leaves only for a stream whose ordinal the limit
\* covers: the frame Pending gives next is for such a stream (#432)
CtlOnlyInLimit == LET P == Pending(T) IN P.kind \in {"reset", "stop", "msd"} => CanSend(T, FindSlot(T, P.id))
\* a stream the peer's limit does not cover: one we opened whose index is at or past the limit the peer gave (the peer
\* has not opened it, and past its cap its locate refuses it with a stream limit error that closes the connection)
PeerRefuses(id) == IsLocal(id) /\ Idx(id) >= T.ad.lim
\* the peer never receives a frame for a stream its limit does not cover: neither a stream frame (a stream allowed to
\* send, CanSend, is covered) nor the stream control frame Pending gives next
PeerNeverRefuses ==
    /\ \A i \in Live : CanSend(T, i) => ~PeerRefuses(T.slots[i].id)
    /\ LET P == Pending(T) IN P.kind \in {"reset", "stop", "msd"} => ~PeerRefuses(P.id)
\* a control frame held for the limit is released once the limit covers its stream: while some stream the limit covers
\* has a control frame to send, Pending gives a frame (none waits behind the gate for good)
CtlReleased == (\E i \in Live : Hot(T.slots[i]) /\ CanSend(T, i)) => Pending(T).kind # "none"
\* the streams allowed to send are the first ones opened
GatePrefix == \A i, j \in Live : (T.slots[i].ord < T.slots[j].ord /\ CanSend(T, j)) => CanSend(T, i)
\* the credit given never lets a peer that keeps to it have more streams live than the configured limit MAXREM: the
\* streams it may still open plus those live are at most MAXREM (Streams_cap_w.cfg plants the cap that ignored it)
CreditInLimit == T.ad.adv > AdmittedN(T) => T.ad.adv - AdmittedN(T) + T.rl <= MAXREM
\* whatever state a refresh starts from, it leaves nothing of the room unadvertised: no raise is held back for size
\* (the receiver cannot see streams opened and not written on; Streams_raise_w.cfg finds the eighth rule before it
\* holding one back)
RaiseNotHeld == RefreshAdmit(T).ad.adv >= AdmittedN(T) + AdmitRoom(T)
\* every slot above the mark is new, so the scans that stop at the mark miss no stream with data, a retransmission or
\* a control frame to send, after any run of frees, reuses and resets; and the mark is tight: its own slot is held, so
\* a scan covers no more slots than the highest live stream (Streams_mark_w.cfg plants a free that lowers the mark)
NothingAboveMark == /\ T.hw \in 0..N
                    /\ \A k \in 1..N : k > T.hw => T.slots[k] = NewSlot
                    /\ T.hw > 0 => T.slots[T.hw].id # -1
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
\* a witness, not a promise: Streams_live_blocked.cfg must find it violated, which shows Blocked is reachable where
\* Progress is checked (a reader at its limit with the pool's other users holding chunks)
NeverBlocked == \A i \in 1..N : ~Blocked(i)

(* ---- transition properties ---- *)
SameInc(i) == T.slots[i].id # -1 /\ T'.slots[i].id = T.slots[i].id
LimitsMonotone == [][\A i \in 1..N : SameInc(i) => T'.slots[i].limit >= T.slots[i].limit]_vars
ReadMonotone == [][\A i \in 1..N : SameInc(i) => T'.slots[i].read >= T.slots[i].read]_vars
FinalFixed == [][\A i \in 1..N : (SameInc(i) /\ T.slots[i].fin # -1) => T'.slots[i].fin = T.slots[i].fin]_vars
\* METER: a window grows only to what its own stream asks for: twice what its reader drained per round trip, between
\* the initial window and the ceiling. With the connection-wide meter (PERSTREAM = FALSE) a stream that has drained
\* nothing yet takes twice the other streams' rate, and Streams_meter_w finds it.
SizeFollowsOwnRate == [][\A i \in 1..N : (SameInc(i) /\ T'.slots[i].size > T.slots[i].size)
                            => T'.slots[i].size <= Target(T'.slots[i].m.rate)]_vars
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
\* an open passes the limit only while early
OpenPastOnlyEarly == [][(T'.lo[0] + T'.lo[1] > T.lo[0] + T.lo[1] /\ T'.lo[0] + T'.lo[1] > T.ad.lim) => T.ad.early]_vars
\* a stream allowed to send stays allowed: its ordinal never changes and the limit never falls
GateMonotone == [][\A i \in 1..N : (SameInc(i) /\ CanSend(T, i))
                                     => (T'.slots[i].ord = T.slots[i].ord /\ CanSend(T', i))]_vars
\* reachability witness (Streams_early_rel.cfg must violate it): a stream opened past the limit is let send by a raise
NoReleaseOfEarly == [][~(\E i \in 1..N : SameInc(i) /\ ~CanSend(T, i) /\ CanSend(T', i))]_vars
\* a pool charge happens only within the budget
PoolOnAlloc == [][Used(T') > Used(T) => Used(T') <= B]_vars
\* the limits never exceed the pool a stream may hold
ReadFollowsContig == [][\A i \in 1..N : SameInc(i) => T'.slots[i].read <= T'.slots[i].contig]_vars
\* the code of a reset, once set, never changes (the acknowledgement of the reset forgets it)
CodeKept == [][\A i \in 1..N : (SameInc(i) /\ T.slots[i].scode # -1 /\ T'.slots[i].srst # 3) => T'.slots[i].scode = T.slots[i].scode]_vars
\* a stream stops counting only when it is done on the receive side and its send half has flushed, and it never counts
\* again (a lost range queued again after the release does not bring it back)
ReleaseWhenFlushed == [][\A i \in 1..N : (SameInc(i) /\ T.slots[i].cnt /\ ~T'.slots[i].cnt)
                            => (RecvDone(T'.slots[i]) /\ Flushed(T'.slots[i]))]_vars
ReleaseIsFinal == [][\A i \in 1..N : (SameInc(i) /\ ~T.slots[i].cnt) => ~T'.slots[i].cnt]_vars
\* The quick profile's bounds (a CONSTRAINT of proofs/tla/quick configs): behaviours of a few calls.
LOCAL QuickTLC == INSTANCE TLC
Streams_capQuickBound == QuickTLC!TLCGet("level") <= 5
Streams_earlyQuickBound == QuickTLC!TLCGet("level") <= 5
Streams_markQuickBound == QuickTLC!TLCGet("level") <= 5
Streams_releaseQuickBound == QuickTLC!TLCGet("level") <= 5
Streams_early_ctlQuickBound == QuickTLC!TLCGet("level") <= 5
Streams_localQuickBound == QuickTLC!TLCGet("level") <= 4
=============================================================================
