--------------------------- MODULE Incarnation ----------------------------
(***************************************************************************)
(* The incarnation of pinc-membership incarnation.rs, and the address tag. *)
(*                                                                         *)
(* An incarnation word is a 48-bit epoch above a 16-bit record sequence.   *)
(* The words are the 80-bit machine words of U64.tla (limbs), so the       *)
(* 48-bit and 64-bit edges are exact. The operators mirror the code line   *)
(* by line: StartOp (Incarnation::start), NextOp (next_record), ObserveOp  *)
(* (observe), SealOp (the seal helper: the exhaustion check, then the     *)
(* store write when the counter is persistent). An operator returns         *)
(* [err |-> "ok", inc, loc] or [err |-> "store" or "exhausted"]; an error  *)
(* returns no state, as the code assigns the value only after the seal.    *)
(*                                                                         *)
(* The system model lets a host restart a life with any wall clock (zero,  *)
(* small, now-like, the 48-bit edge, the 64-bit edge) and any floor,       *)
(* write records, observe any word a peer may report, and fail its store   *)
(* on read or on write at any time. Checked (Incarnation*.cfg):            *)
(*   EpochBound   an epoch of a life never exceeds 2^48 - 1 (exhaustion is *)
(*                reported, never wrapped);                                *)
(*   SealedBeforeUse  with a persistent store the store holds the epoch in *)
(*                use;                                                     *)
(*   Mono         with a persistent store every announced word is above    *)
(*                every word announced before, across restarts, whatever   *)
(*                the wall clock does;                                     *)
(*   FloorOK      the epoch of every life is above the host floor, and     *)
(*                with the clock fallback above the wall clock;            *)
(*   ObserveOK    a moved word is above the word reported;                 *)
(*   Unchanged    a failed call leaves value and store as they were;       *)
(*   HlcMono      with the clock fallback and a host that passes the       *)
(*                highest epoch it has heard as the floor, the announced   *)
(*                words are strictly increasing too (Incarnation_hlc.cfg); *)
(* and the witness Incarnation_clock.cfg: with the clock fallback and no   *)
(* floor, a clock that jumped back reissues a lower word, so Mono does     *)
(* not hold without the counter or the floor (TLC must find it).           *)
(* Lean counterpart: Pinc/MembershipInc.lean and MembershipIncThm.lean     *)
(* (restart_word_gt, start_epoch_gt, start_hlc_gt_floor, nextRecord_word_lt,*)
(* observe_word_lt, start_inv, nextRecord_inv, observe_inv, the            *)
(* *_exhausted theorems).                                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

U == INSTANCE U64

EpochMax == U!Sub(U!Pw(48), U!One)

(* a.saturating_add(1) *)
SatInc(a) == IF a = U!Max64 THEN a ELSE U!Add(a, U!One)
SatAdd(a, b) == LET s == U!Add(a, b) IN IF U!Fits(s) THEN s ELSE U!Max64

(* the incarnation word (epoch << 16) | seq, seq below 2^16 *)
Word(inc) == U!Add(U!Shl(inc.epoch, 16), U!W(inc.seq))

(* a local: persistent, the store content (<<>> none, <<w>>), read and write failures *)
SealOp(l, e) ==
    IF U!Lt(EpochMax, e) THEN [err |-> "exhausted"]
    ELSE IF l.pers
         THEN IF l.sf THEN [err |-> "store"] ELSE [err |-> "ok", loc |-> [l EXCEPT !.sealed = <<e>>]]
         ELSE [err |-> "ok", loc |-> l]

StartOp(l, wall, floor) ==
    LET remembered == IF ~l.pers THEN [err |-> "ok", v |-> U!Zero]
                      ELSE IF l.rf THEN [err |-> "store"]
                      ELSE [err |-> "ok", v |-> IF l.sealed = <<>> THEN U!Zero ELSE l.sealed[1]]
    IN IF remembered.err # "ok" THEN remembered
       ELSE LET base == U!Max(remembered.v, floor)
                epoch == IF l.pers THEN SatInc(base) ELSE U!Max(SatInc(wall), SatInc(base))
                s == SealOp(l, epoch)
            IN IF s.err # "ok" THEN s
               ELSE [err |-> "ok", inc |-> [epoch |-> epoch, seq |-> 0], loc |-> s.loc]

NextOp(l, inc) ==
    IF inc.seq + 1 <= 65535
    THEN [err |-> "ok", inc |-> [inc EXCEPT !.seq = inc.seq + 1], loc |-> l]
    ELSE LET epoch == SatInc(inc.epoch)
             s == SealOp(l, epoch)
         IN IF s.err # "ok" THEN s ELSE [err |-> "ok", inc |-> [epoch |-> epoch, seq |-> 0], loc |-> s.loc]

ObserveOp(l, inc, seen) ==
    IF U!Le(seen, Word(inc)) THEN [err |-> "ok", ch |-> FALSE, inc |-> inc, loc |-> l]
    ELSE LET epoch == SatInc(U!Max(U!Shr(seen, 16), inc.epoch))
             s == SealOp(l, epoch)
         IN IF s.err # "ok" THEN s
            ELSE [err |-> "ok", ch |-> TRUE, inc |-> [epoch |-> epoch, seq |-> 0], loc |-> s.loc]

(* n records in a row, stopping at the first error, in closed form: the rest of the sequence, then one rollover that
   needs a seal, and so on. Returns the state after, the number done and the outcome of the last call. *)
RECURSIVE BulkOp(_, _, _, _)
BulkOp(l, inc, n, done) ==
    IF n = 0 THEN [err |-> "ok", inc |-> inc, loc |-> l, done |-> done]
    ELSE LET room == 65535 - inc.seq IN
         IF n <= room THEN [err |-> "ok", inc |-> [inc EXCEPT !.seq = inc.seq + n], loc |-> l, done |-> done + n]
         ELSE LET inc1 == [inc EXCEPT !.seq = 65535]
                  r == NextOp(l, inc1)
              IN IF r.err # "ok" THEN [err |-> r.err, inc |-> inc1, loc |-> l, done |-> done + room]
                 ELSE BulkOp(r.loc, r.inc, n - room - 1, done + room + 1)

(***************************************************************************)
(* The address tag: the move counter wraps at 256, several moves at one    *)
(* instant count once, and the previous tag is kept for MOVE_SETTLE after  *)
(* a move while the reflexive address is unknown. The host's address_hash  *)
(* is [ticket, moves, 0, 0, 0, 0, 0, 7] in the test host and a function of *)
(* the move counter in general.                                            *)
(***************************************************************************)
MoveSettle == <<24064, 45776, 0, 0, 0>>

TagInit == [moves |-> 0, movedAt |-> <<>>, cur |-> <<>>]

HashOf(tk, m) == <<tk, m, 0, 0, 0, 0, 0, 7>>

MovedOp(t, now) ==
    [moves |-> IF t.movedAt = <<now>> THEN t.moves ELSE (t.moves + 1) % 256,
     movedAt |-> <<now>>, cur |-> t.cur]

SatSub(a, b) == IF U!Lt(a, b) THEN U!Zero ELSE U!Sub(a, b)

SettlingOp(t, now, refl) ==
    t.movedAt # <<>> /\ U!Lt(SatSub(now, t.movedAt[1]), MoveSettle) /\ ~refl

(* AddressTag::tag: returns the tag and the new state *)
TagOp(t, now, refl, tk) ==
    IF t.cur # <<>> /\ SettlingOp(t, now, refl)
    THEN [tag |-> t.cur[1], t |-> t]
    ELSE [tag |-> HashOf(tk, t.moves), t |-> [t EXCEPT !.cur = <<HashOf(tk, t.moves)>>]]

(***************************************************************************)
(* The system model                                                        *)
(***************************************************************************)
CONSTANTS PersModes,   \* the hosts to check: {TRUE}, {FALSE} or BOOLEAN
          TrackFloor,  \* the host passes the highest epoch it has heard as the floor
          Faults,      \* the store may fail on read or on write
          MaxSteps

VARIABLES loc, inc, ann, mono, floorOK, obsOK, heard, steps
vars == <<loc, inc, ann, mono, floorOK, obsOK, heard, steps>>

Seals == {<<>>, <<U!W(5)>>, <<U!Sub(EpochMax, U!W(1))>>, <<EpochMax>>}
Walls == {U!Zero, U!W(1), <<26624, 53221, 395, 0, 0>>, U!Sub(EpochMax, U!One), EpochMax, U!Pw(48), U!Max64}
Floors == IF TrackFloor THEN {heard} ELSE {U!Zero, heard, U!W(7)}

Init == /\ loc \in [pers : PersModes, sealed : Seals, rf : {FALSE}, sf : {FALSE}]
        /\ inc = <<>> /\ ann = <<>> /\ mono = TRUE /\ floorOK = TRUE /\ obsOK = TRUE
        /\ heard = U!Zero /\ steps = 0

(* a word is announced: it must be above the last one *)
Announce(w) == /\ ann' = <<w>>
               /\ mono' = (mono /\ (ann = <<>> \/ U!Lt(ann[1], w)))
               /\ heard' = U!Max(heard, U!Shr(w, 16))

DoStart ==
    \E wall \in Walls, fl \in Floors :
        LET r == StartOp(loc, wall, fl)
        IN /\ steps < MaxSteps /\ steps' = steps + 1
           /\ IF r.err = "ok"
              THEN /\ inc' = <<r.inc>> /\ loc' = r.loc
                   /\ floorOK' = (floorOK /\ U!Lt(fl, r.inc.epoch) /\ (loc.pers \/ U!Lt(wall, r.inc.epoch)))
                   /\ obsOK' = obsOK
                   /\ Announce(Word(r.inc))
              ELSE UNCHANGED <<inc, loc, ann, mono, floorOK, obsOK, heard>>

DoNext ==
    /\ inc # <<>> /\ steps < MaxSteps /\ steps' = steps + 1
    /\ LET r == NextOp(loc, inc[1])
       IN IF r.err = "ok"
          THEN /\ inc' = <<r.inc>> /\ loc' = r.loc /\ Announce(Word(r.inc)) /\ UNCHANGED <<floorOK, obsOK>>
          ELSE UNCHANGED <<inc, loc, ann, mono, floorOK, obsOK, heard>>

(* the rest of the sequence at once: 65535 - seq records *)
DoBulk ==
    /\ inc # <<>> /\ steps < MaxSteps /\ steps' = steps + 1
    /\ LET r == BulkOp(loc, inc[1], 65535 - inc[1].seq, 0)
       IN IF r.err = "ok" /\ r.done > 0
          THEN /\ inc' = <<r.inc>> /\ loc' = r.loc /\ Announce(Word(r.inc)) /\ UNCHANGED <<floorOK, obsOK>>
          ELSE UNCHANGED <<inc, loc, ann, mono, floorOK, obsOK, heard>>

Seens(i) == {U!Zero, U!Sub(Word(i), U!One) , Word(i), U!Add(Word(i), U!One), U!Add(Word(i), U!Pw(16)),
             U!Shl(EpochMax, 16), U!Max64}

DoObserve ==
    /\ inc # <<>> /\ steps < MaxSteps /\ steps' = steps + 1
    /\ \E seen \in Seens(inc[1]) :
        LET r == ObserveOp(loc, inc[1], seen)
        IN IF r.err = "ok"
           THEN /\ inc' = <<r.inc>> /\ loc' = r.loc
                /\ IF r.ch THEN /\ Announce(Word(r.inc)) /\ obsOK' = (obsOK /\ U!Lt(seen, Word(r.inc)))
                           ELSE /\ UNCHANGED <<ann, mono, obsOK>> /\ heard' = U!Max(heard, U!Shr(seen, 16))
                /\ UNCHANGED floorOK
           ELSE UNCHANGED <<inc, loc, ann, mono, floorOK, obsOK, heard>>

DoFault ==
    /\ Faults /\ steps < MaxSteps /\ steps' = steps + 1
    /\ \E rf, sf \in BOOLEAN : loc' = [loc EXCEPT !.rf = rf, !.sf = sf]
    /\ UNCHANGED <<inc, ann, mono, floorOK, obsOK, heard>>

Next == DoStart \/ DoNext \/ DoBulk \/ DoObserve \/ DoFault
Spec == Init /\ [][Next]_vars

EpochBound == inc # <<>> => U!Le(inc[1].epoch, EpochMax)
SealedBeforeUse == (inc # <<>> /\ loc.pers) => loc.sealed = <<inc[1].epoch>>
Mono == loc.pers => mono
MonoAll == mono
FloorOK == floorOK
ObserveOK == obsOK
HlcMono == (TrackFloor /\ ~loc.pers) => mono

(***************************************************************************)
(* The closed form of BulkOp is the n-fold NextOp: checked for every      *)
(* sequence position near the end and every n up to 12 (BulkOK), over the  *)
(* stores that succeed and the ones that fail.                              *)
(***************************************************************************)
RECURSIVE FoldNext(_, _, _, _)
FoldNext(l, i, n, done) ==
    IF n = 0 THEN [err |-> "ok", inc |-> i, loc |-> l, done |-> done]
    ELSE LET r == NextOp(l, i)
         IN IF r.err # "ok" THEN [err |-> r.err, inc |-> i, loc |-> l, done |-> done]
            ELSE FoldNext(r.loc, r.inc, n - 1, done + 1)

BulkOK ==
    \A l \in [pers : BOOLEAN, sealed : {<<>>, <<U!W(9)>>}, rf : {FALSE}, sf : BOOLEAN] :
    \A e \in {U!W(3), U!Sub(EpochMax, U!W(1)), EpochMax} :
    \A s \in 65530..65535 :
    \A n \in 0..12 :
        LET a == BulkOp(l, [epoch |-> e, seq |-> s], n, 0)
            b == FoldNext(l, [epoch |-> e, seq |-> s], n, 0)
        IN a.done = b.done /\ a.inc = b.inc /\ a.loc = b.loc /\ (a.err = "ok") = (b.err = "ok")
ASSUME BulkOK
=============================================================================
