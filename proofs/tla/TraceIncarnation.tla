--------------------------- MODULE TraceIncarnation ---------------------------
(***************************************************************************)
(* Trace validation of the incarnation and the address tag: pinc-membership *)
(* incarnation.rs (Incarnation::start, next_record, observe, AddressTag).   *)
(*                                                                         *)
(* The Rust test tests/trace_membership.rs (part inc) runs the real code    *)
(* through seeded lives on a persistent store (with read and write          *)
(* failures), on the clock fallback, across restarts with wall clock jumps  *)
(* back and forward, floors, records past the end of the sequence, observed *)
(* words below, at and above the node's own, the epoch space running out,   *)
(* and a tag moved many times (more than 255) around the settle time. Each  *)
(* event carries the store as the call found it; it must equal the result   *)
(* of the operator of Incarnation.tla (StartOp, NextOp, BulkOp, ObserveOp,  *)
(* MovedOp, TagOp): the same outcome, the same word, the same store after   *)
(* (an error leaves the store as it was).                                   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment      *)
(* variable PINC_TRACE_DIR, the directory that holds minc.ndjson.           *)
(* Lean counterpart: Pinc/TraceMembershipInc.lean.                          *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLES i, run, inc, tg
vars == <<i, run, inc, tg>>

INC == INSTANCE Incarnation WITH PersModes <- {TRUE}, TrackFloor <- FALSE, Faults <- FALSE, MaxSteps <- 0,
                                 loc <- 0, inc <- 0, ann <- 0, mono <- 0, floorOK <- 0, obsOK <- 0, heard <- 0, steps <- 0
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/minc.ndjson")

Ev == Trace[i]

Opt(l) == IF l = <<>> THEN <<>> ELSE <<U!FromLimbs(l[1])>>
LocalOf == [pers |-> Ev.pers, sealed |-> Opt(Ev.sl), rf |-> Ev.rf, sf |-> Ev.sf]

(* the state of this run: a new run starts with no incarnation and a fresh tag *)
Fresh == Ev.run # run
CurInc == IF Fresh THEN <<>> ELSE inc
CurTag == IF Fresh THEN INC!TagInit ELSE tg

Init == i = 1 /\ run = -1 /\ inc = <<>> /\ tg = INC!TagInit

(* the recorded outcome against the operator's: the error name, the word, the store afterwards *)
OutOK(r) ==
    IF r.err = "ok"
    THEN /\ Ev.ok /\ U!FromLimbs(Ev.w) = INC!Word(r.inc) /\ Opt(Ev.sl2) = r.loc.sealed
    ELSE /\ ~Ev.ok /\ Ev.err = r.err /\ Opt(Ev.sl2) = Opt(Ev.sl)

StartEv ==
    LET r == INC!StartOp(LocalOf, U!FromLimbs(Ev.wall), U!FromLimbs(Ev.fl))
    IN /\ Ev.op = "st" /\ OutOK(r)
       /\ inc' = (IF r.err = "ok" THEN <<r.inc>> ELSE CurInc) /\ tg' = CurTag

NextEv ==
    LET r == INC!NextOp(LocalOf, CurInc[1])
    IN /\ Ev.op = "nr" /\ CurInc # <<>> /\ OutOK(r)
       /\ inc' = (IF r.err = "ok" THEN <<r.inc>> ELSE CurInc) /\ tg' = CurTag

BulkEv ==
    LET r == INC!BulkOp(LocalOf, CurInc[1], Ev.n, 0)
    IN /\ Ev.op = "nrn" /\ CurInc # <<>> /\ Ev.done = r.done
       /\ IF r.err = "ok"
          THEN Ev.ok /\ U!FromLimbs(Ev.w) = INC!Word(r.inc) /\ Opt(Ev.sl2) = r.loc.sealed
          ELSE ~Ev.ok /\ Ev.err = r.err /\ Opt(Ev.sl2) = r.loc.sealed
       /\ inc' = <<r.inc>> /\ tg' = CurTag

ObserveEv ==
    LET r == INC!ObserveOp(LocalOf, CurInc[1], U!FromLimbs(Ev.seen))
    IN /\ Ev.op = "ob" /\ CurInc # <<>> /\ OutOK(r) /\ (r.err = "ok" => Ev.ch = r.ch)
       /\ inc' = (IF r.err = "ok" THEN <<r.inc>> ELSE CurInc) /\ tg' = CurTag

MoveEv ==
    /\ Ev.op = "mv" /\ tg' = INC!MovedOp(CurTag, U!FromLimbs(Ev.now)) /\ inc' = CurInc

TagEv ==
    LET r == INC!TagOp(CurTag, U!FromLimbs(Ev.now), Ev.refl, Ev.tk)
    IN /\ Ev.op = "tg" /\ Ev.tag = r.tag /\ Ev.mv = r.t.moves /\ tg' = r.t /\ inc' = CurInc

Step ==
    /\ i <= Len(Trace)
    /\ Ev.t = "mi"
    /\ \/ StartEv \/ NextEv \/ BulkEv \/ ObserveEv \/ MoveEv \/ TagEv
    /\ run' = Ev.run /\ i' = i + 1

(* the trace has ended: every event was a step of the model *)
Finished == i > Len(Trace) /\ UNCHANGED vars

TNext == Step \/ Finished

TraceSpec == Init /\ [][TNext]_vars

(* the facts of the model hold on every recorded state *)
Inv == inc # <<>> => /\ U!Le(inc[1].epoch, INC!EpochMax) /\ inc[1].seq \in 0..65535
=============================================================================
