--------------------------- MODULE TraceDtnRequest ---------------------------
(***************************************************************************)
(* Trace validation of a delay-tolerant transfer's request side            *)
(* (pinc-node dtn_rx.rs `dtn_offered`, `dtn_advance`, `dtn_data`,          *)
(* `dtn_finish`; dtn.rs `Dtn::want`) against DtnRequest.tla, one holder,   *)
(* no drops.                                                               *)
(*                                                                         *)
(* The Rust test tests/trace_dtn_request.rs sends one bundle of the        *)
(* model's geometry (k = 2, m = 1, two blocks, slices of 4 KiB, so         *)
(* `Dtn::want` asks at most 16 symbols at once) from a source to a         *)
(* destination, with the source's copy corrupt in the symbols of one of    *)
(* the model's cases ("none", "one" {1, 3}, "two" {3, 5}, "allbad"         *)
(* every symbol). It writes, for each case, a "case" event and then the    *)
(* destination's own node trace of the transfer, in order: DtnSymbols      *)
(* ("sym", the first symbol of a run that verified), DtnLost ("lost", the  *)
(* symbol that failed its proof), DtnParity ("parity", the parity symbols  *)
(* of a new ask), DtnRefused ("refused", reason 4: a stuck block) and      *)
(* DtnComplete ("complete"), up to the first complete or the third         *)
(* refusal. The source offers again after a refusal.                       *)
(*                                                                         *)
(* With one holder and no drops the model has exactly one behaviour per   *)
(* case. The trace spec runs the model's own Offer and Serve and requires  *)
(* each to be followed by the events the code traces for it: a Serve by    *)
(* "sym" (nothing failed: the run's first symbol) or "lost" (the first     *)
(* corrupt symbol asked for); then, after either action, "parity" when the *)
(* new ask holds parity, "complete" when the bundle was finished, or       *)
(* "refused" when the holder was refused as stuck. An Offer that only asks *)
(* for data traces nothing, so the model's Offer may take no event. Every  *)
(* state satisfies the invariants of DtnRequest.cfg.                       *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dtn_request.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

VARIABLES have, lost, shared, st, ask, base, refused, done, drops, cs, i
mvars == <<have, lost, shared, st, ask, base, refused, done, drops>>
vars == <<have, lost, shared, st, ask, base, refused, done, drops, cs, i>>

\* One instance per corruption case; one holder, no drops, a run of at most 16 symbols (64 KiB of 4 KiB slices),
\* every guard as the code has it.
DN == INSTANCE DtnRequest WITH NH <- 1, Case <- "none", MaxRun <- 16, MaxDrops <- 0, MarkLost <- TRUE,
                               DataFirst <- TRUE, NeedCap <- TRUE, PerTransfer <- TRUE, StopStuck <- TRUE
DO == INSTANCE DtnRequest WITH NH <- 1, Case <- "one", MaxRun <- 16, MaxDrops <- 0, MarkLost <- TRUE,
                               DataFirst <- TRUE, NeedCap <- TRUE, PerTransfer <- TRUE, StopStuck <- TRUE
DT == INSTANCE DtnRequest WITH NH <- 1, Case <- "two", MaxRun <- 16, MaxDrops <- 0, MarkLost <- TRUE,
                               DataFirst <- TRUE, NeedCap <- TRUE, PerTransfer <- TRUE, StopStuck <- TRUE
DA == INSTANCE DtnRequest WITH NH <- 1, Case <- "allbad", MaxRun <- 16, MaxDrops <- 0, MarkLost <- TRUE,
                               DataFirst <- TRUE, NeedCap <- TRUE, PerTransfer <- TRUE, StopStuck <- TRUE

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dtn_request.ndjson")
Ev == Trace[i]

\* The refusal code of a stuck block (dtn_wire.rs Refusal::BadProof).
BadProof == 4

MinOf(S) == CHOOSE s \in S : \A t \in S : s <= t

\* The corrupt symbols of the holder's copy in the current case.
BadNow == CASE cs = "none" -> DN!Bad[1] [] cs = "one" -> DO!Bad[1] [] cs = "two" -> DT!Bad[1] [] cs = "allbad" -> DA!Bad[1]

\* The events the code traces once a model step has decided what comes next (Next1): the parity of a new ask, a
\* finished bundle, or a refusal (the only other way a transfer ends here).
Outcome ==
    IF st'[1] = "asking"
    THEN LET p == Cardinality({s \in ask'[1] : DN!IsParity(s)})
         IN IF p > 0 THEN <<[t |-> "parity", n |-> p]>> ELSE <<>>
    ELSE IF done' THEN <<[t |-> "complete"]>>
    ELSE <<[t |-> "refused", reason |-> BadProof]>>

\* What dtn_data traces for the answer to the ask out: the run's first symbol when all of it verified, else the
\* first corrupt symbol (the ones before it are kept).
Answer == LET bad == ask[1] \cap BadNow
          IN IF bad = {} THEN [t |-> "sym", first |-> MinOf(ask[1])] ELSE [t |-> "lost", symbol |-> MinOf(bad)]

\* The next events of the trace are exactly sq.
Expect(sq) == /\ i + Len(sq) - 1 <= Len(Trace)
              /\ \A j \in 1..Len(sq) : Trace[i + j - 1] = sq[j]
              /\ i' = i + Len(sq)

\* A case starts: the bundle's geometry is the model's, the receiver holds nothing.
Start == /\ Ev.t = "case"
         /\ Ev.case \in {"none", "one", "two", "allbad"}
         /\ Ev.k = 2 /\ Ev.m = 1 /\ Ev.blocks = 2 /\ Ev.max = 16
         /\ cs' = Ev.case
         /\ have' = {} /\ lost' = [x \in {1} |-> {}] /\ shared' = {} /\ st' = [x \in {1} |-> "idle"]
         /\ ask' = [x \in {1} |-> {}] /\ base' = [x \in {1} |-> {}] /\ refused' = {} /\ done' = FALSE /\ drops' = 0
         /\ i' = i + 1

OfferStep == /\ \/ cs = "none" /\ DN!Offer(1)
                \/ cs = "one" /\ DO!Offer(1)
                \/ cs = "two" /\ DT!Offer(1)
                \/ cs = "allbad" /\ DA!Offer(1)
             /\ Expect(Outcome)
             /\ UNCHANGED cs

ServeStep == /\ \/ cs = "none" /\ DN!Serve(1)
                \/ cs = "one" /\ DO!Serve(1)
                \/ cs = "two" /\ DT!Serve(1)
                \/ cs = "allbad" /\ DA!Serve(1)
             /\ Expect(<<Answer>> \o Outcome)
             /\ UNCHANGED cs

Init == /\ DN!Init /\ cs = "none" /\ i = 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (Start \/ OfferStep \/ ServeStep)) \/ Done
TraceSpec == Init /\ [][TNext]_vars

\* the invariants of DtnRequest.cfg; whether a refused holder had a corrupt copy depends on the case
Inv == /\ DN!TypeOK /\ DN!NoParityWithoutLoss /\ DN!AskWithinNeed /\ DN!AskFresh /\ DN!ActiveReachable
       /\ DN!LostBounded /\ DN!FinishDecodable
       /\ \A x \in refused : BadNow # {}
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
