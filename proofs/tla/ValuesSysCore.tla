------------------------------ MODULE ValuesSysCore ------------------------------
(***************************************************************************)
(* The part of the value fetch system model that does not depend on the    *)
(* scenario constants: the bookkeeping of events and of the final event,    *)
(* and the predicates every state of every run must satisfy. ValuesSys.tla  *)
(* model checks them over all behaviours; TraceValuesSys.tla applies the    *)
(* very same definitions to the states a recorded run of the Rust fetcher   *)
(* passes through.                                                          *)
(*                                                                          *)
(* A state is a record with (at least) these fields: run ("idle", "run",     *)
(* "done"), fin (the final event, "none" before), nfin and late (final       *)
(* events emitted, events emitted after the final one), ann (Readable events *)
(* per group, capped at 2), wr (what the store holds per group: "none",      *)
(* "true" or "junk"), ver (committed groups), ver0 (committed at the start), *)
(* hd (the held first granule, -1 none), inP (still a candidate) and lied.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

NONE == "none"

Late(T) == IF T.run = "done" THEN 1 ELSE 0

Readable(T, g) == [T EXCEPT !.ann[g] = IF T.ann[g] = 2 THEN 2 ELSE T.ann[g] + 1, !.late = T.late + Late(T)]

(* the final event *)
Final(T, f) == [T EXCEPT !.run = "done", !.fin = f, !.nfin = T.nfin + 1, !.late = T.late + Late(T)]

(* the held first granule is announced *)
ReleaseHd(T) == IF T.hd >= 0 THEN [Readable(T, T.hd) EXCEPT !.hd = -1, !.rel = TRUE] ELSE T

(* 1: every byte in the store and every Readable event is a byte of the true value *)
SoundStore(T, Grps) == \A g \in Grps : T.wr[g] # "junk" /\ (g \in T.ver => T.wr[g] = "true")
SoundEvents(T, Grps) ==
    /\ \A g \in Grps : T.ann[g] > 0 => (g \in T.ver /\ T.wr[g] = "true")
    /\ (T.hd >= 0 => T.hd \in T.ver)

(* exactly one final event, none after it *)
OneFinalP(T) ==
    /\ T.late = 0 /\ T.nfin <= 1 /\ (T.run = "done") = (T.nfin = 1) /\ (T.fin = NONE) = (T.nfin = 0)

(* the final event is the right one *)
ReasonOk(T, Want, Listed, Empty, RootOk, StoreFail, HasDl, DeadlineT) ==
    /\ T.fin = "EveryProviderLied" => (Listed # {} /\ \A p \in Listed : ~T.inP[p] /\ Listed \subseteq T.lied)
    /\ T.fin = "Deadline" => (HasDl /\ T.now > DeadlineT)
    /\ T.fin = "NoProvider" => Listed = {}
    /\ T.fin = "Store" => StoreFail
    /\ T.fin = "BadRoot" => (Empty /\ ~RootOk)
    /\ T.fin = "Complete" => (Want \subseteq T.ver /\ T.hd = -1 /\ \A g \in Want \ T.ver0 : T.ann[g] >= 1)

=============================================================================
