------------------------- MODULE TraceFacadeReserved -------------------------
(***************************************************************************)
(* Trace validation of crates/pinc/src/reserved.rs (`PREFIXES`, `check`)   *)
(* against FacadeReserved.tla.                                             *)
(*                                                                         *)
(* The unit test `reserved::tests::trace_reserved` (both builds of the     *)
(* crate `pinc`, file facade_reserved.ndjson) records the code's PREFIXES, *)
(* the statements the modules really sign (from their own functions, as    *)
(* `signed_statements` builds them) with `check`'s answer, and `check`'s   *)
(* answer on the cases of FacadeReserved built from the recorded prefixes. *)
(* The prefixes must be the documented constants of the model, each        *)
(* statement must start with its prefix and be refused, and every answer   *)
(* must be the model's.                                                    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds                       *)
(* facade_reserved.ndjson.                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd
VARIABLE x

R == INSTANCE FacadeReserved WITH cs <- [d |-> <<>>, want |-> FALSE, root |-> TRUE]

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/facade_reserved.ndjson")
Of(op) == {k \in DOMAIN Trace : Trace[k].op = op}

EvOK(k) ==
    LET ev == Trace[k]
    IN CASE ev.op = "prefixes" -> ev.p = R!Prefixes
         [] ev.op = "stmt" -> ev.k \in 1..4 /\ R!StartsWith(ev.d, R!Prefixes[ev.k]) /\ ev.refused = TRUE
         [] ev.op = "case" -> ev.refused = R!Refused(ev.d)
         [] OTHER -> FALSE

Init == x = 0
Next == UNCHANGED x
TraceSpec == Init /\ [][Next]_x

AllOK == /\ \A k \in DOMAIN Trace : Trace[k].t = "reserved" /\ EvOK(k)
         /\ Cardinality(Of("prefixes")) >= 1
         /\ {Trace[k].k : k \in Of("stmt")} = 1..4
         \* every case of the model was recorded
         /\ {c.d : c \in R!Cut} \subseteq {Trace[k].d : k \in Of("case")}
\* the end check (TraceEnd.tla): the one state checks every line of a trace that has one
ReplayAtEnd == ReplaySeen(TRUE)
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
