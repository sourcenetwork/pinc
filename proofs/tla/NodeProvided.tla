----------------------------- MODULE NodeProvided -----------------------------
(***************************************************************************)
(* The roots a node serves (pinc-node values_provide.rs, Provided,         *)
(* Node::values_provide and values_unprovide) over every sequence of the   *)
(* two calls at a small cap (PROVIDED_MAX, 4096, in the code), with the    *)
(* values layer on (a node with the layer off answers false and holds no   *)
(* set). The operators are in NodeValuesNetOps.tla.                       *)
(*                                                                         *)
(* Checked, from the module and item documentation:                        *)
(*  - Bounded: at most PCAP roots;                                         *)
(*  - ProvideAnswer: a provide answers true exactly when the root is       *)
(*    registered afterwards, false when PCAP other roots are registered,   *)
(*    and a refused provide changes nothing;                               *)
(*  - UnprovideAnswer: an unprovide answers whether the root was           *)
(*    registered, and the root is not registered afterwards.               *)
(* Witness NodeProvided_full: the set fills and a provide is refused.      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets
CONSTANTS ROOTS, PCAP
VARIABLES pv, op
vars == <<pv, op>>

INSTANCE NodeValuesNetOps

Init == pv = {} /\ op = [k |-> "init", r |-> 0, ok |-> TRUE]
Next == \E r \in ROOTS :
          \/ LET x == Provide(pv, r, PCAP) IN pv' = x.pv /\ op' = [k |-> "provide", r |-> r, ok |-> x.ok]
          \/ LET x == Unprovide(pv, r) IN pv' = x.pv /\ op' = [k |-> "unprovide", r |-> r, ok |-> x.ok]
Spec == Init /\ [][Next]_vars

Bounded == Cardinality(pv) <= PCAP
ProvideAnswer == op'.k = "provide" =>
                     /\ op'.ok = (op'.r \in pv')
                     /\ ~op'.ok => (pv' = pv /\ op'.r \notin pv /\ Cardinality(pv) = PCAP)
UnprovideAnswer == op'.k = "unprovide" => (op'.ok = (op'.r \in pv) /\ op'.r \notin pv')
StepProps == [][ProvideAnswer /\ UnprovideAnswer]_vars

\* witness: a provide is refused
NeverRefused == ~(op.k = "provide" /\ ~op.ok)
=============================================================================
