------------------------------- MODULE Ext --------------------------------
(***************************************************************************)
(* The registry of extension frame types and the dispatch of a received    *)
(* extension frame (ExtOps.tla), checked on every type of a universe that  *)
(* holds the registered types, their neighbours, the unassigned types up   *)
(* to 0x60 and the varint widths, with every body length of interest and   *)
(* both answers of the release predicate of the access check               *)
(* (may_release: the session is allowed and its peer's cached answer       *)
(* still stands).                                                          *)
(*                                                                         *)
(*   TableOK      the const check of ext.rs accepts the table;             *)
(*   Disjoint     no two entries overlap and all are at or above the base  *)
(*                (stated apart from the check; UniqIsDisjoint: the check  *)
(*                accepts exactly the tables that satisfy it);             *)
(*   OneOwner     a type has at most one entry;                            *)
(*   Registered   every registered type is one the decoder accepts as an   *)
(*                extension;                                               *)
(*   Exclusive    a frame is handed to the sub-session layer only with its *)
(*                type, to the REACH_OUT ring only with its type, and the  *)
(*                application ring never takes either of those types;      *)
(*   Total        for every registered type there is an input that is      *)
(*                handed to the layer that registered it;                  *)
(*   Gate         a frame of a session that may not release (not allowed, *)
(*                denied, or its peer's answer lapsed) never reaches the   *)
(*                application ring;                                        *)
(*   Unregistered a type at or above the base nobody registered is taken   *)
(*                by the decoder, goes to the application ring and neither *)
(*                values handler takes it (it is ignored, and the          *)
(*                connection stays open: no route closes it);              *)
(*   Values       the values server takes PROOF_REQ and the fetch takes    *)
(*                PROOF, no type is taken by both, and each type a handler *)
(*                takes is the one registered to its layer.                *)
(***************************************************************************)
EXTENDS ExtOps, Naturals, FiniteSets, TLC

VARIABLE x

Tys == (0..96) \cup {127, 128, 16383, 16384, 1073741823}
Lens == {0, 1, 2, 100, 153, 154, 1100}
Dests == {"sub", "reach", "ring", "drop"}

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

\* The table is a constant, so each property below reads the variable too: TLC then reports a false one as an invariant
\* "violated by the initial state", which is what the witness check of scripts/proofs.sh looks for.
On == x = 0

TableOK == On /\ Uniq(Tab)
Disjoint == /\ On
            /\ \A i \in 1..Len(Tab) : Tab[i].lo <= Tab[i].hi /\ Tab[i].lo >= BASE
            /\ \A i, j \in 1..Len(Tab) : i # j => ~Overlap(Tab[i], Tab[j])
UniqIsDisjoint == Uniq(Tab) <=> Disjoint
OneOwner == \A t \in Tys : Cardinality(Owners(t)) <= 1
Registered == \A t \in Tys : Owner(t) # "none" => Decodes(t)
Exclusive == On /\ \A t \in Tys, l \in Lens, a \in BOOLEAN :
    /\ Route(t, l, a) \in Dests
    /\ Route(t, l, a) = "sub" => t = SUB
    /\ Route(t, l, a) = "reach" => t = REACH
    /\ Route(t, l, a) = "ring" => t # SUB /\ t # REACH
    /\ Owner(t) \in {"sub", "reach"} => Route(t, l, a) # "ring"
Total == \A i \in 1..Len(Tab) : \A t \in Tab[i].lo..Tab[i].hi :
    \E l \in Lens, a \in BOOLEAN : Route(t, l, a) = DestOf(Tab[i].who)
Gate == On /\ \A t \in Tys, l \in Lens : Route(t, l, FALSE) # "ring"
Unregistered == \A t \in Tys : (t >= BASE /\ Owner(t) = "none") =>
    /\ Decodes(t)
    /\ \A l \in Lens, a \in BOOLEAN : Route(t, l, a) = (IF l > 0 /\ a THEN "ring" ELSE "drop")
    /\ ~ServeTakes(t) /\ ~FetchTakes(t)
Values == \A t \in Tys :
    /\ ~(ServeTakes(t) /\ FetchTakes(t))
    /\ ServeTakes(t) => Owner(t) = "serve"
    /\ FetchTakes(t) => Owner(t) = "fetch"
    /\ Owner(t) \in {"serve", "fetch"} =>
         \A l \in Lens, a \in BOOLEAN : Route(t, l, a) = (IF l > 0 /\ a THEN "ring" ELSE "drop")

=============================================================================
