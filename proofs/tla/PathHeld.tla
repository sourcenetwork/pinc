------------------------------ MODULE PathHeld ------------------------------
(***************************************************************************)
(* The held-address flag of a connection's paths, pinc-transport           *)
(* conn/path_held.rs: `Paths::recount`, `Connection::set_path_held` and    *)
(* `Connection::has_held_paths`, with the slot changes of conn/path.rs     *)
(* that recount after them: `new_path_slot` (from `add_path` and           *)
(* `learn_path`: a path not yet tracked, unheld, into a free slot or over  *)
(* another path), `remove_path` and `forget_gone` (a slot emptied). The    *)
(* path.rs rules for which slot may be taken or emptied (never the active  *)
(* path) are not this unit's; the model lets every slot be taken or        *)
(* emptied, which only adds behaviours. A path id is in at most one slot   *)
(* (path.rs: "A path is never held twice").                                *)
(*                                                                         *)
(* Checked, the invariants of the module doc:                              *)
(*  - HeldCount: `Paths::held` equals the number of tracked paths whose    *)
(*    flag is set, so `has_held_paths` (one read) is whether any is held;  *)
(*  - SetExact: `set_path_held` on a tracked path sets that path's flag    *)
(*    and nothing else; on a path not tracked it changes nothing.          *)
(* PathHeld_drop is a reachability witness: a held path leaves its slot,   *)
(* so HeldCount is checked where the count must fall.                      *)
(* Not modelled: what the flag stops (conn/send.rs, outside this unit):   *)
(* the size probe, and in a validated session a send past the path's own  *)
(* budget (amp_room).                                                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets
CONSTANTS NP, IDS
ASSUME NP >= 1
VARIABLES slots, held, last
vars == <<slots, held, last>>

None == [id |-> 0, held |-> FALSE, on |-> FALSE]
Slot0 == 0..(NP - 1)
Tracked(s) == {s[i].id : i \in {j \in Slot0 : s[j].on}}
\* `Paths::recount`
Recount(s) == Cardinality({i \in Slot0 : s[i].on /\ s[i].held})
\* `Paths::find`: the slot of path id, or -1
Find(s, id) == IF id \in Tracked(s) THEN CHOOSE i \in Slot0 : s[i].on /\ s[i].id = id ELSE -1

Init == slots = [i \in Slot0 |-> None] /\ held = 0 /\ last = [op |-> "init", gone |-> FALSE]

\* `new_path_slot`: a path not tracked, its flag clear, then a recount
NewPath == \E i \in Slot0, id \in IDS :
    /\ id \notin Tracked(slots)
    /\ slots' = [slots EXCEPT ![i] = [id |-> id, held |-> FALSE, on |-> TRUE]]
    /\ held' = Recount(slots')
    /\ last' = [op |-> "new", gone |-> slots[i].on /\ slots[i].held]
\* `remove_path` or `forget_gone`: a slot emptied, then a recount
Empty == \E i \in Slot0 :
    /\ slots[i].on
    /\ slots' = [slots EXCEPT ![i] = None]
    /\ held' = Recount(slots')
    /\ last' = [op |-> "empty", gone |-> slots[i].held]
\* `set_path_held(id, h)`
SetHeld == \E id \in IDS, h \in BOOLEAN :
    LET i == Find(slots, id)
    IN IF i < 0
       THEN UNCHANGED <<slots, held>> /\ last' = [op |-> "ignored", gone |-> FALSE]
       ELSE /\ slots' = [slots EXCEPT ![i].held = h]
            /\ held' = IF slots[i].held # h THEN Recount(slots') ELSE held
            /\ last' = [op |-> "set", gone |-> FALSE, id |-> id, h |-> h]

Next == NewPath \/ Empty \/ SetHeld
Spec == Init /\ [][Next]_vars

TypeOK == held \in 0..NP /\ \A i \in Slot0 : slots[i].on => slots[i].id \in IDS
OneSlotPerId == \A i, j \in Slot0 : (i # j /\ slots[i].on /\ slots[j].on) => slots[i].id # slots[j].id
HeldCount == held = Recount(slots)
HasHeld == (held > 0) = (\E i \in Slot0 : slots[i].on /\ slots[i].held)
SetExact == [][/\ last'.op = "ignored" => (slots' = slots /\ held' = held)
               /\ last'.op = "set" =>
                    LET i == Find(slots, last'.id)
                    IN /\ slots'[i].held = last'.h
                       /\ \A j \in Slot0 : j # i => slots'[j] = slots[j]
                       /\ slots'[i].id = slots[i].id]_vars

\* a reachability witness: a held path leaves its slot
NoHeldGone == ~last.gone
=============================================================================
