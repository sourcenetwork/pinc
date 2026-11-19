---------------------------- MODULE TracePathHeld ----------------------------
(***************************************************************************)
(* Trace validation of the held-address flag, pinc-transport               *)
(* conn/path_held.rs, on a real connection.                                *)
(*                                                                         *)
(* The Rust test tests/trace_path_held.rs drives a connected client (4     *)
(* path slots) through `add_path`, `remove_path` and `set_path_held` with  *)
(* tracked and untracked ids and both flags, and records after each call   *)
(* what `trace_held_paths` (cargo feature `trace`) reads: the count        *)
(* `Paths::held` and every slot as null or [id limbs, flag], with          *)
(* `has_held_paths`. A `set_path_held` must be the step of PathHeld.tla:   *)
(* the tracked path's flag set and nothing else changed, nothing changed   *)
(* for an untracked id. Any other call may only empty slots or put a path  *)
(* not tracked before, flag clear, into a slot. After every call the count *)
(* is the recount of the slots and `has_held_paths` is whether it is       *)
(* above zero.                                                             *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds path_held.ndjson.     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
VARIABLES i, slots
vars == <<i, slots>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/path_held.ndjson")
Ev0 == Trace[i]

\* a slot as recorded: <<>> (JSON null is written as []) or <<id limbs, flag>>
On(s) == s # <<>>
Places(ss) == DOMAIN ss
Tracked(ss) == {ss[k][1] : k \in {j \in Places(ss) : On(ss[j])}}
Recount(ss) == Cardinality({k \in Places(ss) : On(ss[k]) /\ ss[k][2]})

Read(v) == /\ v.held = Recount(v.slots)
           /\ v.has = (v.held > 0)

SetEv == LET ss == Ev0.v.slots
             hit == {k \in Places(slots) : On(slots[k]) /\ slots[k][1] = Ev0.id}
         IN /\ Ev0.op = "set"
            /\ IF hit = {}
               THEN ss = slots
               ELSE \E k \in hit : /\ ss[k] = <<Ev0.id, Ev0.h>>
                                   /\ \A j \in Places(slots) : j # k => ss[j] = slots[j]
            /\ slots' = ss
OtherEv == LET ss == Ev0.v.slots
           IN /\ Ev0.op \in {"init", "add", "remove", "drive"}
              /\ (Ev0.op = "init" => \A k \in Places(ss) : ~On(ss[k]) \/ ~ss[k][2])
              /\ (Ev0.op # "init" => /\ DOMAIN ss = Places(slots)
                                     /\ \A k \in Places(ss) :
                                          \/ ss[k] = slots[k]
                                          \/ ~On(ss[k])
                                          \/ (ss[k][2] = FALSE /\ ss[k][1] \notin Tracked(slots)))
              /\ slots' = ss

Init == i = 1 /\ slots = <<>>
Step == /\ i <= Len(Trace) /\ Ev0.t = "path_held"
        /\ Read(Ev0.v)
        /\ (SetEv \/ OtherEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* a path id is in at most one slot
Inv == \A j, k \in Places(slots) : (j # k /\ On(slots[j]) /\ On(slots[k])) => slots[j][1] # slots[k][1]
=============================================================================
