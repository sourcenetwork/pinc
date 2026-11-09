----------------------------- MODULE NanosCheck -----------------------------
(* Loads Nanos.tla so TLC evaluates its ASSUME statements (the operators against hand-computed values). *)
EXTENDS Nanos
VARIABLE x
Init == x = 0
Next == x' = x
=============================================================================
