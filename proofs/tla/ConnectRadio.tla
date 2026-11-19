------------------------------ MODULE ConnectRadio ------------------------------
(***************************************************************************)
(* Model check of the radio adapter of local discovery: pinc-connect       *)
(* local.rs, Radio (new, admit), over every sequence of admissions of a    *)
(* frame of every length in LENS at every time 0..T (nanoseconds; the      *)
(* clock may step back), for every medium of MTUS x NSPBS x DUTIES (air    *)
(* time per byte and duty share in parts per thousand, 0 included). TOP is *)
(* the clock's maximum (u64::MAX), -1 when the clock never reaches it;     *)
(* MAXU stands for u64::MAX in the products (ConnectDutyOps.tla).          *)
(*                                                                         *)
(* Checked in every step (the doc of Radio: "it admits a beacon only if    *)
(* the medium's frame fits and the share of air time allows it"; of admit: *)
(* "On success the next admission waits for the off time that keeps the    *)
(* share"):                                                                *)
(*  - FitAndShare: an admitted frame fits the medium, the share is not 0,  *)
(*    and it comes no earlier than the previous admission plus that        *)
(*    frame's off time, air * 1000 / duty (rounded down, as the code       *)
(*    divides: the share is kept to within 1 ns per frame);                *)
(*  - RefusedUnchanged: a refused frame changes nothing.                   *)
(* Witness ConnectRadio_sat (TOP = T: the clock reaches u64::MAX) violates *)
(* FitAndShare: at the maximum the off time saturates away and frames are  *)
(* admitted back to back (a finding, see the report).                      *)
(***************************************************************************)
EXTENDS Integers, ConnectDutyOps

CONSTANTS TOP, MAXU, T, LENS, MTUS, NSPBS, DUTIES

VARIABLES rd, la, ev
vars == <<rd, la, ev>>

Init == /\ rd \in {RadioNew(m, n, du) : m \in MTUS, n \in NSPBS, du \in DUTIES}
        /\ la = [t |-> -1, ex |-> 0]
        /\ ev = [r |-> FALSE, len |-> 0]

Next == \E now \in 0..T, len \in LENS :
            LET r == RadioAdmit(TOP, MAXU, rd, now, len)
            IN /\ rd' = r.rd
               /\ la' = IF r.r THEN [t |-> now, ex |-> r.exact] ELSE la
               /\ ev' = [r |-> r.r, len |-> len]
Spec == Init /\ [][Next]_vars

FitAndShare == [][ev'.r => /\ ev'.len <= rd.mtu
                           /\ rd.duty > 0
                           /\ (la.t < 0 \/ la'.t >= la.t + la.ex)]_vars
RefusedUnchanged == [][~ev'.r => rd' = rd]_vars
=============================================================================
