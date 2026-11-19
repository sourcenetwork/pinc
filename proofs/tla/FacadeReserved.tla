---------------------------- MODULE FacadeReserved ----------------------------
(***************************************************************************)
(* The bytes an application may not sign with the identity key:            *)
(* crates/pinc/src/reserved.rs `PREFIXES` and `check` (called by           *)
(* `Endpoint::sign`). Bytes are sequences of byte codes.                   *)
(*                                                                         *)
(* The four prefixes are written here from the documented constants, not   *)
(* read from the code: pinc-crypto kdf.rs `labels::RESERVED` ("PINC 2026 ", *)
(* the start of every label of any version), pinc-connect record.rs        *)
(* `MAGIC_PREFIX` ("VNCREC"), local.rs `MAGIC_PREFIX` ("VNCBCN") and       *)
(* relay/sleep.rs `LABEL` ("pinc-sleep"). TraceFacadeReserved checks that  *)
(* the code's PREFIXES are these and that each starts what its module      *)
(* really signs.                                                           *)
(*                                                                         *)
(* Cases (a machine whose root has one successor per case): every prefix,  *)
(* every proper cut of one (empty included), every prefix with one byte    *)
(* changed (to the code + 1, XOR 0x20 and 0), every prefix with a byte     *)
(* appended, the label start with versions "v1 " and "v9 " and a tail.     *)
(* Each case says by construction whether it begins with a reserved        *)
(* statement (want); RefusesExactly: `check` refuses it exactly then.      *)
(* Distinct: no prefix starts another, so a cut is never refused because   *)
(* of a shorter prefix.                                                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

\* "PINC 2026 ", "VNCREC", "VNCBCN", "pinc-sleep" as byte codes
Label == <<80, 73, 78, 67, 32, 50, 48, 50, 54, 32>>
Record == <<86, 78, 67, 82, 69, 67>>
Beacon == <<86, 78, 67, 66, 67, 78>>
Sleep == <<112, 105, 110, 99, 45, 115, 108, 101, 101, 112>>
Prefixes == <<Label, Record, Beacon, Sleep>>
PSet == {Prefixes[k] : k \in 1..4}

StartsWith(d, p) == Len(d) >= Len(p) /\ SubSeq(d, 1, Len(p)) = p
\* `check`: refused when some prefix starts the data
Refused(d) == \E k \in 1..4 : StartsWith(d, Prefixes[k])

Changed(p, k, v) == [p EXCEPT ![k] = v]
Xor32(c) == IF (c \div 32) % 2 = 1 THEN c - 32 ELSE c + 32
Vals(c) == {(c + 1) % 256, Xor32(c), 0} \ {c}

\* the cases: a cut is proper, a change is one of Vals at a position inside the prefix
Cut == {[d |-> p, want |-> TRUE] : p \in PSet}
       \cup {[d |-> SubSeq(p, 1, n), want |-> FALSE] : p \in PSet, n \in {m \in 0..10 : m < Len(p)}}
       \cup UNION {{[d |-> Changed(p, k, v), want |-> FALSE] : v \in Vals(p[k])} : <<p, k>> \in
                   {<<q, j>> \in PSet \X (1..10) : j <= Len(q)}}
       \cup {[d |-> p \o <<x>>, want |-> TRUE] : p \in PSet, x \in {0, 32, 120, 255}}
       \cup {[d |-> Label \o <<118, x, 32, 1, 2, 3>>, want |-> TRUE] : x \in {49, 57}}

VARIABLE cs
Init == cs = [d |-> <<>>, want |-> FALSE, root |-> TRUE]
Next == cs.root /\ \E c \in Cut : cs' = [d |-> c.d, want |-> c.want, root |-> FALSE]
Spec == Init /\ [][Next]_cs

RefusesExactly == Refused(cs.d) = cs.want
Distinct == \A j, k \in 1..4 : j # k => ~StartsWith(Prefixes[j], Prefixes[k])
=============================================================================
