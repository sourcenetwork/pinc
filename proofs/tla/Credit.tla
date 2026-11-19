------------------------------- MODULE Credit -------------------------------
(***************************************************************************)
(* The credit record of pinc-security credit.rs: three u16 fields (stream  *)
(* window in units, concurrent streams, largest datagram), 6 bytes on the  *)
(* wire, three big-endian u16s.                                            *)
(*                                                                         *)
(* SCALING. The code has fields of 16 bits and bytes of 8 bits (a field is *)
(* two bytes), and a window unit of 2^14 bytes. The model is parameterised *)
(* by W, the field width in bits (even; the byte width is W / 2), and Unit,*)
(* the window unit: the real code is W = 16, Unit = 16384 (TraceSecurity   *)
(* instantiates exactly that); TLC checks W = 2 (4 field values, 2 byte    *)
(* values) and W = 4 (16 field values, 4 byte values) exhaustively, with   *)
(* Unit = 4 (W = 6 also passes, in 31 s on a busy host). The facts below *)
(* are checked over every record and every 6-byte string of the width, so  *)
(* they are the exhaustive statement at that width; Lean (Credit.lean)     *)
(* proves them for W = 16.                                                 *)
(*                                                                         *)
(* Checked: decode (encode r) = r for every record; encode (decode b) = b  *)
(* for every 6-byte string, and decode b is a record (so every string      *)
(* decodes to exactly one record and encode is a bijection); encode is     *)
(* injective (the image has as many elements as there are records); new    *)
(* rounds the window down to whole units, saturates at the largest field,  *)
(* never grants more than asked in window, streams or datagram bytes, and  *)
(* window_bytes < 2^W * Unit (2^30 in the code) and = units * Unit;       *)
(* covers is reflexive, transitive (on records up to CovMax per field),    *)
(* antisymmetric, every record covers NONE and NONE covers only itself.    *)
(*                                                                         *)
(* NewFromUnits takes the quotient window_bytes / Unit, which is how the   *)
(* trace check supplies a window request that does not fit a TLC integer.  *)
(* The operators are CreditOps.tla, which the trace check instantiates.    *)
(* Lean counterpart: proofs/lean/Pinc/Credit.lean.                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS W, Unit, CovMax
VARIABLE x

C == INSTANCE CreditOps

None == C!None
Encode(r) == C!Encode(r)
Decode(b) == C!Decode(b)
NewFromUnits(q, s, d) == C!NewFromUnits(q, s, d)
New(w, s, d) == C!New(w, s, d)
WindowBytes(r) == C!WindowBytes(r)
Covers(a, b) == C!Covers(a, b)
Bs == C!Bs
MaxF == C!MaxF

Records == [wu: 0..MaxF, ms: 0..MaxF, md: 0..MaxF]
Bytes6 == [1..6 -> 0..(Bs - 1)]
CovRecords == [wu: 0..CovMax, ms: 0..CovMax, md: 0..CovMax]
WMax == (MaxF + 3) * Unit

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

DecodeEncode == \A r \in Records : Decode(Encode(r)) = r
EncodeDecode == \A b \in Bytes6 : Decode(b) \in Records /\ Encode(Decode(b)) = b
EncodeLength == \A r \in Records : Len(Encode(r)) = 6 /\ \A i \in 1..6 : Encode(r)[i] \in 0..(Bs - 1)
EncodeInjective == Cardinality({Encode(r) : r \in Records}) = Cardinality(Records)
Bijection == Cardinality(Records) = Cardinality(Bytes6)

NewSpec ==
    \A w \in 0..WMax, s \in 0..MaxF, d \in 0..MaxF :
        LET r == New(w, s, d)
        IN /\ r \in Records
           /\ r.ms = s /\ r.md = d
           /\ WindowBytes(r) <= w                                  \* never grants more than asked
           /\ WindowBytes(r) % Unit = 0                            \* whole units
           /\ (w < WindowBytes(r) + Unit \/ r.wu = MaxF)           \* rounded down by less than a unit
           /\ (w >= MaxF * Unit => r.wu = MaxF)                    \* saturates
           /\ (w < MaxF * Unit => r.wu = w \div Unit)

WindowBound == \A r \in Records : WindowBytes(r) < (MaxF + 1) * Unit /\ WindowBytes(r) = r.wu * Unit

CoversRefl == \A r \in CovRecords : Covers(r, r)
CoversTrans == \A a, b, c \in CovRecords : (Covers(a, b) /\ Covers(b, c)) => Covers(a, c)
CoversAntisym == \A a, b \in CovRecords : (Covers(a, b) /\ Covers(b, a)) => a = b
CoversNone == \A r \in Records : Covers(r, None)
NoneCoversOnlyNone == \A r \in Records : Covers(None, r) => r = None
=============================================================================
