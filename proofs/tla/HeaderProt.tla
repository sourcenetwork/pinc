----------------------------- MODULE HeaderProt -----------------------------
(***************************************************************************)
(* Model of the header protection of vinc-security record.rs               *)
(* (HeaderKey::protect, unprotect and the helper apply) on bytes.          *)
(*                                                                         *)
(* apply XORs the first mask byte, under the first-byte mask (4 low bits   *)
(* of a long header, 5 of a short one), into the first byte and the other  *)
(* mask bytes into the packet-number bytes. protect refuses a field that   *)
(* is not 1 to 4 bytes. unprotect unmasks a copy of the first byte to read *)
(* the packet-number length (its low two bits plus one), refuses a field   *)
(* shorter than that, and unmasks the first byte and that many bytes.      *)
(*                                                                         *)
(* A byte is a number below 256 and the XOR and AND are written on bits.   *)
(* The mask is any 5 bytes (the AES or ChaCha block is only a source of    *)
(* bytes). Checked over the declared sets of first bytes, first mask       *)
(* bytes, field bytes and mask bytes (HeaderProt.cfg takes every first     *)
(* byte, HeaderProt_pn.cfg every byte pattern of the field):               *)
(*   Involution       applying the same mask twice is the identity;        *)
(*   OnlyLowBits      only the low 4 (long) or 5 (short) bits of the first *)
(*                    byte change;                                         *)
(*   LenRange         the length unprotect reveals is 1 to 4;              *)
(*   RoundTrip        unprotect (protect x) = x when the caller wrote the  *)
(*                    length minus one in the low two bits of the first    *)
(*                    byte, with whatever bytes follow the field;          *)
(*   ProtectRefuses   protect refuses lengths 0 and 5.                     *)
(* Lean counterpart: Vinc/Record.lean (apply_involutive, apply_first_low,  *)
(* unprotect_len_range, unprotect_protect).                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS FirstSet, M0Set, Smp     \* sets of first bytes, first mask bytes, field and mask bytes

RECURSIVE BitXor(_, _), BitAnd(_, _)
BitXor(a, b) == IF a = 0 /\ b = 0 THEN 0 ELSE 2 * BitXor(a \div 2, b \div 2) + (IF (a % 2) # (b % 2) THEN 1 ELSE 0)
BitAnd(a, b) == IF a = 0 \/ b = 0 THEN 0 ELSE 2 * BitAnd(a \div 2, b \div 2) + (IF a % 2 = 1 /\ b % 2 = 1 THEN 1 ELSE 0)

FbMask(long) == IF long THEN 15 ELSE 31

(* apply: mask is a sequence of bytes, the first one for the first byte *)
Apply(mask, first, pn, long) ==
    [first |-> BitXor(first, BitAnd(mask[1], FbMask(long))),
     pn |-> [i \in DOMAIN pn |-> BitXor(pn[i], mask[i + 1])]]

Protect(mask, first, pn, long) ==
    IF Len(pn) \in 1..4 THEN [err |-> "ok", r |-> Apply(mask, first, pn, long)] ELSE [err |-> "header_length"]

Unprotect(mask, first, pn, long) ==
    LET unmasked == Apply(mask, first, <<>>, long).first
        len == BitAnd(unmasked, 3) + 1
    IN IF len > Len(pn) THEN [err |-> "header_length"]
       ELSE LET r == Apply(mask, first, SubSeq(pn, 1, len), long)
            IN [err |-> "ok", first |-> r.first, pn |-> r.pn \o SubSeq(pn, len + 1, Len(pn)), len |-> len]

VARIABLES long, first, m0, rest, pn, tail
vars == <<long, first, m0, rest, pn, tail>>

SeqsOf(S, n) == [1..n -> S]

Init == /\ long \in BOOLEAN
        /\ first \in FirstSet
        /\ m0 \in M0Set
        /\ rest \in SeqsOf(Smp, 4)
        /\ pn \in UNION {SeqsOf(Smp, n) : n \in 1..4}
        /\ tail \in {<<>>, <<77, 78>>}

Spec == Init /\ [][UNCHANGED vars]_vars

Mask == <<m0>> \o rest

Involution ==
    LET a == Apply(Mask, first, pn, long)
        b == Apply(Mask, a.first, a.pn, long)
    IN b.first = first /\ b.pn = pn

OnlyLowBits ==
    LET a == Apply(Mask, first, pn, long)
        bits == IF long THEN 4 ELSE 5          \* the specification: 4 bits of a long header, 5 of a short one
    IN BitXor(a.first, first) < 2 ^ bits /\ BitAnd(BitXor(a.first, first), 255 - (2 ^ bits - 1)) = 0

LenRange ==
    LET u == Unprotect(Mask, first, pn, long) IN u.err = "ok" => u.len \in 1..4

ProtectRefuses ==
    Protect(Mask, first, <<>>, long).err = "header_length" /\ Protect(Mask, first, <<0, 0, 0, 0, 0>>, long).err = "header_length"

RoundTrip ==
    (BitAnd(first, 3) = Len(pn) - 1) =>
        LET p == Protect(Mask, first, pn, long)
            u == Unprotect(Mask, p.r.first, p.r.pn \o tail, long)
        IN /\ p.err = "ok"
           /\ u.err = "ok"
           /\ u.first = first
           /\ u.pn = pn \o tail
           /\ u.len = Len(pn)
=============================================================================
