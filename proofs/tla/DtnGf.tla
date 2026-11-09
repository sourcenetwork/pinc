------------------------------- MODULE DtnGf -------------------------------
(***************************************************************************)
(* GF(2^8) with the polynomial 0x11d: the tables of gf256.rs against the  *)
(* polynomial definition, and the field laws, model checked on the exact   *)
(* arithmetic of DtnGfOps.                                                 *)
(*                                                                         *)
(* Checked by TLC (DtnGf.cfg), all of them over the full byte domain:      *)
(*  - ExpLog      exp is a bijection of 0..254 onto 1..255 (the 255        *)
(*                powers of 2 are distinct and nonzero), exp[i + 255] =    *)
(*                exp[i], log (exp i) = i and exp (log a) = a, and 2 has   *)
(*                order 255 (the 255th power is 1, no earlier one is);     *)
(*  - MulIsPoly   the table product equals the polynomial product for all  *)
(*                65536 pairs of bytes;                                    *)
(*  - Field       commutativity for all pairs, 1 is the identity, 0        *)
(*                absorbs, a * inv a = 1 for every nonzero a, inv 0 = 0,   *)
(*                no zero divisors, and associativity and distributivity   *)
(*                for every a, b against a spread of c (the unbounded      *)
(*                statements are DtnGfField.lean).                         *)
(*  - Kernels     the three slice kernels against the pointwise operation, *)
(*                on slices of every length up to 3 over a byte alphabet,  *)
(*                equal and unequal lengths, for a spread of constants.    *)
(*                                                                         *)
(* Lean counterparts: DtnGf.mulT_eq_pmul, DtnGf.eT_lT, DtnGf.lT_eT,        *)
(* DtnGf.mulT_assoc, DtnGf.mulT_xor, DtnGf.mulT_invT, DtnGfSlice.mulAdd_eq. *)
(***************************************************************************)
EXTENDS DtnGfOps, FiniteSets

\* One state per first operand a, so TLC spreads the 256 rows over its workers.
VARIABLE row
Init == TabInit /\ row \in 0..255
Next == UNCHANGED <<row, tabs>>

Bytes == 0..255
Spread == {0, 1, 2, 3, 29, 77, 128, 200, 254, 255}

ExpLog ==
    /\ \A i, j \in 0..254 : i # j => PwF(i) # PwF(j)
    /\ \A i \in 0..254 : PwF(i) \in 1..255
    /\ \A i \in 0..254 : ExpT(i + 255) = ExpT(i) /\ LogT(ExpT(i)) = i
    /\ \A a \in 1..255 : ExpT(LogT(a)) = a
    /\ XTime(PwF(254)) = 1
    /\ \A i \in 1..254 : PwF(i) # 1

MulIsPoly == \A b \in Bytes : Mul(row, b) = PMul(row, b)

Field ==
    /\ \A b \in Bytes : Mul(row, b) = Mul(b, row) /\ Mul(row, b) \in Bytes
    /\ Mul(row, 1) = row /\ Mul(row, 0) = 0
    /\ row # 0 => Mul(row, Inv(row)) = 1 /\ Inv(row) # 0 /\ \A b \in 1..255 : Mul(row, b) # 0
    /\ Inv(0) = 0
    /\ \A b \in Bytes, c \in Spread :
           Mul(Mul(row, b), c) = Mul(row, Mul(b, c)) /\ Mul(row, X(b, c)) = X(Mul(row, b), Mul(row, c))

\* all sequences of length 0..3 over a small alphabet
Alpha == {0, 1, 129, 255}
Seqs(n) == [1..n -> Alpha]
AllSeqs == UNION {Seqs(n) : n \in 0..3}

Kernels ==
    \A d, s \in AllSeqs, c \in Spread :
        /\ MulAddS(d, s, c) = [p \in 1..Len(d) |-> IF p <= Len(s) THEN X(d[p], Mul(c, s[p])) ELSE d[p]]
        /\ ScaleS(d, c) = [p \in 1..Len(d) |-> Mul(c, d[p])]
        /\ XorInto(d, s) = [p \in 1..Len(d) |-> IF p <= Len(s) THEN X(d[p], s[p]) ELSE d[p]]

Inv_ == (row = 0 => ExpLog) /\ MulIsPoly /\ Field /\ (row = 0 => Kernels)

Spec == Init /\ [][Next]_<<row, tabs>>
=============================================================================
