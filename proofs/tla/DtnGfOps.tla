----------------------------- MODULE DtnGfOps -----------------------------
(***************************************************************************)
(* The arithmetic of GF(2^8) with the polynomial 0x11d, as vinc-dtn's      *)
(* gf256.rs builds and uses it, and the slice kernels of the same file.    *)
(*                                                                         *)
(* The tables are built the way build_tables builds them: x starts at 1    *)
(* and is multiplied by 2 (XTime: shift left, then xor the polynomial when *)
(* bit 8 is set) 255 times; exp[i] and exp[i + 255] are x, log[x] is i.    *)
(* Mul is the entry of the MUL table (exp[log a + log b], 0 when an        *)
(* operand is 0) and Inv is exp[255 - log a] (0 for 0). PMul is the        *)
(* definition by the polynomial: shift-and-add with reduction. Bytes are   *)
(* the integers 0..255 and addition is the xor of the bits (X).            *)
(*                                                                         *)
(* A symbol is a sequence of bytes. XorInto, MulAddS and ScaleS are the    *)
(* three slice kernels: on the common length of the slices, byte by byte   *)
(* (the eight-byte word path of the code computes the same bytes; that is  *)
(* proved in Lean, DtnGfSlice.wordXor_eq, and checked in the trace).       *)
(*                                                                         *)
(* Lean counterparts: proofs/lean/Vinc/DtnGf.lean (tables, mulT_eq_pmul),  *)
(* DtnGfField.lean (the field), DtnGfSlice.lean (the kernels).             *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

Poly == 285

RECURSIVE XorBits(_, _)
XorBits(a, b) == IF a = 0 /\ b = 0 THEN 0 ELSE (((a % 2) + (b % 2)) % 2) + (2 * XorBits(a \div 2, b \div 2))

\* x <<= 1; if x & 0x100 != 0 { x ^= POLY }
XTime(x) == LET s == 2 * x IN IF s >= 256 THEN XorBits(s, Poly) ELSE s

\* The tables are built once, in the initial state, as sequences held in variables (a definition would be evaluated
\* again at every use). tPw[i + 1] is x at iteration i of the loop of build_tables.
VARIABLES tPw, tExp, tLog, tNib
tabs == <<tPw, tExp, tLog, tNib>>

RECURSIVE Gen(_, _)
Gen(n, acc) == IF n = 0 THEN acc ELSE Gen(n - 1, Append(acc, XTime(acc[Len(acc)])))

\* log[x] = i is written in increasing i; with the powers distinct the last write is the only one
LogOf(a) == CHOOSE i \in 0..254 : tPw[i + 1] = a
RECURSIVE GenLog(_, _)
GenLog(a, acc) == IF a = 256 THEN acc ELSE GenLog(a + 1, Append(acc, IF a = 0 THEN 0 ELSE LogOf(a)))

\* the xor of two nibbles, as a 16 x 16 table
RECURSIVE GenRow(_, _, _)
GenRow(a, b, acc) == IF b = 16 THEN acc ELSE GenRow(a, b + 1, Append(acc, XorBits(a, b)))
RECURSIVE GenN(_, _)
GenN(a, acc) == IF a = 16 THEN acc ELSE GenN(a + 1, Append(acc, GenRow(a, 0, <<>>)))

\* exp[i] = exp[i + 255] = x for i < 255; the last two entries stay 0
TabInit ==
    /\ tPw = Gen(254, <<1>>)
    /\ tExp = tPw \o tPw \o <<0, 0>>
    /\ tLog = GenLog(0, <<>>)
    /\ tNib = GenN(0, <<>>)

\* the xor of two bytes, nibble by nibble
X(a, b) == 16 * tNib[(a \div 16) + 1][(b \div 16) + 1] + tNib[(a % 16) + 1][(b % 16) + 1]
PwF(i) == tPw[i + 1]
ExpT(i) == tExp[i + 1]
LogT(a) == tLog[a + 1]

Mul(a, b) == IF a = 0 \/ b = 0 THEN 0 ELSE ExpT(LogT(a) + LogT(b))
Inv(a) == IF a = 0 THEN 0 ELSE ExpT(255 - LogT(a))

RECURSIVE PMulN(_, _, _)
PMulN(n, a, b) == IF n = 0 THEN 0 ELSE X(IF b % 2 = 1 THEN a ELSE 0, PMulN(n - 1, XTime(a), b \div 2))
PMul(a, b) == PMulN(8, a, b)

\* ---- the slice kernels, byte by byte on the common length ----
Zero(len) == [p \in 1..len |-> 0]
XorInto(d, s) == [p \in 1..Len(d) |-> IF p <= Len(s) THEN X(d[p], s[p]) ELSE d[p]]
MulAddS(d, s, c) ==
    IF c = 0 THEN d
    ELSE IF c = 1 THEN XorInto(d, s)
    ELSE [p \in 1..Len(d) |-> IF p <= Len(s) THEN X(d[p], Mul(c, s[p])) ELSE d[p]]
ScaleS(b, c) ==
    IF c = 1 THEN b
    ELSE IF c = 0 THEN [p \in 1..Len(b) |-> 0]
    ELSE [p \in 1..Len(b) |-> Mul(c, b[p])]
=============================================================================
