------------------------------- MODULE U64 -------------------------------
(***************************************************************************)
(* Machine integers for the specifications of pinc-wire and pinc-dag.      *)
(*                                                                         *)
(* TLC integers are 32 bits wide, so a u64 is a word of five 16-bit limbs  *)
(* (little endian, 80 bits): a value of the code is a word whose fifth     *)
(* limb is 0, and the fifth limb holds the carry that makes an overflow    *)
(* visible. Every operation of the Rust code has an operator here with the *)
(* semantics of the code:                                                  *)
(*  - a plain `+`, `-`, `*`, `<<`, `>>`, `/`, `%` that overflows,          *)
(*    underflows, shifts by 64 or more or divides by zero is a panic in a  *)
(*    debug build and a silent wrap in a release build: here it stops TLC  *)
(*    with an error (Panic), so a model check that finishes has shown that *)
(*    no such operation is reachable in the checked domain;                *)
(*  - `checked_*` and `try_from` return an option, [ok |-> b, v |-> w];    *)
(*  - `saturating_*` saturate.                                             *)
(* Every divisor and multiplier of the code is a power of two (a group     *)
(* size, 64, 2, 7 * i is a shift amount), so division and multiplication   *)
(* are by 2^k; the operators check that the operand is a power of two.     *)
(*                                                                         *)
(* The exact operators (Add, Sub, Shl, Shr, Lt) are on the 80-bit words    *)
(* without a check; the specifications state properties with them, as     *)
(* every quantity a property mentions is below 2^80.                       *)
(*                                                                         *)
(* Lean counterpart: the operations of proofs/lean/Pinc/Machine.lean       *)
(* (add, mul, sub, satMul, shl, div, tryFrom) on Nat with the same         *)
(* overflow rule.                                                          *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

B == 65536
Zero == <<0, 0, 0, 0, 0>>
One == <<1, 0, 0, 0, 0>>

(* the word 2^k, k < 80 *)
Pw(k) == <<IF k \div 16 = 0 THEN 2 ^ (k % 16) ELSE 0, IF k \div 16 = 1 THEN 2 ^ (k % 16) ELSE 0,
           IF k \div 16 = 2 THEN 2 ^ (k % 16) ELSE 0, IF k \div 16 = 3 THEN 2 ^ (k % 16) ELSE 0,
           IF k \div 16 = 4 THEN 2 ^ (k % 16) ELSE 0>>

(* a word from a native integer below 2^30 *)
W(k) == <<k % B, (k \div B) % B, 0, 0, 0>>

(* a word from the four limbs the Rust traces record for a u64 *)
FromLimbs(l) == <<l[1], l[2], l[3], l[4], 0>>

(* the native integer of a word below 2^30 *)
Val(a) == a[1] + B * a[2]

RECURSIVE AddAt(_, _, _, _)
AddAt(a, b, i, c) ==
    IF i > 5 THEN <<>>
    ELSE <<(a[i] + b[i] + c) % B>> \o AddAt(a, b, i + 1, (a[i] + b[i] + c) \div B)

RECURSIVE SubAt(_, _, _, _)
SubAt(a, b, i, bw) ==
    IF i > 5 THEN <<>>
    ELSE LET d == a[i] - b[i] - bw
         IN <<IF d < 0 THEN d + B ELSE d>> \o SubAt(a, b, i + 1, IF d < 0 THEN 1 ELSE 0)

(* exact sum and difference (the difference of a pair with b <= a) *)
Add(a, b) == AddAt(a, b, 1, 0)
Sub(a, b) == SubAt(a, b, 1, 0)

RECURSIVE LtAt(_, _, _)
LtAt(a, b, i) == IF i = 0 THEN FALSE ELSE IF a[i] # b[i] THEN a[i] < b[i] ELSE LtAt(a, b, i - 1)
Lt(a, b) == LtAt(a, b, 5)
Le(a, b) == ~Lt(b, a)
Min(a, b) == IF Lt(a, b) THEN a ELSE b
Max(a, b) == IF Lt(a, b) THEN b ELSE a

(* exact a * 2^k and floor(a / 2^k), k < 80; bits shifted past 80 are lost *)
Shl(a, k) ==
    LET q == k \div 16
        r == k % 16
        lo(i) == IF i - q < 1 THEN 0 ELSE (a[i - q] * 2 ^ r) % B
        carry(i) == IF i - q - 1 < 1 THEN 0 ELSE a[i - q - 1] \div 2 ^ (16 - r)
    IN <<lo(1) + carry(1), lo(2) + carry(2), lo(3) + carry(3), lo(4) + carry(4), lo(5) + carry(5)>>

Shr(a, k) ==
    LET q == k \div 16
        r == k % 16
        hi(i) == IF i + q > 5 THEN 0 ELSE a[i + q] \div 2 ^ r
        carry(i) == IF i + q + 1 > 5 THEN 0 ELSE (a[i + q + 1] % 2 ^ r) * 2 ^ (16 - r)
    IN <<hi(1) + carry(1), hi(2) + carry(2), hi(3) + carry(3), hi(4) + carry(4), hi(5) + carry(5)>>

(* a mod 2^k *)
Low(a, k) == Sub(a, Shl(Shr(a, k), k))

Max64 == Sub(Pw(64), One)
Fits(a) == a[5] = 0

(* the panic of a debug build: TLC stops with the message *)
Panic(msg) == IF Assert(FALSE, msg) THEN Zero ELSE Zero
PanicN(msg) == IF Assert(FALSE, msg) THEN 0 ELSE 0

Some(v) == [ok |-> TRUE, v |-> v]
None == [ok |-> FALSE, v |-> Zero]

(* index of the top non-zero limb, 0 for the zero word *)
Top(a) == IF a[5] # 0 THEN 5 ELSE IF a[4] # 0 THEN 4 ELSE IF a[3] # 0 THEN 3 ELSE IF a[2] # 0 THEN 2
          ELSE IF a[1] # 0 THEN 1 ELSE 0

(* the number of significant bits of a 16-bit limb *)
LB4(z) == IF z >= 8 THEN 4 ELSE IF z >= 4 THEN 3 ELSE IF z >= 2 THEN 2 ELSE IF z >= 1 THEN 1 ELSE 0
LB8(y) == IF y >= 16 THEN 4 + LB4(y \div 16) ELSE LB4(y)
LimbBits(x) == IF x >= 256 THEN 8 + LB8(x \div 256) ELSE LB8(x)

(* the number of significant bits (u64::bit_width) *)
BitLen(a) == IF a = Zero THEN 0 ELSE 16 * (Top(a) - 1) + LimbBits(a[Top(a)])

(* u64::leading_zeros and u64::ilog2 *)
LeadingZeros(a) == 64 - BitLen(a)
Ilog2(a) == IF a = Zero THEN PanicN("ilog2 of zero") ELSE BitLen(a) - 1

IsPow2(a) == a # Zero /\ a = Pw(BitLen(a) - 1)
Log2(g) == IF IsPow2(g) THEN BitLen(g) - 1 ELSE PanicN("a divisor or multiplier that is not a power of two")

(* plain a + b and a - b *)
Add64(a, b) == LET s == Add(a, b) IN IF Fits(s) THEN s ELSE Panic("u64 addition overflows")
Sub64(a, b) == IF Lt(a, b) THEN Panic("u64 subtraction underflows") ELSE Sub(a, b)

(* a.checked_add(b), a.checked_sub(b) *)
CAdd(a, b) == LET s == Add(a, b) IN IF Fits(s) THEN Some(s) ELSE None
CSub(a, b) == IF Lt(a, b) THEN None ELSE Some(Sub(a, b))

(* a + b and a - b on a usize of the given width *)
Add2(a, b, bits) == LET s == Add(a, b) IN IF Lt(s, Pw(bits)) THEN s ELSE Panic("usize addition overflows")
CAddU(a, b, bits) == LET s == Add(a, b) IN IF Lt(s, Pw(bits)) THEN Some(s) ELSE None

(* a * g and a.saturating_mul(g), g a power of two *)
Mul64(a, g) == LET k == Log2(g) IN IF Lt(a, Pw(64 - k)) THEN Shl(a, k) ELSE Panic("u64 multiplication overflows")
SatMul64(a, g) == LET k == Log2(g) IN IF Lt(a, Pw(64 - k)) THEN Shl(a, k) ELSE Max64

(* a / g and a % g, g a power of two; a zero divisor panics *)
Div64(a, g) == IF g = Zero THEN Panic("division by zero") ELSE Shr(a, Log2(g))
Rem64(a, g) == IF g = Zero THEN Panic("remainder by zero") ELSE Low(a, Log2(g))
IsMultipleOf(a, g) == IF g = Zero THEN a = Zero ELSE Rem64(a, g) = Zero

(* a.div_ceil(g) as the standard library writes it: d = a / g, r = a % g, d + 1 when r > 0 *)
DivCeil(a, g) == LET d == Div64(a, g) IN IF Rem64(a, g) # Zero THEN Add64(d, One) ELSE d

(* a << s and a >> s for a native shift amount s: a shift by 64 or more panics; a << s drops the bits past 64 *)
Shl64(a, s) == IF s >= 64 THEN Panic("shift left by 64 or more") ELSE [Shl(a, s) EXCEPT ![5] = 0]
Shr64(a, s) == IF s >= 64 THEN Panic("shift right by 64 or more") ELSE Shr(a, s)

(* T::try_from(x) into a w-bit unsigned integer *)
TryFrom(x, w) == IF Lt(x, Pw(w)) THEN Some(x) ELSE None

(* bitwise or of two words, limb by limb *)
RECURSIVE OrBits(_, _, _)
OrBits(x, y, k) ==
    IF k = 16 THEN 0
    ELSE (IF (x \div 2 ^ k) % 2 = 1 \/ (y \div 2 ^ k) % 2 = 1 THEN 2 ^ k ELSE 0) + OrBits(x, y, k + 1)
Or(a, b) == <<OrBits(a[1], b[1], 0), OrBits(a[2], b[2], 0), OrBits(a[3], b[3], 0), OrBits(a[4], b[4], 0),
              OrBits(a[5], b[5], 0)>>

=============================================================================
