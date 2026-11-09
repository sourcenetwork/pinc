------------------------------- MODULE Nanos --------------------------------
(***************************************************************************)
(* Exact time arithmetic for the membership specifications: the Nanos      *)
(* (u64) of vinc-membership session.rs on the 80-bit limb words of         *)
(* U64.tla (TLC integers are 32 bits wide, a time in nanoseconds is not).  *)
(*                                                                         *)
(* Every operation of the code has an operator here with the semantics of  *)
(* the code: `a + b`, `a * k` and `a - b` that overflow or underflow stop  *)
(* TLC with an error (a debug build panics; a model check that finishes    *)
(* has shown the checked domain never gets there); saturating_add and      *)
(* saturating_sub saturate; `a / k` is the floor division by a small       *)
(* constant k (a long division on the limbs); Ms is                         *)
(* `u32::try_from(d / 1_000_000).unwrap_or(u32::MAX)` and FromMs is        *)
(* `u64::from(ms) * 1_000_000`. A duration in milliseconds is a word too   *)
(* (a u32 does not fit a TLC integer).                                     *)
(*                                                                         *)
(* Checked in Nanos.cfg (ASSUME): the operators against hand-computed      *)
(* values at the edges (0, 1, 2^16, 2^32, 2^63, 2^64 - 1).                 *)
(* Lean counterpart: Nat arithmetic in Vinc/MembershipModelTypes.lean.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

U == INSTANCE U64

Zero == U!Zero
One == U!One
W(k) == U!W(k)

Lt(a, b) == U!Lt(a, b)
Le(a, b) == U!Le(a, b)
Min(a, b) == U!Min(a, b)
Max(a, b) == U!Max(a, b)

(* a + b, which panics on overflow *)
Add(a, b) == U!Add64(a, b)

(* a.saturating_add(b), a.saturating_sub(b) *)
SatAdd(a, b) == LET s == U!Add(a, b) IN IF U!Fits(s) THEN s ELSE U!Max64
SatSub(a, b) == IF U!Lt(a, b) THEN Zero ELSE U!Sub(a, b)

(* a - b, which panics on underflow *)
Sub(a, b) == U!Sub64(a, b)

(* a * k for a small constant k (below 2^15): limb by limb with a carry; the fifth limb holds an overflow *)
RECURSIVE MulAt(_, _, _, _)
MulAt(a, k, i, c) ==
    IF i > 5 THEN <<>>
    ELSE <<(a[i] * k + c) % 65536>> \o MulAt(a, k, i + 1, (a[i] * k + c) \div 65536)
Mul(a, k) == LET p == MulAt(a, k, 1, 0) IN IF U!Fits(p) THEN p ELSE U!Panic("u64 multiplication overflows")

(* floor(a / k) for a small constant k (below 2^15): long division from the top limb *)
RECURSIVE DivAt(_, _, _, _)
DivAt(a, k, i, r) ==
    IF i < 1 THEN <<>>
    ELSE LET cur == r * 65536 + a[i]
         IN DivAt(a, k, i - 1, cur % k) \o <<cur \div k>>
Div(a, k) == IF k = 0 THEN U!Panic("division by zero") ELSE DivAt(a, k, 5, 0)

(* the Nanos of a native integer below 2^30 *)
Of(k) == U!W(k)

(* u64::from(ms) * 1_000_000 and u32::try_from(d / 1_000_000).unwrap_or(u32::MAX) *)
FromMs(ms) == Mul(Mul(ms, 1000), 1000)
Ms(d) == LET q == Div(Div(d, 1000), 1000)
         IN IF Lt(q, U!Pw(32)) THEN q ELSE U!Sub(U!Pw(32), One)

(* a plain `a * 3 / 4` on a Nanos *)
ThreeQuarters(a) == Div(Mul(a, 3), 4)
TwoThirds(a) == Div(Mul(a, 2), 3)

(* n seconds and n milliseconds, in nanoseconds *)
Sec(n) == Mul(Mul(Mul(W(n), 1000), 1000), 1000)
Millis(n) == Mul(Mul(W(n), 1000), 1000)

(***************************************************************************)
(* Checked once at start                                                    *)
(***************************************************************************)
ASSUME Sec(80) = <<8192, 41055, 18, 0, 0>> /\ Millis(250) = <<45696, 3814, 0, 0, 0>> /\ Sec(1) = <<51712, 15258, 0, 0, 0>>
ASSUME Mul(Of(3), 3) = Of(9) /\ Mul(U!Pw(40), 3) = <<0, 0, 768, 0, 0>>
ASSUME Div(Of(10), 4) = Of(2) /\ Div(U!Pw(40), 3) = <<21845, 21845, 85, 0, 0>> /\ Div(U!Max64, 4) = <<65535, 65535, 65535, 16383, 0>>
ASSUME Div(U!Max64, 1000) = <<42991, 19398, 35127, 65, 0>> /\ Div(<<8192, 41055, 18, 0, 0>>, 1000) = <<46080, 1220, 0, 0, 0>>
ASSUME Ms(Sec(80)) = Of(80000) /\ Ms(Of(999999)) = Zero /\ Ms(Of(1000000)) = Of(1) /\ Ms(U!Max64) = <<65535, 65535, 0, 0, 0>>
ASSUME FromMs(Of(5000)) = <<61952, 10757, 1, 0, 0>> /\ FromMs(<<65535, 65535, 0, 0, 0>>) = <<48576, 65520, 16959, 15, 0>>
ASSUME ThreeQuarters(<<53632, 2288, 0, 0, 0>>) = <<40224, 1716, 0, 0, 0>> /\ TwoThirds(<<53632, 2288, 0, 0, 0>>) = <<57600, 1525, 0, 0, 0>>
ASSUME SatAdd(U!Max64, One) = U!Max64 /\ SatAdd(One, One) = Of(2) /\ SatSub(One, Of(5)) = Zero /\ SatSub(Of(5), One) = Of(4)
=============================================================================
