--------------------------- MODULE RecoveryMathOps ---------------------------
(***************************************************************************)
(* The integer helpers of pinc-transport recovery/math.rs, `sat` and       *)
(* `icbrt`, as operators over word widths given as parameters (TLC         *)
(* integers are 32 bits wide, so RecoveryMath.tla checks them scaled and   *)
(* TraceRecoveryMath.tla checks the real code's answers on the inputs TLC  *)
(* can hold). No constants, no variables.                                  *)
(***************************************************************************)
EXTENDS Integers

WordMax(w) == 2 ^ w - 1

\* `u64::try_from(v).unwrap_or(u64::MAX)`, into a target word of sw bits
Sat(v, sw) == IF v <= WordMax(sw) THEN v ELSE WordMax(sw)

\* `u128::from(cand).checked_pow(3)`: the cube, or -1 (None) when it does not fit the word of w bits
CCube(x, w) == IF x ^ 3 <= WordMax(w) THEN x ^ 3 ELSE -1

\* the loop of `icbrt`: `cand = root | (1 << bit)` (bit is above every bit root has, so `|` is `+`), kept when its
\* cube is some and at most n
RECURSIVE IcLoop(_, _, _, _)
IcLoop(n, root, bit, w) ==
    IF bit < 0 THEN root
    ELSE LET cand == root + 2 ^ bit
             cb == CCube(cand, w)
         IN IcLoop(n, IF cb >= 0 /\ cb <= n THEN cand ELSE root, bit - 1, w)
\* `icbrt(n)` with a root of rb bits (43 in the code) in a word of w bits (128 in the code)
Icbrt(n, rb, w) == IcLoop(n, 0, rb - 1, w)

\* whether some candidate the loop tries for n has a cube that overflows the word (`checked_pow` gives None)
RECURSIVE OvfLoop(_, _, _, _)
OvfLoop(n, root, bit, w) ==
    IF bit < 0 THEN FALSE
    ELSE LET cand == root + 2 ^ bit
             cb == CCube(cand, w)
         IN cb < 0 \/ OvfLoop(n, IF cb >= 0 /\ cb <= n THEN cand ELSE root, bit - 1, w)

\* the floor cube root, by its definition: the largest r with r^3 <= n
IsFloorCbrt(r, n) == r ^ 3 <= n /\ (r + 1) ^ 3 > n
=============================================================================
