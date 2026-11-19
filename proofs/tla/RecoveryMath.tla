---------------------------- MODULE RecoveryMath ----------------------------
(***************************************************************************)
(* The integer helpers of pinc-transport recovery/math.rs: `sat` (narrow   *)
(* u128 to u64, saturating) and `icbrt` (the integer cube root, bit by bit *)
(* from bit 42 down, each candidate's cube computed with `checked_pow`),   *)
(* as the operators of RecoveryMathOps.tla.                                *)
(*                                                                         *)
(* TLC integers are 32 bits wide, so the model checks them scaled: a word  *)
(* of W bits for the u128, a root of RB bits for the 43 of the code, and a *)
(* narrow word of SW bits for the u64. The scaled widths keep the code's   *)
(* relation: RB is the least number of bits with (2^RB)^3 above the       *)
(* largest word (3 * 43 = 129 > 128 and 3 * 42 = 126 < 128; 3 * 10 = 30 >  *)
(* 28 and 3 * 9 = 27 < 28), so some candidates' cubes overflow the word    *)
(* and `checked_pow` refuses them, as in the code.                         *)
(*                                                                         *)
(* The cases are the states of a machine whose root has one successor per  *)
(* input: every n below 2000, k^3 - 1, k^3 and k^3 + 1 for every k below   *)
(* 2^RB, 2^j - 1, 2^j and 2^j + 1 for every j below W, and the largest     *)
(* word, each kept when it is a word. Checked for every case:              *)
(*  - IcbrtOK: `icbrt(n)` is the largest r with r^3 <= n (the doc of       *)
(*    `icbrt`), and it never overflows (the cube of a candidate is never   *)
(*    used unchecked; r stays below 2^RB);                                 *)
(*  - SatOK: `sat(n)` is n when it fits SW bits and the largest narrow     *)
(*    word otherwise. On the scaled widths this restates the operator; the *)
(*    real `sat` is checked by the trace on u128 values written as limbs.  *)
(* RecoveryMath_ovf is a reachability witness: some input makes a          *)
(* candidate's cube overflow the word, so the refusal branch is taken.     *)
(* The code's own widths are run by the trace (TraceRecoveryMath.tla: the  *)
(* real `icbrt` on n below 2^30, the real `sat` on u128 values) and by     *)
(* tests/trace_recovery_math.rs, which checks r^3 <= n < (r + 1)^3 with    *)
(* u128 arithmetic on boundary values up to u128::MAX.                     *)
(***************************************************************************)
EXTENDS Integers
CONSTANTS W, RB, SW
ASSUME W <= 28 /\ RB <= 10 /\ 3 * RB > W /\ 3 * (RB - 1) < W /\ SW >= 1 /\ 2 * SW <= W
\* the code's widths keep the same relation
ASSUME 3 * 43 > 128 /\ 3 * 42 < 128
VARIABLE c

INSTANCE RecoveryMathOps

Inputs == {n \in (0..1999) \cup {k ^ 3 + d : k \in 0..(2 ^ RB - 1), d \in {-1, 0, 1}}
                           \cup {2 ^ j + d : j \in 0..(W - 1), d \in {-1, 0, 1}}
                           \cup {WordMax(W)} :
           0 <= n /\ n <= WordMax(W)}

Init == c = [t |-> "root"]
Next == c.t = "root" /\ \E n \in Inputs : c' = [t |-> "case", n |-> n]
Spec == Init /\ [][Next]_c

IcbrtOK == c.t = "case" => LET r == Icbrt(c.n, RB, W) IN IsFloorCbrt(r, c.n) /\ r < 2 ^ RB
SatOK == c.t = "case" => /\ Sat(c.n, SW) <= WordMax(SW)
                         /\ (c.n <= WordMax(SW) => Sat(c.n, SW) = c.n)
                         /\ (c.n > WordMax(SW) => Sat(c.n, SW) = WordMax(SW))

\* a reachability witness: the overflow refusal of `checked_pow` is taken for some input
NoOverflow == c.t = "case" => ~OvfLoop(c.n, 0, RB - 1, W)
=============================================================================
