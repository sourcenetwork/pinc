------------------------------- MODULE DtnRs -------------------------------
(***************************************************************************)
(* The systematic Reed-Solomon code of pinc-dtn's rs.rs, step for step on  *)
(* symbols (sequences of bytes), over the exact GF(2^8) of DtnGfOps.       *)
(*                                                                         *)
(* EncodeB is Rs::encode: parity symbol j is zero, then for each data      *)
(* symbol i in order mul_add with the Cauchy coefficient                   *)
(* coef(k, j, i) = inv((k + j) ^ i). Reconstruct is Rs::reconstruct: the   *)
(* count of present symbols (fewer than k is Incomplete and the block is   *)
(* left alone), the missing data indices ys, the first e present parity    *)
(* rows, then solve: each used parity symbol minus the known data,         *)
(* scaled by G, becomes a syndrome; each missing data symbol is the        *)
(* Cauchy combination of the syndromes scaled by F (the closed-form        *)
(* inverse, ProdSum and ProdSumSkip are prod_sum and prod_sum_skip);       *)
(* last, encode recomputes all parity from the repaired data.              *)
(*                                                                         *)
(* Checked by TLC, in the configurations DtnRs_*.cfg (Recover in a, b and c over different shapes):                      *)
(*  - Recover   for every data block over the byte alphabet Vals, every    *)
(*              set of present symbols (the absent ones scrambled): with   *)
(*              at least k present the result is the whole code word, with *)
(*              fewer it is Incomplete and the block is unchanged; the     *)
(*              encoding is systematic and linear;                         *)
(*  - Mds       every k x k submatrix of the systematic generator          *)
(*              [I; C] is invertible over GF(2^8) (determinant, Laplace    *)
(*              expansion) for small codes, and every square submatrix of  *)
(*              an 8 x 8 Cauchy matrix up to order 4;                      *)
(*  - Bounds    Rs::new accepts exactly 1 <= k and k + m <= 255 (checked   *)
(*              for every k, m <= 300); for those the x = k + j and y = i  *)
(*              of the Cauchy nodes are 255 distinct bytes at most, and    *)
(*              the number of erasures is at most min(k, m) <= 127, the    *)
(*              size of the ys buffer.                                     *)
(*                                                                         *)
(* Lean counterparts (proofs/lean/Pinc/DtnRs.lean, DtnCauchy.lean):        *)
(*   Recover  reconCol_ok     Mds  mds, cauchy_BA, cauchy_AB               *)
(*   Bounds   validParams_iff, erasures_le, nodes_of                       *)
(* The Lean model works on one byte column, which is sound because the     *)
(* kernels act on every byte alike (DtnGfSlice); this model keeps whole    *)
(* symbols, as the code does.                                              *)
(***************************************************************************)
EXTENDS DtnRsOps

CONSTANTS Vals, Cfgs

\* ---- the checked domain ----
Syms(len) == [1..len -> Vals]
Junk(len) == [p \in 1..len |-> 165]

Datas(k, len) == [0..k - 1 -> Syms(len)]
Presents(n) == [0..n - 1 -> BOOLEAN]

Scrambled(whole, present, len) == [s \in DOMAIN whole |-> IF present[s] THEN whole[s] ELSE Junk(len)]

\* One state per code shape and data block, so TLC spreads the data blocks over its workers; the checks that are not
\* per data block (Mds, Bounds) run in the single state of InitJobs.
VARIABLES cf, dd
vars == <<cf, dd, tabs>>
Init == TabInit /\ cf \in Cfgs /\ dd \in Datas(cf.k, cf.len)
InitJobs == TabInit /\ cf = "jobs" /\ dd = 0
Next == UNCHANGED vars

\* every set of present symbols for the data block d, the absent ones scrambled
RecoverOne(c, d) ==
    \A pr \in Presents(c.k + c.m) :
        LET whole == EncodeB(c.k, c.m, c.len, d)
            blk == Scrambled(whole, pr, c.len)
            r == Reconstruct(c.k, c.m, c.len, blk, pr)
        IN /\ \A i \in 0..c.k - 1 : whole[i] = d[i]
           /\ IF Held(c.k + c.m, pr) >= c.k THEN r.res = "ok" /\ r.blk = whole
              ELSE r.res = "incomplete" /\ r.blk = blk

\* linearity: the xor of two code words is the code word of the xor of the data (the second block runs over the
\* blocks that repeat one symbol)
LinearOne(c, d1) ==
    \A d2 \in {[i \in 0..c.k - 1 |-> sy] : sy \in Syms(c.len)} :
        LET w1 == EncodeB(c.k, c.m, c.len, d1)
            w2 == EncodeB(c.k, c.m, c.len, d2)
            d3 == [i \in 0..c.k - 1 |-> XorInto(d1[i], d2[i])]
        IN EncodeB(c.k, c.m, c.len, d3) = [s \in DOMAIN w1 |-> XorInto(w1[s], w2[s])]

Recover == RecoverOne(cf, dd) /\ LinearOne(cf, dd)

\* ---- MDS: determinants over GF(2^8) ----
RECURSIVE Det(_)
Det(M) ==
    IF Len(M) = 1 THEN M[1][1]
    ELSE LET RECURSIVE Sum(_, _)
             Sum(j, acc) == IF j > Len(M) THEN acc
                 ELSE Sum(j + 1, X(acc, Mul(M[1][j],
                          IF M[1][j] = 0 THEN 0
                          ELSE Det([r \in 1..Len(M) - 1 |-> [c \in 1..Len(M) - 1 |-> M[r + 1][IF c < j THEN c ELSE c + 1]]]))))
         IN Sum(1, 0)

\* row s of the systematic generator [I; C]
GeneratorRow(k, s) == [i \in 1..k |-> IF s < k THEN (IF s = i - 1 THEN 1 ELSE 0) ELSE Coef(k, s - k, i - 1)]

KSubsets(k, n) == {S \in SUBSET (0..n - 1) : Cardinality(S) = k}

RECURSIVE SortedSeq(_)
SortedSeq(S) == IF S = {} THEN <<>> ELSE LET m == CHOOSE x \in S : \A y \in S : x <= y IN <<m>> \o SortedSeq(S \ {m})

MdsGen(k, m) ==
    \A S \in KSubsets(k, k + m) :
        LET rs == SortedSeq(S) IN Det([r \in 1..k |-> GeneratorRow(k, rs[r])]) # 0

\* every square submatrix of the Cauchy block (k x m code) of order <= o is invertible
MdsCauchy(k, m, o) ==
    \A z \in 1..o : \A R \in KSubsets(z, m), Cc \in KSubsets(z, k) :
        LET rr == SortedSeq(R)
            cc == SortedSeq(Cc)
        IN Det([r \in 1..z |-> [c \in 1..z |-> Coef(k, rr[r], cc[c])]]) # 0

Mds == /\ MdsGen(2, 3) /\ MdsGen(3, 3) /\ MdsGen(4, 3) /\ MdsGen(3, 5) /\ MdsGen(5, 2)
       /\ MdsCauchy(8, 8, 4)

\* ---- the parameter bounds ----
Bounds ==
    /\ \A k, m \in 0..300 :
        /\ Valid(k, m) <=> (1 <= k /\ k + m <= 255)
        /\ Valid(k, m) => (k <= 255 /\ m <= 255)
    /\ \A k \in 1..255 : \A m \in 0..(255 - k) :
        LET xs == {k + j : j \in 0..m - 1}
            ys == {i : i \in 0..k - 1}
        IN /\ Cardinality(xs) = m /\ Cardinality(ys) = k
           /\ xs \cap ys = {}
           /\ \A v \in xs \cup ys : v < 255
           /\ \A e \in 0..(IF k < m THEN k ELSE m) : e <= 127

CfgsA == {[k |-> 1, m |-> 3, len |-> 2], [k |-> 2, m |-> 2, len |-> 2], [k |-> 3, m |-> 1, len |-> 2]}
CfgsB == {[k |-> 3, m |-> 3, len |-> 1], [k |-> 4, m |-> 2, len |-> 1]}
CfgsC == {[k |-> 2, m |-> 4, len |-> 1], [k |-> 5, m |-> 1, len |-> 1], [k |-> 1, m |-> 0, len |-> 1],
          [k |-> 4, m |-> 3, len |-> 1]}

InvRecover == Recover
InvMds == Mds
InvBounds == Bounds

Spec == Init /\ [][Next]_vars
SpecJobs == InitJobs /\ [][Next]_vars
=============================================================================
