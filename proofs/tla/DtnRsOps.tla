----------------------------- MODULE DtnRsOps -----------------------------
(***************************************************************************)
(* The operators of the systematic Reed-Solomon code of rs.rs, step for    *)
(* step on symbols over the exact GF(2^8) of DtnGfOps: Rs::encode          *)
(* (EncodeB) and Rs::reconstruct (Reconstruct). See DtnRs.tla for the      *)
(* description and what is checked; TraceDtnRs.tla replays the real code   *)
(* against these operators.                                                *)
(***************************************************************************)
EXTENDS DtnGfOps, FiniteSets

B8(n) == IF n < 256 THEN n ELSE 0
Coef(k, j, i) == Inv(X(B8(k + j), B8(i)))

RECURSIVE ParityAcc(_, _, _, _, _, _)
ParityAcc(k, j, len, blk, i, acc) ==
    IF i >= k THEN acc ELSE ParityAcc(k, j, len, blk, i + 1, MulAddS(acc, blk[i], Coef(k, j, i)))
ParitySym(k, len, blk, j) == ParityAcc(k, j, len, blk, 0, Zero(len))
EncodeB(k, m, len, blk) == [s \in 0..k + m - 1 |-> IF s < k THEN blk[s] ELSE ParitySym(k, len, blk, s - k)]

RECURSIVE Asc(_, _, _)
Asc(lo, hi, f) == IF lo > hi THEN <<>> ELSE IF f[lo] THEN <<lo>> \o Asc(lo + 1, hi, f) ELSE Asc(lo + 1, hi, f)

RECURSIVE PSA(_, _, _, _)
PSA(v, a, i, acc) == IF i > Len(a) THEN acc ELSE PSA(v, a, i + 1, Mul(acc, X(v, a[i])))
ProdSum(v, a) == PSA(v, a, 1, 1)
RECURSIVE PSS(_, _, _, _, _)
PSS(v, a, skip, i, acc) ==
    IF i > Len(a) THEN acc
    ELSE PSS(v, a, skip, i + 1, IF i - 1 = skip THEN acc ELSE Mul(acc, X(v, a[i])))
ProdSumSkip(v, a, skip) == PSS(v, a, skip, 1, 1)
GFac(x, idx, xs, ys) == Mul(ProdSum(x, ys), Inv(ProdSumSkip(x, xs, idx)))
FFac(y, idx, xs, ys) == Mul(ProdSum(y, xs), Inv(ProdSumSkip(y, ys, idx)))

Held(n, present) == Cardinality({s \in 0..n - 1 : present[s]})

\* the result of Rs::reconstruct on a block of the right size: the verdict and the block afterwards
Reconstruct(k, m, len, blk, present) ==
    LET n == k + m
        ys == Asc(0, k - 1, [i \in 0..k - 1 |-> ~present[i]])
        e == Len(ys)
        rowsAll == Asc(0, m - 1, [j \in 0..m - 1 |-> present[k + j]])
        rows == SubSeq(rowsAll, 1, e)
        xs == [t \in 1..e |-> B8(k + rows[t])]
        yv == [t \in 1..e |-> B8(ys[t])]
        known == Asc(0, k - 1, [i \in 0..k - 1 |-> present[i]])
        RECURSIVE Known(_, _, _, _)
        Known(row, idx, s, acc) == IF idx > Len(known) THEN acc
            ELSE Known(row, idx + 1, s, MulAddS(acc, blk[known[idx]], Coef(k, row, known[idx])))
        Syn(t) == ScaleS(Known(rows[t], 1, 0, blk[k + rows[t]]), GFac(xs[t], t - 1, xs, yv))
        RECURSIVE BuildS(_, _)
        BuildS(t, acc) == IF t > e THEN acc ELSE BuildS(t + 1, Append(acc, Syn(t)))
        syns == BuildS(1, <<>>)
        RECURSIVE Comb(_, _, _)
        Comb(s, t, acc) == IF t > e THEN acc ELSE Comb(s, t + 1, MulAddS(acc, syns[t], Inv(X(xs[t], yv[s]))))
        Out(s) == ScaleS(Comb(s, 1, Zero(len)), FFac(yv[s], s - 1, xs, yv))
        RECURSIVE BuildO(_, _)
        BuildO(s, acc) == IF s > e THEN acc ELSE BuildO(s + 1, Append(acc, Out(s)))
        outs == BuildO(1, <<>>)
        data == [i \in 0..k - 1 |->
                   IF \E s \in 1..e : ys[s] = i THEN outs[CHOOSE s \in 1..e : ys[s] = i] ELSE blk[i]]
    IN IF Held(n, present) < k THEN [res |-> "incomplete", blk |-> blk]
       ELSE [res |-> "ok", blk |-> EncodeB(k, m, len, data)]
\* Rs::new accepts k >= 1 and k + m <= 255
Valid(k, m) == ~(k = 0 \/ k + m > 255)
=============================================================================
