------------------------------ MODULE DtnLayout ------------------------------
(***************************************************************************)
(* The geometry of a bundle, vinc-dtn/src/layout.rs, written step for step *)
(* on the machine integers of U64.tla: `SliceLayout::new`, `try_total_len`,*)
(* `data_symbols`, `padded_len`, `blocks`, `block_k`, `block_n`,           *)
(* `block_start`, `total_symbols`, `total_len`, `locate`, `data_symbol`    *)
(* and `byte_range`. Every `+`, `-`, `*` and `/` of the code that          *)
(* overflows or divides by zero stops TLC with an error (Panic), so a      *)
(* finished model check shows that none is reachable in the checked        *)
(* domain. The divisors of the code are the plain length (below 2^15), k,  *)
(* k + m and m, so the model has a multiply and a divide by a small        *)
(* number on the five 16-bit limbs of U64.tla (MulSmall, DivSmall), whose  *)
(* partial products stay below 2^31.                                       *)
(*                                                                         *)
(* The specification is stated apart from the code, with exact arithmetic: *)
(* a count n of items of size c for x is right when (n - 1) * c < x <=     *)
(* n * c; the symbol count is data + blocks * m; the sealed length is that *)
(* times the slice length; a symbol s is at block s div (k + m), index     *)
(* s mod (k + m), valid when the index is inside the block.                *)
(*                                                                         *)
(* Checked by TLC (DtnLayout.cfg) over: every pair (k, m) of a boundary    *)
(* set (k = 0, k + m = 255 and 256 included), every slice log 0..5, and    *)
(* the payload lengths 0, 1, around every data count D * plain for D in a  *)
(* small range, around 2^j for every j, around the largest count that      *)
(* fits the sealed length in a u64 (found from the model, then +-3), and   *)
(* u64::MAX; for each valid layout the counts, the padding, block_k,       *)
(* block_n, block_start at the boundary blocks, locate, data_symbol and    *)
(* byte_range at the boundary symbols and every pair of boundary symbols.  *)
(*                                                                         *)
(* Lean counterpart (proofs/lean/Vinc/DtnLayout.lean, on unbounded         *)
(* naturals): NewOK new_iff / valid_iff, CountsOK data_spec blocks_spec    *)
(* padding_lt, FitOK all_fit, BlockOK blockK_spec blockN_spec              *)
(* blockStart_spec blocks_cover last_block_end, LocateOK locate_iff        *)
(* locate_spec locate_inj locate_block_start, DataSymbolOK                 *)
(* dataSymbol_locate, ByteRangeOK byteRange_spec byteRange_fits.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64

B16 == 65536

(* ---- small multiply and divide on five limbs ---- *)
RECURSIVE MulAt(_, _, _, _)
MulAt(a, c, i, carry) ==
    IF i > 5 THEN <<>>
    ELSE <<(a[i] * c + carry) % B16>> \o MulAt(a, c, i + 1, (a[i] * c + carry) \div B16)
(* the exact product a * c of a word and a native number c < 2^15 (the limbs above the fifth are dropped) *)
MulX(a, c) == MulAt(a, c, 1, 0)
(* a * c as the code computes it: a debug build stops on overflow *)
Mul64S(a, c) == LET p == MulX(a, c) IN IF U!Fits(p) THEN p ELSE U!Panic("u64 multiplication overflows")
SatMulS(a, c) == LET p == MulX(a, c) IN IF U!Fits(p) THEN p ELSE U!Max64
CMulS(a, c) == LET p == MulX(a, c) IN IF U!Fits(p) THEN U!Some(p) ELSE U!None

RECURSIVE DivAt(_, _, _, _)
DivAt(a, d, i, r) ==
    IF i < 1 THEN <<>>
    ELSE LET cur == r * B16 + a[i] IN DivAt(a, d, i - 1, cur % d) \o <<cur \div d>>
(* floor(a / d) for a native 0 < d < 2^15, and the remainder as a native number *)
DivS(a, d) == IF d = 0 THEN U!Panic("division by zero") ELSE DivAt(a, d, 5, 0)
RemS(a, d) ==
    IF d = 0 THEN U!PanicN("remainder by zero")
    ELSE LET q == DivS(a, d) IN U!Val(U!Sub(a, MulX(q, d)))
DivCeilS(a, d) == LET q == DivS(a, d) IN IF RemS(a, d) # 0 THEN U!Add64(q, U!One) ELSE q

(* ---- the code ---- *)
SliceLen(log) == U!Shl64(U!W(1024), log)
PlainLen(log) == U!Sub64(SliceLen(log), U!W(16))
Plain(log) == U!Val(PlainLen(log))

DataSyms(log, p) == DivCeilS(p, Plain(log))
PaddedLen(log, p) == Mul64S(DataSyms(log, p), Plain(log))
Blocks(k, log, p) == DivCeilS(DataSyms(log, p), k)

(* try_total_len: parity = ceil(data / k).checked_mul(m); data.checked_add(parity); .checked_mul(slice_len) *)
TryTotal(k, m, log, p) ==
    LET data == DataSyms(log, p)
        par == CMulS(DivCeilS(data, k), m)
    IN IF ~par.ok THEN U!None
       ELSE LET s == U!CAdd(data, par.v)
            IN IF ~s.ok THEN U!None
               ELSE IF U!Lt(s.v, U!Pw(54 - log)) THEN U!Some(U!Shl(s.v, 10 + log)) ELSE U!None   \* checked_mul by 2^(10 + log)

(* SliceLayout::new: valid && p != 0 && try_total_len().is_some() ; the `||` short circuits *)
NewOK(k, m, log, p) ==
    IF ~(k >= 1 /\ k + m <= 255 /\ log <= 4) \/ p = U!Zero THEN FALSE ELSE TryTotal(k, m, log, p).ok

TotalSyms(k, m, log, p) == U!Add64(DataSyms(log, p), Mul64S(Blocks(k, log, p), m))
TotalLen(k, m, log, p) == U!Mul64(TotalSyms(k, m, log, p), SliceLen(log))

(* block_k: the first symbol of block b saturating, the data left, capped at k *)
BlockK(k, log, p, b) ==
    LET d == DataSyms(log, p)
        first == SatMulS(b, k)
    IN IF U!Le(d, first) THEN U!Zero
       ELSE IF U!Lt(U!Sub64(d, first), U!W(k)) THEN U!Sub64(d, first) ELSE U!W(k)
BlockN(k, m, log, p, b) ==
    IF BlockK(k, log, p, b) = U!Zero THEN U!Zero ELSE U!Add64(BlockK(k, log, p, b), U!W(m))
BlockStart(k, m, b) == SatMulS(b, k + m)

(* locate: none, or [block, index, bk] *)
Locate(k, m, log, p, s) ==
    LET pb == k + m
        block == DivS(s, pb)
        index == RemS(s, pb)
        bk == U!Val(BlockK(k, log, p, block))
    IN IF BlockK(k, log, p, block) # U!Zero /\ index < bk + m
       THEN [ok |-> TRUE, block |-> block, index |-> index, bk |-> bk]
       ELSE [ok |-> FALSE]
IsParity(pos) == pos.index >= pos.bk

(* data_symbol: block_start(d / k) + d % k *)
DataSymbol(k, m, log, p, d) ==
    IF U!Lt(d, DataSyms(log, p))
    THEN U!Some(U!Add64(BlockStart(k, m, DivS(d, k)), U!W(RemS(d, k))))
    ELSE U!None

(* byte_range: [start * slice_len, end * slice_len) or the Buffer error *)
ByteRange(k, m, log, p, a, b) ==
    IF U!Lt(b, a) \/ U!Lt(TotalSyms(k, m, log, p), b) THEN [err |-> "buffer"]
    ELSE [s |-> U!Mul64(a, SliceLen(log)), e |-> U!Mul64(b, SliceLen(log))]

(* ---- the specification, apart from the code ---- *)
\* exact sealed length of a valid parameter set, the number the code must agree with
ExactData(log, p) == IF p = U!Zero THEN U!Zero ELSE U!Add(U!Add(U!Zero, DivS(U!Sub(p, U!One), Plain(log))), U!One)
ExactBlocks(k, log, p) == IF p = U!Zero THEN U!Zero
                          ELSE U!Add(DivS(U!Sub(ExactData(log, p), U!One), k), U!One)
ExactSyms(k, m, log, p) == U!Add(ExactData(log, p), MulX(ExactBlocks(k, log, p), m))
ExactLen(k, m, log, p) == MulX(ExactSyms(k, m, log, p), U!Val(SliceLen(log)))
ParamsOK(k, m, log) == k >= 1 /\ k + m <= 255 /\ log <= 4

\* n items of size c cover x exactly: (n - 1) * c < x <= n * c
Covers(n, c, x) == U!Lt(MulX(U!Sub(n, U!One), c), x) /\ U!Le(x, MulX(n, c))

NewSpec(k, m, log, p) ==
    ParamsOK(k, m, log) /\ p # U!Zero /\ U!Lt(ExactLen(k, m, log, p), U!Pw(64))

NewIff(k, m, log, p) == NewOK(k, m, log, p) = NewSpec(k, m, log, p)

CountsOK(k, m, log, p) ==
    LET d == DataSyms(log, p)
        bl == Blocks(k, log, p)
    IN /\ Covers(d, Plain(log), p)
       /\ Covers(bl, k, d)
       /\ d = ExactData(log, p)
       /\ PaddedLen(log, p) = MulX(d, Plain(log))
       /\ U!Lt(U!Sub(PaddedLen(log, p), p), PlainLen(log))
       /\ TotalSyms(k, m, log, p) = ExactSyms(k, m, log, p)
       /\ TotalLen(k, m, log, p) = ExactLen(k, m, log, p)
       /\ U!Fits(ExactLen(k, m, log, p))

\* blocks: k data symbols except the last; start = b * (k + m); the blocks tile the symbol range exactly
BlockOKAt(k, m, log, p, b) ==
    LET bl == Blocks(k, log, p)
        d == DataSyms(log, p)
        bk == BlockK(k, log, p, b)
        bn == BlockN(k, m, log, p, b)
        st == BlockStart(k, m, b)
    IN /\ IF U!Lt(b, U!Sub(bl, U!One)) THEN bk = U!W(k)
          ELSE IF b = U!Sub(bl, U!One) THEN bk = U!Sub(d, MulX(U!Sub(bl, U!One), k))
          ELSE bk = U!Zero
       /\ IF U!Lt(b, bl) THEN bn = U!Add(bk, U!W(m)) /\ U!Lt(U!Zero, bk) /\ U!Le(bk, U!W(k)) ELSE bn = U!Zero
       /\ IF U!Le(b, bl) THEN st = MulX(b, k + m) ELSE TRUE
       /\ IF U!Lt(b, bl) /\ b = U!Sub(bl, U!One) THEN U!Add(st, bn) = TotalSyms(k, m, log, p) ELSE TRUE
       /\ IF U!Lt(U!Add(b, U!One), bl) THEN U!Add(st, bn) = BlockStart(k, m, U!Add(b, U!One)) ELSE TRUE

LocateOKAt(k, m, log, p, s) ==
    LET r == Locate(k, m, log, p, s)
        t == TotalSyms(k, m, log, p)
    IN /\ r.ok = U!Lt(s, t)
       /\ r.ok => /\ U!Add(MulX(r.block, k + m), U!W(r.index)) = s
                  /\ r.index < r.bk + m
                  /\ IsParity(r) = (r.index >= U!Val(BlockK(k, log, p, r.block)))

DataSymbolOKAt(k, m, log, p, d) ==
    LET r == DataSymbol(k, m, log, p, d)
        dd == DataSyms(log, p)
    IN /\ r.ok = U!Lt(d, dd)
       /\ r.ok => LET pos == Locate(k, m, log, p, r.v)
                  IN /\ pos.ok /\ ~IsParity(pos)
                     /\ pos.block = DivS(d, k) /\ pos.index = RemS(d, k)

ByteRangeOKAt(k, m, log, p, a, b) ==
    LET r == ByteRange(k, m, log, p, a, b)
        t == TotalSyms(k, m, log, p)
    IN IF U!Lt(b, a) \/ U!Lt(t, b) THEN r.err = "buffer"
       ELSE /\ r.s = MulX(a, U!Val(SliceLen(log))) /\ r.e = MulX(b, U!Val(SliceLen(log)))
            /\ U!Le(r.s, r.e) /\ U!Le(r.e, TotalLen(k, m, log, p))

(* ---- the checked domain ---- *)
KMs == {<<0, 5>>, <<1, 0>>, <<1, 254>>, <<1, 255>>, <<3, 252>>, <<128, 127>>, <<254, 1>>, <<255, 0>>, <<255, 1>>, <<7, 3>>}
Logs == {0, 3, 4, 5}

\* data counts of interest, as words: small ones, powers of two around, and the largest that fits a u64 sealed length
SmallD == {U!W(x) : x \in 0..3}
PowD == {x : x \in {U!Add(U!Pw(j), U!W(d)) : j \in {8, 32, 53}, d \in 0..1} \cup {U!Sub(U!Pw(j), U!One) : j \in {8, 32, 53}}}
\* the count D such that the sealed length of D data symbols is near 2^64: slice_len * (D + ceil(D/k) * m)
Fit(k, m, log) ==
    LET s == U!Val(SliceLen(log))
        \* D * (k + m) / k * s ~ 2^64: D ~ 2^64 * k / ((k + m) * s); computed as (2^64 / s) / (k + m) * k
        top == DivS(U!Max64, s)
    IN MulX(DivS(top, k + m), k)
FitD(k, m, log) == IF k = 0 THEN {} ELSE {U!Add(Fit(k, m, log), U!W(t)) : t \in 0..3} \cup
                   {U!Sub(Fit(k, m, log), U!W(t)) : t \in 1..3} \cup {DivS(U!Max64, U!Val(SliceLen(log)))}

\* payloads around D data slices: D * plain - plain + 1 (the smallest), D * plain, D * plain + 1, when below 2^64
Around(D, log) ==
    LET pl == Plain(log)
        top == MulX(D, pl)
    IN {x \in {top, U!Add(top, U!One), U!Sub(top, U!One), U!Sub(top, U!W(pl - 1))} :
          U!Fits(x) /\ U!Le(U!One, top) /\ U!Le(U!One, x)}

Payloads(k, m, log) ==
    {U!Zero, U!One, U!Max64, U!Sub(U!Max64, U!One)} \cup
    UNION {Around(D, log) : D \in SmallD \cup {U!W(k), U!W(k + 1)} \cup PowD \cup FitD(k, m, log)}

Seeds == {<<km, log>> : km \in KMs, log \in Logs}

VARIABLE c
Init == c = [t |-> "root"]
Next ==
    \/ c.t = "root" /\ \E sd \in Seeds : c' = [t |-> "seed", k |-> sd[1][1], m |-> sd[1][2], log |-> sd[2]]
    \/ c.t = "seed" /\ \E p \in Payloads(c.k, c.m, c.log) : c' = [t |-> "lay", k |-> c.k, m |-> c.m, log |-> c.log, p |-> p]
Spec == Init /\ [][Next]_c

\* indices of interest for a valid layout: around 0, k, the last block and the total, and u64::MAX
BlockIdx(k, m, log, p) ==
    LET bl == Blocks(k, log, p)
    IN {U!Zero, U!One, U!Max64, bl, U!Add(bl, U!One), U!Sub(bl, U!One)}
       \cup (IF U!Le(U!W(2), bl) THEN {U!Sub(bl, U!W(2))} ELSE {})
SymIdx(k, m, log, p) ==
    LET t == TotalSyms(k, m, log, p)
        bl == Blocks(k, log, p)
        ls == BlockStart(k, m, U!Sub(bl, U!One))
    IN {U!Zero, U!One, U!Max64, t, U!Add(t, U!One), U!Sub(t, U!One), ls, U!Add(ls, U!One), U!W(k + m - 1), U!W(k + m),
        U!W(k + m + 1)} \cup (IF U!Le(U!One, ls) THEN {U!Sub(ls, U!One)} ELSE {})
        \cup (IF U!Le(U!W(2), t) THEN {U!Sub(t, U!W(2))} ELSE {})
DataIdx(k, m, log, p) ==
    LET d == DataSyms(log, p)
    IN {U!Zero, U!One, U!Max64, d, U!Add(d, U!One), U!Sub(d, U!One), U!W(k - 1), U!W(k), U!W(k + 1)}
RangeIdx(k, m, log, p) ==
    LET t == TotalSyms(k, m, log, p)
    IN {U!Zero, U!One, t, U!Add(t, U!One), U!Sub(t, U!One), U!Max64}

Inv ==
    c.t \in {"root", "seed"} \/
    ( /\ NewIff(c.k, c.m, c.log, c.p)
      /\ NewOK(c.k, c.m, c.log, c.p) =>
           /\ CountsOK(c.k, c.m, c.log, c.p)
           /\ \A b \in BlockIdx(c.k, c.m, c.log, c.p) : BlockOKAt(c.k, c.m, c.log, c.p, b)
           /\ \A s \in SymIdx(c.k, c.m, c.log, c.p) : LocateOKAt(c.k, c.m, c.log, c.p, s)
           /\ \A d \in DataIdx(c.k, c.m, c.log, c.p) : DataSymbolOKAt(c.k, c.m, c.log, c.p, d)
           /\ \A a \in RangeIdx(c.k, c.m, c.log, c.p), b \in RangeIdx(c.k, c.m, c.log, c.p) :
                ByteRangeOKAt(c.k, c.m, c.log, c.p, a, b) )
=============================================================================
