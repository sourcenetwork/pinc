----------------------------- MODULE LimitsFitOps -----------------------------
(***************************************************************************)
(* The arithmetic of Limits::check and fits (crates/pinc/src/mem.rs on     *)
(* the branch work9/platform, worktree vinc-wt/t-99p: `check_for` 159-180, *)
(* `worst_case` 191-201, `fits` 206-210; `rung` node.rs 84-86 over the     *)
(* ladder 1, 2, 4 .. 65,536, node.rs 63-64), exact on numbers above TLC's *)
(* 32-bit integers: a number is a sequence of 15-bit limbs, lowest first   *)
(* (<<>> is 0), so a limb times a limb stays below 2^30.                   *)
(*                                                                         *)
(* A limit set is a record with the fields of Limits (conn, pool, sw, snd, *)
(* streams, ast, as, tmsg, tlog, topics); slot is SLOT_BYTES, chunk        *)
(* CHUNK_SIZE, pb the pointer width in bytes.                              *)
(***************************************************************************)
EXTENDS Integers, Sequences

B == 32768

RECURSIVE Norm(_)
\* the number without its zero high limbs
Norm(a) == IF a # <<>> /\ a[Len(a)] = 0 THEN Norm(SubSeq(a, 1, Len(a) - 1)) ELSE a
\* a number below 2^31
N(x) == Norm(<<x % B, (x \div B) % B, x \div (B * B)>>)

Lo(a) == IF a = <<>> THEN 0 ELSE Head(a)
Hi(a) == IF a = <<>> THEN <<>> ELSE Tail(a)
RECURSIVE AddC(_, _, _)
AddC(a, b, c) == IF a = <<>> /\ b = <<>> THEN N(c)
                 ELSE LET x == Lo(a) + Lo(b) + c IN <<x % B>> \o AddC(Hi(a), Hi(b), x \div B)
Add(a, b) == Norm(AddC(a, b, 0))
RECURSIVE MulSC(_, _, _)
\* times one limb k < B
MulSC(a, k, c) == IF a = <<>> THEN N(c) ELSE LET x == Head(a) * k + c IN <<x % B>> \o MulSC(Tail(a), k, x \div B)
RECURSIVE Mul(_, _)
Mul(a, b) == IF b = <<>> THEN <<>> ELSE Add(Norm(MulSC(a, Head(b), 0)), Norm(<<0>> \o Mul(a, Tail(b))))

RECURSIVE LeTop(_, _, _)
LeTop(x, y, k) == IF k = 0 THEN TRUE ELSE IF x[k] # y[k] THEN x[k] < y[k] ELSE LeTop(x, y, k - 1)
Le(a, b) == LET x == Norm(a) y == Norm(b) IN Len(x) < Len(y) \/ (Len(x) = Len(y) /\ LeTop(x, y, Len(x)))

\* 2^bits - 1
Ones(bits) == Norm([i \in 1..(bits \div 15) |-> B - 1] \o (IF bits % 15 = 0 THEN <<>> ELSE <<2^(bits % 15) - 1>>))
\* the bound of fits: 2^(8 pb - 1) - 1, saturating at 128 bits as the code's checked_shl
Bound(pb) == LET bits == IF 8 * pb = 0 THEN 0 ELSE 8 * pb - 1 IN Ones(IF bits >= 128 THEN 128 ELSE bits)

Range(f) == {f[k] : k \in DOMAIN f}
Ladder == [k \in 1..17 |-> 2^(k - 1)]
\* the smallest rung at or above c, 0 for none
Rung(c) == IF c > 65536 THEN 0 ELSE CHOOSE r \in Range(Ladder) : c <= r /\ \A s \in Range(Ladder) : c <= s => r <= s
\* worst_case: [ok, v]; not ok above the ladder (the code's checked u128 cannot overflow for inputs below 2^31)
Worst(l, slot, chunk) ==
    IF Rung(l.conn) = 0 THEN [ok |-> FALSE, v |-> <<>>]
    ELSE [ok |-> TRUE,
          v |-> Add(Mul(N(Rung(l.conn)), Add(Mul(N(l.pool), N(chunk)), N(slot))), Mul(N(l.topics), N(l.tlog)))]
Fits(l, pb, slot, chunk) == LET w == Worst(l, slot, chunk) IN w.ok /\ Le(w.v, Bound(pb))

InRange(l) == /\ 1 <= l.conn /\ l.conn <= 65536
              /\ 8 <= l.pool /\ l.pool <= 65535
              /\ 16384 <= l.sw /\ l.sw <= 16777216
              /\ 16384 <= l.snd /\ l.snd <= 1073741824
              /\ 1 <= l.streams /\ l.streams <= 100
              /\ l.ast >= 1 /\ l.as >= 1
              /\ 1 <= l.tmsg /\ l.tmsg <= 16777216
              /\ 1 <= l.tlog /\ l.tlog <= 1073741824
              /\ 1 <= l.topics /\ l.topics <= 4096
\* check_for: a limit out of range first, then what the target can address
Check(l, pb, slot, chunk) == IF ~InRange(l) THEN "range" ELSE IF ~Fits(l, pb, slot, chunk) THEN "address" ELSE "ok"
=============================================================================
