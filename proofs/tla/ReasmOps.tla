------------------------------ MODULE ReasmOps ------------------------------
(***************************************************************************)
(* The operations of pinc-transport conn/reasm.rs (Reassembly), step for   *)
(* step: one handshake message put together from fragments that arrive in  *)
(* any order and any number of times, kept as at most nr disjoint sorted   *)
(* runs [start, end). Reasm.tla checks them over every interleaving at     *)
(* small sizes; TraceReasm.tla replays the recorded calls of the real      *)
(* code.                                                                   *)
(*                                                                         *)
(* The state r: runs (the runs, lowest first) and total (the length of the *)
(* message being assembled, 0 for none). mx is the largest message and nr  *)
(* the most runs; Add returns out, the length of the message when it is    *)
(* complete and -1 otherwise, and the new state. The bytes themselves are  *)
(* not in the model: the code copies a fragment into the buffer at its     *)
(* offset when it keeps it, and the Rust test checks the buffer against    *)
(* the fragments it sent.                                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences

Mn(a, b) == IF a < b THEN a ELSE b
Mx(a, b) == IF a > b THEN a ELSE b

Reasm0 == [runs |-> <<>>, total |-> 0]

\* the runs that do not touch the new one are kept; the ones that do are folded into it
RECURSIVE MergeRuns(_, _, _, _)
MergeRuns(rs, lo, hi, keep) ==
    IF rs = <<>> THEN [keep |-> keep, lo |-> lo, hi |-> hi]
    ELSE IF rs[1][2] < lo \/ rs[1][1] > hi THEN MergeRuns(Tail(rs), lo, hi, Append(keep, rs[1]))
    ELSE MergeRuns(Tail(rs), Mn(lo, rs[1][1]), Mx(hi, rs[1][2]), keep)

RECURSIVE Below(_, _)
Below(keep, s) == IF keep = <<>> \/ keep[1][1] >= s THEN 0 ELSE 1 + Below(Tail(keep), s)
InsertRun(keep, iv) == LET p == Below(keep, iv[1]) IN SubSeq(keep, 1, p) \o <<iv>> \o SubSeq(keep, p + 1, Len(keep))

Add(r, mx, nr, total, off, dlen) ==
    IF total = 0 \/ total > mx THEN [out |-> -1, r |-> r]
    ELSE LET r1 == IF total # r.total THEN [runs |-> <<>>, total |-> total] ELSE r
             stop == Mn(off + dlen, total)
         IN IF stop <= off THEN [out |-> -1, r |-> r1]
            ELSE LET m == MergeRuns(r1.runs, off, stop, <<>>)
                 IN IF Len(m.keep) = nr THEN [out |-> -1, r |-> r1]
                    ELSE LET runs2 == InsertRun(m.keep, <<m.lo, m.hi>>)
                         IN IF Len(runs2) = 1 /\ m.lo = 0 /\ m.hi = total
                            THEN [out |-> total, r |-> Reasm0]
                            ELSE [out |-> -1, r |-> [runs |-> runs2, total |-> r1.total]]

\* The agreement rule of the handshake fix, with the bytes in the model as versions: a fragment's bytes are all of one
\* version v (the message of one sender), and two fragments agree on an offset exactly when their versions are equal.
\* rv is a reassembly r with vs, the version of every offset 0 .. mx - 1 (0 where the runs cover nothing).
V0(mx) == [p \in 0..(mx - 1) |-> 0]
RV0(mx) == [r |-> Reasm0, vs |-> V0(mx)]

\* the offsets the runs cover
Covered(rs) == UNION {{p \in rs[i][1]..(rs[i][2] - 1) : TRUE} : i \in DOMAIN rs}

\* Add copies the fragment's bytes into the buffer
Writes(r, mx, nr, total, off, dlen) ==
    /\ total > 0 /\ total <= mx
    /\ LET r1 == IF total # r.total THEN [runs |-> <<>>, total |-> total] ELSE r
           stop == Mn(off + dlen, total)
       IN stop > off /\ Len(MergeRuns(r1.runs, off, stop, <<>>).keep) < nr

\* the fragment disagrees with what is held: a message of another length while one is under way, or another version at
\* an offset the runs cover (Reassembly::add compares the bytes it overlaps, O(fragment)). w gives the version of every
\* offset of the fragment (a fragment may mix the bytes of two senders: a copy of a genuine datagram damaged in places).
\* The code's rule without the bytes: a fragment of another length while runs are held is refused and changes nothing
\* (the first case of ConflictW); a fragment of one message's bytes is never refused for them.
AddT(r, mx, nr, total, off, dlen) ==
    IF total > 0 /\ total <= mx /\ r.runs # <<>> /\ total # r.total THEN [out |-> -1, r |-> r]
    ELSE Add(r, mx, nr, total, off, dlen)

ConflictW(rv, mx, total, off, dlen, w) ==
    /\ total > 0 /\ total <= mx
    /\ \/ rv.r.runs # <<>> /\ total # rv.r.total
       \/ total = rv.r.total /\ \E p \in off..(Mn(off + dlen, total) - 1) : p \in Covered(rv.r.runs) /\ rv.vs[p] # w[p]
Conflict(rv, mx, total, off, dlen, v) == ConflictW(rv, mx, total, off, dlen, [p \in 0..(mx - 1) |-> v])

\* Add with the bytes. agree = TRUE is the code's rule: a fragment that disagrees changes nothing and is refused
\* (out = -2). agree = FALSE is the rule before: the last bytes written to an offset win, and a fragment of another
\* length starts over. msg is the versions of the message handed over (out >= 0). AddW takes the version of every
\* offset (w); AddV is a fragment of one version v.
AddW(rv, mx, nr, total, off, dlen, w, agree) ==
    IF agree /\ ConflictW(rv, mx, total, off, dlen, w) THEN [out |-> -2, rv |-> rv, msg |-> V0(mx)]
    ELSE LET x == Add(rv.r, mx, nr, total, off, dlen)
             stop == Mn(off + dlen, total)
             valid == total > 0 /\ total <= mx
             base == IF valid /\ total # rv.r.total THEN V0(mx) ELSE rv.vs
             vs1 == IF Writes(rv.r, mx, nr, total, off, dlen)
                    THEN [p \in 0..(mx - 1) |-> IF p >= off /\ p < stop THEN w[p] ELSE base[p]]
                    ELSE base
         IN IF x.out >= 0 THEN [out |-> x.out, rv |-> RV0(mx), msg |-> vs1]
            ELSE [out |-> -1, rv |-> [r |-> x.r, vs |-> vs1], msg |-> V0(mx)]
AddV(rv, mx, nr, total, off, dlen, v, agree) == AddW(rv, mx, nr, total, off, dlen, [p \in 0..(mx - 1) |-> v], agree)
=============================================================================
