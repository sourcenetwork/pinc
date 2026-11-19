---------------------------- MODULE ReconcileCore ----------------------------
(***************************************************************************)
(* The part rules and the handlers of pinc-reconcile (core.rs, session.rs) *)
(* on the byte operators of ReconcileOps.tla; the TLA+ counterpart of      *)
(* Pinc/ReconcileParts.lean and Pinc/ReconcileSession.lean, written to be  *)
(* read against both and against the Rust code.                            *)
(*                                                                         *)
(* A core is a record with the fields of `Core`; a handler takes the bytes *)
(* the peer sent and returns Ok(<<step, bytes written, new state>>) or     *)
(* Er(reason). The order of every read, check and write is the code's.     *)
(* ALEAF / 8 (the size of the seen bitmap) is SeenBytes = ceil(ALEAF / 8), *)
(* the same 4 bytes at ALEAF = 32 and well defined at the scaled leaf      *)
(* sizes of the exhaustive configurations.                                 *)
(*                                                                         *)
(* A limits record is [maxItem, maxMessage, maxReport, maxRounds].         *)
(***************************************************************************)
EXTENDS ReconcileOps

Cap(lim) == Min(lim.maxMessage, FRAME_MAX)
MinMessage(lim) == LET bound == 1 + Len(Venc(lim.maxItem)) + lim.maxItem
                   IN 4 * bound + 2 * (1 + FPLEN) + 16

AnsEmpty == [cnt |-> 0, cold |-> FALSE, coldEnd |-> FALSE, miss |-> FALSE]

NewCore(lim, init) ==
    [lim |-> lim, n |-> 0, init |-> init, exact |-> FALSE, leafed |-> FALSE, rounds |-> 0, coldAt |-> 0,
     coldLo |-> <<>>, frames |-> <<>>, blast |-> <<>>, bsnap |-> <<>>, out |-> OutEmpty, ans |-> AnsEmpty,
     hdr |-> <<>>, here |-> <<>>, there |-> <<>>]

CoreClear(c) == [c EXCEPT !.exact = FALSE, !.leafed = FALSE, !.rounds = 0, !.coldAt = 0, !.frames = <<>>,
                          !.here = <<>>, !.there = <<>>]

Bump(c, n) == [c EXCEPT !.ans.cnt = c.ans.cnt + n]

PushItem(arena, other, max, item) ==
    IF DataLen(arena) + other + Len(item) + VARMAX > max THEN Er("reportTooLarge") ELSE Ok(Append(arena, item))

BoundLen(len) == 1 + Len(Venc(len)) + len

(* ---- ranges of items, ids and leaves ---- *)

RECURSIVE ReadRange(_, _, _, _)
ReadRange(lim, S, a, k) ==
    IF k = 0 THEN Ok(<<>>)
    ELSE Bind(ReadItem(lim, S, a), LAMBDA x :
         Bind(ReadRange(lim, S, a + 1, k - 1), LAMBDA xs : Ok(<<x>> \o xs)))

RECURSIVE LeafSum(_, _, _, _)
LeafSum(lim, S, j, k) ==
    IF k = 0 THEN Ok(0)
    ELSE Bind(ReadItem(lim, S, j), LAMBDA x :
         Bind(LeafSum(lim, S, j + 1, k - 1), LAMBDA s : Ok(VARMAX + Len(x) + s)))

LeafOk(lim, S, lo, hi, a, b, items) ==
    IF b - a <= 1 THEN Ok(TRUE)
    ELSE LET base == 1 + BoundLen(Len(lo)) + (IF hi = None THEN 0 ELSE BoundLen(Len(hi[1])))
                     + 2 * VARMAX + SeenBytes
         IN IF items
            THEN Bind(LeafSum(lim, S, a, b - a), LAMBDA s : Ok(base + s <= Cap(lim)))
            ELSE Ok(base + (b - a) * IDLEN <= Cap(lim))

IdBytes(o, x) == IdOf(o, x)

RECURSIVE IdsBytes(_, _)
IdsBytes(o, xs) == IF xs = <<>> THEN <<>> ELSE IdBytes(o, Head(xs)) \o IdsBytes(o, Tail(xs))

RECURSIVE ItemsBytes(_)
ItemsBytes(xs) == IF xs = <<>> THEN <<>> ELSE Venc(Len(Head(xs))) \o Head(xs) \o ItemsBytes(Tail(xs))

IdsPart(o, lim, S, out, lo, hi, a, b) ==
    Bind(ReadRange(lim, S, a, b - a), LAMBDA xs :
        LET o1 == OutHead(out, 2, lo, hi)
        IN Ok([o1 EXCEPT !.body = o1.body \o Venc(b - a) \o IdsBytes(o, xs)]))

ItemsPart(lim, S, out, kind, lo, hi, a, b) ==
    Bind(ReadRange(lim, S, a, b - a), LAMBDA xs :
        LET o1 == OutHead(out, kind, lo, hi)
        IN Ok([o1 EXCEPT !.body = o1.body \o Venc(b - a) \o ItemsBytes(xs)]))

(* ---- split ---- *)

RECURSIVE SplitGo(_, _, _, _, _, _, _, _, _, _, _, _)
SplitGo(o, lim, S, b, hi, step, x, l, out, cnt, fuel, dummy) ==
    IF fuel = 0 \/ x >= b THEN Ok(<<out, cnt>>)
    ELSE LET y == Min(b, x + step)
             fpb == FpRange(o, S, x, y)
         IN IF y < b
            THEN Bind(ReadItem(lim, S, y - 1), LAMBDA p :
                 Bind(ReadItem(lim, S, y), LAMBDA q :
                    LET k == Cpl(p, q) + 1 IN
                    IF k > Len(q) THEN Er("badIndex")
                    ELSE LET sep == Take(q, k)
                             o1 == OutHead(out, 1, l, Some(sep))
                         IN SplitGo(o, lim, S, b, hi, step, y, sep, [o1 EXCEPT !.body = o1.body \o fpb],
                                    cnt + 1, fuel - 1, 0)))
            ELSE LET o1 == OutHead(out, 1, l, hi)
                 IN SplitGo(o, lim, S, b, hi, step, y, l, [o1 EXCEPT !.body = o1.body \o fpb], cnt + 1, fuel - 1, 0)

SplitParts(o, lim, S, out, lo, hi, a, b, fan) ==
    SplitGo(o, lim, S, b, hi, Max(1, ((b - a) + fan - 1) \div fan), a, lo, out, 0, b - a + 1, 0)

RECURSIVE SplitFit(_, _, _, _, _, _, _, _, _, _, _)
SplitFit(o, lim, S, out, lo, hi, a, b, mark, fan, dummy) ==
    Bind(SplitParts(o, lim, S, out, lo, hi, a, b, fan), LAMBDA sp :
        IF Len(sp[1].body) <= Cap(lim) \/ mark > 0 \/ fan <= 2 THEN Ok(sp)
        ELSE SplitFit(o, lim, S, OutRollback(out, mark), lo, hi, a, b, mark, fan \div 2, 0))

(* ---- the items of a list, read one at a time, and the merge ---- *)

IsRead(r) == Count(r)

IsNext(mx, is) ==
    IF is[1] = 0 THEN Ok(None)
    ELSE Bind(Count(is[2]), LAMBDA c :
        IF c[1] > mx THEN Er("item")
        ELSE Bind(ReadBytes(c[1], c[2]), LAMBDA s : Ok(Some(<<s[1], <<is[1] - 1, s[2]>>>>))))

RECURSIVE Drain(_, _, _)
Drain(mx, fuel, is) ==
    IF fuel = 0 THEN Ok(is[2])
    ELSE Bind(IsNext(mx, is), LAMBDA nx : IF nx = None THEN Ok(is[2]) ELSE Drain(mx, fuel - 1, nx[1][2]))

SetBit(seen, k) == [i \in DOMAIN seen |-> IF i - 1 = k \div 8 THEN SetBitByte(seen[i], k % 8) ELSE seen[i]]

(* The merge callbacks. Mode "full": the accumulator is <<seen, out, extra>> of a responder leaf. Mode "init": it is
   <<here, there>>, pushed against the report limit. *)
MergeStep(mode, lim, m, acc) ==
    IF mode = "full"
    THEN IF m.t = "both" THEN Ok(<<SetBit(acc[1], m.k), acc[2], acc[3]>>)
         ELSE IF m.t = "theirs" THEN Ok(acc)
         ELSE Ok(<<acc[1], OutStageItem(acc[2], m.x), acc[3] + 1>>)
    ELSE IF m.t = "both" THEN Ok(acc)
         ELSE IF m.t = "theirs"
              THEN Bind(PushItem(acc[1], DataLen(acc[2]), lim.maxReport, m.x), LAMBDA h : Ok(<<h, acc[2]>>))
              ELSE Bind(PushItem(acc[2], DataLen(acc[1]), lim.maxReport, m.x), LAMBDA t : Ok(<<acc[1], t>>))

RECURSIVE MergeGo(_, _, _, _, _, _, _, _, _, _, _)
RECURSIVE MergeAdv(_, _, _, _, _, _, _, _, _, _, _)
MergeGo(mode, lim, S, b, fuel, j, k, prev, nxt, is, acc) ==
    IF fuel = 0 THEN Ok(<<acc, is[2]>>)
    ELSE Bind(IF j < b THEN Bind(ReadItem(lim, S, j), LAMBDA x : Ok(Some(x))) ELSE Ok(None), LAMBDA mo :
        IF mo = None /\ nxt = None THEN Ok(<<acc, is[2]>>)
        ELSE IF nxt = None
             THEN Bind(MergeStep(mode, lim, [t |-> "mine", x |-> mo[1]], acc), LAMBDA acc2 :
                    MergeGo(mode, lim, S, b, fuel - 1, j + 1, k, prev, None, is, acc2))
        ELSE IF mo # None /\ LexLt(mo[1], nxt[1])
             THEN Bind(MergeStep(mode, lim, [t |-> "mine", x |-> mo[1]], acc), LAMBDA acc2 :
                    MergeGo(mode, lim, S, b, fuel - 1, j + 1, k, prev, nxt, is, acc2))
        ELSE IF mo # None /\ mo[1] = nxt[1]
             THEN Bind(MergeStep(mode, lim, [t |-> "both", k |-> k], acc), LAMBDA acc2 :
                    MergeAdv(mode, lim, S, b, fuel - 1, j + 1, k, prev, nxt, is, acc2))
        ELSE Bind(MergeStep(mode, lim, [t |-> "theirs", x |-> nxt[1]], acc), LAMBDA acc2 :
                    MergeAdv(mode, lim, S, b, fuel - 1, j, k, prev, nxt, is, acc2)))

MergeAdv(mode, lim, S, b, fuel, j, k, prev, nxt, is, acc) ==
    IF prev # None /\ ~LexLt(prev[1], nxt[1]) THEN Er("item")
    ELSE Bind(IsNext(lim.maxItem, is), LAMBDA nx :
        IF nx = None
        THEN MergeGo(mode, lim, S, b, fuel, j, k + 1, Some(nxt[1]), None, is, acc)
        ELSE MergeGo(mode, lim, S, b, fuel, j, k + 1, Some(nxt[1]), Some(nx[1][1]), nx[1][2], acc))

Merge(mode, lim, S, a, b, is, acc) ==
    Bind(IsNext(lim.maxItem, is), LAMBDA first :
        IF first = None
        THEN MergeGo(mode, lim, S, b, (b - a) + is[1] + 2, a, 0, None, None, is, acc)
        ELSE MergeGo(mode, lim, S, b, (b - a) + is[1] + 2, a, 0, None, Some(first[1][1]), first[1][2], acc))

(* ---- replies ---- *)

ReplyPart(out, lo, hi, c, seen, extra) ==
    LET o1 == OutHead(out, 4, lo, hi)
    IN [o1 EXCEPT !.body = o1.body \o Venc(c) \o Take(seen, (c + 7) \div 8) \o Venc(extra) \o o1.stage,
                  !.stage = <<>>]

SeenInit == [i \in 1..SeenBytes |-> 0]

RECURSIVE IdsFold(_, _, _, _)
IdsFold(o, idl, xs, st) ==
    IF xs = <<>> THEN st
    ELSE LET id == IdBytes(o, Head(xs))
             ks == {k \in 0..(Len(idl) - 1) : idl[k + 1] = id}
         IN IF ks = {}
            THEN IdsFold(o, idl, Tail(xs), <<st[1], OutStageItem(st[2], Head(xs)), st[3] + 1>>)
            ELSE LET m == CHOOSE m \in ks : \A k \in ks : k <= m
                 IN IdsFold(o, idl, Tail(xs), <<SetBit(st[1], m), st[2], st[3]>>)

(* the unseen positions of a reply bitmap go to `there` *)
RECURSIVE Unseen(_, _, _, _, _, _, _, _)
Unseen(lim, S, a, seen, cc, here, rem, there) ==
    IF rem = 0 THEN Ok(there)
    ELSE LET j == cc - rem
             bit == j \div 8 < Len(seen) /\ BitOf(seen[j \div 8 + 1], j % 8) = 1
         IN IF bit THEN Unseen(lim, S, a, seen, cc, here, rem - 1, there)
            ELSE Bind(ReadItem(lim, S, a + j), LAMBDA x :
                 Bind(PushItem(there, DataLen(here), lim.maxReport, x), LAMBDA t :
                    Unseen(lim, S, a, seen, cc, here, rem - 1, t)))

RECURSIVE PushExtras(_, _, _, _, _)
PushExtras(lim, there, fuel, is, here) ==
    IF fuel = 0 THEN Ok(<<here, is[2]>>)
    ELSE Bind(IsNext(lim.maxItem, is), LAMBDA nx :
         IF nx = None THEN Ok(<<here, is[2]>>)
         ELSE Bind(PushItem(here, DataLen(there), lim.maxReport, nx[1][1]), LAMBDA h :
              PushExtras(lim, there, fuel - 1, nx[1][2], h)))

(* ---- the arms of answer ---- *)

ArmFP(o, S, c, r, mark, lo, hi, a, b) ==
    Bind(ReadBytes(FPLEN, r), LAMBDA f :
        IF f[1] = FpRange(o, S, a, b) THEN Ok(<<c, f[2]>>)
        ELSE LET items == ~c.init \/ c.exact
                 leaf == IF c.init THEN ALEAF ELSE BLEAF
             IN Bind(IF b - a <= leaf THEN LeafOk(c.lim, S, lo, hi, a, b, items) ELSE Ok(FALSE), LAMBDA ok :
                IF ok
                THEN LET c1 == IF c.init THEN [c EXCEPT !.leafed = TRUE] ELSE c
                     IN Bind(IF items THEN ItemsPart(c.lim, S, c1.out, 3, lo, hi, a, b)
                                      ELSE IdsPart(o, c.lim, S, c1.out, lo, hi, a, b), LAMBDA out :
                            Ok(<<Bump([c1 EXCEPT !.out = out], 1), f[2]>>))
                ELSE Bind(SplitFit(o, c.lim, S, c.out, lo, hi, a, b, mark, SPLIT, 0), LAMBDA sp :
                        Ok(<<Bump([c EXCEPT !.out = sp[1]], sp[2]), f[2]>>))))

ArmIds(o, S, c, r, mark, lo, hi, a, b) ==
    Bind(Count(r), LAMBDA cc :
        IF cc[1] > ALEAF THEN Er("count")
        ELSE Bind(ReadBytes(cc[1] * IDLEN, cc[2]), LAMBDA ids :
            Bind(IF b - a > ALEAF THEN Ok(TRUE)
                 ELSE Bind(LeafOk(c.lim, S, lo, hi, a, b, TRUE), LAMBDA ok : Ok(~ok)), LAMBDA narrow :
              IF narrow
              THEN Bind(SplitFit(o, c.lim, S, c.out, lo, hi, a, b, mark, SPLIT, 0), LAMBDA sp :
                    Ok(<<Bump([c EXCEPT !.out = sp[1]], sp[2]), ids[2]>>))
              ELSE Bind(ReadRange(c.lim, S, a, b - a), LAMBDA xs :
                    LET idl == [i \in 1..cc[1] |-> SubSeq(ids[1], (i - 1) * IDLEN + 1, i * IDLEN)]
                        st == IdsFold(o, idl, xs, <<SeenInit, c.out, 0>>)
                    IN Ok(<<Bump([c EXCEPT !.out = ReplyPart(st[2], lo, hi, cc[1], st[1], st[3])], 1), ids[2]>>)))))

ArmFull(o, S, c, r, mark, lo, hi, a, b) ==
    Bind(IsRead(r), LAMBDA is :
        IF is[1] > ALEAF THEN Er("count")
        ELSE Bind(IF b - a > ALEAF THEN Ok(TRUE)
                  ELSE Bind(LeafOk(c.lim, S, lo, hi, a, b, TRUE), LAMBDA ok : Ok(~ok)), LAMBDA narrow :
             IF narrow
             THEN Bind(Drain(c.lim.maxItem, is[1] + 1, is), LAMBDA r2 :
                  Bind(SplitFit(o, c.lim, S, c.out, lo, hi, a, b, mark, SPLIT, 0), LAMBDA sp :
                    Ok(<<Bump([c EXCEPT !.out = sp[1]], sp[2]), r2>>)))
             ELSE Bind(Merge("full", c.lim, S, a, b, is, <<SeenInit, c.out, 0>>), LAMBDA mr :
                  Ok(<<Bump([c EXCEPT !.out = ReplyPart(mr[1][2], lo, hi, is[1], mr[1][1], mr[1][3])], 1), mr[2]>>))))

ArmInitItems(S, c, r, a, b, kind, hi) ==
    Bind(IsRead(r), LAMBDA is :
    Bind(Merge("init", c.lim, S, a, b, is, <<c.here, c.there>>), LAMBDA mr :
        LET c1 == [c EXCEPT !.here = mr[1][1], !.there = mr[1][2]]
        IN Ok(<<IF kind = 5 THEN [c1 EXCEPT !.ans.cold = TRUE, !.ans.coldEnd = (hi = None)] ELSE c1, mr[2]>>)))

ArmReply(S, c, r, a, b) ==
    Bind(Count(r), LAMBDA cc :
        IF cc[1] # b - a \/ cc[1] > ALEAF THEN Er("count")
        ELSE Bind(ReadBytes((cc[1] + 7) \div 8, cc[2]), LAMBDA sn :
            IF cc[1] % 8 # 0 /\ sn[1] # <<>> /\ Last(sn[1]) \div Pow2(cc[1] % 8) # 0 THEN Er("count")
            ELSE Bind(Unseen(c.lim, S, a, sn[1], cc[1], c.here, cc[1], c.there), LAMBDA there :
                 Bind(IsRead(sn[2]), LAMBDA is :
                 Bind(PushExtras(c.lim, there, is[1] + 1, is, c.here), LAMBDA he :
                    Ok(<<[c EXCEPT !.here = he[1], !.there = there], he[2]>>))))))

ArmCheck(o, S, c, r, lo, hi) ==
    Bind(ReadBytes(FPLEN, r), LAMBDA f :
        IF lo # <<>> \/ hi # None THEN Er("bound")
        ELSE IF f[1] # FpRange(o, S, 0, c.n)
             THEN Ok(<<Bump([c EXCEPT !.out = OutHead(c.out, 7, <<>>, None)], 1), f[2]>>)
             ELSE Ok(<<c, f[2]>>))

(* ProcPart: one part of `answer`: read it, rank its bounds, run its arm. mark is the reply length before the part *)
ProcPart(o, S, c, r, mark) ==
    Bind(ReadU8(r), LAMBDA t :
    LET kind == t[1] % 128
        inf == t[1] >= 128
    IN Bind(ReadBound(c.blast, t[2], c.lim.maxItem), LAMBDA lo :
       LET c1 == [c EXCEPT !.blast = lo[1]] IN
       Bind(IF inf THEN Ok(<<None, lo[2], c1>>)
            ELSE Bind(ReadBound(c1.blast, lo[2], c.lim.maxItem), LAMBDA h :
                    Ok(<<Some(h[1]), h[2], [c1 EXCEPT !.blast = h[1]]>>)), LAMBDA hh :
       LET hi == hh[1]
           r2 == hh[2]
           c2 == hh[3]
           a == Rank(S, lo[1])
           b == IF hi = None THEN c2.n ELSE Rank(S, hi[1])
       IN IF b < a THEN Er("bound")
          ELSE IF kind = 1 THEN ArmFP(o, S, c2, r2, mark, lo[1], hi, a, b)
          ELSE IF kind = 2 /\ ~c2.init THEN ArmIds(o, S, c2, r2, mark, lo[1], hi, a, b)
          ELSE IF kind = 3 /\ ~c2.init THEN ArmFull(o, S, c2, r2, mark, lo[1], hi, a, b)
          ELSE IF (kind = 3 \/ kind = 5) /\ c2.init THEN ArmInitItems(S, c2, r2, a, b, kind, hi)
          ELSE IF kind = 4 /\ c2.init THEN ArmReply(S, c2, r2, a, b)
          ELSE IF kind = 6 /\ ~c2.init THEN ArmCheck(o, S, c2, r2, lo[1], hi)
          ELSE IF kind = 7 /\ c2.init
               THEN IF lo[1] # <<>> \/ hi # None THEN Er("bound")
                    ELSE Ok(<<[c2 EXCEPT !.ans.miss = TRUE], r2>>)
          ELSE Er("tag"))))

=============================================================================
