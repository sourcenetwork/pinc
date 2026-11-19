---------------------------- MODULE ValuesPlanSource ----------------------------
(***************************************************************************)
(* ValueSource::read_at of pinc-values (source.rs) against the bytes of    *)
(* the response. The source keeps a window of Batch frame descriptors      *)
(* (SERVE_BATCH = 16 in the code), refilled from the located frame, and   *)
(* fills a read from the part of the frame the offset is in (the header    *)
(* from the plan, a pair from the store's outboard at the offset           *)
(* proof_pair gives, group bytes from the store's value), stopping when a  *)
(* part comes back short. The model is the code step for step              *)
(* (FrameAt, Refill, Fill, ReadGo), over the plan operators of             *)
(* ValuesPlanOps.tla.                                                      *)
(*                                                                         *)
(* A byte of the response is a symbol: a header byte is determined by the  *)
(* four fields of the header and its index, an outboard byte by its store  *)
(* offset, a value byte by its store offset. The specification is the      *)
(* reference stream (the concatenated encodings of pinc-dag, framed), cut *)
(* at the end of the response and at the first byte the store lacks (the  *)
(* store returns the bytes it has, as ValueRead promises).                 *)
(*                                                                         *)
(* The machine takes a read of any offset and any length, over and over,   *)
(* on one source: the window evolves, and every answer must equal the      *)
(* specification whatever the window holds (so a retransmission, from a    *)
(* different window, is the same bytes; a partial read is a prefix; a     *)
(* short return is only at the end or at a byte the store lacks).          *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/ValuesPlanSourceRead.lean            *)
(* (readAt_spec, readAt_retx, readAt_prefix, readAt_short, fill_spec) and  *)
(* ValuesPlanFlat.lean (byteAt_flat, readAt_closed).                       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS G, HDR, PAR, MaxU, MaxS, MaxR, Batch, MaxN

Ops == INSTANCE ValuesPlanOps

VARIABLES c, win, ok

(* ---- the store: the longest prefix of the bytes it holds ---- *)
Present(c0, sym) ==
    IF sym[1] = "h" THEN TRUE
    ELSE IF sym[1] = "o" THEN sym[2] < c0.obSize /\ ~(sym[2] \in c0.holeO)
    ELSE sym[2] < c0.len /\ ~(sym[2] \in c0.holeV)

RECURSIVE StoreGo(_, _, _, _, _)
StoreGo(c0, kind, off, n, acc) ==
    IF n = 0 THEN acc
    ELSE IF Present(c0, <<kind, off>>) THEN StoreGo(c0, kind, off + 1, n - 1, Append(acc, <<kind, off>>))
    ELSE acc
StoreRead(c0, kind, off, n) == StoreGo(c0, kind, off, n, <<>>)

HdrBytes(f) == [j \in 1 .. HDR |-> <<"h", f.off, f.dlen, Ops!Min(f.plen, 65535), f.follows, j - 1>>]

(* ---- the code ---- *)
RECURSIVE RefillGo(_, _, _, _, _)
RefillGo(len, rs, i, k, n) ==
    IF n = 0 THEN <<>>
    ELSE LET f == Ops!Frame(len, rs, i, k)
         IN IF "none" \in DOMAIN f THEN [j \in 1 .. n |-> [none |-> TRUE]]
            ELSE <<f>> \o RefillGo(len, rs, i, k + 1, n - 1)

RECURSIVE Cached(_, _, _)
Cached(w, at, i) ==
    IF i > Len(w) THEN [none |-> TRUE]
    ELSE IF ~("none" \in DOMAIN w[i]) /\ w[i].start <= at /\ at < Ops!FrameEnd(w[i]) THEN w[i]
    ELSE Cached(w, at, i + 1)

(* frame_at: the frame holding at, and the window after *)
FrameAt(c0, plan, w, at) ==
    LET cf == Cached(w, at, 1)
    IN IF ~("none" \in DOMAIN cf) THEN [f |-> cf, w |-> w]
       ELSE LET first == Ops!Locate(c0.len, plan.rs, plan.total, at)
            IN IF "none" \in DOMAIN first THEN [f |-> first, w |-> w]
               ELSE [f |-> first, w |-> RefillGo(c0.len, plan.rs, first.range, first.k, Batch)]

Fill(c0, plan, f, at, rem) ==
    IF at < f.start + HDR
    THEN LET rel == at - f.start
             n == Ops!Min(HDR - rel, rem)
         IN [bytes |-> SubSeq(HdrBytes(f), rel + 1, rel + n), wanted |-> n]
    ELSE IF at < f.start + HDR + f.plen
    THEN LET into == at - (f.start + HDR)
             room == Ops!Min(PAR - (into % PAR), rem)
             pp == Ops!ProofPair(c0.len, plan.rs, f, into \div PAR)
         IN IF "none" \in DOMAIN pp THEN [bytes |-> <<>>, wanted |-> room]
            ELSE [bytes |-> StoreRead(c0, "o", pp.off + (into % PAR), room), wanted |-> room]
    ELSE LET into == at - (f.start + HDR + f.plen)
             room == Ops!Min(f.dlen - into, rem)
         IN [bytes |-> StoreRead(c0, "v", f.off + into, room), wanted |-> room]

RECURSIVE ReadGo(_, _, _, _, _)
ReadGo(c0, plan, w, at, rem) ==
    IF rem = 0 THEN [bytes |-> <<>>, w |-> w]
    ELSE LET fa == FrameAt(c0, plan, w, at)
         IN IF "none" \in DOMAIN fa.f THEN [bytes |-> <<>>, w |-> fa.w]
            ELSE LET r == Fill(c0, plan, fa.f, at, rem)
                 IN IF Len(r.bytes) < r.wanted THEN [bytes |-> r.bytes, w |-> fa.w]
                    ELSE LET t == ReadGo(c0, plan, fa.w, at + Len(r.bytes), rem - Len(r.bytes))
                         IN [bytes |-> r.bytes \o t.bytes, w |-> t.w]

(* ---- the specification: the reference stream ---- *)
RECURSIVE RefPairs(_)
RefPairs(pend) == IF pend = <<>> THEN <<>> ELSE [w \in 1 .. PAR |-> <<"o", Head(pend) + w - 1>>] \o RefPairs(Tail(pend))

FrameSyms(rf, k) ==
    HdrBytes([off |-> rf.off, dlen |-> rf.len, plen |-> Len(rf.pend) * PAR, follows |-> k > 0])
    \o RefPairs(rf.pend) \o [w \in 1 .. rf.len |-> <<"v", rf.off + w - 1>>]

RECURSIVE RangeSyms(_, _)
RangeSyms(F, k) == IF k > Len(F) THEN <<>> ELSE FrameSyms(F[k], k - 1) \o RangeSyms(F, k + 1)

RECURSIVE StreamSyms(_, _, _)
StreamSyms(len, rs, i) ==
    IF i > Len(rs) THEN <<>>
    ELSE RangeSyms(Ops!RefFrames(len, rs[i].first, rs[i].last), 1) \o StreamSyms(len, rs, i + 1)

RECURSIVE SpecPrefix(_, _, _, _)
SpecPrefix(c0, stream, pos, n) ==
    IF n = 0 \/ pos >= Len(stream) \/ ~Present(c0, stream[pos + 1]) THEN <<>>
    ELSE <<stream[pos + 1]>> \o SpecPrefix(c0, stream, pos + 1, n - 1)

(* ---- the requests: values and spans, with a store that lacks nothing or one byte ---- *)
Reqs == {<<3 * G + 1, <<<<0, 3 * G + 1>>>>>>, <<2 * G, <<<<0, 2 * G>>, <<G, G>>>>>>, <<5 * G, <<<<G + 1, 3 * G>>>>>>,
         <<1, <<<<0, 1>>>>>>, <<4 * G - 1, <<<<G - 1, 2>>, <<0, 1>>, <<3 * G, G - 1>>>>>>, <<7 * G + 1, <<<<0, 7 * G + 1>>>>>>}
Holes(l) == {<<{}, {}>>, <<{0}, {}>>, <<{PAR}, {}>>, <<{}, {1}>>, <<{}, {l - 1}>>, <<{}, {G}>>}
CaseSet == UNION {{[len |-> r[1], spans |-> r[2], obSize |-> PAR * (Ops!Groups(r[1]) - 1), holeO |-> h[1], holeV |-> h[2]]
                   : h \in Holes(r[1])} : r \in Reqs}
\* the cases of the quick profile (proofs/tla/quick): a value of one span, two spans and three spans, with no hole, the
\* first header byte missing and the value byte at G missing
CaseSetQuick ==
    UNION {{[len |-> r[1], spans |-> r[2], obSize |-> PAR * (Ops!Groups(r[1]) - 1), holeO |-> h[1], holeV |-> h[2]]
            : h \in Holes(r[1]) \cap {<<{}, {}>>, <<{0}, {}>>, <<{}, {G}>>}}
           : r \in {rq \in Reqs : rq[2] \in {<<<<0, 3 * G + 1>>>>, <<<<0, 2 * G>>, <<G, G>>>>, <<<<G - 1, 2>>, <<0, 1>>, <<3 * G, G - 1>>>>}}}

(* ---- the machine ---- *)
Plan(c0) == Ops!PlanNew(c0.len, c0.spans)

Init == /\ c \in CaseSet
        /\ win = [j \in 1 .. Batch |-> [none |-> TRUE]]
        /\ ok = TRUE

Probes(c0) ==
    LET plan == Plan(c0)
        frs == UNION {UNION {{Ops!Frame(c0.len, plan.rs, i, k).start, Ops!Frame(c0.len, plan.rs, i, k).start + 1,
                              Ops!FrameEnd(Ops!Frame(c0.len, plan.rs, i, k)) - 1}
                             : k \in 0 .. (plan.rs[i].last - plan.rs[i].first - 1)} : i \in 1 .. Len(plan.rs)}
    IN (0 .. 3) \cup {plan.total - 1, plan.total, plan.total + 1} \cup {x \in frs : x >= 0}

Next ==
    \E off \in Probes(c), n \in 0 .. MaxN :
        LET plan == Plan(c)
            r == ReadGo(c, plan, win, off, n)
            want == SpecPrefix(c, StreamSyms(c.len, plan.rs, 1), off, n)
        IN /\ win' = r.w
           /\ ok' = (r.bytes = want)
           /\ c' = c

Spec == Init /\ [][Next]_<<c, win, ok>>

(* every answer is the specification, whatever the window held *)
Inv == ok

(* the flat byte of the response: the byte at stream offset p is found through Locate and the part of its frame,      *)
(* and equals the byte of the concatenation of every frame of every range (the reference stream); the response has *)
(* exactly `total` bytes                                                                                          *)
Lacks == <<"none", 0>>
ByteAtSym(c0, plan, p) ==
    LET f == Ops!Locate(c0.len, plan.rs, plan.total, p)
    IN IF "none" \in DOMAIN f THEN Lacks
       ELSE IF p < f.start + HDR THEN HdrBytes(f)[p - f.start + 1]
       ELSE IF p < f.start + HDR + f.plen
            THEN LET into == p - (f.start + HDR)
                     pp == Ops!ProofPair(c0.len, plan.rs, f, into \div PAR)
                 IN IF "none" \in DOMAIN pp THEN Lacks ELSE <<"o", pp.off + (into % PAR)>>
            ELSE <<"v", f.off + (p - (f.start + HDR + f.plen))>>

FlatOK ==
    LET plan == Plan(c)
        stream == StreamSyms(c.len, plan.rs, 1)
    IN /\ Len(stream) = plan.total
       /\ \A p \in 0 .. plan.total + 1 :
             ByteAtSym(c, plan, p) = IF p < Len(stream) THEN stream[p + 1] ELSE Lacks

(* the window holds only frames of the plan *)
WinOK == \A j \in 1 .. Len(win) :
            ~("none" \in DOMAIN win[j]) =>
              win[j] = Ops!Frame(c.len, Plan(c).rs, win[j].range, win[j].k)
=============================================================================
