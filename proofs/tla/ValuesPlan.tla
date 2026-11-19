------------------------------ MODULE ValuesPlan ------------------------------
(***************************************************************************)
(* The closed-form response geometry of pinc-values (plan.rs) against the  *)
(* concatenated range encodings of pinc-dag. The operators are in          *)
(* ValuesPlanOps.tla; this module enumerates requests and checks, for each:*)
(*                                                                         *)
(*  - PlanNew (the checked u64 arithmetic of Plan::new) equals the         *)
(*    specification (exact sizes of the reference frames): the same refusal*)
(*    (too many ranges, past the value, over the response limit), the same*)
(*    ranges rounded out to whole groups, empty spans dropped, the same    *)
(*    total;                                                               *)
(*  - every frame of every range is the reference frame at the reference   *)
(*    stream offset (the range start plus the bytes of the frames before   *)
(*    it): offset, length, proof length, follows;                          *)
(*  - frames tile [0, total) exactly, starts strictly increase, no frame   *)
(*    passes the response limit;                                           *)
(*  - locate finds, for the first, last and (single-span cases) every      *)
(*    offset, the frame that holds it, and none at or past the end;        *)
(*  - frame_of_group, proof_pair (every pair of every frame, and none past *)
(*    them) and the 64-node path (never truncated).                        *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/ValuesPlanMain.lean (planNew_eq_spec,*)
(* frame_spec, range_ends, start_strict, locate_frame, locate_some,       *)
(* proofPair_spec, frameOfGroup_spec, pathGo_eq), unbounded.              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS G, HDR, PAR, MaxU, MaxS, MaxR, MaxLen

Ops == INSTANCE ValuesPlanOps

(* ---- the checks of one request ---- *)

RECURSIVE FrameStartRef(_, _, _)
FrameStartRef(F, k, acc) == IF k = 0 THEN acc ELSE FrameStartRef(F, k - 1, acc + Ops!FrameBytes(F[k]))

(* the frame (range i, group k) of the reference holding stream offset at, among all ranges *)
RefHolder(len, rs, at) ==
    LET cand == UNION {{<<i, k>> : k \in 0 .. (rs[i].last - rs[i].first - 1)} : i \in 1 .. Len(rs)}
        holds(c) == LET r == rs[c[1]]
                        F == Ops!RefFrames(len, r.first, r.last)
                        st == FrameStartRef(F, c[2], r.start)
                    IN st <= at /\ at < st + Ops!FrameBytes(F[c[2] + 1])
    IN {c \in cand : holds(c)}

FramesOK(len, pn, full) ==
    LET rs == pn.rs
        total == pn.total
        n == Ops!Groups(len)
    IN /\ \* ranges back to back from 0
          (rs = <<>> => total = 0)
       /\ \A i \in 1 .. Len(rs) :
            LET r == rs[i]
                F == Ops!RefFrames(len, r.first, r.last)
                size == Ops!RefSize(len, r.first, r.last)
            IN /\ r.first < r.last /\ r.last <= n
               /\ r.start = IF i = 1 THEN 0 ELSE rs[i - 1].start + Ops!RefSize(len, rs[i - 1].first, rs[i - 1].last)
               /\ (i = Len(rs) => total = r.start + size)
               /\ Len(F) = r.last - r.first
               /\ \A k \in 0 .. (Len(F) - 1) :
                    LET f == Ops!Frame(len, rs, i, k)
                        rf == F[k + 1]
                    IN /\ ~("none" \in DOMAIN f)
                       /\ f.start = FrameStartRef(F, k, r.start)
                       /\ f.off = rf.off /\ f.dlen = rf.len /\ f.plen = Len(rf.pend) * PAR /\ f.follows = (k > 0)
                       /\ Ops!FrameEnd(f) <= total /\ total <= MaxS
                       /\ (k + 1 < Len(F) => Ops!FrameEnd(f) = FrameStartRef(F, k + 1, r.start))
                       /\ (k = 0 => f.start = r.start)
                       /\ (k = Len(F) - 1 => Ops!FrameEnd(f) = r.start + size)
                       /\ \A j \in 0 .. Len(rf.pend) :
                            LET pp == Ops!ProofPair(len, rs, f, j)
                            IN IF j < Len(rf.pend) THEN pp = [off |-> rf.pend[j + 1]] ELSE "none" \in DOMAIN pp
                       /\ Len(Ops!Path(n, r.first + k)) < 64
               /\ "none" \in DOMAIN Ops!Frame(len, rs, i, Len(F))
       /\ "none" \in DOMAIN Ops!Frame(len, rs, Len(rs) + 1, 0)
       \* locate: the frame that holds the offset (every offset when `full`, the edges of every frame otherwise)
       /\ LET probes == IF full THEN 0 .. (total + 2)
                        ELSE {0, total - 1, total, total + 1, total + 2} \cup
                             UNION {UNION {{Ops!Frame(len, rs, i, k).start, Ops!FrameEnd(Ops!Frame(len, rs, i, k)) - 1} :
                                      k \in 0 .. (rs[i].last - rs[i].first - 1)} : i \in 1 .. Len(rs)}
          IN \A at \in probes :
               at >= 0 =>
                 LET f == Ops!Locate(len, rs, total, at)
                     h == RefHolder(len, rs, at)
                 IN IF at >= total THEN "none" \in DOMAIN f /\ h = {}
                    ELSE /\ Cardinality(h) = 1
                         /\ ~("none" \in DOMAIN f)
                         /\ <<f.range, f.k>> \in h
                         /\ f.start <= at /\ at < Ops!FrameEnd(f)
       \* frame_of_group: the first range that holds the group; unaligned offsets none
       /\ \A g \in 0 .. (n + 1) :
            LET f == Ops!FrameOfGroup(len, rs, g * G)
                held == {i \in 1 .. Len(rs) : rs[i].first <= g /\ g < rs[i].last}
            IN IF held = {} THEN "none" \in DOMAIN f
               ELSE LET i == CHOOSE i \in held : \A j \in held : i <= j
                    IN /\ ~("none" \in DOMAIN f) /\ f.range = i /\ f.k = g - rs[i].first /\ f.off = g * G
       /\ \A d \in 1 .. (G - 1) : "none" \in DOMAIN Ops!FrameOfGroup(len, rs, d)

PlanOK(len, spans, full) ==
    LET sp == Ops!SpecNew(len, spans)
        pn == Ops!PlanNew(len, spans)
    IN /\ pn = sp
       /\ IF "err" \in DOMAIN pn THEN TRUE ELSE FramesOK(len, pn, full)

(* ---- the requests ---- *)
SpanSet(len) == {<<o, l>> : o \in 0 .. (len + 1), l \in 0 .. (len + 2)}
EdgeSpans(len) == {<<o, l>> : o \in {0, 1, G, G + 1, len - 1, len}, l \in {0, 1, G + 1, len}}
SmallSpans(len) == {<<0, len>>, <<1, len>>, <<len - 1, 1>>, <<G, G + 1>>}

CasesFor(len) ==
    (IF len <= 8 THEN {[len |-> len, spans |-> <<s>>, full |-> TRUE] : s \in SpanSet(len)}
     ELSE {[len |-> len, spans |-> <<s>>, full |-> FALSE] : s \in EdgeSpans(len)})
    \cup {[len |-> len, spans |-> <<s, t>>, full |-> FALSE] : s \in EdgeSpans(len), t \in EdgeSpans(len)}
    \cup {[len |-> len, spans |-> <<s, t, u>>, full |-> FALSE] : s \in SmallSpans(len), t \in SmallSpans(len), u \in SmallSpans(len)}
    \cup {[len |-> len, spans |-> <<<<0, 1>>, <<0, 1>>, <<0, 1>>, <<0, 1>>>>, full |-> FALSE]}
    \cup {[len |-> len, spans |-> <<>>, full |-> FALSE]}

Cases == UNION {CasesFor(len) : len \in 1 .. MaxLen}

VARIABLE c
Init == c \in Cases
Next == UNCHANGED c
Spec == Init /\ [][Next]_c

Inv == PlanOK(c.len, c.spans, c.full)
=============================================================================
