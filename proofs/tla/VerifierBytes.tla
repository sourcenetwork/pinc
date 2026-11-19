---------------------------- MODULE VerifierBytes ----------------------------
(***************************************************************************)
(* The range verifier of pinc-dag (tree/verify.rs) at the byte level: the  *)
(* call `feed` with its buffer of GROUP bytes, `filled`, the zero-copy     *)
(* fast path (nothing buffered and the whole next item in the input) and   *)
(* the buffered path, `next_item` (`usize::try_from` of the item size),    *)
(* `take = input.len().min(need - filled)`, `filled + take`, and           *)
(* `Walk::complete` (the root test, the hash of a group or of a parent     *)
(* pair, the pop, the push of the children with `node.lo + left_groups`),  *)
(* written step for step on the machine integers of U64.tla, on a usize   *)
(* of 32 or 64 bits. A step that overflows, underflows or narrows to a     *)
(* usize that does not fit stops TLC with an error.                        *)
(*                                                                         *)
(* The buffer is the list of the stream segments copied into it (every     *)
(* stream byte is named by its offset, a segment is <<offset, length>>,    *)
(* adjacent segments merge), so a buffered item is the one stream segment  *)
(* [start, start + need) exactly when the copies were contiguous, and the  *)
(* fast path hashes the segment [pos, pos + need) of the input. The hash   *)
(* is symbolic (a term of its arguments, which is collision resistance).   *)
(* The stream is the genuine stream of the encoder (the items of the       *)
(* pre-order walk over the requested groups, a parent's item holding the   *)
(* chaining values of its children, a group's item its bytes) or the same  *)
(* stream with one item tampered with (the bytes of a group or the pair    *)
(* of a parent replaced), and, in both cases, extra bytes after the end.   *)
(*                                                                         *)
(* Plan is the part of `feed` that depends only on the buffer and the     *)
(* lengths (which path, how many bytes are taken, what `next_len` is); the *)
(* trace check of TraceRangeVerifier.tla uses the same Plan.               *)
(*                                                                         *)
(* Checked by TLC (VerifierBytes.cfg) as a state machine that feeds pieces *)
(* (the caller feeding the unconsumed tail of each piece and stopping at   *)
(* the first error):                                                       *)
(*  - every value of up to 4 groups of group lengths 2 and 4 bytes with    *)
(*    pairs of 1, 2 and 3 bytes (the model is parametric in the group      *)
(*    length and the pair length, which the code uses only through         *)
(*    `group_len()` and PARENT_LEN, the buffer holding either),            *)
(*    every requested group range, the genuine stream and the stream with  *)
(*    each item tampered with, in every split into pieces of every size;   *)
(*  - the real sizes (pairs of 64 bytes, groups of 1 KiB, 2 KiB and        *)
(*    1 GiB) with pieces from the boundary sizes, on both usize widths.    *)
(* At every state `Lockstep` holds: the verifier's stack, releases and     *)
(* failure equal the item-by-item reference run over the items completed,  *)
(* each item completed is exactly the stream segment the reference run     *)
(* names (the buffered copies are contiguous and from the right offset),   *)
(* the offset of the next item is the bytes consumed minus those buffered, *)
(* `TooMuchData` is returned exactly when the stream is complete and the   *)
(* input is not empty, and no step fails; on a genuine stream the verifier *)
(* completes with exactly the requested groups released, in order.         *)
(*                                                                         *)
(* Lean counterparts (proofs/lean/Pinc/VerifyBytes.lean):                  *)
(*   Lockstep        VerifyBytes.feedCode_sim, VerifyBytes.needW_eq        *)
(*   Equivalence     VerifyBytes.split_invariance, stream_equiv            *)
(*                   (with drivePiece_eq, driveAll_eq, bytes_items,        *)
(*                   itemwise_core)                                        *)
(*   Complete        VerifyBytes.complete_arith, Encode.complete_accepts   *)
(*   the boundary sets  Pinc.Link (Verifier boundary theorems)             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64
L == INSTANCE Layout WITH SmallLen <- 0, PreN <- 0, c <- 0

StackCap == 64
Two == U!W(2)

(* ---- the stream of the encoder ---- *)

(* the items of the pre-order walk of the node [a, b) over the groups [first, last): the node and the bytes of its item *)
Inter(a, b, first, last) == U!Lt(a, last) /\ U!Lt(first, b)
RECURSIVE ItemsOf(_, _, _, _, _)
ItemsOf(lay, a, b, first, last) ==
    IF U!Sub(b, a) = U!One
    THEN <<[lo |-> a, hi |-> b, need |-> L!GroupSizeG(lay.len, lay.g, a)]>>
    ELSE LET m == U!Add(a, L!SpecLeft(U!Sub(b, a)))
         IN <<[lo |-> a, hi |-> b, need |-> lay.p]>>
            \o (IF Inter(a, m, first, last) THEN ItemsOf(lay, a, m, first, last) ELSE <<>>)
            \o (IF Inter(m, b, first, last) THEN ItemsOf(lay, m, b, first, last) ELSE <<>>)

MkCfg(len, g, p, bits, first, last, tam) ==
    [k |-> "cfg",
     lay |-> [len |-> len, g |-> g, p |-> U!W(p), bits |-> bits, n |-> L!GroupsG(len, g)],
     first |-> U!W(first), last |-> U!W(last), tam |-> tam]

RECURSIVE SumNeeds(_, _)
SumNeeds(its, k) == IF k > Len(its) THEN U!Zero ELSE U!Add(its[k].need, SumNeeds(its, k + 1))

Items(cfg) ==
    IF cfg.first = cfg.last THEN <<>>
    ELSE ItemsOf(cfg.lay, U!Zero, cfg.lay.n, cfg.first, cfg.last)

(* the stream offset of item j (0-based): the sum of the bytes of the items before it *)
StartOf(its, j) == SumNeeds(SubSeq(its, 1, j), 1)

(* the stream segment of item j, as the content a verifier holds when the item is complete *)
ContentOf(cfg, its, j) == <<<<StartOf(its, j), its[j + 1].need>>>>

(* ---- genuine chaining values and the content an item reads as ---- *)

(* the item whose stream segment is `content` (a single segment), or 0 when there is none *)
ItemAt(cfg, its, content) ==
    IF Len(content) = 1 /\ \E j \in 0..(Len(its) - 1) : ContentOf(cfg, its, j) = content
    THEN CHOOSE j \in 0..(Len(its) - 1) : ContentOf(cfg, its, j) = content
    ELSE -1

(* the payload a group's bytes carry: the tampered group's bytes differ *)
Payload(cfg, its, content) ==
    IF cfg.tam >= 0 /\ ItemAt(cfg, its, content) = cfg.tam THEN <<"bad", content>> ELSE content

RECURSIVE GenCv(_, _, _, _)
GenCv(cfg, its, a, b) ==
    LET lay == cfg.lay
        isRoot == a = U!Zero /\ b = lay.n
    IN IF ~Inter(a, b, cfg.first, cfg.last) THEN <<"out", a, b>>
       ELSE IF U!Sub(b, a) = U!One
            THEN LET j == CHOOSE j \in 0..(Len(its) - 1) : its[j + 1].lo = a /\ its[j + 1].hi = b
                 IN <<"L", isRoot, U!Mul64(a, lay.g), ContentOf(cfg, its, j)>>
            ELSE LET m == U!Add(a, L!SpecLeft(U!Sub(b, a)))
                 IN <<"P", isRoot, GenCv(cfg, its, a, m), GenCv(cfg, its, m, b)>>

(* how the verifier reads the 64-byte pair of a parent: the chaining values of its children; the genuine pair of the
   parent item holds the genuine values, a tampered pair holds others *)
ParseSide(cfg, its, content, side) ==
    LET j == ItemAt(cfg, its, content)
    IN IF j >= 0 /\ j # cfg.tam /\ U!Sub(its[j + 1].hi, its[j + 1].lo) # U!One
       THEN LET it == its[j + 1]
                m == U!Add(it.lo, L!SpecLeft(U!Sub(it.hi, it.lo)))
            IN IF side = "l" THEN GenCv(cfg, its, it.lo, m) ELSE GenCv(cfg, its, m, it.hi)
       ELSE <<"junk", side, content>>

(* ---- the code ---- *)

InitVs(cfg, its) ==
    [filled |-> U!Zero, segs |-> <<>>, failed |-> "none", released |-> <<>>,
     stack |-> IF cfg.first = cfg.last THEN <<>>
               ELSE <<[cv |-> GenCv(cfg, its, U!Zero, cfg.lay.n), lo |-> U!Zero, hi |-> cfg.lay.n]>>,
     lc |-> <<>>]

(* Walk::next_item: the node on top and the bytes of its item, None when the stack is empty or the size does not narrow *)
NextItem(lay, vs) ==
    IF vs.stack = <<>> THEN [ok |-> FALSE]
    ELSE LET node == Head(vs.stack)
             size == IF U!Sub64(node.hi, node.lo) = U!One THEN L!GroupSizeG(lay.len, lay.g, node.lo) ELSE lay.p
             t == U!TryFrom(size, lay.bits)
         IN [ok |-> t.ok, node |-> node, need |-> t.v]

(* next_len: the bytes the current item still needs; -1 when complete or failed *)
NextLen(lay, vs) ==
    IF vs.failed # "none" THEN -1
    ELSE LET nx == NextItem(lay, vs) IN IF nx.ok THEN U!Val(U!Sub64(nx.need, vs.filled)) ELSE -1

(* the part of feed that depends only on the buffer and the lengths *)
Plan(lay, vs, ilen) ==
    IF vs.failed # "none" THEN [kind |-> "sticky"]
    ELSE IF ilen = U!Zero THEN [kind |-> "empty"]
    ELSE LET nx == NextItem(lay, vs)
         IN IF ~nx.ok THEN [kind |-> "toomuch"]
            ELSE IF vs.filled = U!Zero /\ U!Le(nx.need, ilen)
            THEN [kind |-> "item", fast |-> TRUE, need |-> nx.need, take |-> nx.need, filled |-> U!Zero]
            ELSE LET take == U!Min(ilen, U!Sub64(nx.need, vs.filled))
                     fl == U!Add2(vs.filled, take, lay.bits)
                 IN IF U!Lt(lay.g, fl) THEN [kind |-> "outputtoosmall"]
                    ELSE [kind |-> IF U!Lt(fl, nx.need) THEN "partial" ELSE "item", fast |-> FALSE,
                          need |-> nx.need, take |-> take, filled |-> IF U!Lt(fl, nx.need) THEN fl ELSE U!Zero]

(* Walk::complete on the node on top and the content of the item: the new state and what it did (a group
   released, a parent expanded, or the item rejected) *)
Complete(cfg, its, vs, content) ==
    LET lay == cfg.lay
        node == Head(vs.stack)
        isRoot == node.lo = U!Zero /\ node.hi = lay.n
        rest == Tail(vs.stack)
    IN IF U!Sub64(node.hi, node.lo) = U!One
       THEN LET cv == <<"L", isRoot, U!Mul64(node.lo, lay.g), Payload(cfg, its, content)>>
            IN IF cv # node.cv THEN [vs |-> [vs EXCEPT !.failed = "group"], kind |-> "reject"]
               ELSE [vs |-> [vs EXCEPT !.stack = rest, !.lc = content,
                                       !.released = Append(vs.released, U!Mul64(node.lo, lay.g))],
                     kind |-> "release"]
       ELSE LET l == ParseSide(cfg, its, content, "l")
                r == ParseSide(cfg, its, content, "r")
                cv == <<"P", isRoot, l, r>>
            IN IF cv # node.cv THEN [vs |-> [vs EXCEPT !.failed = "parent"], kind |-> "reject"]
               ELSE LET mid == U!Add64(node.lo, L!LeftGroups(U!Sub64(node.hi, node.lo)))
                        push == (IF U!Lt(cfg.first, mid) THEN <<[cv |-> l, lo |-> node.lo, hi |-> mid]>> ELSE <<>>)
                                \o (IF U!Lt(mid, cfg.last) THEN <<[cv |-> r, lo |-> mid, hi |-> node.hi]>> ELSE <<>>)
                        st == push \o rest
                    IN IF Len(st) > StackCap THEN [vs |-> [vs EXCEPT !.failed = "stack overflow"], kind |-> "reject"]
                       ELSE [vs |-> [vs EXCEPT !.stack = st, !.lc = content], kind |-> "parent"]

(* the segments of the buffer after copying the segment <<start, len>>: adjacent segments merge *)
AppendSeg(segs, start, ln) ==
    IF segs # <<>> /\ U!Add(segs[Len(segs)][1], segs[Len(segs)][2]) = start
    THEN SubSeq(segs, 1, Len(segs) - 1) \o <<<<segs[Len(segs)][1], U!Add(segs[Len(segs)][2], ln)>>>>
    ELSE segs \o <<<<start, ln>>>>

(* RangeVerifier::feed on the input [pos, pos + ilen): the new state, the bytes consumed and what the call reports *)
Feed(cfg, its, vs, pos, ilen) ==
    LET lay == cfg.lay
        pl == Plan(lay, vs, ilen)
    IN CASE pl.kind = "sticky" -> [vs |-> vs, res |-> "sticky", consumed |-> U!Zero]
         [] pl.kind = "empty" -> [vs |-> vs, res |-> "empty", consumed |-> U!Zero]
         [] pl.kind = "toomuch" -> [vs |-> vs, res |-> "toomuch", consumed |-> U!Zero]
         [] pl.kind = "outputtoosmall" -> [vs |-> vs, res |-> "outputtoosmall", consumed |-> U!Zero]
         [] pl.kind = "partial" ->
              [vs |-> [vs EXCEPT !.filled = pl.filled, !.segs = AppendSeg(vs.segs, pos, pl.take)],
               res |-> "more", consumed |-> pl.take]
         [] pl.kind = "item" ->
              LET content == IF pl.fast THEN <<<<pos, pl.need>>>> ELSE AppendSeg(vs.segs, pos, pl.take)
                  c == Complete(cfg, its, [vs EXCEPT !.filled = U!Zero, !.segs = <<>>], content)
              IN [vs |-> c.vs, res |-> c.kind, consumed |-> pl.take, content |-> content, fast |-> pl.fast]

(* ---- the reference: the verifier fed whole items ---- *)

(* the state after items k up to end - 1 of the stream, each completed with its own segment; a failure stops it *)
RECURSIVE RefRun(_, _, _, _, _)
RefRun(cfg, its, vs, k, end) ==
    IF k = end \/ vs.failed # "none" \/ vs.stack = <<>> THEN vs
    ELSE RefRun(cfg, its, Complete(cfg, its, vs, ContentOf(cfg, its, k)).vs, k + 1, end)

(* ---- the state machine that feeds pieces ---- *)

Total(cfg, its) == SumNeeds(its, 1)

(* the stream has `Extra` bytes after the last item *)
CONSTANT Extra

Seeds ==
    (UNION {{[f |-> "small", g |-> gp[1], p |-> gp[2], len |-> len] : len \in 0..(3 * gp[1] + 1)} :
            gp \in {<<2, 1>>, <<2, 2>>, <<4, 3>>}})
    \cup {[f |-> "real", g |-> g, bits |-> bits] : g \in {1024, 2048}, bits \in {32, 64}}
    \cup {[f |-> "gib", bits |-> bits] : bits \in {32, 64}}
(* the configurations of a seed: the value, the requested groups and the tampered item (-1 for none) *)
Tampers(c0) == {c0} \cup {[c0 EXCEPT !.tam = t] : t \in 0..(Len(Items(c0)) - 1)}
Ranges(nn) == {r \in (0..nn) \X (0..nn) : r[1] <= r[2]}

CfgsOf(sd) ==
    CASE sd.f = "small" ->
            LET nn == (sd.len + sd.g - 1) \div sd.g
            IN UNION {Tampers(MkCfg(U!W(sd.len), U!W(sd.g), sd.p, 64, r[1], r[2], -1)) : r \in Ranges(nn)}
      [] sd.f = "real" ->
            UNION {Tampers(MkCfg(U!W(len), U!W(sd.g), 64, sd.bits, r[1], r[2], -1)) :
                     len \in {sd.g + 1, 3 * sd.g}, r \in {<<0, 2>>, <<1, 2>>, <<0, 1>>}}
      [] sd.f = "gib" ->
            UNION {Tampers(MkCfg(len, U!Pw(30), 64, sd.bits, r[1], r[2], -1)) :
                     len \in {U!Add(U!Pw(30), U!One), U!Add(U!Shl(U!Pw(30), 1), U!Pw(30))}, r \in {<<0, 2>>, <<1, 2>>}}

(* the stream offsets a piece may end at: around every item start and every item middle (two bytes each side), and
   the end of the stream *)
Targets(cfg, its) ==
    LET total == U!Add(Total(cfg, its), U!W(Extra))
        pts == {StartOf(its, k) : k \in 0..Len(its)}
               \cup {U!Add(StartOf(its, k), U!Shr(its[k + 1].need, 1)) : k \in 0..(Len(its) - 1)}
        around == UNION {{U!Add(e, U!W(d)), IF U!Le(U!W(d), e) THEN U!Sub(e, U!W(d)) ELSE e} : e \in pts, d \in 0..2}
    IN {t \in around \cup {total} : U!Le(t, total)}

(* the piece sizes tried from the offset pos: every size up to the bytes left of the stream (with the extra bytes)
   for the small items; for the real ones the pieces that end at a target, so the pieces include one byte, two
   bytes, an item less one byte, an item and an item plus one byte at every offset *)
PieceSizes(cfg, its, pos) ==
    LET left == U!Sub(U!Add(Total(cfg, its), U!W(Extra)), pos)
    IN IF U!Le(cfg.lay.g, Two)
       THEN {U!W(k) : k \in 0..U!Val(left)}
       ELSE {U!Sub(t, pos) : t \in {t \in Targets(cfg, its) : U!Le(pos, t)}}

VARIABLES cfg, its, vs, pos, rem, stop, j

Init == cfg = [k |-> "root"] /\ its = <<>> /\ vs = <<>> /\ pos = U!Zero /\ rem = U!Zero /\ stop = FALSE /\ j = 0

Next ==
    \/ cfg.k = "root" /\ \E sd \in Seeds : cfg' = [k |-> "seed", sd |-> sd] /\ UNCHANGED <<its, vs, pos, rem, stop, j>>
    \/ cfg.k = "seed" /\ \E x \in CfgsOf(cfg.sd) :
           /\ cfg' = x
           /\ its' = Items(x)
           /\ vs' = InitVs(x, Items(x))
           /\ UNCHANGED <<pos, rem, stop, j>>
    \/ cfg.k = "cfg" /\ ~stop /\ \E k \in (IF rem = U!Zero THEN PieceSizes(cfg, its, pos) ELSE {rem}) :
           LET ilen == k
               f == Feed(cfg, its, vs, pos, ilen)
           IN /\ vs' = f.vs
              /\ pos' = U!Add(pos, f.consumed)
              /\ rem' = IF f.res \in {"sticky", "toomuch", "reject", "outputtoosmall"} THEN U!Zero ELSE U!Sub(ilen, f.consumed)
              /\ stop' = (f.res \in {"sticky", "toomuch", "reject", "outputtoosmall"})
              /\ j' = IF f.res \in {"reject", "release", "parent"} THEN j + 1 ELSE j
              /\ UNCHANGED <<cfg, its>>

Spec == Init /\ [][Next]_<<cfg, its, vs, pos, rem, stop, j>>

(* ---- the properties ---- *)

Inv ==
    IF cfg.k # "cfg" THEN TRUE
    ELSE LET ref == RefRun(cfg, its, InitVs(cfg, its), 0, j)
             need == IF vs.stack = <<>> \/ vs.failed # "none" THEN U!Zero ELSE NextItem(cfg.lay, vs).need
         IN /\ \* the item-by-item reference run over the items completed
               vs.stack = ref.stack /\ vs.released = ref.released /\ vs.failed = ref.failed
            /\ \* each item completed is exactly the stream segment of the reference run
               vs.lc = ref.lc
            /\ \* the offset of the next item is the bytes consumed minus those buffered
               (vs.failed = "none" /\ j <= Len(its)) => U!Sub(pos, vs.filled) = StartOf(its, j)
            /\ \* the buffer holds one contiguous segment, less than the item needs
               (vs.filled # U!Zero => (Len(vs.segs) = 1 /\ vs.segs[1] = <<StartOf(its, j), vs.filled>> /\ U!Lt(vs.filled, need)))
            /\ vs.filled = U!Zero \/ vs.segs # <<>>
            /\ vs.failed \notin {"stack overflow"}
            /\ Len(vs.stack) <= 55
            /\ \* no step failed: the narrowing of the item size and the buffer copy
               (vs.stack # <<>> /\ vs.failed = "none") => NextItem(cfg.lay, vs).ok
            /\ \* TooMuchData only on a complete stream
               stop /\ vs.failed = "none" => vs.stack = <<>>
            /\ \* the genuine stream is never rejected; the tampered item is rejected as soon as it is complete, with the
               \* error of its kind, and nothing else is
               (cfg.tam = -1 => vs.failed = "none")
            /\ (vs.failed # "none" => (cfg.tam >= 0 /\ j = cfg.tam + 1))
            /\ (cfg.tam >= 0 /\ j >= cfg.tam + 1 =>
                  vs.failed = IF U!Sub(its[cfg.tam + 1].hi, its[cfg.tam + 1].lo) = U!One THEN "group" ELSE "parent")
            /\ \* on the genuine stream the verifier completes with exactly the requested groups released, in order
               (cfg.tam = -1 /\ U!Le(Total(cfg, its), pos)) =>
                  /\ vs.stack = <<>> /\ vs.failed = "none"
                  /\ Len(vs.released) = U!Val(U!Sub(cfg.last, cfg.first))
                  /\ \A i \in 1..Len(vs.released) : vs.released[i] = U!Mul64(U!Add(cfg.first, U!W(i - 1)), cfg.lay.g)
(* The quick profile of VerifierBytes (quick/VerifierBytes.cfg substitutes Seeds <- SeedsQuick and CfgsOf <-
   CfgsOfQuick): small values of up to one group and one byte (not three groups), 1 KiB groups (not 2 KiB) on both
   usizes and every GiB case; a real or GiB seed is one genuine stream of one group and one byte, groups 0..2, with no
   tampered item and no other length or range (the small seeds keep every range and every tampered item) *)
SeedsQuick ==
    (UNION {{[f |-> "small", g |-> gp[1], p |-> gp[2], len |-> len] : len \in 0..(gp[1] + 1)} :
            gp \in {<<2, 1>>, <<2, 2>>, <<4, 3>>}})
    \cup {[f |-> "real", g |-> 1024, bits |-> bits] : bits \in {32, 64}}
    \cup {[f |-> "gib", bits |-> bits] : bits \in {32, 64}}
CfgsOfQuick(sd) ==
    CASE sd.f = "small" ->
            LET nn == (sd.len + sd.g - 1) \div sd.g
            IN UNION {Tampers(MkCfg(U!W(sd.len), U!W(sd.g), sd.p, 64, r[1], r[2], -1)) : r \in Ranges(nn)}
      [] sd.f = "real" -> {MkCfg(U!W(sd.g + 1), U!W(sd.g), 64, sd.bits, 0, 2, -1)}
      [] sd.f = "gib" -> {MkCfg(U!Add(U!Pw(30), U!One), U!Pw(30), 64, sd.bits, 0, 2, -1)}
=============================================================================
