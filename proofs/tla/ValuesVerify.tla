------------------------------ MODULE ValuesVerify ------------------------------
(***************************************************************************)
(* The GroupVerifier of pinc-values (verify.rs) at the byte level, checked *)
(* against the RangeVerifier model of VerifierBytes.tla on every split of  *)
(* the stream into pieces.                                                 *)
(*                                                                         *)
(* GroupVerifier checks the same stream as pinc-dag RangeVerifier (parent  *)
(* pairs and groups in the pre-order of a range) but never holds a group:  *)
(* the bytes of a group go to an incremental hasher as the pieces arrive.  *)
(* The model is `feed` call for call on the machine integers of U64.tla:   *)
(* the 64-byte pair buffer (`pair_n`, the segments copied into it), the    *)
(* hasher (`group_n`, the stream segments it took: BLAKE3's incremental    *)
(* update makes the hasher state stand for the concatenation of what it    *)
(* took), the pair read straight from the input when the buffer is empty   *)
(* and the whole pair is there, `take = try_from(size - group_n)` or the   *)
(* input, min the input, OutputTooSmall past 64, `complete_pair` (the hash *)
(* test, the pop, the two pushes right then left, StackOverflow at 64      *)
(* nodes), the sticky failure, TooMuchData on a complete stream, the       *)
(* empty-input no-op, `next_item`, `next_len`, `at_boundary`,              *)
(* `is_complete`, `failure` and `skip_group`. The part that depends only   *)
(* on the lengths is ValuesVerifyOps.tla (also used by the trace check).   *)
(* The hash is symbolic (a term of its arguments: collision resistance),   *)
(* as in VerifierBytes.tla.                                                *)
(*                                                                         *)
(* A state machine feeds the same pieces to the RangeVerifier model        *)
(* (VerifierBytes.tla, whose own invariants hold when SkipOn is FALSE) and *)
(* to the GroupVerifier model, for every value, requested range, tampered  *)
(* item and split. With SkipOn the machine may also call `skip_group`     *)
(* between pieces, anywhere: it must be refused (the verifier unchanged)   *)
(* unless the verifier is not failed, at the start of an item and the next *)
(* item is a group; accepted, it passes the group (the stream continues    *)
(* after the group's bytes) and leaves the verifier as the RangeVerifier   *)
(* is left by being fed the genuine group.                                 *)
(*                                                                         *)
(* At every state `Inv` holds: on every call the two models returned the   *)
(* same kind of result and consumed the same bytes; a group is reported at *)
(* the call where the RangeVerifier releases it, with the same offset and  *)
(* length, and is made of exactly the stream bytes of that item; the two   *)
(* stacks, failures, groups passed, bytes buffered (pair_n + group_n) and  *)
(* observables (next_len, next_item, at_boundary, is_complete, failure)    *)
(* are equal; every group passed after a match is genuine (the tampered    *)
(* item is never accepted); TooMuchData only on a complete stream; the     *)
(* buffers stay below the item. The temporal properties: a failure is      *)
(* permanent, a rejected item passes nothing, a refused skip changes       *)
(* nothing.                                                                *)
(*                                                                         *)
(* Lean counterparts (proofs/lean/Pinc/ValuesVerify*.lean):                *)
(*   the model            ValuesVerify.feedG, skipG, nextItemG, ...         *)
(*   equivalence          ValuesVerifySim.feedG_sim, driveAllG_eq,          *)
(*                        group_equiv_range, group_split_invariance        *)
(*   soundness            ValuesVerifySound.released_genuine,              *)
(*                        feedG_release_verified, feedG_reject,            *)
(*                        feedG_sticky, complete_releases_range            *)
(*   skip_group           ValuesVerifySound.skipG_eq_feedG, skipG_err      *)
(*   the Rx use           ValuesVerifyRx.hdrDone_inv, proofStep_inv,       *)
(*                        dataStep_inv, enterData_total                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Extra, SkipOn, SeedSet

VARIABLES cfg, its, vs, pos, rem, stop, j, gs, agree, op

U == INSTANCE U64
VB == INSTANCE VerifierBytes WITH Extra <- Extra, cfg <- cfg, its <- its, vs <- vs, pos <- pos, rem <- rem,
                                  stop <- stop, j <- j
GV == INSTANCE ValuesVerifyOps
L == INSTANCE Layout WITH SmallLen <- 0, PreN <- 0, c <- 0

(* ---- the GroupVerifier ---- *)

GInit(c, its0) ==
    [stack |-> VB!InitVs(c, its0).stack, pairN |-> U!Zero, psegs |-> <<>>, groupN |-> U!Zero, hsegs |-> <<>>,
     failed |-> "none", done |-> <<>>, lc |-> <<>>]

(* complete_pair on the node on top and the content of the 64-byte pair *)
GCompletePair(c, its0, g, content) ==
    LET lay == c.lay
        node == Head(g.stack)
        rest == Tail(g.stack)
        isRoot == node.lo = U!Zero /\ node.hi = lay.n
        l == VB!ParseSide(c, its0, content, "l")
        r == VB!ParseSide(c, its0, content, "r")
        cv == <<"P", isRoot, l, r>>
    IN IF cv # node.cv THEN [g EXCEPT !.failed = "parent", !.pairN = U!Zero, !.psegs = <<>>]
       ELSE LET mid == U!Add64(node.lo, L!LeftGroups(U!Sub64(node.hi, node.lo)))
                ex == GV!GExpand(rest, [cv |-> r, lo |-> mid, hi |-> node.hi], [cv |-> l, lo |-> node.lo, hi |-> mid],
                                 U!Lt(mid, c.last), U!Lt(c.first, mid))
            IN [g EXCEPT !.stack = ex.st, !.failed = IF ex.ok THEN "none" ELSE "stack overflow",
                         !.pairN = U!Zero, !.psegs = <<>>]

(* GroupVerifier::feed on the input [pos, pos + ilen): the new state, what the call reports and the bytes consumed *)
GFeed(c, its0, g, p, ilen) ==
    LET lay == c.lay
        pl == GV!GPlan(lay, g, ilen)
    IN CASE pl.kind = "sticky" -> [g |-> g, res |-> "sticky", consumed |-> U!Zero]
         [] pl.kind = "empty" -> [g |-> g, res |-> "empty", consumed |-> U!Zero]
         [] pl.kind = "toomuch" -> [g |-> g, res |-> "toomuch", consumed |-> U!Zero]
         [] pl.kind = "outputtoosmall" -> [g |-> g, res |-> "outputtoosmall", consumed |-> U!Zero]
         [] pl.kind = "partial" ->
              LET node == Head(g.stack)
                  leaf == U!Sub64(node.hi, node.lo) = U!One
                  base == IF g.groupN = U!Zero THEN <<>> ELSE g.hsegs
              IN [g |-> IF leaf THEN [g EXCEPT !.groupN = pl.groupN, !.hsegs = VB!AppendSeg(base, p, pl.take)]
                        ELSE [g EXCEPT !.pairN = pl.pairN, !.psegs = VB!AppendSeg(g.psegs, p, pl.take)],
                  res |-> "more", consumed |-> pl.take]
         [] pl.kind = "item" ->
              LET node == Head(g.stack)
                  isRoot == node.lo = U!Zero /\ node.hi = lay.n
              IN IF pl.leaf
                 THEN LET base == IF g.groupN = U!Zero THEN <<>> ELSE g.hsegs
                          hs == VB!AppendSeg(base, p, pl.take)
                          off == U!Mul64(node.lo, lay.g)
                          cv == <<"L", isRoot, off, VB!Payload(c, its0, hs)>>
                          g0 == [g EXCEPT !.groupN = U!Zero, !.hsegs = <<>>]
                      IN IF cv # node.cv
                         THEN [g |-> [g0 EXCEPT !.failed = "group"], res |-> "reject", consumed |-> pl.take]
                         ELSE [g |-> [g0 EXCEPT !.stack = Tail(g.stack), !.lc = hs,
                                                !.done = Append(g.done, <<off, "fed", hs = VB!Payload(c, its0, hs)>>)],
                               res |-> "release", consumed |-> pl.take,
                               grp |-> [off |-> off, len |-> pl.size], content |-> hs]
                 ELSE LET content == IF pl.whole THEN <<<<p, lay.p>>>> ELSE VB!AppendSeg(g.psegs, p, pl.take)
                          g1 == GCompletePair(c, its0, g, content)
                      IN [g |-> IF g1.failed # "none" THEN g1 ELSE [g1 EXCEPT !.lc = content], res |-> IF g1.failed # "none" THEN "reject" ELSE "parent",
                          consumed |-> pl.take, content |-> content]

(* skip_group: [ok, g] *)
GSkip(c, g) ==
    LET it == GV!GNextItem(c.lay, g)
    IN IF g.failed = "none" /\ GV!GBoundary(g) /\ Len(it) = 3
       THEN [ok |-> TRUE, size |-> U!W(it[3]),
             g |-> [g EXCEPT !.stack = Tail(g.stack), !.done = Append(g.done, <<U!W(it[2]), "skip", TRUE>>)]]
       ELSE [ok |-> FALSE, g |-> g]

(* ---- the agreement of the two models on one call ---- *)

Agrees(c, its0, v, g, f, gf) ==
    LET lay == c.lay
    IN /\ gf.res = f.res
       /\ gf.consumed = f.consumed
       /\ gf.g.stack = f.vs.stack
       /\ gf.g.failed = f.vs.failed
       /\ gf.g.lc = f.vs.lc
       /\ U!Add(gf.g.pairN, gf.g.groupN) = f.vs.filled
       /\ [k \in 1..Len(gf.g.done) |-> gf.g.done[k][1]] = f.vs.released
       /\ \A k \in 1..Len(gf.g.done) : gf.g.done[k][3]
       /\ (f.res = "release" =>
             /\ gf.grp.off = Head(f.vs.released \o <<U!Zero>>) \/ gf.grp.off = f.vs.released[Len(f.vs.released)]
             /\ gf.grp.len = L!GroupSizeG(lay.len, lay.g, Head(v.stack).lo))
       /\ (f.res # "release" => ~("grp" \in DOMAIN gf))
       /\ GV!GNextLen(lay, gf.g) = VB!NextLen(lay, f.vs)
       /\ GV!GBoundary(gf.g) = (f.vs.filled = U!Zero)
       /\ (GV!GNextItem(lay, gf.g) = <<>>) = (f.vs.failed # "none" \/ f.vs.stack = <<>>)
       /\ LET gi == GV!GNextItem(lay, gf.g)
          IN f.vs.failed = "none" /\ f.vs.stack # <<>> =>
               (gi = IF U!Sub64(Head(f.vs.stack).hi, Head(f.vs.stack).lo) = U!One
                     THEN <<"g", U!Val(U!Mul64(Head(f.vs.stack).lo, lay.g)),
                            U!Val(L!GroupSizeG(lay.len, lay.g, Head(f.vs.stack).lo))>>
                     ELSE <<"p">>)

(* ---- the state machine ---- *)

Total(c, it) == VB!Total(c, it)

MySeeds ==
    CASE SeedSet = "tiny" ->
           {[f |-> "small", g |-> 2, p |-> 1, len |-> len] : len \in 0..5}
      [] SeedSet = "small" ->
           (UNION {{[f |-> "small", g |-> gp[1], p |-> gp[2], len |-> len] : len \in 0..(3 * gp[1] + 1)} :
                   gp \in {<<2, 2>>, <<4, 3>>}})
      [] SeedSet = "small_skip" ->
           {[f |-> "small", g |-> 2, p |-> 2, len |-> len] : len \in 0..5}
      [] SeedSet = "real64" -> {[f |-> "real", g |-> 1024, bits |-> 64]}
      [] SeedSet = "real32" -> {[f |-> "real", g |-> 1024, bits |-> 32]}

Init == cfg = [k |-> "root"] /\ its = <<>> /\ vs = <<>> /\ pos = U!Zero /\ rem = U!Zero /\ stop = FALSE /\ j = 0
        /\ gs = <<>> /\ agree = TRUE /\ op = "none"

Fed(k) ==
    LET f == VB!Feed(cfg, its, vs, pos, k)
        gf == GFeed(cfg, its, gs, pos, k)
        bad == {"sticky", "toomuch", "reject", "outputtoosmall"}
    IN /\ vs' = f.vs
       /\ gs' = gf.g
       /\ agree' = Agrees(cfg, its, vs, gs, f, gf)
       /\ pos' = U!Add(pos, f.consumed)
       /\ rem' = IF f.res \in bad THEN U!Zero ELSE U!Sub(k, f.consumed)
       /\ stop' = (f.res \in bad)
       /\ j' = IF f.res \in {"reject", "release", "parent"} THEN j + 1 ELSE j
       /\ op' = "feed"
       /\ UNCHANGED <<cfg, its>>

(* skip_group between pieces; the stream continues after the group *)
Skipped ==
    LET sk == GSkip(cfg, gs)
        v0 == [vs EXCEPT !.filled = U!Zero, !.segs = <<>>]
        refOk == vs.failed = "none" /\ vs.filled = U!Zero /\ vs.stack # <<>> /\ U!Sub64(Head(vs.stack).hi, Head(vs.stack).lo) = U!One
        ref == VB!Complete([cfg EXCEPT !.tam = -1], its, v0, VB!ContentOf(cfg, its, j))
    IN /\ SkipOn /\ cfg.k = "cfg" /\ ~stop /\ rem = U!Zero
       /\ agree' = (sk.ok = refOk /\ (sk.ok => (sk.g.stack = ref.vs.stack /\ sk.g.failed = ref.vs.failed)))
       /\ IF sk.ok
          THEN /\ gs' = [sk.g EXCEPT !.lc = ref.vs.lc]
               /\ vs' = ref.vs
               /\ pos' = U!Add(pos, sk.size)
               /\ j' = j + 1
               /\ op' = "skip"
          ELSE /\ UNCHANGED <<gs, vs, pos, j>>
               /\ op' = "refused"
       /\ UNCHANGED <<cfg, its, rem, stop>>

Next ==
    \/ cfg.k = "root" /\ \E sd \in MySeeds : cfg' = [k |-> "seed", sd |-> sd] /\ UNCHANGED <<its, vs, pos, rem, stop, j, gs, agree, op>>
    \/ cfg.k = "seed" /\ \E x \in VB!CfgsOf(cfg.sd) :
           /\ cfg' = x
           /\ its' = VB!Items(x)
           /\ vs' = VB!InitVs(x, VB!Items(x))
           /\ gs' = GInit(x, VB!Items(x))
           /\ UNCHANGED <<pos, rem, stop, j, agree, op>>
    \/ cfg.k = "cfg" /\ ~stop /\ \E k \in (IF rem = U!Zero THEN VB!PieceSizes(cfg, its, pos) ELSE {rem}) : Fed(k)
    \/ Skipped

Spec == Init /\ [][Next]_<<cfg, its, vs, pos, rem, stop, j, gs, agree, op>>

(* ---- the properties ---- *)

Inv ==
    IF cfg.k # "cfg" THEN TRUE
    ELSE /\ agree
         /\ \* the buffers stay below the item
            (gs.failed = "none" /\ gs.stack # <<>>) =>
               /\ U!Lt(gs.pairN, cfg.lay.p)
               /\ (gs.groupN # U!Zero =>
                     (U!Sub64(Head(gs.stack).hi, Head(gs.stack).lo) = U!One /\
                      U!Lt(gs.groupN, L!GroupSizeG(cfg.lay.len, cfg.lay.g, Head(gs.stack).lo))))
         /\ \* no step failed: the narrowing of the item size
            (gs.stack # <<>> /\ gs.failed = "none") => VB!NextItem(cfg.lay, vs).ok
         /\ \* TooMuchData only on a complete stream
            stop /\ gs.failed = "none" => gs.stack = <<>>
         /\ gs.failed \notin {"stack overflow"}
         /\ Len(gs.stack) <= 55
         /\ \* a failure comes from a tampered item
            (gs.failed # "none" => cfg.tam >= 0)
         /\ \* the genuine stream is never rejected, and on it the verifier completes with exactly the requested groups
            (cfg.tam = -1 /\ ~SkipOn /\ U!Le(Total(cfg, its), pos)) =>
               /\ gs.stack = <<>> /\ gs.failed = "none"
               /\ Len(gs.done) = U!Val(U!Sub(cfg.last, cfg.first))
               /\ \A i \in 1..Len(gs.done) : gs.done[i][1] = U!Mul64(U!Add(cfg.first, U!W(i - 1)), cfg.lay.g)

(* the RangeVerifier model's own lockstep invariants, which hold when no group is skipped *)
VInv == IF SkipOn \/ cfg.k # "cfg" THEN TRUE ELSE VB!Inv

(* a failure is permanent, and the step that fails passes nothing; a refused skip changes nothing *)
FailureSticky == [][(gs # <<>> /\ gs.failed # "none") => (gs'.failed = gs.failed /\ gs'.done = gs.done /\ gs'.stack = gs.stack)]_<<gs>>
RejectPassesNothing == [][(gs # <<>> /\ gs.failed = "none" /\ gs'.failed # "none") => gs'.done = gs.done]_<<gs>>
RefusedSkip == [][op' = "refused" => gs' = gs]_<<gs, op>>
=============================================================================
