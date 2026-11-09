--------------------------- MODULE TraceRangeVerifier ---------------------------
(***************************************************************************)
(* Trace validation of vinc-dag RangeVerifier<GROUP> (tree/verify.rs).     *)
(*                                                                         *)
(* The Rust test tests/trace_verifier.rs runs the real verifier on genuine *)
(* and tampered streams, fed in pieces of every size, and records one      *)
(* event per run (the value length, group size log, requested byte range,  *)
(* root) and one per feed call (the input length, what the verifier        *)
(* reported, and, when the call completed a stream item, the item and the  *)
(* hash call the verifier made for it with its computed chaining value).   *)
(* Chaining values and group bytes are ids.                                *)
(*                                                                         *)
(* Each feed event must be a step of this module, built from the model in  *)
(* RangeVerifier.tla (StepWith, QueryKey, Left, the invariants):           *)
(*  - the buffer: a call takes the whole next item straight from the input *)
(*    when nothing is buffered and the input holds it (the fast path),     *)
(*    otherwise it buffers min(input, still needed) bytes; either way the  *)
(*    item completes when its last byte arrives, so both paths take the    *)
(*    same transition on the completed item; the stream offset `pos` of    *)
(*    each piece advances by exactly the bytes consumed, and a completed   *)
(*    item starts at `pos - filled`, the offset of its first byte;         *)
(*  - the item: the hash call the verifier made (key) must be the one the  *)
(*    model makes for that item, and the recorded value is the oracle, so  *)
(*    the model decides accept or reject from it; the oracle must be a     *)
(*    function (one value per key within a run);                           *)
(*  - the report: consumed bytes, released offset, error, next_len and     *)
(*    is_complete equal the model's, and a released group borrows the      *)
(*    input exactly on the fast path and is the bytes that were hashed;    *)
(*  - the encoder: the step the range encoder emitted for the item names   *)
(*    the model's node (outboard offset = 64 * pre-order position of the   *)
(*    parent, value offset and length of the group).                       *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds verifier.ndjson.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES n, first, last, stack, failed, released, len, G, filled, oracle, errk, pos, i
core == <<n, first, last, stack, failed, released>>
vars == <<n, first, last, stack, failed, released, len, G, filled, oracle, errk, pos, i>>

RV == INSTANCE RangeVerifier WITH MaxGroups <- 6
VB == INSTANCE VerifierBytes WITH Extra <- 0, cfg <- 0, its <- 0, vs <- 0, pos <- 0, rem <- 0, stop <- FALSE, j <- 0
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/verifier.ndjson")

Min(a, b) == IF a < b THEN a ELSE b

(* the layout of the current run as VerifierBytes.tla has it: the value length, the group length and parent length
   in bytes, a usize of 64 bits (the host of the trace) and the number of groups *)
Lay == [len |-> U!W(len), g |-> U!W(G), p |-> U!W(64), bits |-> 64, n |-> VB!L!GroupsG(U!W(len), U!W(G))]

(* the verifier state as Plan and NextLen read it: the bytes buffered, the failure, and the node on top *)
VsOf(st, f, fl) ==
    [filled |-> U!W(fl), failed |-> IF f THEN "failed" ELSE "none",
     stack |-> IF st = <<>> THEN <<>> ELSE <<[lo |-> U!W(Head(st).lo), hi |-> U!W(Head(st).hi)]>>]

(* Layout::group_size: the bytes of group g *)
GroupSize(g) == U!Val(VB!L!GroupSizeG(U!W(len), U!W(G), U!W(g)))

(* how many bytes the node needs as its stream item *)
NodeNeed(nd) == IF nd.hi - nd.lo = 1 THEN GroupSize(nd.lo) ELSE 64

(* next_len: the bytes still needed for the current item, -1 when complete or failed *)
NL(st, f, fl) == VB!NextLen(Lay, VsOf(st, f, fl))

(* the pre-order position of the parent [lo, hi) among the parents of the tree [a, b), counted from the
   definition: the node itself first, then every parent of the left subtree, then those of the right one *)
Parents(a, b) == IF b - a >= 2 THEN b - a - 1 ELSE 0
RECURSIVE Pos(_, _, _, _)
Pos(a, b, lo, hi) ==
    IF a = lo /\ b = hi THEN 0
    ELSE LET m == a + RV!Left(b - a)
         IN IF hi <= m THEN 1 + Pos(a, m, lo, hi) ELSE 1 + Parents(a, m) + Pos(m, b, lo, hi)

Init ==
    /\ i = 0
    /\ n = 0 /\ first = 0 /\ last = 0 /\ stack = <<>> /\ failed = FALSE /\ released = <<>>
    /\ len = 0 /\ G = 1024 /\ filled = 0 /\ oracle = [k \in {} |-> 0] /\ errk = "none" /\ pos = 0

(* a new run: the layout, the requested group range and the initial stack, derived from the request *)
Begin ==
    /\ i = 0
    /\ \E k \in 1..Len(Trace) : Trace[k].t = "vrun" /\ LET ev == Trace[k]
           g == 1024 * 2 ^ ev.log
           cnt == (ev.len + g - 1) \div g
       IN /\ ev.t = "vrun"
          /\ ev.s <= ev.e /\ ev.e <= ev.len
          /\ len' = ev.len /\ G' = g
          /\ n' = cnt /\ ev.n = cnt
          /\ IF ev.s = ev.e THEN first' = 0 /\ last' = 0
             ELSE first' = ev.s \div g /\ last' = (ev.e - 1) \div g + 1
          /\ ev.first = first' /\ ev.last = last'
          /\ stack' = IF first' < last' THEN <<[cv |-> ev.root, lo |-> 0, hi |-> cnt]>> ELSE <<>>
          /\ failed' = FALSE /\ released' = <<>>
          /\ filled' = 0 /\ oracle' = [kk \in {} |-> 0] /\ errk' = "none" /\ pos' = 0
          /\ i' = k + 1

(* one call of feed *)
FeedEv ==
    /\ i >= 1 /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
           pl == VB!Plan(Lay, VsOf(stack, failed, filled), U!W(ev.ilen))
           nlm == NL(stack, failed, filled)
           fast == pl.kind = "item" /\ pl.fast
       IN /\ ev.t = "vfeed"
          /\ ev.pos = pos
          /\ pos' = IF ev.consumed >= 0 THEN pos + ev.consumed ELSE pos
          /\ ev.istart = IF ev.out \in {"parent", "release", "reject"} THEN pos - filled ELSE -1
          /\ ev.nl0 = nlm
          /\ ev.fast = fast
          /\ ev.rd = (IF ev.out = "release" THEN ev.item.d ELSE 0)
          /\ UNCHANGED <<len, G>>
          /\ i' = i + 1
          /\ IF pl.kind = "sticky"
             THEN \* a failed verifier repeats its error and changes nothing
                  /\ ev.out = "sticky" /\ ev.err = errk /\ ev.consumed = -1 /\ ev.off = -1 /\ ev.ptr = "none"
                  /\ ev.nl = -1 /\ ev.cmp = FALSE
                  /\ UNCHANGED <<core, filled, oracle, errk>>
             ELSE IF pl.kind = "empty"
             THEN /\ ev.out = "empty" /\ ev.err = "none" /\ ev.consumed = 0 /\ ev.off = -1 /\ ev.ptr = "none"
                  /\ ev.nl = nlm /\ ev.cmp = (stack = <<>>)
                  /\ UNCHANGED <<core, filled, oracle, errk>>
             ELSE IF pl.kind = "toomuch"
             THEN /\ ev.out = "toomuch" /\ ev.err = "toomuch" /\ ev.consumed = -1 /\ ev.off = -1 /\ ev.ptr = "none"
                  /\ ev.nl = -1 /\ ev.cmp = TRUE
                  /\ UNCHANGED <<core, filled, oracle, errk>>
             ELSE LET take == U!Val(pl.take)
                  IN IF pl.kind = "partial"
                     THEN \* the item is still incomplete: the bytes are buffered
                          /\ ev.out = "more" /\ ev.err = "none" /\ ev.consumed = take /\ ev.off = -1 /\ ev.ptr = "none"
                          /\ filled' = U!Val(pl.filled)
                          /\ ev.nl = NL(stack, failed, filled') /\ ev.cmp = FALSE
                          /\ UNCHANGED <<core, oracle, errk>>
                     ELSE LET top == Head(stack)
                              leaf == top.hi - top.lo = 1
                          IN \* the item is complete: the model takes its step under the recorded oracle
                             /\ filled' = 0
                             /\ ev.key = RV!QueryKey(ev.item)
                             /\ (ev.key \in DOMAIN oracle => oracle[ev.key] = ev.hout)
                             /\ oracle' = IF ev.key \in DOMAIN oracle THEN oracle
                                          ELSE oracle @@ (ev.key :> ev.hout)
                             /\ ev.step = IF leaf THEN <<"g", top.lo * G, GroupSize(top.lo)>>
                                          ELSE <<"p", 64 * Pos(0, n, top.lo, top.hi)>>
                             /\ RV!StepWith(ev.hout, ev.item)
                             /\ IF failed'
                                THEN /\ ev.out = "reject" /\ ev.consumed = -1 /\ ev.off = -1 /\ ev.ptr = "none"
                                     /\ errk' = IF leaf THEN "group" ELSE "parent"
                                     /\ ev.err = errk'
                                     /\ ev.nl = -1 /\ ev.cmp = FALSE
                                ELSE /\ ev.err = "none" /\ ev.consumed = take
                                     /\ errk' = errk
                                     /\ ev.nl = NL(stack', failed', 0) /\ ev.cmp = (stack' = <<>>)
                                     /\ IF leaf
                                        THEN /\ ev.out = "release"
                                             /\ ev.off = released'[Len(released')][1] * G
                                             /\ ev.ptr = IF fast THEN "input" ELSE "buf"
                                        ELSE /\ ev.out = "parent" /\ ev.off = -1 /\ ev.ptr = "none"

\* a run ends where the next one begins, or at the end of the trace
RunEnd == i >= 1 /\ (i > Len(Trace) \/ (i <= Len(Trace) /\ Trace[i].t = "vrun")) /\ UNCHANGED vars

TNext == Begin \/ FeedEv \/ RunEnd

TraceSpec == Init /\ [][TNext]_vars

(* the safety facts of the model hold on every recorded state, for the recorded roots *)
Inv ==
    /\ RV!Ascending /\ RV!InRange /\ RV!Bookkeeping
    /\ Len(stack) <= 55
    /\ filled < 1 \/ (stack # <<>> /\ filled < NodeNeed(Head(stack)))

=================================================================================
