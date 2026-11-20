--------------------------- MODULE TraceValuesVerify ---------------------------
(***************************************************************************)
(* Trace validation of pinc-values GroupVerifier (verify.rs) next to       *)
(* pinc-dag RangeVerifier (tree/verify.rs).                                *)
(*                                                                         *)
(* The Rust test tests/trace_values_verify.rs runs both real verifiers on  *)
(* genuine and tampered streams, fed the same pieces of every size, and    *)
(* records one event per run (gvrun) and one per call (gvfeed): the input  *)
(* length, what each verifier reported, and, when the call completed a     *)
(* stream item, the item and the hash call both made for it (the computed  *)
(* chaining value is the oracle). In skip mode it also records             *)
(* GroupVerifier::skip_group (gvskip), with the genuine group fed to the   *)
(* RangeVerifier alone in its place (gvrfeed), and refused skips.          *)
(*                                                                         *)
(* Each event must be a step of this module:                               *)
(*  - the RangeVerifier half is the step of TraceRangeVerifier.tla         *)
(*    (RPart): the buffer, the fast path, the oracle, StepWith of          *)
(*    RangeVerifier.tla, the reported consumed bytes, offset, error,       *)
(*    next_len and is_complete;                                            *)
(*  - the GroupVerifier half is the step of GPart, built from GPlan of     *)
(*    ValuesVerifyOps.tla (pair buffer, hasher, take, completion) and the  *)
(*    recorded oracle: the reported consumed bytes, group offset and       *)
(*    length, error, and next_len, next_item, at_boundary, is_complete     *)
(*    and failure before and after;                                        *)
(*  - the two halves agree at every state: the same stack, the same        *)
(*    groups passed, the same bytes buffered (pair_n + group_n = filled),  *)
(*    the same failure; and the call returned the same consumed bytes,     *)
(*    group offset and error (one recorded value, checked against both     *)
(*    models);                                                             *)
(*  - a skip is refused (the verifier unchanged) unless it is not failed,  *)
(*    at the start of an item and the next item is a group; an accepted    *)
(*    one pops that group, which the RangeVerifier did when fed it.        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds values_verify.ndjson. *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

VARIABLES n, first, last, stack, failed, released, len, G, filled, oracle, errk, pos, i,
          gst, gfail, grel, pairN, groupN, gerrk
core == <<n, first, last, stack, failed, released>>
gcore == <<gst, gfail, grel, pairN, groupN, gerrk>>
vars == <<n, first, last, stack, failed, released, len, G, filled, oracle, errk, pos, i,
          gst, gfail, grel, pairN, groupN, gerrk>>

RV == INSTANCE RangeVerifier WITH MaxGroups <- 6
VB == INSTANCE VerifierBytes WITH Extra <- 0, cfg <- 0, its <- 0, vs <- 0, pos <- 0, rem <- 0, stop <- FALSE, j <- 0
GV == INSTANCE ValuesVerifyOps
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/values_verify.ndjson")

(* the layout of the current run as VerifierBytes.tla has it *)
Lay == [len |-> U!W(len), g |-> U!W(G), p |-> U!W(64), bits |-> 64, n |-> VB!L!GroupsG(U!W(len), U!W(G))]

VsOf(st, f, fl) ==
    [filled |-> U!W(fl), failed |-> IF f THEN "failed" ELSE "none",
     stack |-> IF st = <<>> THEN <<>> ELSE <<[lo |-> U!W(Head(st).lo), hi |-> U!W(Head(st).hi)]>>]

GroupSize(g) == U!Val(VB!L!GroupSizeG(U!W(len), U!W(G), U!W(g)))
NodeNeed(nd) == IF nd.hi - nd.lo = 1 THEN GroupSize(nd.lo) ELSE 64
NL(st, f, fl) == VB!NextLen(Lay, VsOf(st, f, fl))

Parents(a, b) == IF b - a >= 2 THEN b - a - 1 ELSE 0
RECURSIVE Pos(_, _, _, _)
Pos(a, b, lo, hi) ==
    IF a = lo /\ b = hi THEN 0
    ELSE LET m == a + RV!Left(b - a)
         IN IF hi <= m THEN 1 + Pos(a, m, lo, hi) ELSE 1 + Parents(a, m) + Pos(m, b, lo, hi)

(* the GroupVerifier state as GPlan and the observables read it: the stack is mapped to words *)
GW(st, f, pn, gn) ==
    [failed |-> f,
     stack |-> [k \in 1..Len(st) |-> [lo |-> U!W(st[k].lo), hi |-> U!W(st[k].hi)]],
     pairN |-> U!W(pn), groupN |-> U!W(gn)]

Init ==
    /\ i = 0
    /\ n = 0 /\ first = 0 /\ last = 0 /\ stack = <<>> /\ failed = FALSE /\ released = <<>>
    /\ len = 0 /\ G = 1024 /\ filled = 0 /\ oracle = [k \in {} |-> 0] /\ errk = "none" /\ pos = 0
    /\ gst = <<>> /\ gfail = "none" /\ grel = <<>> /\ pairN = 0 /\ groupN = 0 /\ gerrk = "none"

(* a new run: the layout, the requested group range and the initial stack of both verifiers *)
Begin ==
    /\ i = 0
    /\ \E k \in 1..Len(Trace) : Trace[k].t = "gvrun" /\ LET ev == Trace[k]
           g == 1024 * 2 ^ ev.log
           cnt == (ev.len + g - 1) \div g
       IN /\ ev.s <= ev.e /\ ev.e <= ev.len
          /\ len' = ev.len /\ G' = g
          /\ n' = cnt /\ ev.n = cnt
          /\ IF ev.s = ev.e THEN first' = 0 /\ last' = 0
             ELSE first' = ev.s \div g /\ last' = (ev.e - 1) \div g + 1
          /\ ev.first = first' /\ ev.last = last'
          /\ stack' = IF first' < last' THEN <<[cv |-> ev.root, lo |-> 0, hi |-> cnt]>> ELSE <<>>
          /\ gst' = stack'
          /\ failed' = FALSE /\ released' = <<>>
          /\ gfail' = "none" /\ grel' = <<>> /\ pairN' = 0 /\ groupN' = 0 /\ gerrk' = "none"
          /\ filled' = 0 /\ oracle' = [kk \in {} |-> 0] /\ errk' = "none" /\ pos' = 0
          /\ i' = k + 1

(* the RangeVerifier half of a call of feed: TraceRangeVerifier.tla *)
\* TLC evaluates a LET value again at each of its uses in a step: each \E over a one-value set in the steps below
\* takes a call of the model once
RPart(ev) ==
    \E pl \in {VB!Plan(Lay, VsOf(stack, failed, filled), U!W(ev.ilen))} : \E nlm \in {NL(stack, failed, filled)} :
    LET fast == pl.kind = "item" /\ pl.fast
    IN /\ ev.pos = pos
       /\ pos' = IF ev.consumed >= 0 THEN pos + ev.consumed ELSE pos
       /\ ev.istart = IF ev.out \in {"parent", "release", "reject"} THEN pos - filled ELSE -1
       /\ ev.nl0 = nlm
       /\ ev.fast = fast
       /\ ev.rd = (IF ev.out = "release" THEN ev.item.d ELSE 0)
       /\ UNCHANGED <<len, G>>
       /\ IF pl.kind = "sticky"
          THEN /\ ev.out = "sticky" /\ ev.err = errk /\ ev.consumed = -1 /\ ev.off = -1 /\ ev.ptr = "none"
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
                  THEN /\ ev.out = "more" /\ ev.err = "none" /\ ev.consumed = take /\ ev.off = -1 /\ ev.ptr = "none"
                       /\ filled' = U!Val(pl.filled)
                       /\ ev.nl = NL(stack, failed, filled') /\ ev.cmp = FALSE
                       /\ UNCHANGED <<core, oracle, errk>>
                  ELSE LET top == Head(stack)
                           leaf == top.hi - top.lo = 1
                       IN /\ filled' = 0
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

(* the observables of the GroupVerifier in the state after the call, read from the primed variables *)
GObsAfter(ev) ==
    \E gw \in {GW(gst', gfail', pairN', groupN')} :
       /\ ev.gnl = GV!GNextLen(Lay, gw)
       /\ ev.gb = GV!GBoundary(gw)
       /\ ev.gi = GV!GNextItem(Lay, gw)
       /\ ev.gcmp = (gfail' = "none" /\ gst' = <<>>)
       /\ ev.gfail = gfail'

(* the GroupVerifier half of a call of feed *)
GPart(ev) ==
    \E gw \in {GW(gst, gfail, pairN, groupN)} : \E pl \in {GV!GPlan(Lay, gw, U!W(ev.ilen))} :
       /\ ev.gnl0 = GV!GNextLen(Lay, gw)
       /\ ev.gb0 = GV!GBoundary(gw)
       /\ ev.gi0 = GV!GNextItem(Lay, gw)
       /\ IF pl.kind = "sticky"
          THEN /\ ev.err = gerrk /\ ev.consumed = -1 /\ ev.off = -1 /\ ev.glen = -1
               /\ UNCHANGED gcore /\ GObsAfter(ev)
          ELSE IF pl.kind = "empty"
          THEN /\ ev.err = "none" /\ ev.consumed = 0 /\ ev.off = -1 /\ ev.glen = -1
               /\ UNCHANGED gcore /\ GObsAfter(ev)
          ELSE IF pl.kind = "toomuch"
          THEN /\ ev.err = "toomuch" /\ ev.consumed = -1 /\ ev.off = -1 /\ ev.glen = -1
               /\ UNCHANGED gcore /\ GObsAfter(ev)
          ELSE IF pl.kind = "partial"
          THEN /\ ev.err = "none" /\ ev.consumed = U!Val(pl.take) /\ ev.off = -1 /\ ev.glen = -1
               /\ pairN' = U!Val(pl.pairN) /\ groupN' = U!Val(pl.groupN)
               /\ UNCHANGED <<gst, gfail, grel, gerrk>> /\ GObsAfter(ev)
          ELSE IF pl.kind = "item"
          THEN LET node == Head(gst)
                   rest == Tail(gst)
                   mid == node.lo + RV!Left(node.hi - node.lo)
               IN /\ pairN' = 0 /\ groupN' = 0
                  /\ IF pl.leaf
                     THEN IF ev.hout = node.cv
                          THEN /\ ev.err = "none" /\ ev.consumed = U!Val(pl.take)
                               /\ ev.off = node.lo * G /\ ev.glen = U!Val(pl.size)
                               /\ gst' = rest /\ gfail' = gfail /\ gerrk' = gerrk
                               /\ grel' = Append(grel, <<node.lo, ev.item.d>>)
                          ELSE /\ ev.err = "group" /\ ev.consumed = -1 /\ ev.off = -1 /\ ev.glen = -1
                               /\ gfail' = "group" /\ gerrk' = "group" /\ UNCHANGED <<gst, grel>>
                     ELSE IF ev.hout = node.cv
                          THEN /\ ev.off = -1 /\ ev.glen = -1 /\ UNCHANGED grel
                               /\ \E ex \in {GV!GExpand(rest, [cv |-> ev.item.r, lo |-> mid, hi |-> node.hi],
                                                       [cv |-> ev.item.l, lo |-> node.lo, hi |-> mid],
                                                       mid < last, first < mid)} :
                                  IF ex.ok
                                  THEN /\ ev.err = "none" /\ ev.consumed = U!Val(pl.take)
                                       /\ gst' = ex.st /\ gfail' = gfail /\ gerrk' = gerrk
                                  ELSE /\ ev.err = "stack" /\ ev.consumed = -1
                                       /\ gfail' = "stack" /\ gerrk' = "stack" /\ gst' = ex.st
                          ELSE /\ ev.err = "parent" /\ ev.consumed = -1 /\ ev.off = -1 /\ ev.glen = -1
                               /\ gfail' = "parent" /\ gerrk' = "parent" /\ UNCHANGED <<gst, grel>>
                  /\ GObsAfter(ev)
          ELSE FALSE

(* a call of feed on both verifiers *)
FeedEv ==
    /\ i >= 1 /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
       IN /\ ev.t = "gvfeed"
          /\ RPart(ev)
          /\ GPart(ev)
          /\ ev.gcmp = ev.cmp /\ ev.grd = ev.rd
          /\ i' = i + 1

(* the RangeVerifier alone, fed the genuine group a skip passed over *)
RFeedEv ==
    /\ i >= 1 /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
       IN /\ ev.t = "gvrfeed"
          /\ RPart(ev)
          /\ UNCHANGED gcore
          /\ i' = i + 1

(* skip_group: refused unless not failed, at the start of an item and the next item is a group; accepted, it passes
   the group (offset and length of next_item) and pops it, as the RangeVerifier did when fed the group *)
SkipEv ==
    /\ i >= 1 /\ i <= Len(Trace)
    /\ Trace[i].t = "gvskip"
    /\ \E gw \in {GW(gst, gfail, pairN, groupN)} : \E it \in {GV!GNextItem(Lay, gw)} :
       LET ev == Trace[i]
           accept == gfail = "none" /\ GV!GBoundary(gw) /\ Len(it) = 3
       IN /\ ev.t = "gvskip"
          /\ ev.item0 = it /\ ev.bound0 = GV!GBoundary(gw) /\ ev.nl0 = GV!GNextLen(Lay, gw)
          /\ ev.cmp0 = (gfail = "none" /\ gst = <<>>) /\ ev.fail0 = gfail
          /\ ev.ok = accept
          /\ IF accept
             THEN /\ ev.off = it[2] /\ ev.glen = it[3]
                  /\ gst' = Tail(gst) /\ grel' = Append(grel, <<Head(gst).lo, 0>>)
                  /\ UNCHANGED <<gfail, pairN, groupN, gerrk>>
                  \* the RangeVerifier was fed that group by the gvrfeed just before
                  /\ Tail(gst) = stack /\ (gfail = "none") = ~failed
                  /\ [k \in 1..Len(grel') |-> grel'[k][1]] = [k \in 1..Len(released) |-> released[k][1]]
             ELSE UNCHANGED gcore
          /\ \E gw1 \in {GW(gst', gfail', pairN', groupN')} :
                /\ ev.nl1 = GV!GNextLen(Lay, gw1) /\ ev.bound1 = GV!GBoundary(gw1) /\ ev.item1 = GV!GNextItem(Lay, gw1)
                /\ ev.cmp1 = (gfail' = "none" /\ gst' = <<>>) /\ ev.fail1 = gfail'
          /\ UNCHANGED <<core, len, G, filled, oracle, errk, pos>>
          /\ i' = i + 1

\* a run ends where the next one begins, or at the end of the trace
RunEnd == i >= 1 /\ (i > Len(Trace) \/ (i <= Len(Trace) /\ Trace[i].t = "gvrun")) /\ UNCHANGED vars

TNext == Begin \/ FeedEv \/ RFeedEv \/ SkipEv \/ RunEnd

TraceSpec == Init /\ [][TNext]_vars

(* the safety facts of the model hold on every recorded state, and the two verifiers are in related states: the same
   stack, the same groups passed (a skipped group is logged by GroupVerifier, released by the RangeVerifier it was fed
   to), the same bytes buffered, the same failure. The state after a skip is compared at the next gvrfeed/gvskip pair:
   the gvrfeed comes first, so the RangeVerifier is already there. *)
Inv ==
    /\ RV!Ascending /\ RV!InRange /\ RV!Bookkeeping
    /\ Len(stack) <= 55
    /\ filled < 1 \/ (stack # <<>> /\ filled < NodeNeed(Head(stack)))
    /\ pairN < 64 /\ (groupN > 0 => (gst # <<>> /\ groupN < NodeNeed(Head(gst))))
    /\ Len(gst) <= 55

(* after a call of feed on both verifiers, they agree *)
Related ==
    (i > 1 /\ i <= Len(Trace) + 1 /\ Trace[i - 1].t = "gvfeed") =>
         /\ gst = stack
         /\ [k \in 1..Len(grel) |-> grel[k][1]] = [k \in 1..Len(released) |-> released[k][1]]
         /\ pairN + groupN = filled
         /\ (gfail # "none") = failed
\* the end check (TraceEnd.tla): the trace has a line, its first line starts a run, and every run was taken to its
\* end (the next "gvrun" line or the end of the trace), each end reached marked by its position
RunEnds == {k \in 2..Len(Trace) : Trace[k].t = "gvrun"} \cup {Len(Trace) + 1}
ReplayAtEnd == ReplayMark(i >= 1 /\ (i > Len(Trace) \/ Trace[i].t = "gvrun"), i)
ReplayEnded == ReplayReadAll(Len(Trace), RunEnds) /\ Trace[1].t = "gvrun"
=============================================================================
