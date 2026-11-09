---------------------------- MODULE ValuesVerifyOps ----------------------------
(***************************************************************************)
(* The part of vinc-values GroupVerifier (verify.rs) that depends only on  *)
(* the lengths, on the machine integers of U64.tla, shared by the model    *)
(* check (ValuesVerify.tla) and the trace check (TraceValuesVerify.tla):  *)
(*                                                                         *)
(*  GPlan      `feed` up to the hash call: the sticky failure, the empty    *)
(*             input, TooMuchData on a complete stream, then `feed_pair`   *)
(*             (take = min(input, 64 - pair_n), the whole pair read from   *)
(*             the input when pair_n = 0 and take = 64, else copied into   *)
(*             the pair buffer, OutputTooSmall past 64) or `feed_group`    *)
(*             (take = try_from(size - group_n) or the input, min with the *)
(*             input; group_n + take; the item is complete when group_n    *)
(*             reaches the size), as: which kind of call, the bytes        *)
(*             taken, the new pair_n and group_n                           *)
(*  GNextLen   `next_len`: 64 - pair_n or size - group_n; -1 for None      *)
(*  GNextItem  `next_item`                                                 *)
(*  GBoundary  `at_boundary`                                               *)
(*  GExpand    the end of `complete_pair`: the stack after the pops and    *)
(*             the two pushes (right first, then left), each failing with  *)
(*             StackOverflow at the 64-node cap                            *)
(*                                                                         *)
(* A state is a record with fields failed (a string, "none" or the error), *)
(* stack (a sequence of nodes [lo, hi, ...] with 80-bit words in lo and    *)
(* hi), pairN and groupN (80-bit words).                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64
L == INSTANCE Layout WITH SmallLen <- 0, PreN <- 0, c <- 0

StackCap == 64

(* feed_group: the bytes taken and the group length reached *)
GroupCall(lay, g, node, ilen) ==
    LET size == L!GroupSizeG(lay.len, lay.g, node.lo)
        left == U!Sub64(size, g.groupN)
        t == U!TryFrom(left, lay.bits)
        take == IF t.ok THEN U!Min(t.v, ilen) ELSE ilen
        gn == U!Add64(g.groupN, take)
    IN IF U!Lt(gn, size)
       THEN [kind |-> "partial", take |-> take, pairN |-> g.pairN, groupN |-> gn]
       ELSE [kind |-> "item", leaf |-> TRUE, take |-> take, size |-> size, pairN |-> g.pairN, groupN |-> U!Zero]

(* feed_pair *)
PairCall(lay, g, node, ilen) ==
    LET need == U!Sub64(lay.p, g.pairN)
        take == U!Min(ilen, need)
    IN IF g.pairN = U!Zero /\ take = lay.p
       THEN [kind |-> "item", leaf |-> FALSE, take |-> take, whole |-> TRUE, pairN |-> U!Zero, groupN |-> g.groupN]
       ELSE LET e == U!Add2(g.pairN, take, lay.bits)
            IN IF U!Lt(lay.p, e) THEN [kind |-> "outputtoosmall"]
               ELSE IF U!Lt(e, lay.p)
                    THEN [kind |-> "partial", take |-> take, pairN |-> e, groupN |-> g.groupN]
                    ELSE [kind |-> "item", leaf |-> FALSE, take |-> take, whole |-> FALSE, pairN |-> U!Zero,
                          groupN |-> g.groupN]

GPlan(lay, g, ilen) ==
    IF g.failed # "none" THEN [kind |-> "sticky"]
    ELSE IF ilen = U!Zero THEN [kind |-> "empty"]
    ELSE IF g.stack = <<>> THEN [kind |-> "toomuch"]
    ELSE LET node == Head(g.stack)
         IN IF U!Sub64(node.hi, node.lo) = U!One THEN GroupCall(lay, g, node, ilen) ELSE PairCall(lay, g, node, ilen)

(* next_item *)
GNextItem(lay, g) ==
    IF g.failed # "none" \/ g.stack = <<>> THEN <<>>
    ELSE LET node == Head(g.stack)
         IN IF U!Sub64(node.hi, node.lo) = U!One
            THEN <<"g", U!Val(U!Mul64(node.lo, lay.g)), U!Val(L!GroupSizeG(lay.len, lay.g, node.lo))>>
            ELSE <<"p">>

(* next_len: -1 for None *)
GNextLen(lay, g) ==
    IF g.failed # "none" \/ g.stack = <<>> THEN -1
    ELSE LET node == Head(g.stack)
         IN IF U!Sub64(node.hi, node.lo) = U!One
            THEN U!Val(U!Sub64(L!GroupSizeG(lay.len, lay.g, node.lo), g.groupN))
            ELSE U!Val(U!Sub64(lay.p, g.pairN))

GBoundary(g) == g.pairN = U!Zero /\ g.groupN = U!Zero

(* one push: [ok, st] *)
GPush(st, nd) == IF Len(st) < StackCap THEN [ok |-> TRUE, st |-> <<nd>> \o st] ELSE [ok |-> FALSE, st |-> st]

(* the stack after complete_pair expands a parent: `rest` is the stack below the parent, right and left the two child
   nodes, pushR and pushL whether the range reaches them (mid < last, first < mid); [ok] is FALSE on StackOverflow *)
GExpand(rest, right, left, pushR, pushL) ==
    LET r1 == IF pushR THEN GPush(rest, right) ELSE [ok |-> TRUE, st |-> rest]
        l1 == IF r1.ok /\ pushL THEN GPush(r1.st, left) ELSE r1
    IN l1
=============================================================================
