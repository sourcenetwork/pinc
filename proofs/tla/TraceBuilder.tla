------------------------------ MODULE TraceBuilder ------------------------------
(***************************************************************************)
(* Trace validation of vinc-dag OutboardBuilder (tree/builder.rs).         *)
(*                                                                         *)
(* The Rust test tests/trace_builder.rs runs the real builder on random    *)
(* values, group sizes and splits of the value into pieces. A run starts   *)
(* with the genuine tree of the value (computed from the definition with   *)
(* the BLAKE3 library): the hash call of every group (root flag, index,    *)
(* bytes) and of every parent (root flag, left, right), with its chaining  *)
(* value as an id. Each call of update and finish is then one event: the   *)
(* offset and length of the piece, the length of the outboard buffer, the  *)
(* result and the slots of the outboard that changed, with the ids of the  *)
(* pair written in each.                                                   *)
(*                                                                         *)
(* This module is the builder as a state machine, at the byte level: the   *)
(* counters in_group and consumed, the offset the hasher is set to, the    *)
(* stack of (chaining value, size in groups), the root cell and the log of *)
(* writes. update takes min(room, bytes left) bytes per iteration and      *)
(* completes a group when it is full or the value ends; a completed group  *)
(* is hashed (the recorded table gives the value of the model's call) and  *)
(* merged with the stack top while the two top sizes are equal; finish     *)
(* merges what is left from the right. The slot of a parent is its         *)
(* pre-order position, counted here from the definition of the tree, and   *)
(* the recorded slots must be exactly the slots the model writes, with     *)
(* the model's pairs. The errors are the code's: the buffer size is        *)
(* checked first, then the length of the piece against the bytes still     *)
(* due (nothing is consumed), and finish needs every byte.                 *)
(*                                                                         *)
(* A hash call that is not in the recorded table has no value, so TLC      *)
(* cannot take the step: the trace is then not a behaviour of the model.   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds builder.ndjson.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES P, bst, pos, i
vars == <<P, bst, pos, i>>

(* only Left (the split of a node) is used from the verifier specification; its state variables are unused *)
RV == INSTANCE RangeVerifier WITH MaxGroups <- 8, n <- 0, first <- 0, last <- 0, stack <- <<>>, failed <- FALSE,
                                  released <- <<>>

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/builder.ndjson")

Min(a, b) == IF a < b THEN a ELSE b
CeilDiv(a, g) == (a + g - 1) \div g

(* the pre-order position of the parent [lo, hi) among the parents of the tree [a, b), counted from the
   definition: the node itself first, then every parent of the left subtree, then those of the right one *)
Parents(a, b) == IF b - a >= 2 THEN b - a - 1 ELSE 0
RECURSIVE Pos(_, _, _, _)
Pos(a, b, lo, hi) ==
    IF a = lo /\ b = hi THEN 0
    ELSE LET m == a + RV!Left(b - a)
         IN IF hi <= m THEN 1 + Pos(a, m, lo, hi) ELSE 1 + Parents(a, m) + Pos(m, b, lo, hi)

(* the bytes of the outboard: one 64-byte pair per parent *)
OutSize == 64 * Parents(0, P.n)

SeqToSet(s) == {s[k] : k \in 1..Len(s)}

(* the chaining value the genuine tree records for a hash call; a call that is not recorded has none *)
Tab(rows, a, b, c) == (CHOOSE r \in rows : r[1] = a /\ r[2] = b /\ r[3] = c)[4]

(* complete_group, after in_group and consumed advanced: hash the group, then merge while the two top sizes
   are equal; the merge writes the pair at the parent's slot *)
RECURSIVE Merge(_, _)
Merge(st, k) ==
    IF Len(st.stack) >= 2 /\ st.stack[1][2] = st.stack[2][2]
    THEN LET rs == st.stack[1][2]
             r == st.stack[1][1]
             l == st.stack[2][1]
             lo == k - 2 * rs
             root == (lo = 0 /\ k = P.n)
             cv == Tab(P.par, root, l, r)
         IN Merge([st EXCEPT !.stack = <<<<cv, 2 * rs>>>> \o SubSeq(st.stack, 3, Len(st.stack)),
                             !.wr = Append(st.wr, <<Pos(0, P.n, lo, k), l, r>>),
                             !.root = IF root THEN cv ELSE st.root], k)
    ELSE st

CompleteGroup(st) ==
    LET k == CeilDiv(st.con, P.G)
        idx == st.off \div P.G
        root == (k - 1 = 0 /\ k = P.n)
        leaf == Tab(P.leaf, root, idx, st.ing)
        st0 == [st EXCEPT !.ing = 0]
    IN IF P.n = 1
       THEN [st0 EXCEPT !.root = leaf]
       ELSE Merge([st0 EXCEPT !.stack = <<<<leaf, 1>>>> \o st0.stack], k)

(* the loop of update over k more bytes *)
RECURSIVE UpdLoop(_, _)
UpdLoop(st, k) ==
    IF k = 0 THEN st
    ELSE LET st0 == IF st.ing = 0 THEN [st EXCEPT !.off = (st.con \div P.G) * P.G] ELSE st
             t == Min(P.G - st0.ing, k)
             st1 == [st0 EXCEPT !.ing = st0.ing + t, !.con = st0.con + t]
         IN IF st1.ing = P.G \/ st1.con = P.len
            THEN UpdLoop(CompleteGroup(st1), k - t)
            ELSE UpdLoop(st1, k - t)

(* the loop of finish: merge the two top entries into the node that ends at the last group *)
RECURSIVE FinLoop(_)
FinLoop(st) ==
    IF Len(st.stack) >= 2
    THEN LET r == st.stack[1][1]
             rs == st.stack[1][2]
             l == st.stack[2][1]
             ls == st.stack[2][2]
             lo == P.n - (ls + rs)
             root == (lo = 0)
             cv == Tab(P.par, root, l, r)
         IN FinLoop([st EXCEPT !.stack = <<<<cv, ls + rs>>>> \o SubSeq(st.stack, 3, Len(st.stack)),
                               !.wr = Append(st.wr, <<Pos(0, P.n, lo, P.n), l, r>>),
                               !.root = IF root THEN cv ELSE st.root])
    ELSE st

NewWrites(old, new) == SubSeq(new.wr, Len(old.wr) + 1, Len(new.wr))

(* the recorded slots are exactly the writes of the call *)
SlotsMatch(old, new, slots) ==
    /\ Len(NewWrites(old, new)) = Len(slots)
    /\ SeqToSet(NewWrites(old, new)) = SeqToSet(slots)

Init ==
    /\ i = 1
    /\ P = [len |-> 0, G |-> 1024, n |-> 0, e0 |-> 0, leaf |-> {}, par |-> {}]
    /\ bst = [ing |-> 0, con |-> 0, off |-> 0, stack |-> <<>>, wr |-> <<>>, root |-> 0]
    /\ pos = 0

(* a new run: the layout, the genuine tree and an empty builder; the root cell holds the hash of the empty
   input when the value is empty *)
Begin ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
           g == 1024 * 2 ^ ev.log
           cnt == (ev.len + g - 1) \div g
           lrows == SeqToSet(ev.leaves)
           prows == SeqToSet(ev.parents)
       IN /\ ev.t = "bnew"
          /\ ev.n = cnt
          \* the recorded hash values form a function of the call
          /\ \A a, b \in lrows : (a[1] = b[1] /\ a[2] = b[2] /\ a[3] = b[3]) => a[4] = b[4]
          /\ \A a, b \in prows : (a[1] = b[1] /\ a[2] = b[2] /\ a[3] = b[3]) => a[4] = b[4]
          /\ P' = [len |-> ev.len, G |-> g, n |-> cnt, e0 |-> ev.e0, leaf |-> lrows, par |-> prows]
          /\ bst' = [ing |-> 0, con |-> 0, off |-> 0, stack |-> <<>>, wr |-> <<>>,
                     root |-> IF ev.len = 0 THEN ev.e0 ELSE 0]
          /\ pos' = 0
          /\ i' = i + 1

(* one call of update *)
UpdEv ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
       IN /\ ev.t = "bupd"
          /\ ev.pos = pos
          /\ i' = i + 1
          /\ UNCHANGED P
          /\ IF ev.olen # OutSize
             THEN \* the buffer size is checked first; nothing happens
                  /\ ev.res = "outsize" /\ ev.slots = <<>>
                  /\ UNCHANGED <<bst, pos>>
             ELSE IF ev.ilen > P.len - bst.con
             THEN \* the piece runs past the declared length: nothing is consumed
                  /\ ev.res = "toomuch" /\ ev.slots = <<>>
                  /\ UNCHANGED <<bst, pos>>
             ELSE LET new == UpdLoop(bst, ev.ilen)
                  IN /\ ev.res = "ok"
                     /\ SlotsMatch(bst, new, ev.slots)
                     /\ bst' = new
                     /\ pos' = pos + ev.ilen

(* one call of finish, on a copy of the builder *)
FinEv ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
       IN /\ ev.t = "bfin"
          /\ i' = i + 1
          /\ UNCHANGED <<P, bst, pos>>
          /\ IF ev.olen # OutSize
             THEN ev.res = "outsize" /\ ev.slots = <<>>
             ELSE IF bst.con # P.len
             THEN ev.res = "incomplete" /\ ev.slots = <<>>
             ELSE LET new == FinLoop(bst)
                  IN /\ ev.res = "ok"
                     /\ ev.root = new.root
                     /\ P.len = 0 => ev.root = P.e0
                     /\ SlotsMatch(bst, new, ev.slots)

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == Begin \/ UpdEv \/ FinEv \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

(* the safety facts of the model hold on every recorded state: the stack never reaches 55 entries, no parent is
   written twice, the counters stay inside the declared length and the group *)
Inv ==
    /\ Len(bst.stack) <= 55
    /\ \A a, b \in 1..Len(bst.wr) : a # b => bst.wr[a][1] # bst.wr[b][1]
    /\ \A a \in 1..Len(bst.wr) : bst.wr[a][1] < Parents(0, P.n)
    /\ bst.con <= P.len /\ bst.ing < P.G

(* the whole recorded trace is a behaviour of the model *)
TraceAccepted == <>(i = Len(Trace) + 1)
=================================================================================
