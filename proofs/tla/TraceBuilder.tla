------------------------------ MODULE TraceBuilder ------------------------------
(***************************************************************************)
(* Trace validation of pinc-dag OutboardBuilder (tree/builder.rs).         *)
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
(* The builder itself is BuilderBytes.tla, the byte-level state machine    *)
(* written on the machine integers of U64.tla (in_group and consumed, the *)
(* offset the hasher is set to, the stack of (chaining value, size in     *)
(* groups), the root cell and the log of writes); this module feeds it     *)
(* the recorded calls with the recorded hash tables as the hash (the       *)
(* model's hash call is looked up in the table of the run). The slot of a  *)
(* parent is its pre-order position, counted there from the definition of  *)
(* the tree, and the recorded slots must be exactly the slots the model    *)
(* writes, with the model's pairs. The errors are the code's: the buffer   *)
(* size is checked first, then the length of the piece against the bytes   *)
(* still due (nothing is consumed), and finish needs every byte.           *)
(*                                                                         *)
(* A hash call that is not in the recorded table has no value, so TLC      *)
(* cannot take the step: the trace is then not a behaviour of the model.   *)
(* The runs are independent, so a run is a chain of states started from a  *)
(* root state, and TLC checks the runs on all workers at once.             *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds builder.ndjson.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES i, P, bst
vars == <<i, P, bst>>

BB == INSTANCE BuilderBytes WITH lay <- 0, st <- 0
U == INSTANCE U64
L == INSTANCE Layout WITH SmallLen <- 0, PreN <- 0, c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/builder.ndjson")

(* the layout of the current run *)
Lay == BB!MkLay(U!W(P.len), U!W(P.G), 64)

SeqToSet(s) == {s[k] : k \in 1..Len(s)}

(* the writes of a call, as the recorded rows: the slot of the parent and the pair written in it *)
NewWrites(old, new) ==
    [k \in 1..(Len(new.wr) - Len(old.wr)) |->
        <<U!Val(new.wr[Len(old.wr) + k].slot), new.wr[Len(old.wr) + k].l, new.wr[Len(old.wr) + k].r>>]

(* the recorded slots are exactly the writes of the call *)
SlotsMatch(old, new, slots) ==
    /\ Len(NewWrites(old, new)) = Len(slots)
    /\ SeqToSet(NewWrites(old, new)) = SeqToSet(slots)

Init == i = 0 /\ P = [mode |-> "table", len |-> 0, G |-> 1024, n |-> 0, e0 |-> 0, leaf |-> {}, par |-> {}] /\ bst = <<>>

(* a new run: the layout, the genuine tree and an empty builder; the root cell holds the hash of the empty
   input when the value is empty *)
Begin ==
    /\ i = 0
    /\ \E k \in 1..Len(Trace) :
        /\ Trace[k].t = "bnew"
        /\ LET ev == Trace[k]
               g == 1024 * 2 ^ ev.log
               cnt == (ev.len + g - 1) \div g
               lrows == SeqToSet(ev.leaves)
               prows == SeqToSet(ev.parents)
               P2 == [mode |-> "table", len |-> ev.len, G |-> g, n |-> cnt, e0 |-> ev.e0, leaf |-> lrows, par |-> prows]
           IN /\ ev.n = cnt
              \* the recorded hash values form a function of the call
              /\ \A a, b \in lrows : (a[1] = b[1] /\ a[2] = b[2] /\ a[3] = b[3]) => a[4] = b[4]
              /\ \A a, b \in prows : (a[1] = b[1] /\ a[2] = b[2] /\ a[3] = b[3]) => a[4] = b[4]
              /\ P' = P2
              /\ bst' = BB!InitState(P2, BB!MkLay(U!W(ev.len), U!W(g), 64))
              /\ i' = k + 1

(* one call of update *)
UpdEv ==
    /\ i >= 1 /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
           r == BB!UpdateCall(P, Lay, bst, U!W(ev.ilen), U!W(ev.olen))
       IN /\ ev.t = "bupd"
          /\ ev.pos = U!Val(bst.con)
          /\ ev.res = r.res
          /\ IF r.res = "ok" THEN SlotsMatch(bst, r.st, ev.slots) ELSE ev.slots = <<>>
          /\ bst' = r.st
          /\ i' = i + 1
          /\ UNCHANGED P

(* one call of finish, on a copy of the builder *)
FinEv ==
    /\ i >= 1 /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
           f == BB!FinishCall(P, Lay, bst, U!W(ev.olen))
       IN /\ ev.t = "bfin"
          /\ ev.res = f.res
          /\ IF f.res = "ok"
             THEN /\ ev.root = f.root
                  /\ P.len = 0 => ev.root = P.e0
                  /\ SlotsMatch(bst, f, ev.slots)
             ELSE ev.slots = <<>>
          /\ i' = i + 1
          /\ UNCHANGED <<P, bst>>

\* a run ends where the next one begins, or at the end of the trace
RunEnd == i >= 1 /\ (i > Len(Trace) \/ (i <= Len(Trace) /\ Trace[i].t = "bnew")) /\ UNCHANGED vars

TNext == Begin \/ UpdEv \/ FinEv \/ RunEnd

TraceSpec == Init /\ [][TNext]_vars

(* the safety facts of the model hold on every recorded state: the stack never reaches 55 entries, no parent is
   written twice, every slot is a parent of the tree, the counters stay inside the declared length and the group *)
Inv ==
    i >= 1 =>
        /\ BB!Shape(bst, Lay)
        /\ \A a, b \in 1..Len(bst.wr) : a # b => bst.wr[a].slot # bst.wr[b].slot
        /\ \A a \in 1..Len(bst.wr) : U!Lt(bst.wr[a].slot, L!SpecParents(Lay.n))
=================================================================================
