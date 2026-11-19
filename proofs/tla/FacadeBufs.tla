----------------------------- MODULE FacadeBufs -----------------------------
(***************************************************************************)
(* The buffer pools of two endpoints of one thread, crates/pinc/src/       *)
(* drive.rs (`pools`, `pooled`, `Buf::drop`, `POOLED`), with the operators *)
(* of FacadeBufsOps.tla: every holder (a future) of either endpoint takes  *)
(* a buffer of its endpoint's length or gives back the one it holds, in    *)
(* any order. STD picks the shape: the thread's one pool (the `std`        *)
(* feature) or a pool of each endpoint's own with one buffer reserved at   *)
(* the build (without it).                                                 *)
(*                                                                         *)
(* The contract a host without `std` keeps (platform.rs, the crate docs):  *)
(* a monotonic clock; unpredictable randomness; an allocator that returns  *)
(* memory or fails cleanly; one thread driving an endpoint. The last is    *)
(* what makes each call here one step: no pool is borrowed while another   *)
(* call runs. An allocator that fails stops the program (Vec's `alloc`     *)
(* error), which is outside the model; nothing here depends on the clock   *)
(* or on randomness. With several threads driving one endpoint the code    *)
(* does not build (the pools are `Rc`), so that breach has no behaviour.   *)
(*                                                                         *)
(* Checked, from the docs of POOLED, `pools`, `pooled`, `Shared` and the   *)
(* module:                                                                 *)
(*  - PoolBound: a pool never holds more than POOLED buffers;              *)
(*  - OneHolder: a buffer is in one place at a time: one holder or one     *)
(*    slot of one pool (or freed);                                         *)
(*  - ExactLen: a buffer handed out has exactly its endpoint's length;     *)
(*  - OwnLen (without std): a pooled buffer has its endpoint's length, so  *)
(*    `pooled` never cuts or extends one;                                  *)
(*  - NoGrow (without std): a pool's Vec keeps the capacity reserved at    *)
(*    the build, so a buffer that goes back never allocates.               *)
(* Witnesses: FacadeBufs_mix (with std a pool holds buffers of both        *)
(* endpoints' lengths, so `pooled` cuts or extends: PoolOneLen fails) and  *)
(* FacadeBufs_free (without std a buffer finds its pool full and is freed: *)
(* NoneFreed fails).                                                       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS POOLED, STD, H1, H2, L1, L2, NB
ASSUME STD \in BOOLEAN /\ H1 \in Nat \ {0} /\ H2 \in Nat \ {0} /\ L1 # L2 /\ NB \in Nat
INSTANCE FacadeBufsOps

Hs == 1..(H1 + H2)
Ep(h) == IF h <= H1 THEN 1 ELSE 2
Lens == <<L1, L2>>

VARIABLE st

Init == st = Built(STD, Hs, Lens)
\* a holder takes a buffer; a new allocation is bounded by NB (the model's bound, not the code's)
TakeA == \E h \in Hs :
    /\ st.held[h] = NoBuf
    /\ Popped(STD, st, Ep(h)) \/ st.nb <= NB
    /\ st' = Take(STD, st, h, Ep(h), Lens[Ep(h)])
GiveA == \E h \in Hs : st.held[h] # NoBuf /\ st' = Give(STD, st, h, Ep(h))
Next == TakeA \/ GiveA
Spec == Init /\ [][Next]_st

Pooled(q) == {st.pools[q][k].id : k \in DOMAIN st.pools[q]}
Holders == {h \in Hs : st.held[h] # NoBuf}
HeldIds == {st.held[h].id : h \in Holders}

PoolBound == \A q \in 1..2 : Len(st.pools[q]) <= POOLED
OneHolder == /\ \A q \in 1..2 : Cardinality(Pooled(q)) = Len(st.pools[q])
             /\ Pooled(1) \cap Pooled(2) = {}
             /\ \A g, h \in Holders : g # h => st.held[g].id # st.held[h].id
             /\ HeldIds \cap (Pooled(1) \cup Pooled(2)) = {}
             /\ HeldIds \cup Pooled(1) \cup Pooled(2) \subseteq 1..(st.nb - 1)
ExactLen == \A h \in Holders : st.held[h].len = Lens[Ep(h)]
PoolOneLen == \A q \in 1..2 : \A k \in DOMAIN st.pools[q] : st.pools[q][k].len = Lens[q]
OwnLen == ~STD => PoolOneLen
NoGrow == ~STD => st.cap = <<POOLED, POOLED>>

\* witness: every buffer allocated is still held or pooled
NoneFreed == HeldIds \cup Pooled(1) \cup Pooled(2) = 1..(st.nb - 1)
=============================================================================
