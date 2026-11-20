------------------------------- MODULE LimitsFit -------------------------------
(***************************************************************************)
(* What Limits::check and fits decide (LimitsFitOps.tla), over a grid of   *)
(* limit sets: the session count on and between the rungs of the ladder  *)
(* (1, 3, 64, 65, 1024, 65,536), the pool at its floor, default and        *)
(* ceiling (8, 1024, 65,535 chunks), the topics (1, 128, 4096) and their   *)
(* log (1 B, 4 MiB, 1 GiB); every other limit at its default. SLOT_BYTES   *)
(* is not known to the model (it is size_of of the real types): it ranges  *)
(* over SLOTS, from nothing to 1 GiB, far above the about 2.7 MiB the      *)
(* module doc states; the real value is the trace's (TraceLimitsFit).      *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - Monotone: lowering any of the four sizing limits keeps a set that    *)
(*    fits fitting, for 4- and 8-byte pointers; so the Rust test of the    *)
(*    largest set (every limit at its ceiling) speaks for every set in     *)
(*    range;                                                               *)
(*  - WideAll: with 8-byte pointers every set of the grid fits (no host of *)
(*    today sees the new error).                                           *)
(* Witness LimitsFit_wrap (WRAP TRUE: the sum computed in 32-bit wrapping *)
(* arithmetic, as a usize on a 4-byte target would): a set whose most      *)
(* does not fit wraps to a small number and is let through; Sound fails.   *)
(* This is why the code computes in checked 128-bit arithmetic.            *)
(* State space: one state; the grid is 162 sets, about 650 fits values.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, LimitsFitOps

CONSTANTS SLOTS, WRAP
CHUNK == 16384

Base == [conn |-> 1024, pool |-> 1024, sw |-> 1310720, snd |-> 16777216, streams |-> 100, ast |-> 100, as |-> 1024,
         tmsg |-> 65536, tlog |-> 4194304, topics |-> 128, spill |-> 128]
Grid == {[Base EXCEPT !.conn = c, !.pool = p, !.topics = t, !.tlog = g] :
            c \in {1, 3, 64, 65, 1024, 65536}, p \in {8, 1024, 65535}, t \in {1, 128, 4096},
            g \in {1, 4194304, 1073741824}}

\* componentwise at most, on the four sizing limits
LeL(a, b) == a.conn <= b.conn /\ a.pool <= b.pool /\ a.topics <= b.topics /\ a.tlog <= b.tlog

FT == [x \in Grid \X {4, 8} \X SLOTS |-> Fits(x[1], x[2], x[3], CHUNK)]

\* the low 32 bits
W32(a) == LET p == a \o <<0, 0, 0>> IN Norm(<<p[1], p[2], p[3] % 4>>)
WorstWrap(l, slot) ==
    W32(Add(W32(Add(W32(Mul(N(Rung(l.conn)), W32(Add(W32(Mul(N(l.pool), N(CHUNK))), N(slot))))),
                    W32(Mul(N(l.topics), N(l.tlog))))),
            W32(Mul(N(l.spill), N(SpillSlot)))))
FitsImpl(l, pb, slot) == IF WRAP THEN Le(WorstWrap(l, slot), Bound(pb)) ELSE FT[<<l, pb, slot>>]

Monotone == \A pb \in {4, 8}, s \in SLOTS, a, b \in Grid : LeL(a, b) /\ FT[<<b, pb, s>>] => FT[<<a, pb, s>>]
WideAll == \A l \in Grid, s \in SLOTS : FT[<<l, 8, s>>]
Sound == \A l \in Grid, s \in SLOTS : FitsImpl(l, 4, s) => Le(Worst(l, s, CHUNK).v, Bound(4))

VARIABLE x
Init == x = 0
Next == UNCHANGED x
=============================================================================
