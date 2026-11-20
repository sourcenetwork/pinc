---------------------------- MODULE MbtSoftPrekeys ----------------------------
(***************************************************************************)
(* Model-based tests of the software prekey store (pinc-security keys.rs   *)
(* SoftPrekeys): the state graph of SoftAcquire of PrekeyRotation.tla (the *)
(* rule SoftPrekeys.tla checks) for tests/mbt_soft_prekeys.rs to walk.     *)
(*                                                                         *)
(* One action per call of the code, with its result as a parameter (as in *)
(* MbtHalfOpen.tla, so the graph has one node per state):                  *)
(*   CallAcquire(t, h)  acquire at time t; h is the handle of the prekey   *)
(*                      it returns;                                        *)
(*   CallDecap(h, ok)   decapsulate with KeyHandle(h); ok whether it       *)
(*                      answers (TRUE) or refuses with InvalidSecretKey.   *)
(* The state st is the held generation (a sequence of one), the creation   *)
(* time of the current prekey and its use count: handle() is the held      *)
(* generation and uses() the count, which the test reads after every call. *)
(* The creation time is not visible; the test sees it through the calls    *)
(* that rotate or not.                                                     *)
(* Model time t is real time origin + t in nanoseconds, and the policy is  *)
(* PrekeyPolicy { lifetime_ns: LIFE, max_uses: USES }: the code's numbers, *)
(* not scaled. The store is made by new at the origin. GENS is larger than *)
(* any generation of the graph (no wrap; SoftPrekeys_wrap.cfg covers it).  *)
(* A refusal of the generator cannot be produced (the real Drbg does not   *)
(* refuse 32 bytes), so it has no action. Two configs:                     *)
(*  - MbtSoftPrekeys.cfg: lifetime 2, 2 uses, times 0 to 3, generations    *)
(*    up to 3 inside the bound;                                            *)
(*  - MbtSoftPrekeys_zero.cfg: lifetime 0 and 0 uses (every acquire        *)
(*    rotates), times 0 to 2.                                              *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS LIFE, USES, TS, GENS, GMAX
VARIABLE st

R == INSTANCE PrekeyRotation

Init == st = [held |-> <<0>>, created |-> 0, uses |-> 0]

CallAcquire(t, h) ==
    LET n == R!SoftAcquire(st, t, LIFE, USES, GENS)
    IN /\ h = R!Newest(n.held)
       /\ st' = n
CallDecap(h, ok) ==
    /\ ok = R!Holds(st.held, h)
    /\ UNCHANGED st

Next == \/ \E t \in TS, h \in 0..(GMAX + 1) : CallAcquire(t, h)
        \/ \E h \in 0..(GMAX + 1), ok \in BOOLEAN : CallDecap(h, ok)
Spec == Init /\ [][Next]_st

Bound == R!Newest(st.held) <= GMAX
\* every call of a state inside the bound has its result in the set Next ranges over; a leaf past the bound (TLC checks
\* the invariant on it before the constraint drops it) has no edge out, so nothing is promised of its calls
Complete == Bound => /\ Len(st.held) = 1
                     /\ \A t \in TS : R!Newest(R!SoftAcquire(st, t, LIFE, USES, GENS).held) \in 0..(GMAX + 1)
=============================================================================
