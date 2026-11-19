----------------------------- MODULE SoftPrekeys -----------------------------
(***************************************************************************)
(* The software prekey store of pinc-security keys.rs, SoftPrekeys: new,   *)
(* acquire (the rotation), decapsulate (refused for any handle but the     *)
(* current one), handle and uses, with the rule of PrekeyRotation.tla      *)
(* (SoftAcquire). PrekeyPolicy is (LIFE, USES): lifetime_ns and max_uses.  *)
(* The store is made by new at time 0 with generation 0; every acquire is  *)
(* at a time of TS, which may be earlier than the creation of the current  *)
(* prekey (a clock that stepped back: the age saturates at 0).             *)
(*                                                                         *)
(* Checked in every state (the doc of the module and of the type):         *)
(*  - HeldOne: one prekey is held (the store keeps no other key);          *)
(*  - ServesAtMost: the current prekey has served at most max_uses         *)
(*    handshakes (one when max_uses is 0: it rotates on every acquire), so *)
(*    the u32 count never reaches its saturation;                          *)
(*  - FreshEnough: the prekey the last acquire returned was younger than   *)
(*    the lifetime at that time, or made by that acquire;                  *)
(*  - RotatedOutRefused: no handle of a rotated-out prekey names the       *)
(*    current one, so its decapsulation is refused ("a request for a       *)
(*    rotated-out key is refused rather than answered with an unrelated    *)
(*    secret");                                                            *)
(* and in every step GenerationsIncrease: the handle never goes down.      *)
(* The handle is a u64 that the code increments with wrapping_add; GENS is *)
(* the number of handles (2^64 in the code). SoftPrekeys_wrap.cfg takes    *)
(* GENS = 2 and TLC finds RotatedOutRefused violated: after 2^64 rotations *)
(* the handle of generation 0 names the current key again. The code starts *)
(* every store at 0 and rotates at most once per handshake, so this needs  *)
(* 2^64 handshakes on one store; it is stated, not reachable.              *)
(* A refusal of the generator during a rotation changes nothing (acquire   *)
(* returns before any assignment): a stuttering step, not modelled; the    *)
(* real Drbg cannot refuse 32 bytes (MAX_FILL is 2^30).                    *)
(* SoftPrekeys_rot.cfg is a reachability witness: a rotation happens.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS LIFE, USES, TS, GENS, GMAX
VARIABLES st, out, lastT
vars == <<st, out, lastT>>

R == INSTANCE PrekeyRotation

Init == /\ st = [held |-> <<0>>, created |-> 0, uses |-> 0]
        /\ out = {}
        /\ lastT = -1

\* acquire at time t; out collects the handles of the dropped prekeys, lastT the time of the last acquire
Acquire(t) ==
    LET n == R!SoftAcquire(st, t, LIFE, USES, GENS)
    IN /\ st' = n
       /\ out' = out \cup (R!Elems(st.held) \ R!Elems(n.held))
       /\ lastT' = t

Next == \E t \in TS : Acquire(t)
Spec == Init /\ [][Next]_vars

Bound == R!Newest(st.held) <= GMAX

TypeOK == /\ st.held \in Seq(0..(GENS - 1))
          /\ st.created \in TS \cup {0}
          /\ st.uses \in Nat
          /\ out \subseteq 0..(GENS - 1)
HeldOne == Len(st.held) = 1
ServesAtMost == st.uses <= IF USES = 0 THEN 1 ELSE USES
FreshEnough == lastT # -1 => (R!SatSub(lastT, st.created) < LIFE \/ st.created = lastT)
RotatedOutRefused == \A h \in out : ~R!Holds(st.held, h)
GenerationsIncrease == [][R!Newest(st'.held) >= R!Newest(st.held)]_vars

\* a reachability witness: the store rotates
NeverRotated == R!Newest(st.held) = 0
=============================================================================
