--------------------------- MODULE PrekeyRotation ---------------------------
(***************************************************************************)
(* The prekey rotation rule, as pure operators shared by the models of the *)
(* two prekey stores of the tree:                                          *)
(*  - pinc-security keys.rs SoftPrekeys (acquire, decapsulate, handle,     *)
(*    uses): one prekey held, rotated in acquire when it has served        *)
(*    max_uses handshakes or its age (now - created_at, saturating) has    *)
(*    reached lifetime_ns; the new handle is the old one plus one          *)
(*    (wrapping_add on a u64); the rotated-out key is dropped;             *)
(*    SoftAcquire below is that step;                                      *)
(*  - pinc keys.rs Prekeys (rotate, due, decapsulate): the newest and the  *)
(*    one before held; due when now >= rotate_at (now + PREKEY_LIFE,       *)
(*    saturating) or used >= PREKEY_USES. Its model reuses SatAdd,         *)
(*    DueByDeadline, Push (keep 2), Dropped, Holds, Newest, Increasing and *)
(*    Elems.                                                               *)
(* A store's held prekeys are a sequence of generations, oldest first.     *)
(* Generations are model integers: NextGen takes the modulus (2^64 in the  *)
(* code), so a config can scale the wrap down; Top is the clock's maximum  *)
(* (u64::MAX in the code) for the saturating additions.                    *)
(***************************************************************************)
EXTENDS Integers, Sequences

SatSub(a, b) == IF a > b THEN a - b ELSE 0
SatAdd(a, b, top) == IF a + b > top THEN top ELSE a + b
NextGen(g, gens) == (g + 1) % gens

\* SoftPrekeys::acquire: uses >= max_uses || now.saturating_sub(created_at) >= lifetime_ns
DueByAge(created, uses, now, life, maxUses) == uses >= maxUses \/ SatSub(now, created) >= life
\* Prekeys::due: now >= rotate_at || used >= PREKEY_USES
DueByDeadline(rotateAt, used, now, maxUses) == now >= rotateAt \/ used >= maxUses

\* a new generation g joins the held ones and the oldest are dropped until keep are left
Push(held, g, keep) ==
    LET h == Append(held, g)
    IN IF Len(h) > keep THEN SubSeq(h, Len(h) - keep + 1, Len(h)) ELSE h
\* the generations that push drops
Dropped(held, g, keep) ==
    LET h == Append(held, g)
    IN IF Len(h) > keep THEN SubSeq(h, 1, Len(h) - keep) ELSE <<>>
Holds(held, h) == \E i \in 1..Len(held) : held[i] = h
Newest(held) == held[Len(held)]
Increasing(held) == \A i, j \in 1..Len(held) : i < j => held[i] < held[j]
Elems(s) == {s[i] : i \in 1..Len(s)}

\* SoftPrekeys::acquire at time t on the store s = [held, created, uses] (one prekey held): rotate first when due
\* (uses = 0, then the increment, so 1), else count one more use. A refusal of the generator during a rotation
\* returns before any assignment, so it changes nothing: the callers model it as a step that keeps s.
SoftAcquire(s, t, life, maxUses, gens) ==
    IF DueByAge(s.created, s.uses, t, life, maxUses)
    THEN [held |-> Push(s.held, NextGen(Newest(s.held), gens), 1), created |-> t, uses |-> 1]
    ELSE [s EXCEPT !.uses = @ + 1]
=============================================================================
