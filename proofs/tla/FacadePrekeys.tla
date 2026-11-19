---------------------------- MODULE FacadePrekeys ----------------------------
(***************************************************************************)
(* The engine's prekeys of the facade, crates/pinc/src/keys.rs `Prekeys`   *)
(* (`new`, `rotate`, `due`, `decapsulate`), and the engine's trigger,      *)
(* crates/pinc/src/engine.rs `Core::service`: when `prekeys.due(now)` and  *)
(* the identity is not borrowed, the identity's store is offered fresh     *)
(* entropy (`refresh_with`, KeystoreRefresh.tla) and the prekey rotates,   *)
(* its two seeds drawn from that store.                                    *)
(*                                                                         *)
(* The rule is the one of PrekeyRotation.tla, shared with the security     *)
(* crate's store: SatAdd, DueByDeadline, Push (keep 2), Dropped, Holds,    *)
(* Newest, Increasing, Elems. The state pk follows the struct field by     *)
(* field: held is the sequence of generations held, oldest first (each     *)
(* with its key in the store; a generation that leaves held is removed     *)
(* from the store, which zeroizes it); next the next generation; at        *)
(* rotate_at; used the handshakes the newest has served.                   *)
(*  - rotate(now, random): both draws first; a refusal of either returns   *)
(*    before any assignment (Rotate(t, FALSE) keeps everything); then the  *)
(*    new generation is pushed, all but the previous one dropped,          *)
(*    rotate_at = now.saturating_add(PREKEY_LIFE), used = 0. `next += 1`  *)
(*    is a plain u64 add: GMAX keeps it far below the maximum (it needs    *)
(*    2^64 rotations), stated, not modelled.                               *)
(*  - due(now) = now >= rotate_at || used >= PREKEY_USES.                  *)
(*  - decapsulate(h): a request naming next - 1 (saturating) counts one    *)
(*    use (u32, saturating at UTOP), answered or not; it is answered only  *)
(*    for a generation held (and a well-formed ciphertext, the parameter   *)
(*    valid).                                                              *)
(* TOP is the clock's maximum (u64::MAX in the code), so rotate_at         *)
(* saturates there; TS holds 0, TOP and times between, and any order of    *)
(* them is a call sequence, so the clock steps back as well.               *)
(*                                                                         *)
(* Checked (the module doc, the field docs and the unit tests of keys.rs): *)
(*   AtMostTwo       at most two prekeys are held                          *)
(*   Increasing      held generations strictly increase, the newest is     *)
(*                   next - 1                                              *)
(*   DroppedGone     a rotated-out generation is never held again and its  *)
(*                   requests are not answered                             *)
(*   FreshForLife    after a rotation at t and before PREKEY_USES uses,    *)
(*                   due is false at every time in [t, t + LIFE)           *)
(*   GensGrow        (action) next never goes down                         *)
(*   OnlyNewest      (action) only a request naming the newest counts a   *)
(*                   use; only a rotation resets the count                 *)
(*   FailKeeps       (action) a refused draw changes nothing               *)
(*   KeepsPrevious   (action) a rotation keeps the newest it replaces     *)
(*   ServiceRule     (action) the engine rotates exactly when due and not  *)
(*                   borrowed                                              *)
(* Witnesses: FacadePrekeys_drop.cfg (a generation is rotated out:         *)
(* NothingDropped fails) and FacadePrekeys_top.cfg (a prekey made with the *)
(* clock at its maximum is due at once: NotDueAtBirth fails; the engine's  *)
(* clock reaches u64::MAX only after about 584 years).                     *)
(* TraceFacadePrekeys.tla checks the recorded calls of the real code.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS LIFE, USES, TOP, TS, UTOP, GMAX
VARIABLES pk, dropped, born
vars == <<pk, dropped, born>>

R == INSTANCE PrekeyRotation

New == [held |-> <<>>, next |-> 1, at |-> 0, used |-> 0]

Due(s, t) == R!DueByDeadline(s.at, s.used, t, USES)
\* the state after a rotation at t whose two draws succeeded
Rotated(s, t) == [held |-> R!Push(s.held, s.next, 2), next |-> s.next + 1, at |-> R!SatAdd(t, LIFE, TOP), used |-> 0]
\* the state after a request naming generation h, and whether it is answered
Counted(s, h) == IF h = R!SatSub(s.next, 1) THEN [s EXCEPT !.used = R!SatAdd(@, 1, UTOP)] ELSE s
Answered(s, h, valid) == valid /\ R!Holds(s.held, h)

Init == pk = New /\ dropped = {} /\ born = -1

Rotate(t, ok) ==
    IF ok THEN /\ pk' = Rotated(pk, t)
               /\ dropped' = dropped \cup R!Elems(R!Dropped(pk.held, pk.next, 2))
               /\ born' = t
          ELSE UNCHANGED vars

Decap(h) == pk' = Counted(pk, h) /\ UNCHANGED <<dropped, born>>

\* Core::service at t; b: the identity is borrowed; ok: the draws from the identity's store succeed
Service(t, b, ok) == IF Due(pk, t) /\ ~b THEN Rotate(t, ok) ELSE UNCHANGED vars

Gens == 0..(GMAX + 1)
Next == \/ \E t \in TS, ok \in BOOLEAN : Rotate(t, ok)
        \/ \E h \in Gens : Decap(h)
        \/ \E t \in TS, b \in BOOLEAN, ok \in BOOLEAN : Service(t, b, ok)
Spec == Init /\ [][Next]_vars

Bound == pk.next <= GMAX

TypeOK == /\ pk.held \in Seq(1..GMAX)
          /\ pk.next \in 1..(GMAX + 1)
          /\ pk.at \in 0..TOP
          /\ pk.used \in 0..UTOP
          /\ dropped \subseteq 1..GMAX
AtMostTwo == Len(pk.held) <= 2
Increasing == R!Increasing(pk.held) /\ (pk.held # <<>> => R!Newest(pk.held) = pk.next - 1)
DroppedGone == \A g \in dropped : ~R!Holds(pk.held, g) /\ ~Answered(pk, g, TRUE)
FreshForLife ==
    (born # -1 /\ pk.used < USES) => \A u \in TS : (born <= u /\ u < R!SatAdd(born, LIFE, TOP)) => ~Due(pk, u)

GensGrow == [][pk'.next >= pk.next]_vars
OnlyNewest ==
    [][/\ \A h \in Gens : Decap(h) => (pk'.used # pk.used => h = pk.next - 1)
       /\ pk'.used < pk.used => pk'.next = pk.next + 1]_vars
FailKeeps == [][\A t \in TS : Rotate(t, FALSE) => UNCHANGED vars]_vars
KeepsPrevious == [][\A t \in TS : (Rotate(t, TRUE) /\ pk.held # <<>>) => R!Holds(pk'.held, R!Newest(pk.held))]_vars
ServiceRule ==
    [][\A t \in TS, b \in BOOLEAN : Service(t, b, TRUE) => (pk'.next # pk.next <=> Due(pk, t) /\ ~b)]_vars

\* witnesses
NothingDropped == dropped = {}
NotDueAtBirth == (born # -1 /\ pk.used < USES) => ~Due(pk, born)
=============================================================================
