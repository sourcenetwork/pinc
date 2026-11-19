---------------------------- MODULE MembershipConv --------------------------
(***************************************************************************)
(* Convergence of the whole view, checked exhaustively at a small size.     *)
(*                                                                         *)
(* Two nodes (a hub, so removals are not held) hold the same copies of two  *)
(* hubs' rosters; each copy lists any of the members 3 and 4 at either of   *)
(* two epochs or not at all, and each node's view starts as any subset of   *)
(* the members at either epoch. Both recompute every member in order        *)
(* (RecomputeOne of Membership.tla, the operator the trace check validates) *)
(* with no quiet window. ViewAgree: afterwards they list exactly the same   *)
(* members. ViewIsUnion: the members they list are those some hub copy      *)
(* lists.                                                                   *)
(*                                                                         *)
(* Lean counterpart: Pinc/MembershipConvAll.lean (recomputeAll_view_agree). *)
(***************************************************************************)
EXTENDS MembershipOps

Mem == <<3, 4>>
E(k) == U!W(65536 * k)
Rec(k) == [inc |-> E(k), ver |-> 1, th |-> <<0, 0, 0, 0, 0, 0, 0, 0>>]
Env0 == [ev |-> EmptyFn, car |-> EmptyFn, acc |-> {}, ver |-> 1, tk |-> 0, refl |-> TRUE, pers |-> FALSE,
         sealed |-> <<>>, failseal |-> FALSE, failunseal |-> FALSE, floor |-> [p \in 0..255 |-> <<>>], gu |-> EmptyFn, rv |-> {}]
Now == N!Sec(500)
Base == StartOp([me |-> 9, isHub |-> TRUE, hubs |-> <<1, 2>>], Env0, Now, U!W(1000000), Z).S

\* a choice per cell: 0 not listed, 1 or 2 listed at that epoch
Cells == {0, 1, 2}
Entry(c) == [rec |-> Rec(c), round |-> Z, absentSince |-> <<>>]
CopyOf(f) == [entries |-> [m \in {m \in {3, 4} : f[m] # 0} |-> Entry(f[m])], round |-> Z, open |-> FALSE]
ViewOf(f) == [m \in {m \in {3, 4} : f[m] # 0} |-> [rec |-> Rec(f[m])]]

VARIABLES c1, c2, v1, v2, done
vars == <<c1, c2, v1, v2, done>>

Mk(v, ca, cb) ==
    [Base EXCEPT !.hv = [h \in {1, 2, 9} |-> IF h = 1 THEN CopyOf(ca) ELSE IF h = 2 THEN CopyOf(cb) ELSE NewCopy],
                 !.up = [h \in {1, 2} |-> Now], !.heard = [h \in {1, 2} |-> Now],
                 !.members = ViewOf(v), !.quietUntil = Z]

Fold(S) ==
    LET RECURSIVE F(_, _)
        F(s, i) == IF i > Len(Mem) THEN s ELSE F(RecomputeOne(s, Env0, Now, Mem[i]).S, i + 1)
    IN F(S, 1)

Cells2 == [{3, 4} -> Cells]
Init == c1 \in Cells2 /\ c2 \in Cells2 /\ v1 \in Cells2 /\ v2 \in Cells2 /\ done = FALSE
\* the quick profile (proofs/tla/quick): the second view starts empty. Agreement is equality of the member sets, so
\* every first view agreeing with the empty one is every pair agreeing; ViewIsUnion still takes every first view
InitQuick == c1 \in Cells2 /\ c2 \in Cells2 /\ v1 \in Cells2 /\ v2 = [m \in {3, 4} |-> 0] /\ done = FALSE
Next == done' = TRUE /\ UNCHANGED <<c1, c2, v1, v2>>
Spec == Init /\ [][Next]_vars

N1 == Fold(Mk(v1, c1, c2))
N2 == Fold(Mk(v2, c1, c2))
ViewAgree == done => DOMAIN N1.members = DOMAIN N2.members
ViewIsUnion == done => DOMAIN N1.members = {m \in {3, 4} : c1[m] # 0 \/ c2[m] # 0}
=============================================================================
