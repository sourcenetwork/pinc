------------------------- MODULE MembershipHomeSnap -------------------------
(***************************************************************************)
(* The snapshot that confirms a member's home, checked over every small     *)
(* starting state. Member 9 has the copies of hubs 1 and 2 (both fresh),    *)
(* hub 1 is its primary and no home is confirmed yet; its view and the      *)
(* copies list members 3 and 4 at epoch 1 or 2 or not at all, and each      *)
(* view member may wait in the recheck table, held (no home) or deferred    *)
(* (by an open window). Hub 1's snapshot lists each at epoch 1 or 2 or      *)
(* omits it, in one frame or one frame per entry, and is optionally         *)
(* preceded by a snapshot cut short after its first frame (listing 3 at     *)
(* epoch 2) and the end of that session. ApplySnap and DropPeer are the     *)
(* operators of Membership.tla and MembershipOps.tla.                       *)
(*                                                                         *)
(* HomeRec: the view holds the home's record of every member the home      *)
(* lists (a higher record only another copy holds does not stay:            *)
(* membership_world seeds 12, 13, 14). NoGhost: every entry of the home's   *)
(* copy the snapshot did not list ages. Covers: every view member has an    *)
(* entry in the home's copy or waits in the recheck table. DeferKept: a     *)
(* member a window deferred, that the home's copy did not hold, gets no     *)
(* entry there and keeps waiting (its removal is decided at the window's   *)
(* end, not a lease later). HeldDecided: a held member no copy holds is     *)
(* removed when the home is confirmed, with no window open. KeptIfListed:   *)
(* a held member only hub 2's copy lists stays (it is aged, not removed).   *)
(* Witnesses: MembershipHomeSnap_w_recompute (OldViewRecompute) breaks     *)
(* HomeRec, _w_open (OldCloseOpen) NoGhost, _w_reage (NoViewSkip) DeferKept *)
(* and _w_skipall (AnyViewSkip) KeptIfListed.                               *)
(***************************************************************************)
EXTENDS MembershipOps

Mem == <<3, 4>>
E(k) == U!W(65536 * k)
Rec(k) == [inc |-> E(k), ver |-> 1, th |-> <<0, 0, 0, 0, 0, 0, 0, 0>>]
Env0 == [ev |-> EmptyFn, car |-> EmptyFn, acc |-> {}, ver |-> 1, tk |-> 0, refl |-> TRUE, pers |-> FALSE,
         sealed |-> <<>>, failseal |-> FALSE, failunseal |-> FALSE, floor |-> [p \in 0..255 |-> <<>>], gu |-> EmptyFn, rv |-> {}]
Now == N!Sec(500)
Base == StartOp([me |-> 9, isHub |-> FALSE, hubs |-> <<1, 2>>], Env0, Now, U!W(1000000), Z).S

\* a choice per cell: 0 not listed, 1 or 2 listed at that epoch
Cells == {0, 1, 2}
Cells2 == [{3, 4} -> Cells]
Entry(c) == [rec |-> Rec(c), round |-> Z, absentSince |-> <<>>]
CopyOf(f) == [entries |-> [m \in {m \in {3, 4} : f[m] # 0} |-> Entry(f[m])], round |-> Z, open |-> FALSE]
ViewOf(f) == [m \in {m \in {3, 4} : f[m] # 0} |-> [rec |-> Rec(f[m])]]

Waits == {"none", "held", "deferred"}
QuietEnd(r) == IF \E m \in {3, 4} : r[m] = "deferred" THEN SatAdd(Now, QUIET) ELSE Z
RecheckOf(r) == [m \in {m \in {3, 4} : r[m] # "none"} |-> [due |-> QuietEnd(r), grace |-> FALSE, held |-> r[m] = "held"]]

Mk(v, ca, cb, r) ==
    [Base EXCEPT !.hv = [h \in {1, 2} |-> IF h = 1 THEN CopyOf(ca) ELSE CopyOf(cb)],
                 !.up = [h \in {1, 2} |-> Now], !.heard = [h \in {1, 2} |-> Now],
                 !.members = ViewOf(v), !.primary = <<1>>, !.homeOk = <<>>,
                 !.recheck = RecheckOf(r), !.quietUntil = QuietEnd(r)]

Es(s) == LET RECURSIVE F(_, _) F(i, acc) == IF i > Len(Mem) THEN acc
                                          ELSE F(i + 1, IF s[Mem[i]] = 0 THEN acc
                                                        ELSE Append(acc, [m |-> Mem[i], rec |-> Rec(s[Mem[i]])]))
         IN F(1, <<>>)
Frame(es, more) == [k |-> "snap", partial |-> FALSE, more |-> more, es |-> es]
Frames(s, chunk) ==
    LET es == Es(s)
    IN IF chunk /\ Len(es) > 1 THEN <<Frame(<<es[1]>>, TRUE), Frame(<<es[2]>>, FALSE)>> ELSE <<Frame(es, FALSE)>>

\* the snapshot cut short: its first frame lists 3 at epoch 2, then the session ends and returns (the host redials and
\* the node takes hub 1 again as its primary)
Cut(S) == LET s1 == DropPeer(ApplySnap(S, Env0, Now, 1, Frame(<<[m |-> 3, rec |-> Rec(2)]>>, TRUE)), Env0, Now, 1)
          IN [s1 EXCEPT !.up = Put(@, 1, Now), !.primary = <<1>>]

Run(v, ca, cb, r, s, chunk, cut) ==
    LET fs == Frames(s, chunk)
        RECURSIVE F(_, _)
        F(st, i) == IF i > Len(fs) THEN st ELSE F(ApplySnap(st, Env0, Now, 1, fs[i]), i + 1)
        s0 == Mk(v, ca, cb, r)
    IN F(IF cut THEN Cut(s0) ELSE s0, 1)

VARIABLES c1, c2, v, r, s, chunk, cut, fin
vars == <<c1, c2, v, r, s, chunk, cut, fin>>

Init == /\ c1 \in Cells2 /\ c2 \in Cells2 /\ v \in Cells2 /\ s \in Cells2
        /\ r \in [{3, 4} -> Waits] /\ \A m \in {3, 4} : r[m] # "none" => v[m] # 0
        /\ chunk \in BOOLEAN /\ cut \in BOOLEAN
        /\ fin = Run(v, c1, c2, r, s, chunk, cut)
Next == UNCHANGED vars
Spec == Init /\ [][Next]_vars

\* whether hub 1's copy held an entry of m before the final snapshot (its earlier copy, or the cut snapshot)
Held1(m) == c1[m] # 0 \/ (cut /\ m = 3)
Home == fin.hv[1].entries

HomeRec == \A m \in {3, 4} : s[m] # 0 => m \in DOMAIN fin.members /\ fin.members[m].rec = Rec(s[m])
NoGhost == \A m \in DOMAIN Home : s[m] = 0 => Home[m].absentSince # <<>>
Covers == \A m \in DOMAIN fin.members : m \in DOMAIN Home \/ m \in DOMAIN fin.recheck
DeferKept == \A m \in {3, 4} : r[m] = "deferred" /\ s[m] = 0 /\ ~Held1(m) =>
                 m \notin DOMAIN Home /\ m \in DOMAIN fin.recheck /\ m \in DOMAIN fin.members
HeldDecided == \A m \in {3, 4} : r[m] = "held" /\ s[m] = 0 /\ ~Held1(m) /\ c2[m] = 0 /\ QuietEnd(r) = Z =>
                 m \notin DOMAIN fin.members
KeptIfListed == \A m \in {3, 4} : r[m] = "held" /\ s[m] = 0 /\ ~Held1(m) /\ c2[m] # 0 => m \in DOMAIN fin.members
=============================================================================
