---------------------------- MODULE NodeDtnBackoff ----------------------------
(***************************************************************************)
(* The backoff of the node's delay-tolerant dials: pinc-node io.rs         *)
(* `lfailed`, layer.rs `dial_layer`, `layer_failed`, `layer_closed`,       *)
(* node.rs `service` (a membership event) and dtn.rs `redial_at`,          *)
(* `dtn_timeout`, `dtn_deadline`, with the operators of                    *)
(* NodeDtnBackoffOps.tla.                                                  *)
(*                                                                         *)
(* Steps, at times of TIMES that never go back (the node's clock):         *)
(*  - Fail: a delay-tolerant dial of a peer failed or was refused (also    *)
(*    the dial of a leaving node or of a revoked peer, which fails inside  *)
(*    the window too);                                                     *)
(*  - Fire: the node's timer at or after redial_at: redial_at is cleared   *)
(*    and the contacts are looked at;                                      *)
(*  - Look: the contacts are looked at for another reason (a bundle, a     *)
(*    session, the host's contact rule);                                   *)
(*  - Member: a membership event about the peer: its entry goes, and the   *)
(*    contacts are looked at;                                              *)
(*  - Reset: our session to the peer lived SESSION_LIVED and closed: its   *)
(*    entry goes (the lifetime test is the rule of NodeBackoff.tla         *)
(*    `Closed`, not repeated here).                                        *)
(* A look dials each peer outside its window (`dial_layer`); every peer is *)
(* taken to be one the contacts want dialed (in contact, bundles held, no  *)
(* session), the case where the backoff matters.                           *)
(*                                                                         *)
(* owed[p] is history: p failed, the table holds its entry, and no look    *)
(* has dialed it since. Its wait ends at F[p][1].                          *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - Bounded: the table never holds more than MAXT entries (io.rs: every *)
(*    table is bounded and a full table refuses the new entry);           *)
(*  - WaitBounds, FailRight: the first wait is 2 s, a failure with an      *)
(*    entry doubles it up to 60 s, the entry ends the wait after now      *)
(*    (saturating), a full table changes nothing for a peer it has no     *)
(*    entry for, and redial_at becomes the earlier of itself and the end  *)
(*    of the wait;                                                         *)
(*  - OwedHasEntry: a peer is owed a redial only while its entry is held;  *)
(*  - NoLostRedial (NodeDtnBackoff_redial.cfg): the delay-tolerant layer   *)
(*    waits out a backoff (layer.rs `dial_layer`) and redial_at is when a  *)
(*    failed dial may be made again (dtn.rs): every peer still owed a      *)
(*    redial has the node's redial time at or before the end of its wait. *)
(*    The code keeps one redial time and clears it when it fires; a peer   *)
(*    whose wait ends later is skipped by the look and no redial time is   *)
(*    set for it, so TLC is expected to report this invariant violated    *)
(*    (a finding; see the register notes).                                 *)
(* Witnesses: NodeDtnBackoff_w_full (a full table refuses an entry),       *)
(* NodeDtnBackoff_w_cap (a wait reaches 60 s), NodeDtnBackoff_w_sat (an    *)
(* entry's end saturates at u64::MAX).                                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Nanos
CONSTANTS MAXT, PEERS, TIMES
VARIABLES clock, F, redial, owed, refused, bad
vars == <<clock, F, redial, owed, refused, bad>>

INSTANCE NodeDtnBackoffOps

\* the model's times: the start, one second (a second failure inside the first 2 s wait), two seconds (the end of a
\* first wait), and the top of the range (where the end of a wait saturates)
TimesDef == {Zero, Sec(1), Sec(2), U!Max64}

\* a look at now dials every owed peer outside its window
Looked(G, now) == [p \in PEERS |-> owed[p] /\ G[p] # None /\ Window(G, now, p)]

\* the rules of a failure, stated on their own
FailOK(now, p, x) ==
    LET want == IF F[p] = None THEN Sec(2) ELSE Min(SatAdd(F[p][2], F[p][2]), Sec(60))
        room == Size(F) < MAXT \/ F[p] # None
    IN /\ x.back = want
       /\ x.at = SatAdd(now, want)
       /\ x.f = IF room THEN [F EXCEPT ![p] = <<SatAdd(now, want), want>>] ELSE F

Fail(now, p) ==
    LET x == DtnFailed(F, now, p)
        stored == Size(F) < MAXT \/ F[p] # None
    IN /\ F' = x.f
       /\ redial' = Sooner(redial, x.at)
       /\ owed' = IF stored THEN [owed EXCEPT ![p] = TRUE] ELSE owed
       /\ refused' = (refused \/ ~stored)
       /\ bad' = bad \cup (IF FailOK(now, p, x) /\ redial' = <<IF redial = None THEN x.at ELSE Min(redial[1], x.at)>>
                           THEN {} ELSE {"fail"})

Fire(now) == /\ RedialDue(redial, now)
             /\ redial' = None
             /\ owed' = Looked(F, now)
             /\ UNCHANGED <<F, refused, bad>>

Look(now) == owed' = Looked(F, now) /\ UNCHANGED <<F, redial, refused, bad>>

Member(now, p) == LET G == Forget(F, p)
                  IN /\ F' = G
                     /\ owed' = [Looked(G, now) EXCEPT ![p] = FALSE]
                     /\ UNCHANGED <<redial, refused, bad>>

Reset(p) == /\ F' = Forget(F, p) /\ owed' = [owed EXCEPT ![p] = FALSE]
            /\ UNCHANGED <<clock, redial, refused, bad>>

Init == /\ clock = Zero /\ F = Tab0(PEERS) /\ redial = None /\ owed = [p \in PEERS |-> FALSE]
        /\ refused = FALSE /\ bad = {}

Next == \/ \E now \in TIMES : Le(clock, now) /\ clock' = now /\
              (\/ \E p \in PEERS : Fail(now, p) \/ Member(now, p)
               \/ Fire(now)
               \/ Look(now))
        \/ \E p \in PEERS : Reset(p)

Spec == Init /\ [][Next]_vars

Bounded == Size(F) <= MAXT
WaitBounds == \A p \in Used(F) : Le(Sec(2), F[p][2]) /\ Le(F[p][2], Sec(60)) /\ Le(F[p][2], F[p][1])
FailRight == "fail" \notin bad
OwedHasEntry == \A p \in PEERS : owed[p] => F[p] # None

NoLostRedial == \A p \in PEERS : owed[p] => redial # None /\ Le(redial[1], F[p][1])

\* reachability witnesses
NoRefused == ~refused
NoCap == \A p \in Used(F) : F[p][2] # Sec(60)
NoSat == \A p \in Used(F) : F[p][1] # U!Max64
=============================================================================
