--------------------------- MODULE ConnectDrivePrune ---------------------------
(***************************************************************************)
(* Model check of the pending dials around a drive's tick (PruneDrive of  *)
(* ConnectDriveOps, pinc-connect src/client/drive.rs: DIAL_PRUNE and "A   *)
(* pending dial whose lookup is gone asks again"), under every order of:  *)
(* dials to peers without a record (each waits on the pending table and   *)
(* asks for the record), their sessions ending (a failed or finished      *)
(* handshake), a lookup answered with no record (the lookup goes, the dial *)
(* keeps waiting), every lookup cleared (a carrier that never opened,     *)
(* carriers.rs act Close), the record found (found_dial takes the peer)   *)
(* and drives. One session per peer.                                       *)
(*                                                                         *)
(* The tables are scaled: Pend pending peers and Look lookups (16 and 16  *)
(* in the code, LOOKUPS), and Buf, the drive's buffers of dropped and     *)
(* pending peers (LOOKUPS in the code with fix K5; 8 before it). With     *)
(* Pend <= Buf the drive's buffers never cut, which is the code's case     *)
(* (every config). With Pend > Buf they cut, as 16 > 8 did before K5:      *)
(* PruneDropsLookup and ReAsk then fail (the findings).                    *)
(*                                                                         *)
(* Properties (the comments of drive):                                     *)
(*  PruneDropsLookup  "a dial that ended drops its lookup": after a drive *)
(*                    no peer the prune removed has a lookup               *)
(*  ReAsk             "A pending dial whose lookup is gone asks again":   *)
(*                    after a drive every pending peer has a lookup, or   *)
(*                    the lookup table is full                             *)
(***************************************************************************)
EXTENDS ConnectDriveOps

CONSTANTS Pend, Look, Buf, Peers

VARIABLES pd, lk, ended, badDrop, badAsk
vars == <<pd, lk, ended, badDrop, badAsk>>

NOW == 1000000

\* the session of peer k is k (one per peer)
Init == /\ pd = NewPending(Pend, 1) /\ lk = NewLookups(Look) /\ ended = {} /\ badDrop = FALSE /\ badAsk = FALSE

Dial == \E k \in Peers :
    /\ ~PHas(pd, k)
    /\ LET r == DialPending(pd, lk, k, k, NOW) IN pd' = r.P /\ lk' = r.T
    /\ ended' = ended \ {k}
    /\ UNCHANGED <<badDrop, badAsk>>

End == \E k \in Peers : PHas(pd, k) /\ k \notin ended /\ ended' = ended \cup {k} /\ UNCHANGED <<pd, lk, badDrop, badAsk>>

Missing == \E k \in Peers : LHas(lk, k) /\ lk' = LAnswered(lk, k) /\ UNCHANGED <<pd, ended, badDrop, badAsk>>

Clear == LLen(lk) > 0 /\ lk' = LClear(lk) /\ UNCHANGED <<pd, ended, badDrop, badAsk>>

Found == \E k \in Peers : PHas(pd, k) /\ pd' = PTake(pd, k).P /\ lk' = LAnswered(lk, k)
                          /\ UNCHANGED <<ended, badDrop, badAsk>>

Drive == LET r == PruneDrive(pd, lk, ended, NOW, Buf)
             gone == {r.dropped[k] : k \in 1..Len(r.dropped)}
             left == PPeers(r.P)
         IN /\ pd' = r.P /\ lk' = r.T /\ ended' = ended \ gone
            /\ badDrop' = (badDrop \/ \E k \in gone : LHas(r.T, k))
            /\ badAsk' = (badAsk \/ (LLen(r.T) < Look /\ \E k \in 1..Len(left) : ~LHas(r.T, left[k])))

Next == Dial \/ End \/ Missing \/ Clear \/ Found \/ Drive

Spec == Init /\ [][Next]_vars

PruneDropsLookup == ~badDrop
ReAsk == ~badAsk
=============================================================================
