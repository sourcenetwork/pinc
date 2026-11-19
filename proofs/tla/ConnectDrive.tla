----------------------------- MODULE ConnectDrive -----------------------------
(***************************************************************************)
(* Model check of what drive does for one dialed session (EachSession of  *)
(* ConnectDriveOps, pinc-connect src/client/drive.rs each_session), under *)
(* every order of the endpoint's changes between drives: the handshake    *)
(* resends, completes or never completes, the pending dials stop holding  *)
(* the session (its peer's address arrived), the route moves to a relay   *)
(* path and back, probes time out, the punch timer is armed, the endpoint *)
(* forgets the session (a dial that failed raises no close), and drive is *)
(* called at any of Times, the clock jumping forward past every timer or  *)
(* back before them (a wake). The node carrying the relay role on the     *)
(* relay path may be any node; nothing here depends on its kind.          *)
(*                                                                         *)
(* Properties (the comments of each_session in drive.rs):                  *)
(*  HoldMirror      "A dial still waiting for its peer's address resends  *)
(*                  nothing": after each drive the endpoint holds the     *)
(*                  flight exactly while the dial is in its handshake and *)
(*                  waits for the address                                  *)
(*  NoDueAfterDrive no timer of a session is left due after a drive: the  *)
(*                  relay copy, the path given back, and the punch timer   *)
(*                  ("Left armed, a timer that is due would keep the node *)
(*                  waking for it"); a session the endpoint forgot loses  *)
(*                  its timers ("or they would stay due forever")          *)
(*  RelayCopyOnce   the relay copy joins the flight of a direct-first dial *)
(*                  once                                                    *)
(*  ReaddOnce       an established session dialed direct-first gets its   *)
(*                  relay path back once                                   *)
(*  RetryPerTry     later tries choose their paths again, once per try    *)
(* Witness (TLC must violate): ConnectDrive_w_check (NoCheck: a dial that *)
(* reached its third try checks the carriers it could ride).               *)
(***************************************************************************)
EXTENDS ConnectDriveOps

CONSTANTS Directs, MaxRetx, Arms, PVs, Routes, Ptos, Times

VARIABLES sess, live, gone, dialed, st, holds, epHold, nRelay, nReadd, tried, badHold, badDue, badRetry, checked
vars == <<sess, live, gone, dialed, st, holds, epHold, nRelay, nReadd, tried, badHold, badDue, badRetry, checked>>

PV(p) == CASE p = "idle" -> [idle |-> ACTIVEKEEP, rtt |-> 0]
           [] p = "good" -> [idle |-> 0, rtt |-> GOOD]
           [] OTHER -> [idle |-> 0, rtt |-> GOOD + 1]

St0 == [est |-> FALSE, dialer |-> TRUE, retx |-> 0, pto |-> FALSE, rr |-> FALSE, valid |-> FALSE,
        idle |-> PV(CHOOSE p \in PVs : TRUE).idle, rtt |-> PV(CHOOSE p \in PVs : TRUE).rtt]

Init == /\ sess = NoSess /\ live = FALSE /\ gone = FALSE /\ dialed = FALSE /\ st = St0 /\ holds = FALSE
        /\ epHold = FALSE /\ nRelay = 0 /\ nReadd = 0 /\ tried = {1} /\ badHold = FALSE /\ badDue = FALSE
        /\ badRetry = FALSE /\ checked = FALSE

Ghosts == <<nRelay, nReadd, tried, badHold, badDue, badRetry, checked>>

Dial == /\ ~dialed
        /\ \E t \in Times, direct \in Directs, h \in BOOLEAN :
              /\ h => ~direct
              /\ sess' = DialSess(t, direct) /\ holds' = h
        /\ live' = TRUE /\ dialed' = TRUE
        /\ UNCHANGED <<gone, st, epHold>> /\ UNCHANGED Ghosts

Env == /\ live /\ ~gone
       /\ \/ ~st.est /\ st' = [st EXCEPT !.est = TRUE, !.valid = TRUE] /\ UNCHANGED <<holds, sess, gone>>
          \/ ~st.est /\ st.retx < MaxRetx /\ st' = [st EXCEPT !.retx = @ + 1] /\ UNCHANGED <<holds, sess, gone>>
          \/ \E r \in Routes, p \in Ptos, v \in PVs :
                /\ st' = [st EXCEPT !.rr = r, !.pto = p, !.idle = PV(v).idle, !.rtt = PV(v).rtt]
                /\ st' # st /\ UNCHANGED <<holds, sess, gone>>
          \/ holds /\ holds' = FALSE /\ UNCHANGED <<st, sess, gone>>
          \/ \E t \in Arms : sess.punch # t /\ sess' = [sess EXCEPT !.punch = t] /\ UNCHANGED <<st, holds, gone>>
          \/ gone' = TRUE /\ UNCHANGED <<st, holds, sess>>
       /\ UNCHANGED <<live, dialed, epHold>> /\ UNCHANGED Ghosts

Count(q, c) == Cardinality({k \in 1..Len(q) : q[k] = c})

Drive == /\ live
         /\ \E t \in Times :
              IF gone THEN /\ sess' = NoSess /\ live' = FALSE
                           /\ UNCHANGED <<gone, dialed, st, holds, epHold>> /\ UNCHANGED Ghosts
              ELSE LET r == EachSession(sess, st, t, holds)
                       q == r.cmds
                       eh == IF Count(q, "hold") > 0 THEN TRUE ELSE IF Count(q, "unhold") > 0 THEN FALSE ELSE epHold
                       s1 == r.s
                   IN /\ sess' = s1 /\ epHold' = eh
                      /\ badHold' = (badHold \/ eh # (~st.est /\ st.dialer /\ holds))
                      /\ badDue' = (badDue \/ (s1.relayAt # -1 /\ s1.relayAt <= t) \/ (s1.readdAt # -1 /\ s1.readdAt <= t)
                                           \/ (s1.punch # 0 /\ s1.punch <= t))
                      /\ nRelay' = nRelay + Count(q, "relay_copy")
                      /\ nReadd' = nReadd + Count(q, "readd")
                      /\ badRetry' = (badRetry \/ (Count(q, "retry") > 0 /\ s1.tries \in tried))
                      /\ tried' = IF Count(q, "retry") > 0 THEN tried \cup {s1.tries} ELSE tried
                      /\ checked' = (checked \/ r.check)
                      /\ UNCHANGED <<live, gone, dialed, st, holds>>

Next == Dial \/ Env \/ Drive

Spec == Init /\ [][Next]_vars

HoldMirror == ~badHold
NoDueAfterDrive == ~badDue /\ (~live => sess = NoSess)
RelayCopyOnce == nRelay <= 1
ReaddOnce == nReadd <= 1
RetryPerTry == ~badRetry

\* reachability
NoCheck == ~checked

\* the activity of the session in the configs
PVsIdle == {"idle"}
PVsAll == {"idle", "good", "slow"}
NoArms == {}
OnlyFalse == {FALSE}
Both == {FALSE, TRUE}
=============================================================================
