---------------------------- MODULE ConnectDriveOps ----------------------------
(***************************************************************************)
(* What one drive of pinc-connect src/client/drive.rs does, as pure       *)
(* operators: the timers and rules of each session (each_session: the     *)
(* held first flight, the relay copy of a direct-first dial, the relay    *)
(* path given back, the paths chosen again on later tries and the carrier *)
(* check from the third, the carrier's word for a session on a relay path, *)
(* the punch timer), and the pending dials around the tick (DIAL_PRUNE and *)
(* the lookup asked again). ConnectDrive.tla, ConnectDrivePrune.tla (the   *)
(* model checks) and TraceConnectDrive.tla (the trace validation) use     *)
(* them.                                                                    *)
(*                                                                         *)
(* The rules this drive applies are ConnectClient.tla's and reused from   *)
(* ConnectClientOps: the punch timer (PDue), the pending dials (PAdd,     *)
(* PTake, PPeers, PHas) and the lookup table (LAsk, LAnswered, LClear,    *)
(* LHas, LLen). Which paths a reselect or add_paths names is ConnectClient *)
(* (Select); here each is the one FlightPaths command it always sends.     *)
(* Time is in microseconds, as there; -1 is none and a punch timer of 0 is *)
(* off.                                                                     *)
(*                                                                         *)
(* A session s is [held, relayAt, readdAt, tries, punch, rr] (Sess: held,  *)
(* relay_at, readd_at, tries, punch, relay_route). Its endpoint statistics *)
(* st are [est, dialer, retx, pto, rr, valid, idle, rtt]: established,     *)
(* dialer, handshake_retransmits, pto_count > 0, the route is a relay     *)
(* path, path_validated, now - last_app and srtt. The commands a drive     *)
(* sends for the session are named: "hold" and "unhold" (HoldFlight),      *)
(* "relay_copy", "readd" and "retry" (the FlightPaths of the relay copy,   *)
(* of the path given back and of a reselect), "heard" (CarrierHeard) and  *)
(* "punch" (ReachOut and Punch of punch_now). The session of a dial whose *)
(* peer has no record is never a hub session: the pulse of a hub session  *)
(* (pulse_session, ConnectClient and the carrier link) is not modelled.   *)
(***************************************************************************)
EXTENDS ConnectClientOps

HUBRELAYDELAY == 300000
HUBPATHDELAY == 2 * SEC
CHECKTRIES == 3

(* dial: a direct-first dial arms the relay copy and the path given back *)
DialSess(now, direct) ==
    [held |-> FALSE, relayAt |-> IF direct THEN now + HUBRELAYDELAY ELSE -1,
     readdAt |-> IF direct THEN now + HUBPATHDELAY ELSE -1, tries |-> 1, punch |-> 0, rr |-> FALSE]

(* each_session for one session with statistics st; holds: the pending dials hold the session *)
EachSession(s, st, now, holds) ==
    LET hold == ~st.est /\ st.dialer /\ holds
        c1 == IF hold # s.held THEN <<IF hold THEN "hold" ELSE "unhold">> ELSE <<>>
        rFire == s.relayAt # -1 /\ now >= s.relayAt
        c2 == IF rFire /\ ~st.est THEN <<"relay_copy">> ELSE <<>>
        relayAt1 == IF rFire THEN -1 ELSE s.relayAt
        aFire == s.readdAt # -1 /\ now >= s.readdAt
        c3 == IF aFire /\ st.est THEN <<"readd">> ELSE <<>>
        tries == st.retx + 1
        re == ~st.est /\ st.dialer /\ tries # s.tries /\ relayAt1 = -1
        c4 == IF re THEN <<"retry">> ELSE <<>>
        c5 == IF st.pto /\ st.rr THEN <<"heard">> ELSE <<>>
        p1 == IF ~st.est /\ s.punch # 0 /\ s.punch <= now THEN 0 ELSE s.punch
        d == PDue(p1, now, [idle |-> st.idle, direct |-> ~st.rr /\ st.valid, rtt |-> st.rtt, quiet |-> 0])
        pun == st.est /\ p1 # 0 /\ d.res = "punch"
        c6 == IF pun THEN <<"punch">> ELSE <<>>
    IN [s |-> [held |-> hold, relayAt |-> relayAt1, readdAt |-> IF aFire THEN -1 ELSE s.readdAt,
               tries |-> IF re THEN tries ELSE s.tries, punch |-> IF st.est /\ p1 # 0 THEN d.at ELSE p1, rr |-> st.rr],
        cmds |-> c1 \o c2 \o c3 \o c4 \o c5 \o c6,
        check |-> re /\ tries >= CHECKTRIES]

(* the endpoint no longer has the session: its timers go with it *)
NoSess == [held |-> FALSE, relayAt |-> -1, readdAt |-> -1, tries |-> 0, punch |-> 0, rr |-> FALSE]

(* the paths named FlightPaths, as the trace sees them *)
AsSeen(c) == IF c \in {"relay_copy", "readd", "retry"} THEN "paths" ELSE c
CmdsSeen(q) == [k \in 1..Len(q) |-> AsSeen(q[k])]

(* ---- DIAL_PRUNE and the lookup asked again (drive, around the tick) ---- *)

\* every session of a pending peer that is in `ended` leaves; a peer left with none is dropped, in slot order
RECURSIVE PruneEnded(_, _, _, _)
PruneEnded(items, i, ended, dropped) ==
    IF i > Len(items) THEN [items |-> items, dropped |-> dropped]
    ELSE IF ~items[i].e THEN PruneEnded(items, i + 1, ended, dropped)
    ELSE LET ws == [k \in 1..Len(items[i].ws) |-> IF items[i].ws[k] \in ended THEN -1 ELSE items[i].ws[k]]
         IN IF \A k \in 1..Len(ws) : ws[k] = -1
            THEN PruneEnded([items EXCEPT ![i] = [e |-> FALSE, peer |-> 0, ws |-> ws]], i + 1, ended,
                            Append(dropped, items[i].peer))
            ELSE PruneEnded([items EXCEPT ![i].ws = ws], i + 1, ended, dropped)

First(q, b) == SubSeq(q, 1, Min(Len(q), b))

RECURSIVE AnswerAll(_, _)
AnswerAll(T, q) == IF q = <<>> THEN T ELSE AnswerAll(LAnswered(T, Head(q)), Tail(q))

\* lookup(now, p) for each peer of q without a lookup (a relay is configured; the table adds the peer if it has room)
RECURSIVE AskAll(_, _, _)
AskAll(T, q, now) ==
    IF q = <<>> THEN T
    ELSE AskAll(IF LHas(T, Head(q)) THEN T ELSE LAsk(T, now, Head(q), TRUE, FALSE, 0).T, Tail(q), now)

(* the pending dials and lookups of one drive: pruned, the first b dropped peers lose their lookup, the first b
   pending peers without one ask again (b is LOOKUPS, 16, in the code) *)
PruneDrive(P, T, ended, now, b) ==
    LET pr == PruneEnded(P.items, 1, ended, <<>>)
        P1 == [P EXCEPT !.items = pr.items]
        T1 == AnswerAll(T, First(pr.dropped, b))
    IN [P |-> P1, T |-> AskAll(T1, First(PPeers(P1), b), now), dropped |-> pr.dropped]

(* a dial whose peer has no record and no hints: it waits on the pending dials and asks for the record *)
DialPending(P, T, peer, sid, now) == [P |-> PAdd(P, peer, sid).P, T |-> AskAll(T, <<peer>>, now)]
=============================================================================
