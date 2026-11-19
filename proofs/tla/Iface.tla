-------------------------------- MODULE Iface --------------------------------
(***************************************************************************)
(* Interfaces, link changes and suspension of pinc-core iface.rs           *)
(* (Endpoint::iface_event, link, addr_change, suspend, resume; the         *)
(* commands Suspend and Resume) over every sequence of events at small     *)
(* sizes. IfaceOps.tla has the operators.                                  *)
(*                                                                         *)
(* The state is the node alone (the interfaces, the flags dark, suspended  *)
(* and moved, and the sessions); what an event does is checked in every    *)
(* state for every event that could come next (every interface id, a dead  *)
(* one and the commands among them, every kind, every new address), so no *)
(* history variable multiplies the states. The environment that reaches   *)
(* the states: interface 1 changes its address between 1 and 3, interface  *)
(* 2 keeps 2; session i dials from interface ((i - 1) % NI) + 1, finishes   *)
(* its handshake, has a probe timeout running or not, may hold a standby  *)
(* path from interface 1, and closes; every event and command.            *)
(* Time is not in the state: an event says only whether it sets           *)
(* quiet_until to now + RESUME_QUIET (TraceIface.tla checks the value).    *)
(*                                                                         *)
(* Checked, in every state reached, from the module doc:                   *)
(*  - Ignored: an event on an interface id that names no address changes   *)
(*    nothing and calls no connection;                                     *)
(*  - Scope: a link going down or coming back reaches exactly the sessions *)
(*    (established or in their handshake) whose active path leaves from    *)
(*    the interface, as the transport's link down and link return; an      *)
(*    address change wakes (down, up) exactly the established sessions     *)
(*    whose active path left from it;                                      *)
(*  - AddrMoves: after an address change the interface names the new      *)
(*    address, no path of any session leaves from the old one and every    *)
(*    path that did leaves from the new one; moved is set when suspended;  *)
(*  - SuspendAll: a suspension puts every established session to sleep,    *)
(*    whatever its interface, and touches no other;                        *)
(*  - ResumeRule: a resume closes with a redial every established session  *)
(*    when the node moved (said by the call or seen while suspended) and   *)
(*    every one in doubt, wakes the others, and clears the flags;          *)
(*  - LostThenSuspended: a node that lost its link and was suspended       *)
(*    before the link came back closes its sessions for a redial on resume *)
(*    (the link coming back while suspended does not change that);         *)
(*  - SleepDoubtKept: a session timing out when its SLEEP went out closes  *)
(*    for a redial on resume, even when its probe count fell back to 0 and *)
(*    the suspension was reported again before the resume;                 *)
(*  - MovedWhileSuspended: an address change while suspended closes every  *)
(*    established session for a redial on resume;                         *)
(*  - Quiet: an event sets quiet_until exactly on a link return, an        *)
(*    address change and a resume;                                         *)
(*  - Flags: moved only while suspended; asleep and doubt only for an      *)
(*    established session while suspended.                                 *)
(* Iface.cfg: 2 interfaces, 2 sessions, addresses 1 to 3. Witnesses:       *)
(* Iface_w_doubt (a session is in doubt), Iface_w_moved (the node moved    *)
(* while suspended).                                                       *)
(* TraceIface.tla checks the recorded events of the code against           *)
(* IfaceOps.tla.                                                           *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS NI, K, NA

ASSUME NI >= 2 /\ K >= 1 /\ NA >= 3

I == INSTANCE IfaceOps WITH NI <- NI, K <- K

VARIABLE n

Ev(kind, addr, mv) == [k |-> kind, a |-> addr, m |-> mv]
Down == Ev("down", 0, FALSE)
Up == Ev("up", 0, FALSE)
Susp == Ev("suspend", 0, FALSE)
Res(m) == Ev("resume", 0, m)
AllEvs == {Down, Up, Susp, Res(FALSE), Res(TRUE)} \cup {Ev("addr", x, FALSE) : x \in 1..NA}

Init == n = [ifs |-> [j \in 1..NI |-> j], dark |-> FALSE, susp |-> FALSE, moved |-> FALSE,
             ses |-> [i \in 1..K |-> I!Free]]

Home(i) == n.ifs[((i - 1) % NI) + 1]
Other(a) == IF a = 1 THEN 3 ELSE 1

IfEvent == \E id \in 1..NI, ev \in {Down, Up, Susp, Res(FALSE), Res(TRUE)} \cup
                                   (IF id = 1 THEN {Ev("addr", Other(n.ifs[1]), FALSE)} ELSE {}) :
               n' = I!Event(n, id, ev).nd
Command == \E ev \in {Susp, Res(FALSE), Res(TRUE)} : n' = I!Event(n, 0, ev).nd
Dial == \E i \in 1..K : /\ n.ses[i].st = "free" /\ Home(i) # 0
                        /\ n' = [n EXCEPT !.ses[i] = [I!Free EXCEPT !.st = "hs", !.act = Home(i)]]
Establish == \E i \in 1..K : n.ses[i].st = "hs" /\ n' = [n EXCEPT !.ses[i].st = "est"]
Probe == \E i \in 1..K : n.ses[i].st = "est" /\ n' = [n EXCEPT !.ses[i].pto = ~@]
Standby == \E i \in 1..K : /\ n.ses[i].st # "free" /\ n.ses[i].sb = 0
                           /\ n.ifs[1] # 0 /\ n.ses[i].act # n.ifs[1]
                           /\ n' = [n EXCEPT !.ses[i].sb = n.ifs[1]]
Close == \E i \in 1..K : n.ses[i].st # "free" /\ n' = [n EXCEPT !.ses[i] = I!Free]

Next == IfEvent \/ Command \/ Dial \/ Establish \/ Probe \/ Standby \/ Close
Spec == Init /\ [][Next]_n

Live == {j \in 1..NI : n.ifs[j] # 0}
Dead == {NI + 1} \cup {j \in 1..NI : n.ifs[j] = 0}
On(se, a) == se.st \in {"hs", "est"} /\ se.act = a

TypeOK == /\ n.ifs \in [1..NI -> 0..NA]
          /\ n.dark \in BOOLEAN /\ n.susp \in BOOLEAN /\ n.moved \in BOOLEAN
          /\ n.ses \in [1..K -> [st : {"free", "hs", "est"}, act : 0..NA, sb : 0..NA, pto : BOOLEAN,
                                 doubt : BOOLEAN, asleep : BOOLEAN]]

Ignored == \A id \in Dead, ev \in AllEvs :
               LET r == I!Event(n, id, ev) IN r.nd = n /\ r.calls = I!NoCalls /\ ~r.qset

Scope == \A id \in Live, ev \in AllEvs :
             LET a == n.ifs[id]
                 r == I!Event(n, id, ev)
             IN \A i \in 1..K :
                  /\ ev.k \in {"down", "up"} =>
                       (r.calls[i] = IF On(n.ses[i], a) THEN <<ev.k>> ELSE <<>>)
                  /\ ev.k = "addr" =>
                       (r.calls[i] = IF On(n.ses[i], a) /\ n.ses[i].st = "est" THEN <<"down", "up">> ELSE <<>>)
                  /\ ev.k \in {"down", "up"} => r.nd.ses = n.ses /\ r.nd.ifs = n.ifs

AddrMoves == \A id \in Live, x \in 1..NA :
                 LET old == n.ifs[id]
                     r == I!Event(n, id, Ev("addr", x, FALSE))
                 IN /\ r.nd.ifs = [n.ifs EXCEPT ![id] = x]
                    /\ r.nd.moved = (n.moved \/ n.susp)
                    /\ \A i \in 1..K :
                         /\ n.ses[i].st # "free" /\ x # old => r.nd.ses[i].act # old /\ r.nd.ses[i].sb # old
                         /\ n.ses[i].st # "free" /\ n.ses[i].act = old => r.nd.ses[i].act = x
                         /\ n.ses[i].st # "free" /\ n.ses[i].sb = old => r.nd.ses[i].sb = x
                         /\ n.ses[i].act # old /\ n.ses[i].sb # old => r.nd.ses[i] = n.ses[i]

SuspendAll == \A id \in {0} \cup Live :
                  LET r == I!Event(n, id, Susp)
                  IN /\ r.nd.susp
                     /\ \A i \in 1..K :
                          IF n.ses[i].st = "est" THEN r.nd.ses[i].asleep /\ r.calls[i] = <<"sleep">>
                          ELSE r.nd.ses[i] = n.ses[i] /\ r.calls[i] = <<>>

ResumeRule == \A id \in {0} \cup Live, m \in BOOLEAN :
                  LET r == I!Event(n, id, Res(m))
                  IN /\ ~r.nd.susp /\ ~r.nd.moved /\ ~r.nd.dark
                     /\ \A i \in 1..K :
                          IF n.ses[i].st # "est" THEN r.nd.ses[i] = n.ses[i] /\ r.calls[i] = <<>>
                          ELSE IF m \/ n.moved \/ n.ses[i].doubt
                          THEN r.calls[i] = <<"redial">> /\ r.nd.ses[i].st = "free"
                          ELSE r.calls[i] = <<"wake">> /\ r.nd.ses[i].st = "est" /\ ~r.nd.ses[i].asleep

LostThenSuspended ==
    \A i \in 1..K, id \in Live :
        n.dark /\ ~n.susp /\ n.ses[i].st = "est" =>
            LET n1 == I!Event(n, 0, Susp).nd
                n2 == I!Event(n1, id, Up).nd
            IN I!Event(n2, 0, Res(FALSE)).calls[i] = <<"redial">>

SleepDoubtKept ==
    \A i \in 1..K :
        n.ses[i].st = "est" /\ n.ses[i].pto /\ ~n.ses[i].asleep /\ ~n.susp =>
            LET n1 == I!Event(n, 0, Susp).nd
                n2 == [n1 EXCEPT !.ses[i].pto = FALSE]
                n3 == I!Event(n2, 0, Susp).nd
            IN I!Event(n3, 0, Res(FALSE)).calls[i] = <<"redial">>

MovedWhileSuspended ==
    \A i \in 1..K, id \in Live, x \in 1..NA :
        n.ses[i].st = "est" =>
            LET n1 == I!Event(n, 0, Susp).nd
                n2 == I!Event(n1, id, Ev("addr", x, FALSE)).nd
            IN n2.ses[i].st = "est" => I!Event(n2, 0, Res(FALSE)).calls[i] = <<"redial">>

Quiet == /\ \A id \in Live, ev \in AllEvs : I!Event(n, id, ev).qset = (ev.k \in {"up", "addr", "resume"})
         /\ \A ev \in {Susp, Res(FALSE), Res(TRUE)} : I!Event(n, 0, ev).qset = (ev.k = "resume")

Flags == /\ n.moved => n.susp
         /\ \A i \in 1..K : (n.ses[i].asleep \/ n.ses[i].doubt) => (n.ses[i].st = "est" /\ n.susp)
         /\ \A i \in 1..K : n.ses[i].doubt => n.ses[i].asleep

(* reachability witnesses *)
NeverDoubt == \A i \in 1..K : ~n.ses[i].doubt
NeverMoved == ~n.moved
=============================================================================
