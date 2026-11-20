------------------------------- MODULE IfaceOps -------------------------------
(***************************************************************************)
(* The operators of pinc-core iface.rs (Endpoint::iface_event with link,   *)
(* addr_change, suspend and resume; Command::Suspend and Command::Resume   *)
(* call suspend and resume directly), shared by Iface.tla (the model       *)
(* check) and TraceIface.tla (the recorded events of the code).            *)
(*                                                                         *)
(* A node is [ifs, dark, susp, moved, ses]: ifs the local address of each  *)
(* interface id (0: none), the flags of the endpoint, and per session slot *)
(* [st, act, sb, pto, doubt, asleep]: st "free", "hs" (in its handshake)   *)
(* or "est" (established), act the local address its active path leaves   *)
(* from (0: none), sb the local address of a standby path (0: none), pto  *)
(* whether its recovery has a probe timeout running (pto_count > 0),      *)
(* doubt its sleep_doubt, asleep whether a SLEEP went out and no wake      *)
(* since. An event returns the node after it, the calls it makes on each   *)
(* session's connection in order ("down", "up": set_link_down; "sleep";   *)
(* "wake"; "redial": the session closes for a redial) and whether it sets  *)
(* quiet_until to now + RESUME_QUIET (saturating).                         *)
(*                                                                         *)
(* The address change moves every path of a session that leaves from the  *)
(* old address to the new one (rebind_path, or add_path and path_lost when *)
(* the session already holds that path: either way the session's paths    *)
(* leave from the new address), and wakes (down, up) the established      *)
(* sessions whose active path left from the old one, as the code does.     *)
(*                                                                         *)
(* The doubt is the module doc's: a session is in doubt when it was timing *)
(* out, or the node had lost its link, when its SLEEP went out, and a      *)
(* SLEEP goes out once per suspension (pinc-transport life.rs sleep does   *)
(* nothing on a connection already asleep). The code takes the doubt only  *)
(* for a session not yet asleep (fix C3); before C3 it recomputed it at   *)
(* every Suspend, also for a session already asleep.                       *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS NI, K

Free == [st |-> "free", act |-> 0, sb |-> 0, pto |-> FALSE, doubt |-> FALSE, asleep |-> FALSE]
NoCalls == [i \in 1..K |-> <<>>]

(* leaves_from: established (or, with hs, in its handshake) and its active path leaves from a *)
LeavesFrom(se, a, hs) == (se.st = "est" \/ (hs /\ se.st = "hs")) /\ se.act # 0 /\ se.act = a

Link(n, a, down) ==
    [nd |-> [n EXCEPT !.dark = IF down THEN TRUE ELSE n.dark /\ n.susp],
     calls |-> [i \in 1..K |-> IF LeavesFrom(n.ses[i], a, TRUE) THEN <<IF down THEN "down" ELSE "up">> ELSE <<>>],
     qset |-> ~down]

Moved(x, old, new) == IF x = old THEN new ELSE x

AddrChange(n, id, old, new) ==
    [nd |-> [n EXCEPT !.ifs[id] = new,
                     !.dark = n.dark /\ n.susp,
                     !.moved = n.moved \/ n.susp,
                     !.ses = [i \in 1..K |->
                                IF n.ses[i].st = "free" THEN n.ses[i]
                                ELSE [n.ses[i] EXCEPT !.act = Moved(@, old, new), !.sb = Moved(@, old, new)]]],
     calls |-> [i \in 1..K |-> IF LeavesFrom(n.ses[i], old, FALSE) THEN <<"down", "up">> ELSE <<>>],
     qset |-> TRUE]

Suspend(n) ==
    [nd |-> [n EXCEPT !.susp = TRUE,
                     !.ses = [i \in 1..K |->
                                IF n.ses[i].st # "est" \/ n.ses[i].asleep THEN n.ses[i]
                                ELSE [n.ses[i] EXCEPT !.asleep = TRUE, !.doubt = n.ses[i].pto \/ n.dark]]],
     calls |-> [i \in 1..K |-> IF n.ses[i].st = "est" THEN <<"sleep">> ELSE <<>>],
     qset |-> FALSE]

Resume(n, m) ==
    LET mv == m \/ n.moved
        out(se) == mv \/ se.doubt
    IN [nd |-> [n EXCEPT !.moved = FALSE, !.susp = FALSE, !.dark = FALSE,
                        !.ses = [i \in 1..K |->
                                   IF n.ses[i].st # "est" THEN n.ses[i]
                                   ELSE IF out(n.ses[i]) THEN Free
                                   ELSE [n.ses[i] EXCEPT !.asleep = FALSE]]],
        calls |-> [i \in 1..K |-> IF n.ses[i].st # "est" THEN <<>>
                                  ELSE IF out(n.ses[i]) THEN <<"redial">> ELSE <<"wake">>],
        qset |-> TRUE]

(* iface_event(id, ev), or with id 0 the command Suspend or Resume; ev is [k, a, m] *)
Event(n, id, ev) ==
    IF id = 0
    THEN IF ev.k = "suspend" THEN Suspend(n)
         ELSE IF ev.k = "resume" THEN Resume(n, ev.m)
         ELSE [nd |-> n, calls |-> NoCalls, qset |-> FALSE]
    ELSE IF id \notin DOMAIN n.ifs \/ n.ifs[id] = 0 THEN [nd |-> n, calls |-> NoCalls, qset |-> FALSE]
    ELSE IF ev.k = "down" THEN Link(n, n.ifs[id], TRUE)
    ELSE IF ev.k = "up" THEN Link(n, n.ifs[id], FALSE)
    ELSE IF ev.k = "addr" THEN AddrChange(n, id, n.ifs[id], ev.a)
    ELSE IF ev.k = "suspend" THEN Suspend(n)
    ELSE Resume(n, ev.m)
=============================================================================
