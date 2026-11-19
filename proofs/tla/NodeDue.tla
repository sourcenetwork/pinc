------------------------------- MODULE NodeDue -------------------------------
(***************************************************************************)
(* The node's deadline cache: crates/pinc-node/src/node.rs `Due` (82-89),  *)
(* `Layers` (94-98), `begin` (338-341), `begin_endpoint` (347-354),        *)
(* `settle_with` (Stale first), `poll_transmit` (612-630: nothing waiting  *)
(* is no input; a packet routed to the connectivity layer sets Stale),     *)
(* `data_command` (651-659), `due` (552-580).                              *)
(*                                                                         *)
(* The node's state, abstracted: the clock now (io.now), the endpoint's   *)
(* deadline ep, and the layers' state ls, whose deadline LayerDl(ls, t) is *)
(* worked out for a clock t (layers_deadline). The layers' deadline        *)
(* depends on the clock in the code: the connectivity layer's watchdog is  *)
(* counted only while it is ahead of the clock (pinc-connect               *)
(* client/timers.rs 41-47), a carrier that is down after a restart is due  *)
(* at min(at, now) (client/link.rs 412-415), and the keepalive base is     *)
(* 30 s within KEEP_MEMORY of a failed keepalive and 65 s after (link.rs   *)
(* 343-351). Each of them makes the deadline later, never earlier, as the  *)
(* clock moves; ls is one deadline that stands (fixed) and one counted     *)
(* only while ahead of the clock (watch), and, as a planted variant (MONO  *)
(* FALSE), one that comes due once the clock passes watch (late), which    *)
(* makes the deadline earlier as the clock moves. Deadlines are 2, 4 or   *)
(* none (INF), watch 1, 3 or none, the clock 0..T.                         *)
(*                                                                         *)
(* Calls: Call (begin, any input, settle: everything may move, Stale);     *)
(* EpCall (begin_endpoint and a data command that raised no event, or a    *)
(* poll_transmit that routed nothing: the endpoint's deadline may move;   *)
(* the layers' part is kept unless the DTN layer runs, whose deadline      *)
(* follows the wall clock, so every call may move it); Route (the packet  *)
(* poll_transmit hands to the connectivity layer: its deadlines may move,  *)
(* Stale); Due (due(): the cached answer, or the layers' part kept and the *)
(* endpoint's read again, or both worked out at the clock now).            *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - Coherent: the code's two debug assertions: a known answer is the     *)
(*    endpoint's and the layers' deadline worked out at the clock the      *)
(*    layers' part was taken, and a kept layers' part is theirs at it;     *)
(*  - NeverLate: a known answer is never later than one worked out fresh   *)
(*    at the clock now.                                                    *)
(* Witnesses: NodeDue_exact (Exact: the known answer is the fresh one;     *)
(* fails: a layers' part kept across an EpCall still counts a watchdog the *)
(* clock has passed, so the node answers early: finding); NodeDue_noroute  *)
(* (a routed packet does not set Stale: Coherent fails); NodeDue_dtnkeep  *)
(* (the layers' part is kept with the DTN layer running: Coherent fails); *)
(* NodeDue_fall (a layer deadline that falls as the clock moves: the kept  *)
(* part answers late, NeverLate fails).                                    *)
(* Not modelled: TimerStats and the held repeat of poll_timeout            *)
(* (timers.rs answer), which only raise the answer; which calls are        *)
(* EpCalls is the code's (node.rs 616, 655), taken as given.               *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS T,          \* the last clock explored
          DTN,        \* the DTN layer runs
          MONO,       \* layer deadlines never fall as the clock moves (the code); FALSE plants one that does
          ROUTESTALE, \* a routed packet sets Stale (the code); FALSE: a planted bug
          DTNSTALE    \* with the DTN layer every call is Stale (the code); FALSE: a planted bug

INF == 99
Dls == {2, 4, INF}
Watch == {1, 3, INF}
Min(a, b) == IF a < b THEN a ELSE b
LS == [fixed : Dls, watch : Watch, late : IF MONO THEN {INF} ELSE {2, INF}]

\* the layers' deadline worked out for the clock t
LayerDl(l, t) == Min(Min(l.fixed, IF l.watch > t THEN l.watch ELSE INF),
                     IF ~MONO /\ t >= l.watch THEN l.late ELSE INF)

Stale == [k |-> "stale", d |-> 0, at |-> 0, due |-> 0]

VARIABLES now, ep, ls, cache
vars == <<now, ep, ls, cache>>

Init == now = 0 /\ ep \in Dls /\ ls \in LS /\ cache = Stale

Kept == cache.k \in {"ep", "known"} /\ (~DTN \/ ~DTNSTALE)

Call == /\ \E t \in now..T, e \in Dls, l \in LS : now' = t /\ ep' = e /\ ls' = l
        /\ cache' = Stale

EpCall == /\ \E t \in now..T, e \in Dls : now' = t /\ ep' = e
          /\ IF DTN THEN \E l \in LS : ls' = l ELSE UNCHANGED ls
          /\ cache' = IF Kept THEN [k |-> "ep", d |-> 0, at |-> cache.at, due |-> cache.due] ELSE Stale

Route == /\ \E l \in LS : ls' = l
         /\ cache' = IF ROUTESTALE THEN Stale ELSE cache
         /\ UNCHANGED <<now, ep>>

Due == LET at == IF cache.k = "stale" THEN now ELSE cache.at
           due == IF cache.k = "stale" THEN LayerDl(ls, now) ELSE cache.due
           d == IF cache.k = "known" THEN cache.d ELSE Min(ep, due)
       IN /\ cache' = [k |-> "known", d |-> d, at |-> at, due |-> due]
          /\ UNCHANGED <<now, ep, ls>>

Next == Call \/ EpCall \/ Route \/ Due
Spec == Init /\ [][Next]_vars

Fresh == Min(ep, LayerDl(ls, now))

TypeOK == now \in 0..T /\ ep \in Dls /\ ls \in LS /\ cache.k \in {"stale", "ep", "known"}
Coherent == /\ cache.k = "known" => cache.d = Min(ep, LayerDl(ls, cache.at)) /\ cache.due = LayerDl(ls, cache.at)
            /\ cache.k = "ep" => cache.due = LayerDl(ls, cache.at)
NeverLate == cache.k = "known" => cache.d <= Fresh
Exact == cache.k = "known" => cache.d = Fresh
=============================================================================
