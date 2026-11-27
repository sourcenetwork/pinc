------------------------------ MODULE PathMove ------------------------------
(***************************************************************************)
(* Path validation and migration of an established connection, through    *)
(* the operators of PathMoveOps.tla (pinc-transport conn/path.rs:          *)
(* add_path, rebind_path, remove_path, path_lost, set_active,              *)
(* set_path_info, probe, punch_known, path_returned, on_path_response,     *)
(* challenge_back, choose_path, switch_active, follow_active,              *)
(* forget_gone, on_path_timers, idle_out, fire_probe, fail_over,           *)
(* relay_fallback; conn/recv.rs process_payload and follow_peer;           *)
(* conn/send.rs fill_path; conn/timer.rs run_recovery_timer).              *)
(*                                                                         *)
(* Who acts. The host calls the path API with any id of Ids, any kind of   *)
(* KINDS (a relayed path runs through a node that carries the relay role;  *)
(* it is a path like any other to this code). The network and an attacker *)
(* deliver a packet that opened on any path, held or not: a PATH_RESPONSE  *)
(* carrying any challenge that ever left on any path (a late answer, an    *)
(* answer on the wrong path, an answer after the path's address changed:   *)
(* rebind) or a forged one (FORGED, never drawn); a PATH_CHALLENGE; data,  *)
(* the highest numbered or not, with or without WAKE. A challenge that is  *)
(* queued may leave on its path or never (lost, or held back). Timers fire *)
(* in any order: the 15 s silence of any heard path, the due probes, the   *)
(* re-join floor, the third (and every later) probe timeout in a row.      *)
(* The random draw of a challenge may fail. The session is established     *)
(* throughout: the first path (id 1) is direct, validated, active, heard.  *)
(*                                                                         *)
(* Checked, the code's own rules and claims:                               *)
(*  ActiveLive       the active slot always holds a path (module doc       *)
(*                   invariant);                                           *)
(*  Unique           no path is held twice, rebinds included;              *)
(*  OutstandingKept  the outstanding challenge and the last CH drawn since *)
(*                   the table was cleared are in the table (module doc:   *)
(*                   a replaced challenge cannot strand the answer);       *)
(*  ReplacedKept     an answer to one of them validates its path;          *)
(*  AnswerOnPath     an answer validates a direct path only on the slot it *)
(*                   arrived on and only if the challenge left on that     *)
(*                   slot (module doc invariant);                          *)
(*  ValidCause       a direct path becomes validated only by such an       *)
(*                   answer, path_returned, or the host's add_path or      *)
(*                   set_path_info turning a validated relayed path into a *)
(*                   direct one (the code's rule; DocValid is the doc's);  *)
(*  FollowRule       a data packet moves the active path exactly by        *)
(*                   follow_peer's rule (FollowsPeer is the doc's);        *)
(*  ChooseValid      choose_path moves only onto a usable path;            *)
(*  FallbackRule     fail_over on an active direct path, validated or not  *)
(*                   (fix T5), moves to the validated relayed path, not    *)
(*                   gone, of the highest slot if there is one, a          *)
(*                   validated one left unvalidated and rejoining with     *)
(*                   probes; otherwise it changes nothing (the code's      *)
(*                   rule; DocFallback is the doc's);                      *)
(*  LostRule         after path_lost no gone path is held but the active  *)
(*                   one, and the lost path, if still held, is that one,   *)
(*                   gone and unvalidated;                                 *)
(*  ValidationLive   a validation challenge_path starts on a path          *)
(*                   (follow_peer, challenge_back) is never left with      *)
(*                   nothing armed: until the path is validated, lost or   *)
(*                   emptied, or its last probe has left, its challenge    *)
(*                   waits to leave or a probe is left, so one lost        *)
(*                   challenge or answer is sent again                     *)
(*                   (PathMove_retry; PathMove_w_once, the rule before:    *)
(*                   one challenge never repeated, TLC must violate it).   *)
(* The doc's claim the code does not meet (witness config, TLC must        *)
(* violate it): DocValid (T9, a doc fix). RelayValid, DocFallback,         *)
(* GoneLeft and GoneNeverBack hold with fixes T7, T5, T4 and T6            *)
(* (PathMove_relay, _stuck, _lost, _gone; before them TLC found each       *)
(* violated). FollowsPeer and DocGain state the docs restated by T8 and    *)
(* T11 and hold (PathMove_follow, PathMove_gain); PathMove_follow_gone     *)
(* checks FollowsPeer where a gone path is held beside the active one (T6: *)
(* a gone path is never followed; the doc before it had no such exception  *)
(* and the code then followed it). Reach witnesses: NoReplacedAnswer,      *)
(* NoWrap, NoFallback,                                                     *)
(* NoGoneData (PathMove_w_gonedata).                                       *)
(***************************************************************************)
EXTENDS PathMoveOps, TLC

CONSTANTS Ids, KINDS, SIXES, RTTS, TMAX, OPS

VARIABLES c, wire, ev
vars == <<c, wire, ev>>

FORGED == -1

C0 == [t |-> [x \in 1..NP |-> IF x = 1 THEN [New(1, "d", FALSE, "fresh") EXCEPT !.v = TRUE] ELSE None],
       act |-> 1, srtt |-> 0, hi |-> 0, mv |-> "none", dg |-> FALSE]

\* the ghost of the last step: the call, the slot it acted on, what the properties read of the state before it
E0 == [op |-> "init", id |-> 0, s |-> 0, tok |-> 0, ok |-> FALSE, rep |-> FALSE, rc |-> FALSE, nvd |-> {},
       hi |-> FALSE, fol |-> FALSE, pact |-> 0, pd |-> FALSE, pk |-> "none", hr |-> FALSE, wake |-> FALSE,
       sg |-> FALSE]

Init == c = C0 /\ wire = {} /\ ev = E0

\* the connection a step starts from: the per-step ghosts cleared
Pre == [c EXCEPT !.mv = "none", !.dg = FALSE]
\* A step to one of the connections ncs with the ghost e. A call's arguments that the ghost does not name are folded
\* into ncs, so a connection several of them give is one step (TLC checks the properties on each step it takes); a
\* value used more than once is bound with `\E`, not a LET or an operator argument, which TLC evaluates at each use.
DoAny(ncs, e) == \E n \in ncs : /\ c' = Mark(c, n)
                               /\ ev' = [e EXCEPT !.nvd = NewDirect(c, n)]
Do(nc, e) == DoAny({nc}, e)

AddAct == /\ "add" \in OPS
          /\ \E id \in Ids :
                DoAny({AddPath(Pre, id, k, six, rn).c : k \in KINDS, six \in SIXES, rn \in BOOLEAN},
                      [E0 EXCEPT !.op = "add", !.id = id])
          /\ UNCHANGED wire
RebindAct == /\ "rebind" \in OPS
             /\ \E id1 \in Ids : DoAny({Rebind(Pre, id0, id1).c : id0 \in Ids}, [E0 EXCEPT !.op = "rebind", !.id = id1])
             /\ UNCHANGED wire
RemoveAct == /\ "remove" \in OPS
             /\ \E id \in Ids : Do(Remove(Pre, id).c, [E0 EXCEPT !.op = "remove", !.id = id])
             /\ UNCHANGED wire
LostAct == /\ "lost" \in OPS
           /\ \E id \in Ids : Do(Lost(Pre, id).c, [E0 EXCEPT !.op = "lost", !.id = id, !.s = PO!Find(c.t, id)])
           /\ UNCHANGED wire
SetAct == /\ "set" \in OPS
          /\ \E id \in Ids : Do(SetActive(Pre, id).c, [E0 EXCEPT !.op = "set", !.id = id])
          /\ UNCHANGED wire
InfoAct == /\ "info" \in OPS
           /\ \E id \in Ids : DoAny({SetInfo(Pre, id, k, six) : k \in KINDS, six \in SIXES},
                                    [E0 EXCEPT !.op = "info", !.id = id])
           /\ UNCHANGED wire
ProbeAct == /\ "probe" \in OPS
            /\ \E id \in Ids : DoAny({Probe(Pre, id, rn).c : rn \in BOOLEAN}, [E0 EXCEPT !.op = "probe", !.id = id])
            /\ UNCHANGED wire
PunchAct == /\ "punch" \in OPS
            /\ DoAny({PunchKnown(Pre, rn) : rn \in BOOLEAN}, [E0 EXCEPT !.op = "punch"])
            /\ UNCHANGED wire
SilenceAct == /\ "silence" \in OPS
              /\ \E x \in 1..NP : /\ c.t[x].id # 0 /\ c.t[x].hd = "fresh"
                                  /\ Do(Silence(Pre, x), [E0 EXCEPT !.op = "silence", !.s = x])
              /\ UNCHANGED wire
\* a packet carrying the queued challenge of slot x is sealed; the challenge is on the wire from now on
SendAct == /\ "send" \in OPS
           /\ \E x \in 1..NP : /\ c.t[x].id # 0 /\ c.t[x].sc
                               /\ Do(Send(Pre, x), [E0 EXCEPT !.op = "send", !.s = x])
                               /\ wire' = wire \cup {c.t[x].ch}
\* ok: the challenge answered left on the slot the answer arrives on; rep: it is not the outstanding one; rc: it is
\* one of the last CH drawn on that slot since its table was cleared
RespAct ==
    /\ "resp" \in OPS
    /\ \E id \in Ids, tok \in wire \cup {FORGED} : \E j \in {Learn(Pre, id).i} :
         LET held == j # 0 /\ c.t[j].id = id
         IN DoAny({Resp(Pre, id, tok, r) : r \in RTTS},
               [E0 EXCEPT !.op = "resp", !.id = id, !.s = j, !.tok = tok,
                          !.ok = (held /\ tok \in c.t[j].o),
                          !.rep = (held /\ tok # c.t[j].ch),
                          !.rc = (held /\ tok \in c.t[j].ps /\ Cardinality({u \in c.t[j].ps : u > tok}) < CH)])
    /\ UNCHANGED wire
ChalAct == /\ "chal" \in OPS
           /\ \E id \in Ids : DoAny({Chal(Pre, id, cb, rn, "once" \in OPS) : cb, rn \in BOOLEAN},
                                    [E0 EXCEPT !.op = "chal", !.id = id])
           /\ UNCHANGED wire
\* fol: follow_peer's rule says the active path moves to the packet's; sg: the packet's path was held and gone before
\* the step (read before it, since a step that forgets the slot would leave nothing to read)
DataAct ==
    /\ "data" \in OPS
    /\ \E id \in Ids, hi \in BOOLEAN, wake \in BOOLEAN : \E l \in {Learn(Pre, id)} :
         LET fol == hi /\ l.i # 0 /\ l.i # c.act
                    /\ ~l.c.t[l.i].gone
                    /\ (l.c.t[c.act].id = 0 \/ l.c.t[c.act].k = "r" \/ l.c.t[l.i].k = "d" \/ wake)
         IN DoAny({Data(Pre, id, hi, wake, fresh, rn, "once" \in OPS) : fresh, rn \in BOOLEAN},
               [E0 EXCEPT !.op = "data", !.id = id, !.s = l.i, !.hi = hi, !.fol = fol, !.pact = c.act,
                         !.wake = wake, !.sg = (l.i # 0 /\ l.c.t[l.i].gone)])
    /\ UNCHANGED wire
\* handle_timeout without fail_over: idle-out and the relay escape (d), then the probes that are due: those of F fire,
\* those of W wait, those of L were the last
Fires(d, thin) == UNION {UNION {{FireFrom(d, 1, F, W, L, thin) : L \in SUBSET F} : W \in SUBSET F}
                         : F \in SUBSET {x \in 1..NP : FireDue(d.t[x])}}
TimerAct ==
    /\ "timer" \in OPS
    /\ DoAny(UNION {UNION {Fires(d, thin) : d \in {Timers(Pre, thin, rn)}} : thin, rn \in BOOLEAN},
             [E0 EXCEPT !.op = "timer"])
    /\ UNCHANGED wire
\* run_recovery_timer with three probe timeouts in a row or more
FailAct ==
    /\ "failover" \in OPS
    /\ DoAny({FailOver(Pre, rn) : rn \in BOOLEAN},
             [E0 EXCEPT !.op = "failover", !.pact = c.act,
                        !.pd = (c.t[c.act].id # 0 /\ c.t[c.act].k = "d" /\ c.t[c.act].v),
                        !.pk = IF c.t[c.act].id = 0 THEN "none" ELSE c.t[c.act].k,
                        !.hr = (Fallbacks(c.t) # {})])
    /\ UNCHANGED wire
ReturnedAct == /\ "returned" \in OPS
               /\ \E id \in Ids : DoAny({Returned(Pre, id, r).c : r \in RTTS}, [E0 EXCEPT !.op = "returned", !.id = id])
               /\ UNCHANGED wire
\* the recovery's smoothed round trip moves (an acknowledgement)
MeasureAct == /\ "measure" \in OPS
              /\ \E r \in RTTS : Do([Pre EXCEPT !.srtt = r], [E0 EXCEPT !.op = "measure"])
              /\ UNCHANGED wire

Next == \/ AddAct \/ RebindAct \/ RemoveAct \/ LostAct \/ SetAct \/ InfoAct \/ ProbeAct \/ PunchAct
        \/ SilenceAct \/ SendAct \/ RespAct \/ ChalAct \/ DataAct \/ TimerAct \/ FailAct \/ ReturnedAct
        \/ MeasureAct
Spec == Init /\ [][Next]_vars

\* at most TMAX challenges drawn
Bound == c.hi <= TMAX

SlotOK(p) == /\ p.k \in {"d", "r"} /\ p.hd \in {"never", "fresh", "stale"} /\ p.nx \in 1..CH
             /\ p.ch \in 0..(TMAX + NP) /\ \A x \in 1..CH : p.sent[x] \in 0..(TMAX + NP)
             /\ (p.sc => p.ch # 0) /\ p.vl \in BOOLEAN
TypeOK == /\ c.act \in 1..NP
          /\ \A x \in 1..NP : SlotOK(c.t[x])
          /\ wire \subseteq 1..(TMAX + NP)

ActiveLive == c.t[c.act].id # 0
Unique == \A a, b \in 1..NP : (c.t[a].id # 0 /\ c.t[a].id = c.t[b].id) => a = b

InTable(p, tok) == \E x \in 1..CH : p.sent[x] = tok
SlotKept(p) == /\ p.ch # 0 => InTable(p, p.ch)
               /\ \A u \in p.ps : Cardinality({w \in p.ps : w > u}) < CH => InTable(p, u)
OutstandingKept == \A x \in 1..NP : SlotKept(c.t[x])

\* a gone path validated by a late answer may be forgotten in the same step (choose_path's forget_gone)
ReplacedKept == (ev.op = "resp" /\ ev.rc) => (c.t[ev.s].v \/ c.t[ev.s].id = 0)
AnswerOnPath == ev.op = "resp" => ev.nvd \subseteq (IF ev.ok THEN {ev.s} ELSE {})
ValidCause == \A x \in ev.nvd : (ev.op = "resp" /\ x = ev.s /\ ev.ok) \/ ev.op \in {"returned", "add", "info"}
FollowRule == ev.op = "data" => c.act = (IF ev.fol THEN ev.s ELSE ev.pact)
ChooseValid == c.mv = "choose" => Usable(c.t[c.act])
FallbackRule ==
    ev.op = "failover" =>
        IF ev.pk = "d"
        THEN /\ ev.pd => (~c.t[ev.pact].v /\ c.t[ev.pact].rj /\ c.t[ev.pact].pr)
             /\ c.act = (IF ev.hr THEN Last(Fallbacks(c.t)) ELSE ev.pact)
        ELSE c.act = ev.pact
LostRule ==
    ev.op = "lost" /\ ev.s # 0 =>
        /\ \A x \in 1..NP : (x # c.act /\ c.t[x].id # 0) => ~c.t[x].gone
        /\ c.t[ev.s].id = ev.id => (ev.s = c.act /\ c.t[ev.s].gone /\ ~c.t[ev.s].v)

\* The rules above that read a per-step ghost (ev, c.mv), as properties of every step. TLC checks an action property on
\* each step it takes, also on a step into a state already seen, so with the VIEW below, which folds the states that
\* differ only in those ghosts, every reachable state is still checked as the end of some step (Next reads neither ev
\* nor c.mv nor c.dg: it starts from Pre). At Init they hold as written (ev.op = "init", ev.nvd = {}, c.mv = "none").
ChooseValidStep == [][ChooseValid']_vars
FollowRuleStep == [][FollowRule']_vars
FallbackRuleStep == [][FallbackRule']_vars
LostRuleStep == [][LostRule']_vars
ValidCauseStep == [][ValidCause']_vars
\* what a step depends on: the connection without its per-step ghosts, and the wire
StepView == <<Pre, wire>>

\* The doc's claims (path.rs). DocValid is violated by the code in its witness config; RelayValid, DocFallback,
\* GoneLeft and GoneNeverBack hold with fixes T4 to T7.
\* module doc, invariants: "a direct path is validated only by an answer to a challenge sent to it"
DocValid == \A x \in ev.nvd : ev.op = "resp" /\ x = ev.s /\ ev.ok
\* module doc: "A relay path is valid from the moment the connection tracks it"
RelayValid == \A x \in 1..NP : (c.t[x].id # 0 /\ c.t[x].k = "r" /\ ~c.t[x].gone) => c.t[x].v
\* module doc (restated by T8): "the highest-numbered packet that carries STREAM, DATAGRAM or WAKE data moves the
\* active path to the path it came from, except that only a packet carrying WAKE moves it from a direct path onto a
\* relay path", and (with fix T6) "unless that path's local address is gone: a gone path is never followed" (a data
\* step changes no path's kind, so the kinds after it are the kinds before)
FollowsPeer == (ev.op = "data" /\ ev.hi /\ ev.s # 0 /\ ~ev.sg
                /\ ~(c.t[ev.pact].id # 0 /\ c.t[ev.pact].k = "d" /\ c.t[ev.s].k = "r" /\ ~ev.wake))
               => c.t[c.act].id = ev.id
\* module doc and fail_over: "After three probe timeouts in a row on a direct path ... the connection falls back to a
\* relay path if it has one"
\* (hr: a relayed path validated and not gone is held; a gone one can never be used, Path::gone)
DocFallback == (ev.op = "failover" /\ ev.pk = "d" /\ ev.hr) => c.t[c.act].k = "r"
\* path_lost: "the connection leaves it for the best validated path at once, or as soon as one validates"
GoneLeft == c.t[c.act].gone => Best(c.t) = 0
\* Path::gone: "nothing can use it again"
GoneNeverBack == ~c.t[c.act].lf
\* module doc (restated by T11): "from a relay the connection moves at once, otherwise only when the cheaper path's
\* round trip is more than 5 ms shorter" (dg: a move off a usable direct path for a round-trip gain of GAIN or less)
DocGain == ~c.dg

\* A validation challenge_path starts (follow_peer, challenge_back) is never left with nothing armed: until the path
\* is validated, lost or emptied, or its last probe has left, its challenge waits to leave or a probe is left, so a
\* lost challenge or a lost answer is sent again (bounded progress; "once" in OPS is the rule before, one challenge
\* never repeated: PathMove_w_once)
ValidationLive == \A x \in 1..NP : (c.t[x].vl /\ ~c.t[x].v) => (c.t[x].sc \/ c.t[x].pr)

\* Reach witnesses: an answer to a replaced challenge validates a path; a table that dropped a challenge drawn since it
\* was cleared; fail_over moving to a relayed path
NoReplacedAnswer == ~(ev.op = "resp" /\ ev.rep /\ ev.s \in ev.nvd)
NoWrap == \A x \in 1..NP : Cardinality(c.t[x].ps) <= CH
NoFallback == ~(ev.op = "failover" /\ ev.pd /\ c.t[c.act].k = "r")
\* a data packet with the highest number arrives on a held gone path that is not the active one (the case of T6)
NoGoneData == ~(ev.op = "data" /\ ev.hi /\ ev.sg /\ ev.s # ev.pact)
=============================================================================
