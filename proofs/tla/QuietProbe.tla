------------------------------ MODULE QuietProbe ------------------------------
(***************************************************************************)
(* The quiet-parent probe (QUIET_PROBE): pinc-core sub.rs (open_probe,     *)
(* ride_probes, resolve_probe, end_probe, keep_flight_paths, apply_flight),*)
(* timers.rs (the gate of settle_core, the probe block of run_timer) and   *)
(* commands.rs (connect, the flight commands and Query::Stats on a probing *)
(* id), for one peer, one parent slot and the dials W of that peer, each   *)
(* for its own protocol.                                                   *)
(*                                                                         *)
(* A dial to a peer whose live session was not heard within PARENT_RX     *)
(* (a quiet parent) holds an id and no connection and makes the session    *)
(* challenge its path; at most MaxW (MAX_WAITERS) dials probe one session. A packet back *)
(* on the session (the gate: heard while the probed mark stands) takes the *)
(* mark and resolves every probe of that session in one pass of at most    *)
(* MaxW steps; the probe's deadline (its timer) resolves it alone. A       *)
(* resolution rides a live session of the peer when one is heard (the     *)
(* ride's parts may fail: it then lapses; its build may fail: the dial     *)
(* ends), else lapses: it closes the probed session only when it is the    *)
(* generation probed, was quiet when the probe began (no pulse, nothing in *)
(* flight) and is still no pulse session, still unheard, nothing in        *)
(* flight; then it waits on another dial's running handshake when there is *)
(* one (N2), else flies to the caller's first address, else to the        *)
(* session's learned one, else fails. FlightPaths, FirstResend and         *)
(* HoldFlight on a probing id are kept, the latest of each kind (B1), and  *)
(* applied once to the connection the dial gets (ride, lapse or wait) in   *)
(* the order of apply_flight: paths, resend, hold (only when the latest    *)
(* hold is true). A dropped dial (Close while probing) ends it.            *)
(*                                                                         *)
(* The parent is the environment: heard (a packet came back, maybe an     *)
(* acknowledgement that empties the flight), quiet again (PARENT_RX passes *)
(* without one: only with no probe running, as a probe's window, two probe *)
(* timeouts or the configured one, is shorter), a pulse on or off, a send, *)
(* the flight declared lost, the slot reused by a session of a new         *)
(* generation (of this peer or another, heard or not). A send is the       *)
(* application's: the probe's own challenge is never in flight in the code.*)
(* A dial's fresh handshake is not completed in the model.                 *)
(*                                                                         *)
(* Properties: OneOutcome (a dial rides, flies, waits or ends, never two   *)
(* of them), LapseClosesOnlyItsOwn (B2, the generation check, the still-   *)
(* unheard check), StashOnce (B1: every kept command applied exactly once, *)
(* at the resolution, only when the dial got a connection), QueryAnswered  *)
(* (B1: Stats answers a probing id), NoStuck (after the pass no probe of a *)
(* heard session is left), Frames (B3: the pass never nests), MarkExact    *)
(* (the probed mark stands exactly while probes of the session run),       *)
(* OneRoot (N2: one handshake at a time for dials that probed or waited),  *)
(* CallerFirst (decision 4); under fairness of the timers Resolves (every  *)
(* probe ends).                                                            *)
(* Configs: QuietProbe.cfg (two dials, the slot reused once), _stash (one  *)
(* dial, three commands of every kind), _bound (three dials, two may       *)
(* probe), _live (Resolves); witnesses _w_close, _w_ride, _w_wait,         *)
(* _w_learned, _w_stash. The trace check is TraceQuietProbe.tla.           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences, TLC
CONSTANTS W, MaxW, MaxGen, MaxCmd, Cmds
VARIABLES wt, par, mark, pass, depth, closes, sent
vars == <<wt, par, mark, pass, depth, closes, sent>>

\* a dial: st, the generation it probed, quiet at its start as the code reads it (q0) and as it was (s0), whether
\* the caller gave a routable address, what its flight flies to first, the kept commands (stash, and kept: the ghost
\* of what the caller sent while it probed), the commands applied from the stash in order, its outcomes
Idle == [st |-> "idle", pg |-> 0, q0 |-> FALSE, s0 |-> FALSE, gave |-> FALSE, first |-> "-",
         stash |-> {}, kept |-> {}, got |-> <<>>, out |-> {}]
Holds == {"riding", "flying", "waiting"}

Kind(c) == IF c \in {"hold", "unhold"} THEN "hold" ELSE c
Keep(s, c) == {x \in s : Kind(x) # Kind(c)} \cup {c}
\* apply_flight: the latest FlightPaths, the latest FirstResend, then HoldFlight only when the latest is true
Applied(s) == (IF "paths" \in s THEN <<"paths">> ELSE <<>>) \o (IF "resend" \in s THEN <<"resend">> ELSE <<>>)
              \o (IF "hold" \in s THEN <<"hold">> ELSE <<>>)

Probes == {w \in W : wt[w].st = "probing" /\ wt[w].pg = par.gen}       \* probes_of(parent)
Flying == {w \in W : wt[w].st = "flying"}                                \* find_waiting_parent's candidates
Live == par.ours /\ ~par.closed /\ par.heard                             \* find_parent
QuietLive == par.ours /\ ~par.closed /\ ~par.heard                       \* find_quiet_parent, before its bound

\* Query::Stats: a session for an id with a connection, a not-established dial for a probing id
Answer(w) == IF wt[w].st \in Holds THEN "session" ELSE IF wt[w].st = "probing" THEN "dial" ELSE "none"

\* resolve_probe of dial w; r: the ride's parts and build both work ("ok"), the parts fail ("parts"), the build
\* fails ("build")
Rides(w, r) == Live /\ r # "parts"
Closes(w) == /\ wt[w].q0 /\ par.gen = wt[w].pg
             /\ ~par.closed /\ ~par.pulse /\ ~par.heard /\ ~par.infl
FirstOf(w) == IF Flying # {} THEN "wait"
              ELSE IF wt[w].gave THEN "caller"
              ELSE IF par.gen = wt[w].pg THEN "learned"
              ELSE "none"
After(w, r) ==
    LET x == wt[w] IN
    IF Rides(w, r) /\ r = "ok"
    THEN [x EXCEPT !.st = "riding", !.stash = {}, !.got = x.got \o Applied(x.stash), !.out = @ \cup {"ride"}]
    ELSE IF Rides(w, r)
    THEN [x EXCEPT !.st = "ended", !.stash = {}, !.out = @ \cup {"fail"}]
    ELSE LET f == FirstOf(w) IN
         [x EXCEPT !.st = (IF f = "wait" THEN "waiting" ELSE IF f = "none" THEN "ended" ELSE "flying"),
                   !.first = f, !.stash = {},
                   !.got = (IF f = "none" THEN x.got ELSE x.got \o Applied(x.stash)),
                   !.out = @ \cup {IF f = "wait" THEN "wait" ELSE IF f = "none" THEN "fail" ELSE "fly"}]
Resolve(w, r) ==
    LET c == ~Rides(w, r) /\ Closes(w) IN
    /\ wt' = [wt EXCEPT ![w] = After(w, r)]
    /\ par' = IF c THEN [par EXCEPT !.closed = TRUE] ELSE par
    /\ closes' = IF c THEN closes \cup {[w |-> w, gen |-> par.gen, pg |-> wt[w].pg, pulse |-> par.pulse,
                                         heard |-> par.heard, infl |-> par.infl, s0 |-> wt[w].s0]}
                 ELSE closes
\* recompute_probed after w no longer probes
Recompute(w) == \E v \in W \ {w} : wt[v].st = "probing" /\ wt[v].pg = par.gen

Init == /\ wt = [w \in W |-> Idle]
        /\ par = [gen |-> 1, ours |-> TRUE, closed |-> FALSE, pulse |-> FALSE, heard |-> FALSE, infl |-> FALSE]
        /\ mark = FALSE /\ pass = 0 /\ depth = 0 /\ closes = {} /\ sent = 0

\* connect: ride a heard session, wait on a running handshake, probe a quiet session, else a fresh dial
Dial(w, g) ==
    LET x == [wt[w] EXCEPT !.gave = g] IN
    /\ pass = 0 /\ wt[w].st = "idle"
    /\ IF QuietLive /\ Flying = {} /\ Cardinality(Probes) < MaxW
       THEN /\ wt' = [wt EXCEPT ![w] = [x EXCEPT !.st = "probing", !.pg = par.gen,
                                         !.q0 = ~par.pulse /\ ~par.infl, !.s0 = ~par.pulse /\ ~par.infl]]
            /\ mark' = TRUE
       ELSE /\ wt' = [wt EXCEPT ![w] =
                         IF Live THEN [x EXCEPT !.st = "riding", !.out = {"ride0"}]
                         ELSE IF Flying # {} THEN [x EXCEPT !.st = "waiting", !.out = {"wait0"}]
                         ELSE IF g THEN [x EXCEPT !.st = "flying", !.first = "caller", !.out = {"fly0"}]
                         ELSE [x EXCEPT !.st = "ended", !.out = {"fail0"}]]
            /\ UNCHANGED mark
    /\ UNCHANGED <<par, pass, depth, closes, sent>>

\* FlightPaths, FirstResend or HoldFlight on the dial's id: kept while it probes, else the connection's
Cmd(w, c) ==
    /\ pass = 0 /\ sent < MaxCmd /\ wt[w].st \in Holds \cup {"probing"}
    /\ sent' = sent + 1
    /\ wt' = IF wt[w].st = "probing"
             THEN [wt EXCEPT ![w].stash = Keep(@, c), ![w].kept = Keep(@, c)]
             ELSE wt
    /\ UNCHANGED <<par, mark, pass, depth, closes>>

\* the probe's deadline: run_timer resolves it, then recomputes the mark of the session it probed while it stands
Timer(w, r) ==
    /\ pass = 0 /\ wt[w].st = "probing"
    /\ Resolve(w, r)
    /\ mark' = IF wt[w].pg = par.gen /\ mark THEN Recompute(w) ELSE mark
    /\ UNCHANGED <<pass, depth, sent>>

\* Close on a probing id: end_probe
Cancel(w) ==
    /\ pass = 0 /\ wt[w].st = "probing"
    /\ wt' = [wt EXCEPT ![w].st = "ended", ![w].stash = {}, ![w].out = @ \cup {"cancel"}]
    /\ mark' = Recompute(w)
    /\ UNCHANGED <<par, pass, depth, closes, sent>>

\* a packet back on the session, maybe an acknowledgement that empties its flight; the settle after it runs the
\* gate when the mark stands: ride_probes takes the mark and runs a pass of at most MaxW resolutions
Hear(ack) ==
    /\ pass = 0 /\ par.ours /\ ~par.closed
    /\ par' = [par EXCEPT !.heard = TRUE, !.infl = IF ack THEN FALSE ELSE @]
    /\ IF mark THEN mark' = FALSE /\ pass' = MaxW + 1 /\ depth' = 1 ELSE UNCHANGED <<mark, pass, depth>>
    /\ UNCHANGED <<wt, closes, sent>>
\* one turn of the pass (pass = k + 1: k turns left); a ride settles the parent, which would run the gate again
\* inside the ride while the mark stood
PassStep(w, r) ==
    /\ pass >= 2 /\ w \in Probes
    /\ Resolve(w, r)
    /\ pass' = pass - 1
    /\ depth' = IF Rides(w, r) /\ r = "ok" /\ mark /\ par.heard /\ (Probes \ {w}) # {} THEN depth + 1 ELSE depth
    /\ UNCHANGED <<mark, sent>>
PassEnd ==
    /\ pass >= 1 /\ (pass = 1 \/ Probes = {})
    /\ pass' = 0 /\ depth' = 0
    /\ UNCHANGED <<wt, par, mark, closes, sent>>

\* the environment of the parent
Quiet == /\ pass = 0 /\ par.heard /\ \A w \in W : wt[w].st # "probing"
         /\ par' = [par EXCEPT !.heard = FALSE] /\ UNCHANGED <<wt, mark, pass, depth, closes, sent>>
Pulse(b) == /\ pass = 0 /\ par.ours /\ ~par.closed /\ par.pulse # b
            /\ par' = [par EXCEPT !.pulse = b] /\ UNCHANGED <<wt, mark, pass, depth, closes, sent>>
Send == /\ pass = 0 /\ par.ours /\ ~par.closed /\ ~par.infl
        /\ par' = [par EXCEPT !.infl = TRUE] /\ UNCHANGED <<wt, mark, pass, depth, closes, sent>>
Lost == /\ pass = 0 /\ par.infl
        /\ par' = [par EXCEPT !.infl = FALSE] /\ UNCHANGED <<wt, mark, pass, depth, closes, sent>>
Replace(o, h) ==
    /\ pass = 0 /\ par.gen < MaxGen
    /\ par' = [gen |-> par.gen + 1, ours |-> o, closed |-> FALSE, pulse |-> FALSE, heard |-> h, infl |-> FALSE]
    /\ mark' = FALSE
    /\ UNCHANGED <<wt, pass, depth, closes, sent>>

Rs == {"ok", "parts", "build"}
Next == \/ \E w \in W, g \in BOOLEAN : Dial(w, g)
        \/ \E w \in W, c \in Cmds : Cmd(w, c)
        \/ \E w \in W, r \in Rs : Timer(w, r) \/ PassStep(w, r)
        \/ \E w \in W : Cancel(w)
        \/ \E ack \in BOOLEAN : Hear(ack)
        \/ PassEnd \/ Quiet \/ Send \/ Lost
        \/ \E b \in BOOLEAN : Pulse(b)
        \/ \E o, h \in BOOLEAN : Replace(o, h)
Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(PassEnd)
            /\ \A w \in W : WF_vars(\E r \in Rs : Timer(w, r)) /\ WF_vars(\E r \in Rs : PassStep(w, r))

OneOutcome == \A w \in W : Cardinality(wt[w].out) <= 1
LapseClosesOnlyItsOwn ==
    \A c \in closes : c.gen = c.pg /\ ~c.pulse /\ ~c.heard /\ ~c.infl /\ c.s0
StashOnce == \A w \in W :
    /\ wt[w].stash # {} => wt[w].st = "probing"
    /\ wt[w].got # <<>> => wt[w].out \cap {"ride", "fly", "wait"} # {}
    /\ wt[w].out \cap {"ride", "fly", "wait"} # {} => wt[w].got = Applied(wt[w].kept)
QueryAnswered == \A w \in W : wt[w].st \in Holds \cup {"probing"} => Answer(w) # "none"
NoStuck == pass = 0 => \A w \in W : wt[w].st = "probing" => ~(wt[w].pg = par.gen /\ Live)
Frames == depth <= 1
MarkExact == pass = 0 => (mark <=> Probes # {})
OneRoot == Cardinality(Flying) <= 1
CallerFirst == \A w \in W : wt[w].st = "flying" /\ wt[w].gave => wt[w].first = "caller"
Inv == OneOutcome /\ LapseClosesOnlyItsOwn /\ StashOnce /\ QueryAnswered /\ NoStuck /\ Frames /\ MarkExact
       /\ OneRoot /\ CallerFirst

Perms == Permutations(W)

Resolves == \A w \in W : wt[w].st = "probing" ~> wt[w].st # "probing"

\* witnesses: each must be violated, so the model reaches what it claims about
NoLapseClose == closes = {}
NoProbeRide == \A w \in W : "ride" \notin wt[w].out
NoStashApplied == \A w \in W : wt[w].got = <<>>
NoLapseWait == \A w \in W : "wait" \notin wt[w].out
NoLearnedFirst == \A w \in W : wt[w].first # "learned"
=============================================================================
