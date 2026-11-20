--------------------------- MODULE TraceQuietProbe ---------------------------
(***************************************************************************)
(* Trace validation of the quiet-parent probe: the recorded steps of real  *)
(* endpoints must be a behaviour of QuietProbe.tla.                        *)
(*                                                                         *)
(* One ndjson line per step (core/quiet_probe.ndjson), "t" "qp", "ev" the  *)
(* step, "w" the dial (the test's own number, 1, 2, ... in the order of    *)
(* its Connect calls; 0 for none). A line that reads the probed session    *)
(* (dial, hear, ride, lapse, fail) carries what the code read of the slot  *)
(* the probe names: "gen" its generation, "ours" whether it is a session   *)
(* of the dial's peer, "pulse", "heard" (heard within PARENT_RX), "infl"   *)
(* (something in flight). Those facts are the environment: before the     *)
(* line, the replay sets the parent to them by a step of the model's       *)
(* environment (a new generation is the slot reused; a session heard       *)
(* while the probed mark stands must come as a hear line, the gate). Then *)
(* the line is the model's step:                                           *)
(*  - start: a new run, every dial idle, no parent yet;                    *)
(*  - dial: Connect, "gave" (the caller gave a routable address), "out"    *)
(*    probe (a probe started), fail (Connect refused) or other;            *)
(*  - cmd: FlightPaths ("paths"), FirstResend ("resend"), HoldFlight true  *)
(*    or false ("hold", "unhold") on the dial's id, "kept" when the id was *)
(*    probing;                                                             *)
(*  - stats: Query::Stats on the id, "ans" dial (a probing dial), session  *)
(*    or none;                                                             *)
(*  - hear: the gate fired (a packet back while the mark stood);           *)
(*  - ride, lapse, fail: a probe resolved, in the gate's pass or at its    *)
(*    deadline; "applied" the commands apply_flight applied, in order;     *)
(*    lapse: "closed" (the probed session closed), "first" what the flight *)
(*    flies to first (caller, learned, wait: another dial's handshake,     *)
(*    none: the dial failed); fail: the ride's build failed;               *)
(*  - end: Close on the probing id.                                        *)
(* The invariants of QuietProbe.tla hold in every state of the replay.     *)
(*                                                                         *)
(* Limits: one session of the peer at a time (the model has one parent     *)
(* slot), so a run never has the peer's live session in another slot than *)
(* the one probed. Needs the TLA+ CommunityModules (Json, IOUtils) and the *)
(* environment variable PINC_TRACE_DIR.                                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd
VARIABLES i, ph, wt, par, mark, pass, depth, closes, sent
mvars == <<wt, par, mark, pass, depth, closes, sent>>
tvars == <<i, ph, wt, par, mark, pass, depth, closes, sent>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/core/quiet_probe.ndjson")
Ws == {Trace[k].w : k \in 1..Len(Trace)} \ {0}
Big == 1073741824
QP == INSTANCE QuietProbe WITH W <- Ws, MaxW <- 8, MaxGen <- Big, MaxCmd <- Big,
                               Cmds <- {"paths", "resend", "hold", "unhold"}
Ev == Trace[i]
Facts == "gen" \in DOMAIN Ev
NoParent == [gen |-> -1, ours |-> FALSE, closed |-> TRUE, pulse |-> FALSE, heard |-> FALSE, infl |-> FALSE]

Reset == /\ wt' = [w \in Ws |-> QP!Idle] /\ par' = NoParent
         /\ mark' = FALSE /\ pass' = 0 /\ depth' = 0 /\ closes' = {} /\ sent' = 0

\* the environment's step before a line: the parent becomes what the code read (QuietProbe's Replace, Hear without
\* the gate, Quiet, Pulse, Send, Lost); a hear line's own hearing is the line's step
SetFacts ==
    LET hd == IF Ev.ev = "hear" THEN Ev.gen = par.gen /\ par.heard ELSE Ev.heard IN
    IF Ev.gen # par.gen
    THEN /\ Ev.gen > par.gen
         /\ par' = [gen |-> Ev.gen, ours |-> Ev.ours, closed |-> FALSE, pulse |-> Ev.pulse, heard |-> hd,
                    infl |-> Ev.infl]
         /\ mark' = FALSE
    ELSE /\ Ev.ours = par.ours
         /\ (hd /\ ~par.heard) => ~mark
         /\ (~hd /\ par.heard) => \A w \in Ws : wt[w].st # "probing"
         /\ par' = [par EXCEPT !.pulse = Ev.pulse, !.heard = hd, !.infl = Ev.infl]
         /\ UNCHANGED mark
EnvStep ==
    /\ ph = "env" /\ i <= Len(Trace) /\ Ev.t = "qp"
    /\ pass > 0 => Ev.ev \in {"ride", "lapse", "fail"}
    /\ IF pass > 0 \/ ~Facts \/ Ev.ev = "start" THEN UNCHANGED <<par, mark>> ELSE SetFacts
    /\ ph' = "act"
    /\ UNCHANGED <<i, wt, pass, depth, closes, sent>>

Resolution(r) == QP!PassStep(Ev.w, r) \/ QP!Timer(Ev.w, r)
DialOut == CASE Ev.out = "probe" -> wt'[Ev.w].st = "probing"
             [] Ev.out = "fail" -> wt'[Ev.w].st = "ended"
             [] Ev.out = "other" -> wt'[Ev.w].st \in QP!Holds
             [] OTHER -> FALSE
ActStep ==
    /\ ph = "act"
    /\ CASE Ev.ev = "start" -> Reset
         [] Ev.ev = "dial" -> QP!Dial(Ev.w, Ev.gave) /\ DialOut
         [] Ev.ev = "cmd" -> QP!Cmd(Ev.w, Ev.c) /\ (wt[Ev.w].st = "probing") = Ev.kept
         [] Ev.ev = "stats" -> UNCHANGED mvars /\ QP!Answer(Ev.w) = Ev.ans
         [] Ev.ev = "hear" -> \E ack \in BOOLEAN : QP!Hear(ack) /\ pass' > 0
         [] Ev.ev = "ride" -> Resolution("ok") /\ wt'[Ev.w].st = "riding" /\ wt'[Ev.w].got = Ev.applied
         [] Ev.ev = "lapse" -> \E r \in {"ok", "parts"} :
                                  /\ Resolution(r) /\ wt'[Ev.w].first = Ev.first
                                  /\ (closes' # closes) = Ev.closed /\ wt'[Ev.w].got = Ev.applied
         [] Ev.ev = "fail" -> Resolution("build") /\ "fail" \in wt'[Ev.w].out
         [] Ev.ev = "end" -> QP!Cancel(Ev.w)
         [] OTHER -> FALSE
    /\ i' = i + 1 /\ ph' = "env"
\* the end of a gate's pass is no line: the loop stops when no probe of the session is left or after MaxW turns
PassEnds == ph = "env" /\ QP!PassEnd /\ UNCHANGED <<i, ph>>
Finished == i > Len(Trace) /\ pass = 0 /\ UNCHANGED tvars

Init == /\ i = 1 /\ ph = "env" /\ wt = [w \in Ws |-> QP!Idle] /\ par = NoParent
        /\ mark = FALSE /\ pass = 0 /\ depth = 0 /\ closes = {} /\ sent = 0
TNext == EnvStep \/ ActStep \/ PassEnds \/ Finished
TraceSpec == Init /\ [][TNext]_tvars

Inv == QP!Inv
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
