--------------------------- MODULE TracePathMove ---------------------------
(***************************************************************************)
(* Trace validation of path validation and migration: pinc-transport       *)
(* conn/path.rs, the path part of conn/recv.rs (process_payload,           *)
(* follow_peer, on_frame), conn/send.rs fill_path, conn/timer.rs           *)
(* handle_timeout (run_recovery_timer's fail_over, on_path_timers).        *)
(*                                                                         *)
(* The Rust test tests/trace_path_move.rs drives the dialing side of real  *)
(* established sessions: the host adds (direct and relayed paths: a        *)
(* relayed path runs through a node that carries the relay role), rebinds, *)
(* removes, loses, activates, renames and probes paths and hands back      *)
(* re-joined ones; packets that opened are handed to it on any path        *)
(* (inject_payload): answers to its real challenges, to replaced ones,     *)
(* forged ones, on the wrong path and after a rebind, challenges, and data *)
(* with and without WAKE, the highest numbered or older; its timers run at *)
(* chosen instants (the 15 s silence and one nanosecond past it, probes    *)
(* due, the third probe timeout in a row and later ones, thin and not);    *)
(* its packets are built and thrown away. Every call is recorded with the  *)
(* path table before and after it (Connection::trace_paths), and each must *)
(* be the step the operators of PathMoveOps.tla compute: the table before  *)
(* the call must be the model's, aged by the clock (a heard path may have  *)
(* gone silent, nothing else changes between calls), and the table after  *)
(* it must be the model's result. What the model leaves to time is chosen  *)
(* by TLC within the recorded step: which probes were due, which waited    *)
(* for their floor or were the last, whether a thin session's challenge    *)
(* was recent, which queued challenges left in a packet.                   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds path_move.ndjson.     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
CONSTANTS NP, CH, GAIN, PEN, BONUS
VARIABLES i, c
vars == <<i, c>>
INSTANCE PathMoveOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/path_move.ndjson")
Ev0 == Trace[i]

\* a u64 written as four 16-bit limbs, low first; the test keeps every round trip below 2^30 ns, so a cost fits in
\* TLC's integers
V(l) == IF l[3] = 0 /\ l[4] = 0 /\ l[2] < 16384 THEN l[1] + 65536 * l[2]
        ELSE Assert(FALSE, "a round trip of 2^30 ns or more in the trace")
SrttOf(w) == IF w.smp THEN V(w.srtt) ELSE -1

\* the model's slot of a recorded one (the ghosts start empty)
SlotOf(s) ==
    IF s.id = 0 THEN None
    ELSE [id |-> s.id, k |-> s.k, six |-> s.six, v |-> s.v, ch |-> s.ch, sent |-> [y \in 1..CH |-> s.sent[y]],
          nx |-> s.nx, sc |-> s.sc, pr |-> s.pr, rj |-> s.rj, gone |-> s.gone, hd |-> s.hd, r |-> V(s.r),
          o |-> {}, ps |-> {}, lf |-> FALSE]
Toks(w) == UNION {{w.paths[y].ch} \cup {w.paths[y].sent[z] : z \in 1..CH} : y \in 1..NP}
\* tokens are numbered by the test in the order they first appear, so the last drawn is the largest
FromView(w) == [t |-> [y \in 1..NP |-> SlotOf(w.paths[y])], act |-> w.act, srtt |-> SrttOf(w),
                hi |-> Last(Toks(w)), mv |-> "none", dg |-> FALSE]

SlotEq(p, s) == /\ p.k = s.k /\ p.six = s.six /\ p.v = s.v /\ p.ch = s.ch
                /\ \A z \in 1..CH : p.sent[z] = s.sent[z]
                /\ p.nx = s.nx /\ p.sc = s.sc /\ p.pr = s.pr /\ p.rj = s.rj /\ p.gone = s.gone /\ p.hd = s.hd
                /\ p.r = V(s.r)
Same(x, w) == /\ \A y \in 1..NP : x.t[y].id = w.paths[y].id /\ (x.t[y].id # 0 => SlotEq(x.t[y], w.paths[y]))
              /\ x.act = w.act

\* between calls only the clock moves: a heard path may have gone silent; the smoothed round trip is the recorded one
Age(x, w) ==
    [x EXCEPT !.t = [y \in 1..NP |-> IF x.t[y].id # 0 /\ x.t[y].hd = "fresh" /\ w.paths[y].hd = "stale"
                                    THEN [x.t[y] EXCEPT !.hd = "stale"] ELSE x.t[y]],
              !.srtt = SrttOf(w), !.mv = "none", !.dg = FALSE]
C1 == Age(c, Ev0.pre)
Check(nc) == Same(C1, Ev0.pre) /\ c' = nc /\ Same(nc, Ev0.post)

\* the dialing side of a session just established: path 1, direct, validated, active
C00 == [t |-> [y \in 1..NP |-> IF y = 1 THEN [New(1, "d", FALSE, "fresh") EXCEPT !.v = TRUE] ELSE None],
        act |-> 1, srtt |-> -1, hi |-> 0, mv |-> "none", dg |-> FALSE]

\* the queued challenges of the slots in S left in packets
SendSet(x, S) ==
    [x EXCEPT !.t = [y \in 1..NP |-> IF y \in S THEN [x.t[y] EXCEPT !.o = @ \cup {x.t[y].ch}, !.sc = FALSE]
                                    ELSE x.t[y]]]
\* what inject_payload returns: Drop::NoPath when the table has no room for the packet's path
Rr(id) == IF Learn(C1, id).i = 0 THEN "nopath" ELSE "ok"

InitEv == Ev0.op = "init" /\ Ev0.np = NP /\ c' = FromView(Ev0.post)
AddEv == Ev0.op = "add" /\ LET a == AddPath(C1, Ev0.id, Ev0.k, Ev0.six, TRUE) IN a.r = Ev0.r /\ Check(a.c)
RebindEv == Ev0.op = "rebind" /\ LET a == Rebind(C1, Ev0.id, Ev0.nid) IN a.r = Ev0.r /\ Check(a.c)
RemoveEv == Ev0.op = "remove" /\ LET a == Remove(C1, Ev0.id) IN a.r = Ev0.r /\ Check(a.c)
LostEv == Ev0.op = "lost" /\ LET a == Lost(C1, Ev0.id) IN a.r = Ev0.r /\ Check(a.c)
SetEv == Ev0.op = "set" /\ LET a == SetActive(C1, Ev0.id) IN a.r = Ev0.r /\ Check(a.c)
InfoEv == Ev0.op = "info" /\ Check(SetInfo(C1, Ev0.id, Ev0.k, Ev0.six))
ProbeEv == Ev0.op = "probe" /\ LET a == Probe(C1, Ev0.id, TRUE) IN a.r = Ev0.r /\ Check(a.c)
PunchEv == Ev0.op = "punch" /\ Check(PunchKnown(C1, TRUE))
ReturnedEv == Ev0.op = "returned" /\ LET a == Returned(C1, Ev0.id, V(Ev0.rtt)) IN a.ok = Ev0.r /\ Check(a.c)
\* rtt: the round trip the code reads, the time since a datagram last left on the slot (0 if none ever did)
RespEv == Ev0.op = "resp" /\ Rr(Ev0.id) = Ev0.r /\ Check(Resp(C1, Ev0.id, Ev0.tok, V(Ev0.rtt)))
\* challenge_back and follow_peer read the host's declaration (decl), the timers the session's thinness (thin)
ChalEv == /\ Ev0.op = "chal" /\ Rr(Ev0.id) = Ev0.r
          /\ \E cb \in (IF Ev0.pre.decl THEN {FALSE} ELSE BOOLEAN) : Check(Chal(C1, Ev0.id, cb, TRUE))
DataEv == /\ Ev0.op = "data" /\ Rr(Ev0.id) = Ev0.r
          /\ \E fresh \in (IF Ev0.pre.decl THEN BOOLEAN ELSE {FALSE}) : Check(Data(C1, Ev0.id, Ev0.hi, Ev0.wake, fresh, TRUE))
SendEv == Ev0.op = "send" /\ \E S \in SUBSET {y \in 1..NP : C1.t[y].id # 0 /\ C1.t[y].sc} : Check(SendSet(C1, S))
\* handle_timeout: fail_over when the probe timeouts in a row (after the call) are 3 or more, then on_path_timers
TimerEv ==
    /\ Ev0.op = "timer"
    /\ LET a == IF Ev0.post.pto >= 3 THEN FailOver(C1, TRUE) ELSE C1
           d == Timers(a, Ev0.pre.thin, TRUE)
       IN \E F \in SUBSET {y \in 1..NP : FireDue(d.t[y])} : \E W \in SUBSET F, L \in SUBSET F :
             Check(FireFrom(d, 1, F, W, L, Ev0.pre.thin))

Init == i = 1 /\ c = C00
Step == /\ i <= Len(Trace) /\ Ev0.t = "pm"
        /\ \/ InitEv \/ AddEv \/ RebindEv \/ RemoveEv \/ LostEv \/ SetEv \/ InfoEv \/ ProbeEv \/ PunchEv
           \/ ReturnedEv \/ RespEv \/ ChalEv \/ DataEv \/ SendEv \/ TimerEv
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the active path is held, no path is held twice, and a choice moves only onto a usable path, throughout
Inv == /\ c.t[c.act].id # 0
       /\ \A a, b \in 1..NP : (c.t[a].id # 0 /\ c.t[a].id = c.t[b].id) => a = b
       /\ c.mv = "choose" => Usable(c.t[c.act])
=============================================================================
