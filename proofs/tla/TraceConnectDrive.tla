--------------------------- MODULE TraceConnectDrive ---------------------------
(***************************************************************************)
(* Trace validation of what drive does: pinc-connect client/drive.rs       *)
(* each_session, DIAL_PRUNE and the lookup asked again.                    *)
(*                                                                         *)
(* The Rust test tests/trace_connect_drive.rs drives a real Connectivity   *)
(* against an endpoint stub whose session statistics the test sets. Two   *)
(* kinds of run share the file.                                             *)
(*  A session run ("sinit") dials one peer, then changes the session's    *)
(*  statistics (resends, established, the route on a relay path or not,   *)
(*  probe timeouts, activity and round trip), arms the punch timer        *)
(*  (resume_all), makes the endpoint forget the session, and calls drive  *)
(*  at clocks before and after each timer. Each drive records the commands *)
(*  it sent for the session, in order, as EachSession names them after    *)
(*  CmdsSeen.                                                               *)
(*  A pending run ("pinit") dials up to 12 peers that have no record (each *)
(*  waits on the pending dials and asks for the record), makes the        *)
(*  endpoint forget some of their sessions, and calls drive; each event   *)
(*  records the number of lookups outstanding after it.                    *)
(* Every event must be a step of ConnectDriveOps.tla.                      *)
(*                                                                         *)
(* Times are microseconds from the clock of the run's first event.        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_drive.ndjson. *)
(***************************************************************************)
EXTENDS ConnectDriveOps, Json, IOUtils

VARIABLES i, sess, st, holds, gone, pd, lk, ended
vars == <<i, sess, st, holds, gone, pd, lk, ended>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_drive.ndjson")
Ev == Trace[i]

LOOKUPS == 16
WAITERS == 4
\* the drive's buffers of dropped and of asking peers hold as many peers as the lookup table (drive.rs)
BUF == LOOKUPS

\* last is the endpoint's last_app: a drive's idle is now - last_app (saturating), as each_session computes it
St0 == [est |-> FALSE, dialer |-> TRUE, retx |-> 0, pto |-> FALSE, rr |-> FALSE, valid |-> FALSE, idle |-> 0, rtt |-> 0,
        last |-> 0]

Init == /\ i = 1 /\ sess = NoSess /\ st = St0 /\ holds = FALSE /\ gone = FALSE
        /\ pd = NewPending(LOOKUPS, WAITERS) /\ lk = NewLookups(LOOKUPS) /\ ended = {}

Keep == UNCHANGED <<pd, lk, ended>>
KeepS == UNCHANGED <<sess, st, holds, gone>>

SInit == Ev.op = "sinit" /\ sess' = NoSess /\ st' = St0 /\ holds' = FALSE /\ gone' = FALSE /\ Keep

SDial == Ev.op = "dial" /\ sess' = DialSess(Ev.now, Ev.direct) /\ holds' = Ev.holds /\ UNCHANGED <<st, gone>> /\ Keep

SStats == /\ Ev.op = "stats"
          /\ st' = [est |-> Ev.est, dialer |-> Ev.dialer, retx |-> Ev.retx, pto |-> Ev.pto, rr |-> Ev.rr,
                    valid |-> Ev.valid, idle |-> 0, rtt |-> Ev.rtt, last |-> Ev.last]
          /\ UNCHANGED <<sess, holds, gone>> /\ Keep

\* resume_all arms the punch timer LINK_PUNCH (100 ms) out
SArm == Ev.op = "resume" /\ sess' = [sess EXCEPT !.punch = Ev.now + 100000] /\ UNCHANGED <<st, holds, gone>> /\ Keep

SGone == Ev.op = "gone" /\ gone' = TRUE /\ UNCHANGED <<sess, st, holds>> /\ Keep

\* the prune at the start of the drive leaves the pending dials of an established session
SDrive ==
    /\ Ev.op = "drive"
    /\ IF gone THEN Ev.cmds = <<>> /\ sess' = NoSess /\ UNCHANGED <<st, holds, gone>>
       ELSE LET h1 == holds /\ ~st.est
                r == EachSession(sess, [st EXCEPT !.idle = SatSub(Ev.now, st.last)], Ev.now, h1)
            IN CmdsSeen(r.cmds) = Ev.cmds /\ sess' = r.s /\ holds' = h1 /\ UNCHANGED <<st, gone>>
    /\ Keep

PInit == Ev.op = "pinit" /\ pd' = NewPending(LOOKUPS, WAITERS) /\ lk' = NewLookups(LOOKUPS) /\ ended' = {} /\ KeepS

PDial == /\ Ev.op = "pdial"
         /\ LET r == DialPending(pd, lk, Ev.peer, Ev.sid, Ev.now) IN pd' = r.P /\ lk' = r.T /\ LLen(r.T) = Ev.lookups
         /\ UNCHANGED ended /\ KeepS

PEnd == Ev.op = "pend" /\ ended' = ended \cup {Ev.sid} /\ UNCHANGED <<pd, lk>> /\ KeepS

PDrive == /\ Ev.op = "pdrive"
          /\ LET r == PruneDrive(pd, lk, ended, Ev.now, BUF) IN pd' = r.P /\ lk' = r.T /\ LLen(r.T) = Ev.lookups
          /\ UNCHANGED ended /\ KeepS

Step == /\ i' = i + 1
        /\ \/ SInit \/ SDial \/ SStats \/ SArm \/ SGone \/ SDrive
           \/ PInit \/ PDial \/ PEnd \/ PDrive

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ Step) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of ConnectDriveOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
Inv == TRUE
=============================================================================
