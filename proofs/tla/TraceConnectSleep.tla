--------------------------- MODULE TraceConnectSleep ---------------------------
(***************************************************************************)
(* Trace validation of a node's signing work and suspension: pinc-connect *)
(* client/signing.rs with suspend, resume, tick and drive.                 *)
(*                                                                         *)
(* The Rust test tests/trace_connect_sleep.rs brings a real Connectivity  *)
(* with one relay (UDP and TCP addresses) up to an open carrier in memory, *)
(* then calls suspend, resume, tick and drive with and without a wall     *)
(* clock, answers each signature request with the identity's signature, a *)
(* wrong-length one or a failure, asks for a record (set_hints) and ends  *)
(* the stream (stream_closed: the only node carrying the relay role is    *)
(* gone). Clocks jump forward and back and reach u64::MAX. After each call *)
(* it records the outstanding request's kind and relay, the link state,  *)
(* the sleep datagrams queued to the relay, the beacons queued to the     *)
(* local group, the SignFailed notices and the stream close requests.     *)
(* Every event must be a step of ConnectSleepOps.tla. What the record     *)
(* cannot show is chosen by the check: whether a record or beacon job     *)
(* could be built (a home and a class known), whether the publish time    *)
(* came, whether the beacon duty cycle asked, whether a resume's address  *)
(* refresh wanted a record. The publish schedule (pub) is left free, so   *)
(* it is not compared.                                                     *)
(*                                                                         *)
(* Times are microseconds from the clock at the first event; u64::MAX is  *)
(* written as 2147483647 (TMax). The code's close one nanosecond later is *)
(* the next microsecond here: the test reads whole microseconds.          *)
(* Relay 0 of the code is relay 1 here.                                    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_sleep.ndjson. *)
(***************************************************************************)
EXTENDS ConnectSleepOps, Json, IOUtils

K == [retry |-> 2000000, repub |-> 1800000000, tmax |-> 2147483647, never |-> -2000000000, udp |-> {1}, home |-> 1]

VARIABLES i, s
vars == <<i, s>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_sleep.ndjson")
Ev == Trace[i]

SetOfSeq(q) == {q[k] : k \in 1..Len(q)}

(* the first event is "init", read after the carrier opened: no request outstanding, a wall clock given, nothing
   owed; whether a record is wanted cannot be read *)
Init == /\ i = 1
        /\ \E rec \in BOOLEAN :
              s = [NewS({1}, K) EXCEPT !.wall = TRUE, !.record = rec, !.lk = [x \in {1} |-> "open"]]

Obs(W) == /\ W.s.job.k = Ev.job /\ W.s.job.r = Ev.jr
          /\ W.o.udp = Ev.udp /\ W.o.fails = Ev.fails /\ W.o.bcn = Ev.bcn /\ W.o.closes = SetOfSeq(Ev.closes)
          /\ s' = [W.s EXCEPT !.lk[1] = Ev.link] /\ i' = i + 1

InitE == /\ Ev.op = "init" /\ Ev.job = "none" /\ Ev.link = "open" /\ UNCHANGED s /\ i' = i + 1

CallE ==
    CASE Ev.op = "tick" ->
            \E pw \in BOOLEAN, rj \in BOOLEAN, bj \in BOOLEAN :
                (pw => ~RecordWanted(s)) /\ Obs(TickStep(W0(s), Ev.now, Ev.w, pw, rj, bj, K))
      [] Ev.op = "drive" ->
            \E pw \in BOOLEAN, rj \in BOOLEAN, bj \in BOOLEAN, rj2 \in BOOLEAN, bj2 \in BOOLEAN, bc \in BOOLEAN :
                /\ pw => ~RecordWanted(s) /\ bc => Ev.w
                /\ Obs(DriveStep(W0(s), Ev.now, Ev.w, pw, rj, bj, rj2, bj2, bc, K))
      [] Ev.op = "suspend" -> \E rj \in BOOLEAN, bj \in BOOLEAN : Obs(SuspendStep(W0(s), Ev.now, rj, bj, K))
      [] Ev.op = "resume" -> \E wr \in BOOLEAN : Obs(ResumeStep(W0(s), wr, K))
      [] Ev.op = "answer" -> \E rj \in BOOLEAN, bj \in BOOLEAN : Obs(SignResponse(W0(s), Ev.now, Ev.ok, rj, bj, K))
      [] Ev.op = "want" -> Obs(WantRecord(W0(s)))
      [] Ev.op = "link" -> Obs(LinkSet(W0(s), 1, Ev.link, Ev.now, K))
      [] OTHER -> FALSE

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (InitE \/ (Ev.op # "init" /\ CallE))) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of ConnectSleepOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
Inv == TRUE
=============================================================================
