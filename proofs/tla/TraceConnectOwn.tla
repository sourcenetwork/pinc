---------------------------- MODULE TraceConnectOwn ----------------------------
(***************************************************************************)
(* Trace validation of the node's own record and address discovery:        *)
(* vinc-connect client/{conn,signing,timers,netcheck}.rs.                  *)
(*                                                                         *)
(* The Rust test tests/trace_connect_own.rs drives the real Connectivity   *)
(* (ten relay slots, local discovery off) through its public API: set_local*)
(* set_hints, probe_all and the probes of tick, QADR datagrams (valid,     *)
(* from the wrong address, with the wrong or a replayed nonce, malformed), *)
(* link_changed, tick with and without a wall clock (equal, higher and     *)
(* lower than the last), restore_record_seq (lower and higher than the     *)
(* last number), and the host's answers to the signature requests. After   *)
(* every call it records the candidate list the node offers; a restore     *)
(* records the last number after it; a call that starts a record job       *)
(* records the fields of the record to be signed. Every event must be the  *)
(* step the operators of ConnectOwnOps.tla compute: the same candidate     *)
(* list, an answer taken exactly when the operators take it, the same last *)
(* number, a job exactly when a record is wanted, none is outstanding and  *)
(* a wall clock is known, with the sequence number NextSeq gives (the      *)
(* clock, or one above the last number), the candidates of that moment and *)
(* the hints.                                                              *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds connect_own.ndjson.   *)
(***************************************************************************)
EXTENDS ConnectOwnOps, Json, IOUtils

VARIABLES i, cf, S, hints, want, jobout
vars == <<i, cf, S, hints, want, jobout>>

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/connect_own.ndjson")
Ev == Trace[i]

Init == /\ i = 1 /\ cf = [cap |-> 8, udp |-> <<0>>] /\ S = NewNode(cf) /\ hints = <<>> /\ want = FALSE /\ jobout = FALSE

\* the candidate list the node offered after the call
Offered(S1) == Ev.c = Cands(cf, S1)

Plain(S1) == /\ S' = S1 /\ Offered(S1) /\ UNCHANGED <<cf, hints, want, jobout>> /\ i' = i + 1

NewE == /\ Ev.t = "onew"
        /\ cf' = [cap |-> Ev.cap, udp |-> Ev.udp]
        /\ S' = NewNode(cf') /\ hints' = <<>> /\ want' = FALSE /\ jobout' = FALSE
        /\ Ev.c = Cands(cf', S') /\ i' = i + 1
LocalE == /\ Ev.t = "olocal" /\ Plain(SetLocal(cf, S, Ev.a))
ProbeE == /\ Ev.t = "oprobe" /\ Plain(ProbeAll(cf, S, Ev.n))
AnsE == /\ Ev.t = "oans"
        /\ LET o == Observe(cf, S, Ev.from, Ev.n, Ev.a) IN /\ o.took = (Ev.took = 1) /\ Plain(o.S)
RestartE == /\ Ev.t = "orestart" /\ Plain(Restart(S))
NoopE == /\ Ev.t = "onoop" /\ Plain(S)
SeqE == /\ Ev.t = "oseq" /\ Ev.last = RestoreSeq(S, Ev.n).last /\ Plain(RestoreSeq(S, Ev.n))
HintE == /\ Ev.t = "ohint"
         /\ IF Ev.ok = 1 THEN hints' = Ev.h /\ want' = TRUE ELSE hints' = hints /\ want' = want
         /\ UNCHANGED <<cf, jobout, S>> /\ Offered(S) /\ i' = i + 1

\* start_jobs after a tick or a signature answer: the job slot is free (jb), the record is wanted (w)
StartJobs(S1, w, jb) ==
    /\ UNCHANGED <<cf, hints>> /\ i' = i + 1 /\ Offered(S1)
    /\ IF ~jb /\ S1.wall # 0 /\ w
       THEN /\ want' = FALSE
            /\ IF Ev.hm # 0 /\ Ev.cl # 0
               THEN LET j == RecordJob(cf, S1, Ev.hm, Ev.cl, hints) IN
                    /\ Ev.j = 1 /\ Ev.seq = j.seq /\ Ev.home = j.home /\ Ev.reach = j.reach /\ Ev.a = j.addrs /\ Ev.h = j.hints
                    /\ jobout' = TRUE /\ S' = Built(S1, j)
               ELSE Ev.j = 0 /\ jobout' = FALSE /\ S' = S1
       ELSE Ev.j = 0 /\ want' = w /\ jobout' = jb /\ S' = S1

TickE == /\ Ev.t = "otick" /\ StartJobs(Tick(S, Ev.w), want, jobout)
SignE == /\ Ev.t = "osign" /\ jobout /\ StartJobs(S, want, FALSE)

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (NewE \/ LocalE \/ ProbeE \/ AnsE \/ RestartE \/ NoopE \/ SeqE \/ HintE \/ TickE \/ SignE)) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of ConnectOwnOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
Inv == TRUE
=============================================================================
