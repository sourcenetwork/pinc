-------------------------- MODULE TracePortMapLease --------------------------
(***************************************************************************)
(* Trace validation of the lease of one port mapping (pinc-portmap         *)
(* client.rs, PortMap, over PCP) against PortMapLease.tla.                 *)
(*                                                                         *)
(* The Rust test tests/trace_portmap_lease.rs is the gateway and the       *)
(* network of PortMapLease.tla: it drives a real PortMap one model action  *)
(* at a time (a datagram the client gives out, the gateway's grant or      *)
(* refusal, an announce, a restart, a lost datagram, a tick of the clock,  *)
(* a timer call, stop) and records, after each, the state of the model's   *)
(* variables: the gateway's and the network's from its own bookkeeping,    *)
(* the client's from the crate's `trace` probe, mapped as follows:         *)
(*   now, started, renewAt, cexp, prevAt, floorEnd, annNext  times, in     *)
(*        ticks of Sec = 5 s (every one the test makes is on a tick);      *)
(*        renewAt and cexp keep their last value while no lease is held,   *)
(*        prevAt and annNext are -1 for none                               *)
(*   cstep  Pcp "ask", Held "held", Stopped "stopped", any other step      *)
(*        "idle" (NAT-PMP, which the test's gateway never answers, and     *)
(*        the RETRY wait)                                                  *)
(*   tries  in Pcp the tries that left: tries, less one when the next try  *)
(*        is due and not given out yet; 0 elsewhere                        *)
(*   pub  a mapping is held; renewing, prevSrv as in the code              *)
(*   req, resp  arrays of the sets in flight                               *)
(* A code event the model does not see (a NAT-PMP try, a timer that only   *)
(* re-arms a try) is recorded with the state unchanged. An event "new"     *)
(* starts another run: a new                                               *)
(* client at time 0 and a new gateway.                                     *)
(*                                                                         *)
(* The trace spec has the model's variables and walks the events: each     *)
(* step sets the recorded variables and must be a step of the model        *)
(* (M!Next) or leave them all unchanged; the ghosts follow the model's     *)
(* actions. Every recorded variable is fixed by the event, so a step that  *)
(* no model action takes leaves TLC with no successor: CHECK_DEADLOCK      *)
(* reports the event (i) where code and model part. The model's            *)
(* invariants are checked on every state reached (TraceInv).               *)
(*                                                                         *)
(* Constants: L = 8 ticks (cfg.lifetime and the granted lifetime 40 s,     *)
(* even, so half way is a tick), Sec = 5 (the PCP and NAT-PMP rounds,      *)
(* 1.75 s each, end within a tick), Floor = 2 ticks (ANNOUNCE_FLOOR, 10 s), *)
(* Tries = 3 (TRIES), the announce wait 0 (nonce[0] = 0), the code's       *)
(* guards on, spoofed announces allowed, and MaxT and MaxRestarts far      *)
(* beyond a run (the trace bounds them).                                   *)
(*                                                                         *)
(* What the trace does not reach, because the model is coarser there:      *)
(* the test's gateway answers only the first try of a round and at once,   *)
(* never loses a renewal's request or answer, and refuses a renewal only   *)
(* when cexp - now is even and at least 2 (FailVars rounds FIRST_GAP and   *)
(* an odd half up to a tick; the code does not), so a lease never lapses   *)
(* (ClientExpire is not reached). The test calls handle_timeout in the     *)
(* RETRY wait at the first tick at or after its deadline, so every round   *)
(* starts on a tick. One known difference of code and model stays out of  *)
(* the trace: the test never refuses with an epoch that shows a restart    *)
(* (the model asks again with PCP, the code fails over to NAT-PMP). Stop   *)
(* in Pcp releases the round's request in flight, as the model's           *)
(* ClientStop does: the test puts that release in req.                     *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds portmap/lease.ndjson. *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLES now, boot, restarts, gmap, gexp, req, resp, cstep, tries, renewing, pub, started, renewAt, cexp,
          prevAt, prevSrv, heardBoot, grantBoot, renewTried, lapseUntried, floorEnd, annNext, lastBrought, fast,
          dropBad, hdrBad, overtaken, staleGrants, i

\* every variable, listed here: UNCHANGED of the instance's nested M!vars stopped TLC with an evaluation error at
\* the ghosts
tv == <<now, boot, restarts, gmap, gexp, req, resp, cstep, tries, renewing, pub, started, renewAt, cexp,
        prevAt, prevSrv, heardBoot, grantBoot, renewTried, lapseUntried, floorEnd, annNext, lastBrought, fast, dropBad,
        hdrBad, overtaken, staleGrants>>
M == INSTANCE PortMapLease WITH L <- 8, Sec <- 5, MaxT <- 1000000000, MaxRestarts <- 1000000000, Tries <- 3,
                                Renew <- TRUE, Epoch <- TRUE, Expiry <- TRUE, StopDrop <- TRUE, RefusalDrops <- TRUE,
                                AnnounceDrops <- FALSE, Floor <- 2, FloorOn <- TRUE, KeepFloor <- TRUE, Spoofs <- TRUE,
                                HeaderDrops <- FALSE, ExpireFirst <- TRUE, OverEnds <- TRUE

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/portmap/lease.ndjson")

ToSet(q) == {q[k] : k \in DOMAIN q}

\* the recorded variables of event r, now and after the step
Obs(r) ==
    /\ now = r.now /\ boot = r.boot /\ restarts = r.restarts /\ gmap = r.gmap /\ gexp = r.gexp
    /\ req = ToSet(r.req) /\ resp = ToSet(r.resp)
    /\ cstep = r.cstep /\ tries = r.tries /\ renewing = r.renewing /\ pub = r.pub /\ started = r.started
    /\ renewAt = r.renewAt /\ cexp = r.cexp /\ prevAt = r.prevAt /\ prevSrv = r.prevSrv
    /\ floorEnd = r.floorEnd /\ annNext = r.annNext
ObsP(r) ==
    /\ now' = r.now /\ boot' = r.boot /\ restarts' = r.restarts /\ gmap' = r.gmap /\ gexp' = r.gexp
    /\ req' = ToSet(r.req) /\ resp' = ToSet(r.resp)
    /\ cstep' = r.cstep /\ tries' = r.tries /\ renewing' = r.renewing /\ pub' = r.pub /\ started' = r.started
    /\ renewAt' = r.renewAt /\ cexp' = r.cexp /\ prevAt' = r.prevAt /\ prevSrv' = r.prevSrv
    /\ floorEnd' = r.floorEnd /\ annNext' = r.annNext

TraceInit == i = 1 /\ Trace[1].ev = "new" /\ M!Init /\ Obs(Trace[1])

TraceNext ==
    \/ /\ i < Len(Trace) /\ i' = i + 1
       /\ ObsP(Trace[i + 1])
       /\ IF Trace[i + 1].ev = "new"
          \* a new run: the ghosts start empty and the recorded state must be the model's initial state
          THEN /\ heardBoot' = 0 /\ grantBoot' = 0 /\ renewTried' = FALSE /\ lapseUntried' = FALSE
               /\ lastBrought' = -1 /\ fast' = FALSE /\ dropBad' = FALSE /\ hdrBad' = FALSE
               /\ overtaken' = FALSE /\ staleGrants' = {}
               /\ (M!Init)'
          ELSE M!Next \/ UNCHANGED tv
    \* the end of the trace
    \/ i = Len(Trace) /\ UNCHANGED <<i, tv>>

TraceSpec == TraceInit /\ [][TraceNext]_<<i, tv>>

TraceInv ==
    /\ M!TypeOK /\ M!HeldByGateway /\ M!StoppedUnpublished /\ M!LeaseLive /\ M!RenewedBeforeLapse
    /\ M!AnnounceKeeps /\ M!AnnounceSpaced /\ M!HeaderKeeps
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
