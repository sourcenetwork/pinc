---------------------------- MODULE ConnectSleepOps ----------------------------
(***************************************************************************)
(* The signing work of a node and its suspension, as pure operators:       *)
(* pinc-connect src/client/signing.rs (Signing, sign_response, complete,  *)
(* start_jobs, maybe_close_for_suspend, close_for_suspend), the suspend,  *)
(* resume, tick and publish steps of client/timers.rs, and the beacon     *)
(* step of client/drive.rs (beacon, suspend_all, resume_all).             *)
(* ConnectSleep.tla (the model check) and TraceConnectSleep.tla (the trace *)
(* validation) use them. ConnectOwn.tla models the record a job signs;    *)
(* here a record job is only its kind.                                     *)
(*                                                                         *)
(* A call is a function of W = [s, o]. s is the node:                       *)
(*   sleep    the relays a sleep notice is owed to (Signing::sleep)        *)
(*   record   a record is wanted (Signing::record)                         *)
(*   beacon   a beacon is wanted (Signing::beacon)                         *)
(*   job      the outstanding request: [k |-> "none", "record", "beacon"  *)
(*            or "sleep", r |-> its relay (0 for none and beacon), c |->   *)
(*            cancelled (Job::cancelled: a sleep notice no longer wanted, *)
(*            still asked for; its answer is dropped)]                     *)
(*   susp     Signing::suspending                                          *)
(*   closeAt  Signing::close_at (K.never for none)                         *)
(*   wall     the layer has a wall clock (Signing::wall_ms is some)        *)
(*   pub      next_publish of the node (0 in the code is K.never here,    *)
(*            u64::MAX is K.tmax)                                          *)
(*   lk       per relay, its link state: "open", "dialing" or "down"; the *)
(*            carriers' own life is ConnectCarriers.tla                    *)
(* o is what the call let out: udp the sleep datagrams in order (a relay  *)
(* per datagram), pub the records framed to the home carrier, bcn the      *)
(* beacons queued, fails the SignFailed notices, closes the relays whose  *)
(* carrier was closed for the suspension.                                  *)
(*                                                                         *)
(* K = [retry, repub, tmax, never, udp, home]: HOME_RETRY_NS,              *)
(* RECORD_REPUBLISH_NS and u64::MAX in the unit of the caller, the value  *)
(* standing for none, the relays configured with a UDP address, and the  *)
(* home relay. Saturating sums stop at K.tmax as the code's stop at       *)
(* u64::MAX.                                                                *)
(*                                                                         *)
(* Whether a record job can be built (a home and a class are known,       *)
(* record_job) and whether a beacon job can (beacon_job) are parameters   *)
(* rj and bj of every call that starts jobs. A sleep job is always built: *)
(* the relay it is owed to is configured (suspend took it from the        *)
(* configuration) and its message has a fixed size.                        *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

SatAdd(a, b, K) == IF a >= K.tmax - b THEN K.tmax ELSE a + b
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y

NoJob == [k |-> "none", r |-> 0, c |-> FALSE]
Job(k, r) == [k |-> k, r |-> r, c |-> FALSE]
NewS(relays, K) == [sleep |-> {}, record |-> FALSE, beacon |-> FALSE, job |-> NoJob, susp |-> FALSE,
                    closeAt |-> K.never, wall |-> FALSE, pub |-> K.never, lk |-> [x \in relays |-> "down"]]
NoOut == [udp |-> <<>>, pub |-> 0, bcn |-> 0, fails |-> 0, closes |-> {}]
W0(s) == [s |-> s, o |-> NoOut]

RecordWanted(s) == s.record \/ s.job.k = "record"

(* start_jobs: one request at a time, the sleep notices first (lowest relay first), then the record, then a beacon *)
StartJobs(W, now, rj, bj, K) ==
    IF W.s.job.k # "none" \/ ~W.s.wall THEN W
    ELSE IF W.s.sleep # {} THEN
        LET r == MinOf(W.s.sleep) IN [W EXCEPT !.s.sleep = @ \ {r}, !.s.job = Job("sleep", r)]
    ELSE IF W.s.record THEN
        IF rj THEN [W EXCEPT !.s.record = FALSE, !.s.job = Job("record", K.home)]
        ELSE [W EXCEPT !.s.record = FALSE, !.s.pub = SatAdd(now, K.retry, K)]
    ELSE IF W.s.beacon THEN
        [W EXCEPT !.s.beacon = FALSE, !.s.job = IF bj THEN Job("beacon", 0) ELSE NoJob]
    ELSE W

(* maybe_close_for_suspend: every notice answered, the carriers close one tick later *)
MaybeClose(W, now, K) ==
    IF W.s.susp /\ W.s.sleep = {} /\ W.s.job.k = "none" /\ W.s.closeAt = K.never
    THEN [W EXCEPT !.s.closeAt = SatAdd(now, 1, K)] ELSE W

(* close_for_suspend: once its tick has come, every carrier whose link is not down is closed *)
CloseForSuspend(W, now, K) ==
    IF W.s.closeAt # K.never /\ now >= W.s.closeAt THEN
        LET open == {x \in DOMAIN W.s.lk : W.s.lk[x] # "down"} IN
        [W EXCEPT !.s.closeAt = K.never, !.s.susp = FALSE, !.s.lk = [x \in DOMAIN @ |-> "down"], !.o.closes = @ \cup open]
    ELSE W

(* complete: a signature of the right length was given for the job j; a cancelled sleep notice sends nothing (its
   answer is consumed: nothing sent, nothing failed) *)
Complete(W, j, now, K) ==
    CASE j.k = "record" ->
            IF W.s.lk[j.r] = "open" THEN [W EXCEPT !.o.pub = @ + 1, !.s.pub = SatAdd(now, K.repub, K)]
            ELSE [W EXCEPT !.s.pub = now]
      [] j.k = "beacon" -> [W EXCEPT !.o.bcn = @ + 1]
      [] j.k = "sleep" ->
            IF j.c THEN W ELSE IF j.r \in K.udp THEN [W EXCEPT !.o.udp = @ \o <<j.r, j.r>>] ELSE W
      [] OTHER -> W

(* the complete call answers false only for a sleep notice, not cancelled, to a relay with no UDP address (a suspension
   never owes one) *)
Completes(j, K) == j.k # "sleep" \/ j.c \/ j.r \in K.udp

(* sign_response: ok is a signature of the identity's length; anything else is refused *)
SignResponse(W, now, ok, rj, bj, K) ==
    IF W.s.job.k = "none" THEN W
    ELSE LET j == W.s.job
             W1 == [W EXCEPT !.s.job = NoJob]
             W2 == IF ok /\ Completes(j, K) THEN Complete(W1, j, now, K)
                   ELSE [W1 EXCEPT !.o.fails = @ + 1,
                                   !.s.pub = IF j.k = "record" THEN SatAdd(now, K.retry, K) ELSE @]
         IN MaybeClose(StartJobs(W2, now, rj, bj, K), now, K)

(* tick: the wall clock is the one given now, none without one (fix K8); the suspension's close; publish asks for the record when pw (its due
   time came, no record is wanted, the class is known and the home carrier is open: PubDue and the caller) *)
TickStep(W, now, w, pw, rj, bj, K) ==
    LET W1 == CloseForSuspend([W EXCEPT !.s.wall = w], now, K)
        W2 == IF pw THEN [W1 EXCEPT !.s.record = TRUE, !.s.pub = K.tmax] ELSE W1
    IN StartJobs(W2, now, rj, bj, K)

PubDue(s, now, K) == s.pub # K.never /\ s.pub # K.tmax /\ now >= s.pub /\ ~RecordWanted(s)

(* drive: the tick, then (bc) the beacon duty cycle asks for a beacon, then start_jobs again *)
DriveStep(W, now, w, pw, rj, bj, rj2, bj2, bc, K) ==
    LET W1 == TickStep(W, now, w, pw, rj, bj, K)
    IN StartJobs(IF bc THEN [W1 EXCEPT !.s.beacon = TRUE] ELSE W1, now, rj2, bj2, K)

(* An outstanding sleep notice is cancelled (kept, its answer dropped) *)
CancelSleep(j) == IF j.k = "sleep" THEN [j EXCEPT !.c = TRUE] ELSE j

(* suspend: a notice is owed to every relay with a UDP address and an open link; a close armed by an earlier
   suspend is dropped (fix K7), so the carriers close only after these notices; a notice of an earlier suspension
   still asked for is cancelled (the new suspension's notice replaces it: without this a relay owed by both gets the
   old notice and the new one, four datagrams) *)
SuspendStep(W, now, rj, bj, K) ==
    LET owed == {x \in K.udp \cap DOMAIN W.s.lk : W.s.lk[x] = "open"}
        W1 == [W EXCEPT !.s.wall = TRUE, !.s.sleep = owed, !.s.susp = TRUE, !.s.closeAt = K.never,
                        !.s.job = CancelSleep(@)]
    IN MaybeClose(StartJobs(W1, now, rj, bj, K), now, K)

(* resume: the suspension is cancelled; an outstanding sleep job is kept and its answer dropped (K6 as revised: the
   host still answers the request it was given, and that answer must not land on the next job); the mapped addresses
   refreshed may want a record (wr); no job is started *)
ResumeStep(W, wr, K) ==
    [W EXCEPT !.s.sleep = {}, !.s.susp = FALSE, !.s.closeAt = K.never,
              !.s.job = CancelSleep(@), !.s.record = @ \/ wr]

(* the carrier of relay x changed its state st ("open", "dialing", "down"); the home carrier opening
   (carrier_open) makes the record due now *)
LinkSet(W, x, st, now, K) ==
    [W EXCEPT !.s.lk[x] = st, !.s.pub = IF st = "open" /\ x = K.home THEN now ELSE @]

(* set_hints, or the mapped addresses changed: a record is wanted, no job is started *)
WantRecord(W) == [W EXCEPT !.s.record = TRUE]
=============================================================================
