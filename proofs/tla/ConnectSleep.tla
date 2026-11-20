----------------------------- MODULE ConnectSleep -----------------------------
(***************************************************************************)
(* Model check of a node's signing work and suspension (ConnectSleepOps,  *)
(* pinc-connect src/client/signing.rs with the suspend, resume, tick and  *)
(* beacon steps of timers.rs and drive.rs), under every interleaving of   *)
(* the host's calls: suspend, resume, tick and drive with or without a    *)
(* wall clock, the answer to the outstanding signature (a signature of    *)
(* the right length, or a refused, failed or wrong-length one), a carrier *)
(* that opens, dials or goes down at any time, and a record wanted        *)
(* (set_hints, mapped addresses) at any time. Every call reads its own    *)
(* clock from Times: the clock jumps forward and back between calls and   *)
(* reaches the code's maximum (TMax stands for u64::MAX). A relay may have *)
(* no UDP address (no notice is owed to it); the only relay may be gone   *)
(* (its link down), so no notice is owed at all. Nothing here depends on  *)
(* what kind of node carries the relay role.                               *)
(*                                                                         *)
(* Properties (the module documentation of signing.rs and the doc         *)
(* comments of suspend, tick and close_for_suspend):                       *)
(*  CloseAfterNotices   the carriers close for a suspension only after    *)
(*                      every notice was signed or failed                  *)
(*  PriorityOrder       a job starts in the order sleep notices, record,  *)
(*                      beacon                                             *)
(*  NoticesNotIdle      notices owed always have a request outstanding     *)
(*                      (the host asks after any call)                     *)
(*  NoWallNoSign        no signature starts without a wall clock           *)
(*  RefusedNotSent      a refused or failed signature sends nothing and is *)
(*                      reported as SignFailed                              *)
(*  SleepNotRetried     a failed sleep notice is not asked again           *)
(*  RecordRetry         a failed record waits for its retry time           *)
(*  NoticeTwice         each relay owed a notice gets it twice over UDP,  *)
(*                      and no other relay gets one                        *)
(*  CloseOnlySuspended  a resume cancels the close of a suspension         *)
(* A job started with a wall clock is still answered and used after a    *)
(* tick without one (K8: the clock is forgotten, the job's bytes were made *)
(* with the clock of its start).                                           *)
(* Witnesses (TLC must violate): ConnectSleep_w_close (NoCloseAfterNotice: *)
(* a close for suspension after a notice was sent), ConnectSleep_w_cancel  *)
(* (NoCancelled: a cancelled sleep notice is outstanding). Checks of the   *)
(* fixes (passing once they land): ConnectSleep_twice (CloseAfterNotices   *)
(* with a second suspend, K7), ConnectSleep_w_wall (NoWallNoSign, K8),     *)
(* ConnectSleep_w_behind (NotBehindRecord, the rule restated by K9, with   *)
(* PriorityOrder) and ConnectSleep_resume (NoticeTwice, CloseAfterNotices, *)
(* SleepNotRetried over resume and a second suspend with a notice asked    *)
(* for: K6 as revised, Job::cancelled).                                    *)
(***************************************************************************)
EXTENDS ConnectSleepOps, TLC

CONSTANTS Relays, Udp, Home, Times, TMax, Retry, Repub, Beacons, Twice, LinkStates

K == [retry |-> Retry, repub |-> Repub, tmax |-> TMax, never |-> 0, udp |-> Udp, home |-> Home]

VARIABLES s, owed, sent, failed, sinceSusp, badClose, badPrio, badRefuse, badRetry, badWall, badSusp, reach
vars == <<s, owed, sent, failed, sinceSusp, badClose, badPrio, badRefuse, badRetry, badWall, badSusp, reach>>

Init == /\ s = NewS(Relays, K) /\ owed = {} /\ sent = [x \in Relays |-> 0] /\ failed = {} /\ sinceSusp = FALSE
        /\ badClose = FALSE /\ badPrio = FALSE /\ badRefuse = FALSE /\ badRetry = FALSE /\ badWall = FALSE
        /\ badSusp = FALSE /\ reach = FALSE

Count(sq, x) == Cardinality({k \in 1..Len(sq) : sq[k] = x})
\* the relay of the outstanding sleep notice, if it is still wanted (a cancelled one is owed to nobody)
SleepJob(t) == IF t.job.k = "sleep" /\ ~t.job.c THEN {t.job.r} ELSE {}

(* the ghosts after the call W, made at now; tk: a tick or drive; ans: an answer; started: the call started a job *)
Post(W, now, tk, nowall, started, sus, res) ==
    LET fired == tk /\ s.closeAt # K.never /\ now >= s.closeAt
        base == IF sus THEN [x \in Relays |-> 0] ELSE sent
        j == W.s.job
    IN /\ s' = W.s
       /\ sent' = [x \in Relays |-> base[x] + Count(W.o.udp, x)]
       /\ owed' = IF sus THEN {x \in Udp \cap Relays : s.lk[x] = "open"} ELSE owed
       /\ sinceSusp' = IF sus THEN TRUE ELSE IF res \/ fired THEN FALSE ELSE sinceSusp
       /\ badClose' = (badClose \/ (fired /\ (s.sleep # {} \/ s.job.k = "sleep")))
       /\ badSusp' = (badSusp \/ (fired /\ ~sinceSusp))
       /\ badPrio' = (badPrio \/ (started /\ ((j.k \in {"record", "beacon"} /\ W.s.sleep # {})
                                               \/ (j.k = "beacon" /\ W.s.record))))
       /\ badWall' = (badWall \/ (nowall /\ started))
       /\ reach' = (reach \/ (fired /\ \E x \in Relays : sent[x] > 0))

Tick == \E now \in Times, w \in BOOLEAN, cp \in BOOLEAN, rj \in BOOLEAN, bj \in BOOLEAN :
    LET W == TickStep(W0(s), now, w, PubDue(s, now, K) /\ cp, rj, bj, K) IN
    /\ Post(W, now, TRUE, ~w, s.job.k = "none" /\ W.s.job.k # "none", FALSE, FALSE)
    /\ UNCHANGED <<failed, badRefuse, badRetry>>

Drive == \E now \in Times, w \in BOOLEAN, cp \in BOOLEAN, rj \in BOOLEAN, bj \in BOOLEAN, rj2 \in BOOLEAN,
            bj2 \in BOOLEAN, bc \in (IF Beacons THEN BOOLEAN ELSE {FALSE}) :
    /\ bc => w
    /\ LET W == DriveStep(W0(s), now, w, PubDue(s, now, K) /\ cp, rj, bj, rj2, bj2, bc, K) IN
       /\ Post(W, now, TRUE, ~w, s.job.k = "none" /\ W.s.job.k # "none", FALSE, FALSE)
       /\ UNCHANGED <<failed, badRefuse, badRetry>>

Answer == \E now \in Times, ok \in BOOLEAN, rj \in BOOLEAN, bj \in BOOLEAN :
    /\ s.job.k # "none"
    /\ LET W == SignResponse(W0(s), now, ok, rj, bj, K)
           j == s.job
       IN /\ Post(W, now, FALSE, FALSE, W.s.job.k # "none", FALSE, FALSE)
          \* a cancelled notice is not owed, so its failure raises no retry question
          /\ failed' = IF ~ok /\ j.k = "sleep" /\ ~j.c THEN failed \cup {j.r} ELSE failed
          /\ badRefuse' = (badRefuse \/ (~ok /\ (W.o.udp # <<>> \/ W.o.pub > 0 \/ W.o.bcn > 0 \/ W.o.fails # 1)))
          \* a record wanted again meanwhile (set_hints) is new work and may start at once
          /\ badRetry' = (badRetry \/ (~ok /\ j.k = "record" /\ ~s.record /\ now < TMax
                                        /\ (W.s.pub <= now \/ W.s.job.k = "record")))

Suspend == \E now \in Times, rj \in BOOLEAN, bj \in BOOLEAN :
    /\ Twice \/ ~s.susp
    /\ LET W == SuspendStep(W0(s), now, rj, bj, K) IN
       /\ Post(W, now, FALSE, FALSE, s.job.k = "none" /\ W.s.job.k # "none", TRUE, FALSE)
       /\ failed' = {}
       /\ UNCHANGED <<badRefuse, badRetry>>

Resume == \E wr \in BOOLEAN :
    /\ Post(ResumeStep(W0(s), wr, K), 0, FALSE, FALSE, FALSE, FALSE, TRUE)
    /\ UNCHANGED <<failed, badRefuse, badRetry>>

Link == \E x \in Relays, st \in LinkStates, now \in Times :
    /\ st # s.lk[x]
    /\ Post(LinkSet(W0(s), x, st, now, K), now, FALSE, FALSE, FALSE, FALSE, FALSE)
    /\ UNCHANGED <<failed, badRefuse, badRetry>>

Want == /\ ~s.record
        /\ Post(WantRecord(W0(s)), 0, FALSE, FALSE, FALSE, FALSE, FALSE)
        /\ UNCHANGED <<failed, badRefuse, badRetry>>

Next == Tick \/ Drive \/ Answer \/ Suspend \/ Resume \/ Link \/ Want

Spec == Init /\ [][Next]_vars

CloseAfterNotices == ~badClose
PriorityOrder == ~badPrio
NoticesNotIdle == s.job.k = "none" => s.sleep = {}
RefusedNotSent == ~badRefuse
SleepNotRetried == failed \cap (s.sleep \cup SleepJob(s)) = {}
RecordRetry == ~badRetry
NoticeTwice == \A x \in Relays : sent[x] \in {0, 2} /\ (sent[x] > 0 => x \in owed /\ x \in Udp)
CloseOnlySuspended == ~badSusp

\* the documented claims of the findings K7, K8 and K9 (kept by the code once they land), and a reachability witness
\* signing.rs, restated (K9): "a suspending node's notices wait for at most the one signature already asked for": a
\* record job seen with notices owed is the one outstanding before the step (a record job started while notices are
\* owed is PriorityOrder's case)
NotBehindRecord == [][(s'.sleep # {} /\ s'.job.k = "record") => s.job = s'.job]_vars
NoWallNoSign == ~badWall
NoCloseAfterNotice == ~reach
NoCancelled == ~(s.job.k = "sleep" /\ s.job.c)

\* the link states of the configs
LinksOpenDown == {"open", "down"}
LinksAll == {"open", "dialing", "down"}
=============================================================================
