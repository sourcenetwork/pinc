----------------------------- MODULE BroadcastPending -----------------------------
(***************************************************************************)
(* The publisher's table of unacknowledged publishes in pinc-broadcast     *)
(* publish.rs (Topics::publish, pub_retry) and frames.rs (on_pack), for    *)
(* any number of publishes. The application calls publish again and       *)
(* again; each call is refused (Refused::Backlog, the caller hears it) or  *)
(* answered with a message id. A hub acknowledges a tracked publish, every *)
(* hub refuses it for a full topic table (the publish ends refused), or    *)
(* the timer gives it up, in any order and at any time; BroadcastPublish   *)
(* covers when (every 3 s, give-up at 90 s), this model covers how many.   *)
(*                                                                         *)
(* What must never happen: a call answered with an id that the table does *)
(* not hold, so it is never retried and never ends acknowledged, refused   *)
(* or given up (EveryOkTracked). Checked as well: the table stays within   *)
(* Cap (PendingCap); every call has exactly one answer (Answered); a       *)
(* publish ends once (EndsOnce); and, with fair timers, every answered     *)
(* publish ends acknowledged, refused by every hub or given up (OkEnds).   *)
(*                                                                         *)
(* RefuseWhenFull = TRUE is the code. BroadcastPending_drop.cfg sets it    *)
(* FALSE, the code before the fix: with the table full the call still     *)
(* answered with an id and the publish was never tracked, so TLC finds     *)
(* EveryOkTracked violated.                                                *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/BroadcastPublish.lean (publish,      *)
(* publish_tracked, publish_refused_iff, push_drops).                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

\* Cap: PENDING_MAX; MaxCalls: how many times the application calls publish; RefuseWhenFull: the fix
CONSTANTS Cap, MaxCalls, RefuseWhenFull

\* calls: publish calls made so far, numbered 1..calls; pend: the ids the table holds; okd: the calls answered with an
\* id; refused: the calls answered with Refused::Backlog; acked, hubRefused, gaveup: the publishes that ended
\* acknowledged, refused by every hub (a full topic table) or given up
VARIABLES calls, pend, okd, refused, acked, hubRefused, gaveup
vars == <<calls, pend, okd, refused, acked, hubRefused, gaveup>>

Init == calls = 0 /\ pend = {} /\ okd = {} /\ refused = {} /\ acked = {} /\ hubRefused = {} /\ gaveup = {}

\* Topics::publish: a full table refuses the call before anything is sent (the fix); otherwise the publish is sent,
\* answered with its id and tracked. Without the fix a full table still answers with the id and tracks nothing.
Publish ==
    /\ calls < MaxCalls
    /\ LET id == calls + 1
           full == Cardinality(pend) >= Cap
       IN /\ calls' = id
          /\ IF full /\ RefuseWhenFull
             THEN refused' = refused \union {id} /\ UNCHANGED <<pend, okd>>
             ELSE /\ okd' = okd \union {id}
                  /\ pend' = IF full THEN pend ELSE pend \union {id}
                  /\ UNCHANGED refused
    /\ UNCHANGED <<acked, hubRefused, gaveup>>

\* frames.rs on_pack: a hub acknowledged a tracked publish; it leaves the table
Ack(id) == /\ id \in pend /\ pend' = pend \ {id} /\ acked' = acked \union {id}
           /\ UNCHANGED <<calls, okd, refused, hubRefused, gaveup>>

\* frames.rs: the last hub that had not refused a tracked publish refused it (its topic table is full); it leaves the
\* table and the publisher hears it was refused
Refuse(id) == /\ id \in pend /\ pend' = pend \ {id} /\ hubRefused' = hubRefused \union {id}
              /\ UNCHANGED <<calls, okd, refused, acked, gaveup>>

\* pub_retry: a tracked publish older than the give-up leaves the table
GiveUp(id) == /\ id \in pend /\ pend' = pend \ {id} /\ gaveup' = gaveup \union {id}
              /\ UNCHANGED <<calls, okd, refused, acked, hubRefused>>

Next == Publish \/ \E id \in pend : Ack(id) \/ Refuse(id) \/ GiveUp(id)
\* a tracked publish does not wait for ever: the timer gives it up at the latest
Spec == Init /\ [][Next]_vars /\ \A id \in 1..MaxCalls : WF_vars(GiveUp(id))

(* ---------------------------- the checked properties ---------------------------- *)
\* the table never holds more than PENDING_MAX publishes
PendingCap == Cardinality(pend) <= Cap
\* a call answered with an id is still tracked or has ended: the publisher hears what became of it
EveryOkTracked == okd \subseteq pend \union acked \union hubRefused \union gaveup
\* every call got exactly one answer: an id or a refusal
Answered == okd \union refused = 1..calls /\ okd \cap refused = {}
\* a publish ends once: acknowledged, refused by every hub or given up, never two of them
EndsOnce == acked \cap gaveup = {} /\ acked \cap hubRefused = {} /\ hubRefused \cap gaveup = {}
\* every call answered with an id ends acknowledged, refused by every hub or given up
OkEnds == \A id \in 1..MaxCalls : (id \in okd) ~> (id \in acked \union hubRefused \union gaveup)
=============================================================================
