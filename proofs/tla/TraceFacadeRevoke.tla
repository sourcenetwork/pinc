-------------------------- MODULE TraceFacadeRevoke --------------------------
(***************************************************************************)
(* Trace validation of the facade's access gate against FacadeRevoke.tla:  *)
(* crates/pinc/src/engine/gate.rs `Gate::{bar, lift, is_revoked, admit}`,  *)
(* `Known`; engine/ops.rs `Core::{revoke, unrevoke}`; engine.rs `AcpCheck`, *)
(* `session_up`, `session_admitted`; endpoint.rs `Endpoint::{connect,      *)
(* revoke, unrevoke, admit}`.                                              *)
(*                                                                         *)
(* The test `trace_facade_revoke` of tests/trace_facade_gate.rs (file      *)
(* FILE) drives one endpoint A whose hook answers from a table the test    *)
(* fixes at the start, with real peers p1, p2 over loopback. Each event is *)
(* one model step with its parameters; after it the test reads A through   *)
(* the trace probes and writes what it saw, which must be the model's:     *)
(*   init   {hook}                        the hook's table: [peer, proto,  *)
(*                                         dir] it allows (hub never)      *)
(*   arrive {slot, peer, proto, dir}       a session of A (dir "out": A    *)
(*                                         dialed) reached A's endpoint    *)
(*   decide {slot, st}                     it came up ("live") or ended    *)
(*   revoke {peer, ok}   lift {peer}       Endpoint::revoke, unrevoke      *)
(*   end {slot}  free {slot}               ended for another reason; slot  *)
(*                                         reused                          *)
(*   expire {peer}  lapse {peer}           the endpoint's answer or the    *)
(*                                         facade's remembered allow went: *)
(*                                         by the probes trace_expire and  *)
(*                                         trace_lapse, or because revoke  *)
(*                                         and unrevoke drop both (the     *)
(*                                         test writes these after them)   *)
(*   toggle                                the hook took or gave back the  *)
(*                                         core (it calls admit from       *)
(*                                         inside an endpoint call)        *)
(*   admit {peer, proto, dir, ans}         Endpoint::admit and its answer  *)
(* and on every event but init the probed state: live (the slots A holds   *)
(* up) and revoked (peers); where the state is settled also cache {peer:   *)
(* "none"/"allow"/"deny"} and known {peer: [] or [[proto, dir]]}.         *)
(*                                                                         *)
(* MAXREV is the model's bound read against the traced peers only:         *)
(* TraceFacadeRevoke.cfg sets 4096 (never reached by two peers);           *)
(* TraceFacadeRevokeFull.cfg sets 1 for a run that first revoked 4095      *)
(* other ids, so the first traced revoke takes the last place and the     *)
(* second is refused.                                                      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR.                                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
CONSTANTS MAXREV, FILE

VARIABLES hook, revoked, cache, known, sess, borrowed, last, i
mvars == <<hook, revoked, cache, known, sess, borrowed, last>>

PeerSet == {"p1", "p2"}
M == INSTANCE FacadeRevoke WITH Peers <- PeerSet, Protos <- {"a", "b"}, Slots <- 1..4, MaxRevoked <- MAXREV,
                                FailOpen <- FALSE, Backstop <- TRUE

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/" \o FILE)
Ev == Trace[i]
Q(ev) == <<ev.proto, ev.dir>>
Hook(ev) == [p \in PeerSet |-> {<<h[2], h[3]>> : h \in {x \in {ev.hook[k] : k \in 1..Len(ev.hook)} : x[1] = p}}]

\* the probed state after the event equals the model's; cache and known are written only where the state is settled
\* (not on revoke and unrevoke, which drop both answers at once in the code: the expire and lapse events that follow
\* are the model's steps for that, and the last of them carries the probes)
Seen(ev) ==
    /\ {k \in 1..4 : sess'[k].st = "live"} = {ev.live[k] : k \in 1..Len(ev.live)}
    /\ revoked' = {ev.revoked[k] : k \in 1..Len(ev.revoked)}
    /\ "cache" \in DOMAIN ev =>
          \A p \in PeerSet : /\ cache'[p] = ev.cache[p]
                             /\ known'[p] = {<<x[1], x[2]>> : x \in {ev.known[p][k] : k \in 1..Len(ev.known[p])}}

Step ==
    /\ CASE Ev.op = "arrive" -> M!Arrive(Ev.slot, Ev.peer, Q(Ev))
         [] Ev.op = "decide" -> \E a \in M!Qs : M!Decide(Ev.slot, a) /\ sess'[Ev.slot].st = Ev.st
         [] Ev.op = "revoke" -> IF Ev.ok THEN M!Revoke(Ev.peer)
                                ELSE /\ Ev.peer \notin revoked /\ Cardinality(revoked) >= MAXREV
                                     /\ UNCHANGED mvars
         [] Ev.op = "lift" -> M!Lift(Ev.peer)
         [] Ev.op = "end" -> M!End(Ev.slot)
         [] Ev.op = "free" -> M!Free(Ev.slot)
         [] Ev.op = "expire" -> M!Expire(Ev.peer)
         [] Ev.op = "lapse" -> M!Lapse(Ev.peer)
         [] Ev.op = "toggle" -> M!Toggle
         [] Ev.op = "admit" -> M!Admit(Ev.peer, Q(Ev)) /\ last'.ans = Ev.ans
         [] OTHER -> FALSE
    /\ Seen(Ev)

Init == /\ M!Init
        /\ Trace[1].op = "init" /\ hook = Hook(Trace[1])
        /\ i = 2
Next == \/ i <= Len(Trace) /\ Step /\ i' = i + 1
        \* Finished: the trace was read to its end (a mismatch deadlocks before it)
        \/ i > Len(Trace) /\ UNCHANGED <<mvars, i>>
TraceSpec == Init /\ [][Next]_<<mvars, i>>

Inv == M!NoLiveRevoked /\ M!AdmitSound /\ M!RevokedBound
=============================================================================
