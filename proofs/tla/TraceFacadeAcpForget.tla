------------------------ MODULE TraceFacadeAcpForget ------------------------
(***************************************************************************)
(* Trace validation of the answers the endpoint and the facade keep per    *)
(* peer against FacadeAcpForget.tla (the code as built: every switch       *)
(* TRUE, one peer, two listed protocols): crates/pinc/src/engine.rs        *)
(* `AcpCheck` arm, `admits_other`, `session_admitted`, `session_up`;       *)
(* engine/ops.rs `Core::{revoke, unrevoke, forget_access, connect_start}`; *)
(* engine/gate.rs `direction`, `Known`; endpoint.rs                        *)
(* `Endpoint::{connect, revoke, unrevoke, admission_changed}`; pinc-core   *)
(* acp.rs (ACP_TTL 30 s, ACP_RECHECK 5 s).                                 *)
(*                                                                         *)
(* The test `trace_facade_acp` of tests/trace_facade_gate.rs (file         *)
(* facade_acp.ndjson) drives endpoint A, built on the test platform so the *)
(* test moves its clock, against a real peer p1. Events, each one model    *)
(* step with its parameters:                                               *)
(*   init {hook}                      the hook's table [peer, proto, dir]  *)
(*   decide {peer, proto, dir, ep, up} a session came up at A's endpoint:  *)
(*                                     let through (ep) and taken up (up)  *)
(*   recheck {peer, proto, dir, allow} the clock moved past the recheck    *)
(*                                     point (ACP_TTL - ACP_RECHECK) and   *)
(*                                     the session's next packet asked     *)
(*                                     again; the endpoint's new answer    *)
(*   dial {peer, proto}  hangup {peer} end {peer, proto, dir}              *)
(*   revoke {peer}  lift {peer}  rehook {peer, proto, dir} (the test edits *)
(*                                     its table and calls                 *)
(*                                     admission_changed)                  *)
(*   expire {peer}  lapse {peer}  clear  (the clock moved past ACP_TTL, or *)
(*                                     the probes trace_expire and         *)
(*                                     trace_lapse)                        *)
(* The clock past ACP_TTL runs out both answers of a peer at once, and no  *)
(* probe sees between them: an expire line whose probe shows the           *)
(* remembered allow gone as well is the model's Lapse, a step with no line *)
(* of its own, then the line's Expire.                                      *)
(* and on every event but init the probed state: revoked, cache {peer},   *)
(* known {peer}. The sessions and dials A holds (`sess`, `out`) are not    *)
(* probed; they follow from the events.                                    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds facade_acp.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES hook, revoked, cache, known, last, out, sess, cut, i
mvars == <<hook, revoked, cache, known, last, out, sess, cut>>

PeerSet == {"p1"}
M == INSTANCE FacadeAcpForget WITH Peers <- PeerSet, Listed <- {"a", "b"}, Dialed <- {}, ForgetOnLift <- TRUE,
                                   ForgetOnRevoke <- TRUE, RefuseDial <- TRUE, ForgetOnChange <- TRUE,
                                   AskEach <- TRUE, AnswerAny <- TRUE, AskHeld <- TRUE, DialAsks <- TRUE

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/facade_acp.ndjson")
Ev == Trace[i]
Q(ev) == <<ev.proto, ev.dir>>
Hook(ev) == [p \in PeerSet |-> {<<h[2], h[3]>> : h \in {x \in {ev.hook[k] : k \in 1..Len(ev.hook)} : x[1] = p}}]

Seen(ev) ==
    /\ revoked' = {ev.revoked[k] : k \in 1..Len(ev.revoked)}
    /\ \A p \in PeerSet : /\ cache'[p] = ev.cache[p]
                          /\ known'[p] = {<<x[1], x[2]>> : x \in {ev.known[p][k] : k \in 1..Len(ev.known[p])}}

Step ==
    /\ CASE Ev.op = "decide" -> \E a \in M!AllQs : M!Decide(Ev.peer, Q(Ev), a) /\ last'.ep = Ev.ep
                                                  /\ last'.up = Ev.up /\ UNCHANGED hook
         [] Ev.op = "recheck" -> \E a \in M!AllQs : M!Recheck(Ev.peer, Q(Ev), a)
                                                   /\ cache'[Ev.peer] = (IF Ev.allow THEN "allow" ELSE "deny")
                                                   /\ UNCHANGED hook
         [] Ev.op = "dial" -> M!Dial(Ev.peer, <<Ev.proto, "out">>) /\ UNCHANGED hook
         [] Ev.op = "hangup" -> M!Hangup(Ev.peer) /\ UNCHANGED hook
         [] Ev.op = "end" -> M!End(Ev.peer, Q(Ev)) /\ UNCHANGED hook
         [] Ev.op = "revoke" -> M!Revoke(Ev.peer) /\ UNCHANGED hook
         [] Ev.op = "lift" -> M!Lift(Ev.peer) /\ UNCHANGED hook
         [] Ev.op = "expire" -> M!Expire(Ev.peer) /\ UNCHANGED hook
         [] Ev.op = "lapse" -> M!Lapse(Ev.peer) /\ UNCHANGED hook
         [] Ev.op = "clear" -> M!Clear /\ UNCHANGED hook
         [] Ev.op = "rehook" -> M!Rehook(Ev.peer, Q(Ev))
         [] OTHER -> FALSE
    /\ Seen(Ev)

Init == /\ M!Init
        /\ Trace[1].op = "init" /\ hook = Hook(Trace[1])
        /\ i = 2
Next == \/ i <= Len(Trace) /\ Step /\ i' = i + 1
        \* The clock ran both answers out at once: the remembered allow lapses first, then the line's Expire
        \/ /\ i <= Len(Trace) /\ Ev.op = "expire"
           /\ known[Ev.peer] # {} /\ Len(Ev.known[Ev.peer]) = 0
           /\ M!Lapse(Ev.peer) /\ UNCHANGED <<hook, i>>
        \* Finished: the trace was read to its end (a mismatch deadlocks before it)
        \/ i > Len(Trace) /\ UNCHANGED <<mvars, i>>
TraceSpec == Init /\ [][Next]_<<mvars, i>>

Inv == M!DecideFresh /\ M!CacheSound /\ M!KnownSound /\ M!NoDialRevoked /\ M!NoCrossAllow /\ M!NoCrossDeny
       /\ M!NoCut
=============================================================================
