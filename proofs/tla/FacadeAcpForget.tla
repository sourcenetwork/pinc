--------------------------- MODULE FacadeAcpForget ---------------------------
(***************************************************************************)
(* The facade's revoke and unrevoke against the endpoint's answer cache.   *)
(*                                                                         *)
(* Who acts. Peers dial this node; the endpoint decides each session from  *)
(* its cached answer for the peer, or asks the gate (revoked: no; else the *)
(* hook's answer) and caches what it says (30 s in the code, here until an *)
(* Expire step). This node dials peers too. The application revokes peers *)
(* and lifts revocations, and edits its hook (an allowlist), telling the   *)
(* endpoint through admission_changed.                                    *)
(*                                                                         *)
(* What must never happen. A session is decided on an answer the gate      *)
(* would not give now (DecideFresh): a deny cached while the peer was      *)
(* revoked refusing it after the lift, or an allow cached before a revoke  *)
(* letting it through after. A cached answer that is not the gate's        *)
(* current one (CacheSound). A dial of this node reaching a revoked peer   *)
(* (NoDialRevoked): the peer would hold it as a session until our deny     *)
(* arrives, and its own dial after the lift would ride it and fail.        *)
(*                                                                         *)
(* Rust: crates/vinc-core/src/commands.rs `Command::AcpForget` (drops      *)
(* `self.acp[node]`); crates/vinc-core/src/acp.rs `start_acp`,             *)
(* `acp_cached`, `acp_answer`; crates/vinc/src/engine.rs                   *)
(* `Core::{revoke, unrevoke, forget_acp}`, the `AcpCheck` arm of           *)
(* `on_event`; crates/vinc/src/endpoint.rs                                 *)
(* `Endpoint::{revoke, unrevoke, connect, admission_changed}`.             *)
(* Lean counterpart: Vinc/FacadeAcpForget.lean (`inv_reach`,               *)
(* `noForgetOnLift_bad`, `noForgetOnRevoke_bad`, `noRefuseDial_bad`,       *)
(* `noForgetOnChange_bad`).                                                *)
(*                                                                         *)
(* Witnesses (scripts/proofs.sh witness_tlc): ForgetOnLift = FALSE is the  *)
(* code before the fix: a peer that dialed while revoked is still refused  *)
(* after unrevoke, on the cached deny. ForgetOnRevoke = FALSE keeps a      *)
(* cached allow across a revoke: the endpoint lets the revoked peer's      *)
(* session through without asking. Both break DecideFresh. RefuseDial =    *)
(* FALSE lets a dial to a revoked peer go out: NoDialRevoked fails.        *)
(* ForgetOnChange = FALSE is a host that edits its allowlist without       *)
(* telling the endpoint: the peer it just listed is refused on the cached  *)
(* deny, and DecideFresh fails.                                            *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANTS
    Peers,           \* the peers that may dial this node
    Allowed,         \* the peers the application's hook admits at the start
    ForgetOnLift,    \* TRUE: unrevoke drops the peer's cached answer (FALSE: the bug, a witness config)
    ForgetOnRevoke,  \* TRUE: revoke drops the peer's cached answer (FALSE: a witness config)
    RefuseDial,      \* TRUE: a dial to a revoked peer is refused before anything is sent (FALSE: a witness config)
    ForgetOnChange   \* TRUE: the host calls admission_changed when the hook's answer changes (FALSE: a witness config)

VARIABLES
    allowed,  \* the peers the application's hook admits now; the host edits it (an allowlist)
    revoked,  \* the gate's revoked set
    cache,    \* the endpoint's cached answer per peer: "none", "allow" or "deny"
    last,     \* the last decision: [done, peer, ans, gate]; ans is what the session got, gate what the gate says now
    out       \* the peers a dial of this node has reached and that hold its session

vars == <<allowed, revoked, cache, last, out>>

\* Some peer, to fill fields that are not used yet.
AnyPeer == CHOOSE p \in Peers : TRUE

\* The gate's answer: a revoked peer is refused, any other gets the hook's.
Gate(p) == p \notin revoked /\ p \in allowed

\* A cache entry as an answer: "allow" lets in, anything else does not.
AsBool(a) == a = "allow"

\* Every variable has the shape it should.
TypeOK ==
    /\ allowed \subseteq Peers
    /\ revoked \subseteq Peers
    /\ cache \in [Peers -> {"none", "allow", "deny"}]
    /\ last.done \in BOOLEAN /\ last.peer \in Peers /\ last.ans \in BOOLEAN /\ last.gate \in BOOLEAN
    /\ out \subseteq Peers

\* The start: nobody revoked, nothing cached, nothing decided, nothing dialed.
Init ==
    /\ allowed = Allowed
    /\ revoked = {}
    /\ cache = [p \in Peers |-> "none"]
    /\ last = [done |-> FALSE, peer |-> AnyPeer, ans |-> FALSE, gate |-> FALSE]
    /\ out = {}

\* A session of `p` is decided: on the cached answer if there is one, else the gate is asked (synchronously, as the
\* facade answers `AcpCheck` inside the event) and its answer cached.
Decide(p) ==
    LET ans == IF cache[p] = "none" THEN Gate(p) ELSE AsBool(cache[p]) IN
    /\ cache' = IF cache[p] = "none" THEN [cache EXCEPT ![p] = IF Gate(p) THEN "allow" ELSE "deny"] ELSE cache
    /\ last' = [done |-> TRUE, peer |-> p, ans |-> ans, gate |-> Gate(p)]
    /\ UNCHANGED <<revoked, out>>

\* The application revokes `p`; the fix drops its cached answer in the same call, and every session with `p` ends.
Revoke(p) ==
    /\ revoked' = revoked \cup {p}
    /\ cache' = IF ForgetOnRevoke THEN [cache EXCEPT ![p] = "none"] ELSE cache
    /\ out' = out \ {p}
    /\ UNCHANGED last

\* The application lifts the revocation of `p`; the fix drops its cached answer in the same call.
Lift(p) ==
    /\ revoked' = revoked \ {p}
    /\ cache' = IF ForgetOnLift THEN [cache EXCEPT ![p] = "none"] ELSE cache
    /\ UNCHANGED <<last, out>>

\* A cached answer lapses after its 30 s.
Expire(p) ==
    /\ cache[p] # "none"
    /\ cache' = [cache EXCEPT ![p] = "none"]
    /\ UNCHANGED <<revoked, last, out>>

\* This node dials `p`: refused before anything is sent while `p` is revoked, else the session reaches `p`.
Dial(p) ==
    /\ out' = IF RefuseDial /\ p \in revoked THEN out ELSE out \cup {p}
    /\ UNCHANGED <<revoked, cache, last>>

\* A session this node dialed ends for another reason.
Hangup(p) ==
    /\ p \in out
    /\ out' = out \ {p}
    /\ UNCHANGED <<revoked, cache, last>>

\* Any of the actions, for any peer.
\* The host edits its allowlist for `p` (adds or removes it) and, with the fix, calls admission_changed for it.
Rehook(p) ==
    /\ allowed' = IF p \in allowed THEN allowed \ {p} ELSE allowed \cup {p}
    /\ cache' = IF ForgetOnChange THEN [cache EXCEPT ![p] = "none"] ELSE cache
    /\ UNCHANGED <<revoked, last, out>>

\* Any of the actions, for any peer; every action but Rehook leaves the hook as it is.
Next ==
    \/ \E p \in Peers : (Decide(p) \/ Revoke(p) \/ Lift(p) \/ Expire(p) \/ Dial(p) \/ Hangup(p)) /\ UNCHANGED allowed
    \/ \E p \in Peers : Rehook(p)

\* The behaviours: start at Init, then take Next steps (or stutter).
Spec == Init /\ [][Next]_vars

\* Every session is decided with the answer the gate gives at that moment, cached or not.
DecideFresh == last.done => last.ans = last.gate
\* Every cached answer is the one the gate would give now.
CacheSound == \A p \in Peers : cache[p] # "none" => AsBool(cache[p]) = Gate(p)
\* No revoked peer holds a session this node dialed.
NoDialRevoked == out \cap revoked = {}
=============================================================================
