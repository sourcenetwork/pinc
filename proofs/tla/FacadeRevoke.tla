---------------------------- MODULE FacadeRevoke ----------------------------
(***************************************************************************)
(* The facade's access gate: revocation and admit.                          *)
(*                                                                         *)
(* Who acts. Peers open sessions (either direction) that reach the         *)
(* endpoint; the endpoint asks the gate about a peer it holds no fresh      *)
(* answer for, and caches the answer (30 s in the code, here until an       *)
(* Expire step); the application revokes peers; a layer above asks admit    *)
(* at any moment, also while an endpoint call holds the core borrowed (the  *)
(* hook runs inside such a call).                                           *)
(*                                                                         *)
(* What must never happen. A session of a revoked peer is live after the    *)
(* revoke step (NoLiveRevoked: the revoke ends them in the same step, and a *)
(* session that comes up later on a cached allow is turned away); admit     *)
(* says yes to a revoked peer or to one the hook refuses (AdmitSound); the  *)
(* revoked set grows past its bound (RevokedBound).                        *)
(*                                                                         *)
(* Rust: crates/vinc/src/engine/gate.rs                                    *)
(* `Gate::{bar, lift, is_revoked, admit}`; crates/vinc/src/engine/ops.rs   *)
(* `Core::revoke`; crates/vinc/src/engine.rs `Core::session_up` (the       *)
(* revoked check) and the `AcpCheck` arm of `on_event`;                    *)
(* crates/vinc/src/endpoint.rs `Endpoint::{revoke, unrevoke, admit}`.      *)
(* Lean counterpart: Vinc/FacadeRevoke.lean (`inv_reach`, `failOpen_bad`,   *)
(* `noBackstop_bad`).                                                       *)
(*                                                                         *)
(* Witnesses (scripts/proofs.sh witness_tlc): FailOpen = TRUE is the old    *)
(* admit, which answered yes whenever the core was borrowed: AdmitSound     *)
(* fails. Backstop = FALSE drops the revoked check in session_up: a revoked *)
(* peer comes back on the endpoint's cached allow and NoLiveRevoked fails.  *)
(*                                                                         *)
(* The code also drops the cached answer on revoke and unrevoke and refuses *)
(* a dial to a revoked peer up front; FacadeAcpForget models those. Here    *)
(* the cache outlives both and dials go out, so the backstop is shown to   *)
(* hold on its own.                                                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Peers,       \* the peers that may open sessions
    Slots,       \* the session slots of the endpoint
    Allowed,     \* the peers the application's hook admits
    MaxRevoked,  \* REVOKED_MAX, shrunk
    FailOpen,    \* TRUE: the old admit (a witness config)
    Backstop     \* FALSE: no revoked check when a session comes up (a witness config)

VARIABLES
    revoked,   \* the gate's revoked set
    cache,     \* the endpoint's cached answer per peer: "none", "allow" or "deny"
    sess,      \* per slot: [peer, st] with st "free", "wait" (at the endpoint, no answer yet), "live", "ended"
    borrowed,  \* an endpoint call holds the core
    last       \* the last admit call: [asked, peer, ans, wasRevoked]; asked is FALSE before the first

vars == <<revoked, cache, sess, borrowed, last>>

\* Some peer, to fill fields that are not used yet.
AnyPeer == CHOOSE p \in Peers : TRUE

\* The gate's answer: a revoked peer is refused, any other gets the hook's.
Gate(p) == p \notin revoked /\ p \in Allowed

Init ==
    /\ revoked = {}
    /\ cache = [p \in Peers |-> "none"]
    /\ sess = [i \in Slots |-> [peer |-> AnyPeer, st |-> "free"]]
    /\ borrowed = FALSE
    /\ last = [asked |-> FALSE, peer |-> AnyPeer, ans |-> FALSE, wasRevoked |-> FALSE]

\* A session of `p` reaches the endpoint, from either side's dial. A dial to a revoked peer is not refused
\* up front: its session is turned away when it comes up (Up).
Arrive(i, p) ==
    /\ sess[i].st = "free"
    /\ sess' = [sess EXCEPT ![i] = [peer |-> p, st |-> "wait"]]
    /\ UNCHANGED <<revoked, cache, borrowed, last>>

\* The session comes up at the facade: turned away if its peer is revoked (with the backstop), else live.
Up(i) == [sess EXCEPT ![i].st = IF Backstop /\ sess[i].peer \in revoked THEN "ended" ELSE "live"]

\* The endpoint decides a waiting session: a cached allow lets it up without asking, a cached deny ends it, and
\* otherwise the gate is asked and its answer cached.
Decide(i) ==
    LET p == sess[i].peer IN
    /\ sess[i].st = "wait"
    /\ IF cache[p] = "allow" THEN sess' = Up(i) /\ UNCHANGED cache
       ELSE IF cache[p] = "deny" THEN sess' = [sess EXCEPT ![i].st = "ended"] /\ UNCHANGED cache
       ELSE /\ cache' = [cache EXCEPT ![p] = IF Gate(p) THEN "allow" ELSE "deny"]
            /\ sess' = IF Gate(p) THEN Up(i) ELSE [sess EXCEPT ![i].st = "ended"]
    /\ UNCHANGED <<revoked, borrowed, last>>

\* The application revokes `p`: refused (nothing changes) when the set is full and `p` is not in it; otherwise every
\* live session of `p` ends in the same step. Sessions still waiting at the endpoint are decided later, by the gate.
Revoke(p) ==
    /\ p \in revoked \/ Cardinality(revoked) < MaxRevoked
    /\ revoked' = revoked \cup {p}
    /\ sess' = [i \in Slots |-> IF sess[i].peer = p /\ sess[i].st = "live" THEN [sess[i] EXCEPT !.st = "ended"]
                                ELSE sess[i]]
    /\ UNCHANGED <<cache, borrowed, last>>

\* The application lifts the revocation of `p` (unrevoke); the hook decides about it again.
Lift(p) ==
    /\ revoked' = revoked \ {p}
    /\ UNCHANGED <<cache, sess, borrowed, last>>

\* A session ends for another reason.
End(i) ==
    /\ sess[i].st \in {"wait", "live"}
    /\ sess' = [sess EXCEPT ![i].st = "ended"]
    /\ UNCHANGED <<revoked, cache, borrowed, last>>

\* An ended session gives its slot back.
Free(i) ==
    /\ sess[i].st = "ended"
    /\ sess' = [sess EXCEPT ![i].st = "free"]
    /\ UNCHANGED <<revoked, cache, borrowed, last>>

\* A cached answer lapses.
Expire(p) ==
    /\ cache[p] # "none"
    /\ cache' = [cache EXCEPT ![p] = "none"]
    /\ UNCHANGED <<revoked, sess, borrowed, last>>

\* An endpoint call takes or gives back the core.
Toggle ==
    /\ borrowed' = ~borrowed
    /\ UNCHANGED <<revoked, cache, sess, last>>

\* A layer asks admit about `p`. The old code answered yes whenever the core was borrowed.
Admit(p) ==
    /\ last' = [asked |-> TRUE, peer |-> p, ans |-> IF FailOpen /\ borrowed THEN TRUE ELSE Gate(p),
                wasRevoked |-> p \in revoked]
    /\ UNCHANGED <<revoked, cache, sess, borrowed>>

Next ==
    \/ \E i \in Slots, p \in Peers : Arrive(i, p)
    \/ \E i \in Slots : Decide(i) \/ End(i) \/ Free(i)
    \/ \E p \in Peers : Revoke(p) \/ Lift(p) \/ Expire(p) \/ Admit(p)
    \/ Toggle

Spec == Init /\ [][Next]_vars

\* No session of a revoked peer is live.
NoLiveRevoked == \A i \in Slots : sess[i].st = "live" => sess[i].peer \notin revoked
\* Admit says yes only to a peer that was not revoked at the call and that the hook admits.
AdmitSound == (last.asked /\ last.ans) => (~last.wasRevoked /\ last.peer \in Allowed)
\* The revoked set stays within its bound.
RevokedBound == Cardinality(revoked) <= MaxRevoked
\* Every variable holds a value of its kind.
TypeOK ==
    /\ revoked \subseteq Peers
    /\ \A p \in Peers : cache[p] \in {"none", "allow", "deny"}
    /\ \A i \in Slots : sess[i].peer \in Peers /\ sess[i].st \in {"free", "wait", "live", "ended"}
=============================================================================
