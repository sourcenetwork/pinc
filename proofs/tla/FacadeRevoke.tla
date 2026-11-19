---------------------------- MODULE FacadeRevoke ----------------------------
(***************************************************************************)
(* The facade's access gate: revocation and admit.                          *)
(*                                                                         *)
(* Who acts. Peers open sessions (either direction, on any protocol, the    *)
(* hub's included) that reach the endpoint. The endpoint decides a session  *)
(* on its answer for the peer, or raises a check: the facade asks the gate  *)
(* about the session's protocol in a direction, remembers an allow for     *)
(* exactly that question, and tells the endpoint whether the gate allows    *)
(* the peer anything; the endpoint caches that (30 s in the code, here      *)
(* until an Expire step) and the remembered allow lasts as long (here until *)
(* a Lapse step). A session the endpoint lets through comes up at the       *)
(* facade (session_admitted): refused while its peer is revoked, else taken *)
(* up if the remembered allow is for its protocol and direction or the gate *)
(* allows them. The application revokes peers; a layer above asks admit at  *)
(* any moment, also while an endpoint call holds the core borrowed (the     *)
(* hook runs inside such a call).                                           *)
(*                                                                         *)
(* What must never happen. A session of a revoked peer is live after the    *)
(* revoke step (NoLiveRevoked: the revoke ends them in the same step, and a *)
(* session that comes up later on a cached or remembered allow is turned    *)
(* away); admit says yes to a revoked peer or for a protocol and direction  *)
(* the hook refuses (AdmitSound); the revoked set grows past its bound      *)
(* (RevokedBound).                                                         *)
(*                                                                         *)
(* Rust: crates/pinc/src/engine/gate.rs                                    *)
(* `Gate::{bar, lift, is_revoked, admit}`, `Known::covers`;                *)
(* crates/pinc/src/engine/ops.rs `Core::revoke`; crates/pinc/src/engine.rs *)
(* `Core::{session_up, session_admitted}` (the revoked check) and the      *)
(* `AcpCheck` arm of `on_event`; crates/pinc/src/endpoint.rs               *)
(* `Endpoint::{revoke, unrevoke, admit}`.                                  *)
(* Lean counterpart: Pinc/FacadeRevoke.lean (`inv_reach`, `failOpen_bad`,   *)
(* `noBackstop_bad`).                                                       *)
(*                                                                         *)
(* Witnesses (scripts/proofs.sh witness_tlc): FailOpen = TRUE is the old    *)
(* admit, which answered yes whenever the core was borrowed: AdmitSound     *)
(* fails. Backstop = FALSE drops the revoked check of session_admitted: a   *)
(* revoked peer comes back on the endpoint's cached allow and the facade's  *)
(* remembered allow, and NoLiveRevoked fails.                               *)
(*                                                                         *)
(* The code also drops both answers on revoke and unrevoke and refuses a    *)
(* dial to a revoked peer up front; FacadeAcpForget models those, and the   *)
(* question each check asks. Here both answers outlive the revoke and the   *)
(* lift and dials go out, so the backstop is shown to hold on its own.      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Peers,       \* the peers that may open sessions
    Protos,      \* the protocols sessions are on
    Slots,       \* the session slots of the endpoint
    MaxRevoked,  \* REVOKED_MAX, shrunk
    FailOpen,    \* TRUE: the old admit (a witness config)
    Backstop     \* FALSE: no revoked check when a session comes up (a witness config)

VARIABLES
    hook,      \* the questions the application's hook allows, per peer: any at the start, then fixed
    revoked,   \* the gate's revoked set
    cache,     \* the endpoint's answer per peer: "none", "allow" or "deny"
    known,     \* the facade's remembered allow per peer: {} or {q}, the one question it covers
    sess,      \* per slot: [peer, q, st] with st "free", "wait" (at the endpoint, no answer yet), "live", "ended"
    borrowed,  \* an endpoint call holds the core
    last       \* the last admit call: [asked, peer, q, ans, wasRevoked]; asked is FALSE before the first

vars == <<hook, revoked, cache, known, sess, borrowed, last>>

Dirs == {"in", "out"}
\* The question of a session: a protocol and a direction.
Qs == Protos \X Dirs

\* Some peer and some question, to fill fields that are not used yet.
AnyPeer == CHOOSE p \in Peers : TRUE
AnyQ == CHOOSE q \in Qs : TRUE

\* The gate's answer: a revoked peer is refused, any other gets the hook's answer for the question.
Gate(p, q) == p \notin revoked /\ q \in hook[p]

Init ==
    /\ hook \in [Peers -> SUBSET Qs]
    /\ revoked = {}
    /\ cache = [p \in Peers |-> "none"]
    /\ known = [p \in Peers |-> {}]
    /\ sess = [i \in Slots |-> [peer |-> AnyPeer, q |-> AnyQ, st |-> "free"]]
    /\ borrowed = FALSE
    /\ last = [asked |-> FALSE, peer |-> AnyPeer, q |-> AnyQ, ans |-> FALSE, wasRevoked |-> FALSE]

\* A session of `p` with question `q` reaches the endpoint, from either side's dial. A dial to a revoked peer is not
\* refused up front: its session is turned away when it comes up (Up).
Arrive(i, p, q) ==
    /\ sess[i].st = "free"
    /\ sess' = [sess EXCEPT ![i] = [peer |-> p, q |-> q, st |-> "wait"]]
    /\ UNCHANGED <<hook, revoked, cache, known, borrowed, last>>

\* The session comes up at the facade with the remembered allow `kn` of its peer: turned away if its peer is revoked
\* (with the backstop), else live when `kn` is for its question or the gate allows it.
Up(i, kn) ==
    [sess EXCEPT ![i].st = IF Backstop /\ sess[i].peer \in revoked THEN "ended"
                           ELSE IF sess[i].q \in kn \/ Gate(sess[i].peer, sess[i].q) THEN "live" ELSE "ended"]

\* The endpoint decides a waiting session: a cached allow lets it up without a check, a cached deny ends it, and
\* otherwise a check asks the gate about its protocol in a direction (`a`), the facade remembers an allow for `a` and
\* tells the endpoint whether the gate allows the peer anything, and the endpoint caches that.
Decide(i, a) ==
    LET p == sess[i].peer
        told == \E x \in Qs : Gate(p, x)
        kn == IF Gate(p, a) THEN {a} ELSE {}
    IN
    /\ sess[i].st = "wait"
    /\ a \in {<<sess[i].q[1], d>> : d \in Dirs}
    /\ IF cache[p] = "allow" THEN sess' = Up(i, known[p]) /\ UNCHANGED <<cache, known>>
       ELSE IF cache[p] = "deny" THEN sess' = [sess EXCEPT ![i].st = "ended"] /\ UNCHANGED <<cache, known>>
       ELSE /\ cache' = [cache EXCEPT ![p] = IF told THEN "allow" ELSE "deny"]
            /\ known' = [known EXCEPT ![p] = kn]
            /\ sess' = IF told THEN Up(i, kn) ELSE [sess EXCEPT ![i].st = "ended"]
    /\ UNCHANGED <<hook, revoked, borrowed, last>>

\* The application revokes `p`: refused (nothing changes) when the set is full and `p` is not in it; otherwise every
\* live session of `p` ends in the same step. Sessions still waiting at the endpoint are decided later.
Revoke(p) ==
    /\ p \in revoked \/ Cardinality(revoked) < MaxRevoked
    /\ revoked' = revoked \cup {p}
    /\ sess' = [i \in Slots |-> IF sess[i].peer = p /\ sess[i].st = "live" THEN [sess[i] EXCEPT !.st = "ended"]
                                ELSE sess[i]]
    /\ UNCHANGED <<hook, cache, known, borrowed, last>>

\* The application lifts the revocation of `p` (unrevoke); the hook decides about it again.
Lift(p) ==
    /\ revoked' = revoked \ {p}
    /\ UNCHANGED <<hook, cache, known, sess, borrowed, last>>

\* A session ends for another reason.
End(i) ==
    /\ sess[i].st \in {"wait", "live"}
    /\ sess' = [sess EXCEPT ![i].st = "ended"]
    /\ UNCHANGED <<hook, revoked, cache, known, borrowed, last>>

\* An ended session gives its slot back.
Free(i) ==
    /\ sess[i].st = "ended"
    /\ sess' = [sess EXCEPT ![i].st = "free"]
    /\ UNCHANGED <<hook, revoked, cache, known, borrowed, last>>

\* The endpoint's answer for `p` lapses.
Expire(p) ==
    /\ cache[p] # "none"
    /\ cache' = [cache EXCEPT ![p] = "none"]
    /\ UNCHANGED <<hook, revoked, known, sess, borrowed, last>>

\* The remembered allow of `p` lapses, or the bounded table drops it.
Lapse(p) ==
    /\ known[p] # {}
    /\ known' = [known EXCEPT ![p] = {}]
    /\ UNCHANGED <<hook, revoked, cache, sess, borrowed, last>>

\* An endpoint call takes or gives back the core.
Toggle ==
    /\ borrowed' = ~borrowed
    /\ UNCHANGED <<hook, revoked, cache, known, sess, last>>

\* A layer asks admit about `p` on question `q`. The old code answered yes whenever the core was borrowed.
Admit(p, q) ==
    /\ last' = [asked |-> TRUE, peer |-> p, q |-> q, ans |-> IF FailOpen /\ borrowed THEN TRUE ELSE Gate(p, q),
                wasRevoked |-> p \in revoked]
    /\ UNCHANGED <<hook, revoked, cache, known, sess, borrowed>>

Next ==
    \/ \E i \in Slots, p \in Peers, q \in Qs : Arrive(i, p, q)
    \/ \E i \in Slots, a \in Qs : Decide(i, a)
    \/ \E i \in Slots : End(i) \/ Free(i)
    \/ \E p \in Peers : Revoke(p) \/ Lift(p) \/ Expire(p) \/ Lapse(p)
    \/ \E p \in Peers, q \in Qs : Admit(p, q)
    \/ Toggle

Spec == Init /\ [][Next]_vars

\* No session of a revoked peer is live.
NoLiveRevoked == \A i \in Slots : sess[i].st = "live" => sess[i].peer \notin revoked
\* Admit says yes only to a peer that was not revoked at the call, for a question the hook allows.
AdmitSound == (last.asked /\ last.ans) => (~last.wasRevoked /\ last.q \in hook[last.peer])
\* The revoked set stays within its bound.
RevokedBound == Cardinality(revoked) <= MaxRevoked
\* Every variable holds a value of its kind.
TypeOK ==
    /\ hook \in [Peers -> SUBSET Qs]
    /\ revoked \subseteq Peers
    /\ \A p \in Peers : cache[p] \in {"none", "allow", "deny"} /\ known[p] \subseteq Qs /\ Cardinality(known[p]) <= 1
    /\ \A i \in Slots : sess[i].peer \in Peers /\ sess[i].q \in Qs /\ sess[i].st \in {"free", "wait", "live", "ended"}
=============================================================================
