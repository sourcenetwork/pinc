--------------------------- MODULE FacadeAcpForget ---------------------------
(***************************************************************************)
(* The facade's access decisions: the hook asked for the protocol and      *)
(* direction of each session, the endpoint's one answer per peer, and      *)
(* revoke, unrevoke and hook changes against both.                         *)
(*                                                                         *)
(* Who acts. Peers dial this node and this node dials them; a session has  *)
(* a protocol and a direction, the question the hook is asked about it.    *)
(* The endpoint keeps one answer per peer (30 s in the code, here until an *)
(* Expire step): a session of a peer with an answer is decided on it,      *)
(* else the endpoint raises a check. The facade asks the hook about the    *)
(* check's question, remembers an allow for exactly that question (Known,  *)
(* the same 30 s, here until a Lapse step or a Clear of the whole table)   *)
(* and tells the endpoint "allow" when the gate allows the peer that       *)
(* question or any other of the listed protocols and directions. A session *)
(* the endpoint lets through comes up at the facade (session_admitted):    *)
(* refused while its peer is revoked, else taken up if the remembered      *)
(* allow is for its own question or the hook allows that question now. A   *)
(* live session asks again before its peer's answer runs out (Recheck),    *)
(* and a deny then closes every session of the peer. The application       *)
(* revokes peers, lifts revocations and edits its hook (one answer at a    *)
(* time), telling the endpoint through admission_changed.                  *)
(*                                                                         *)
(* The question a check asks: the code asks outbound while a dial of that  *)
(* protocol to the peer waits, else inbound. So the first check of a       *)
(* session this node dialed asks its own question, the first check of an   *)
(* accepted session asks inbound or outbound, and a recheck asks inbound   *)
(* or outbound (the dial of a live session no longer waits). The hub's     *)
(* protocol, asked with the gossip direction, is one more listed question. *)
(*                                                                         *)
(* What must never happen. A session taken up on an allow the hook gave    *)
(* for another protocol or direction (NoCrossAllow, issue #440): every     *)
(* session taken up is one the gate allows for its own question at that    *)
(* moment, or one the remembered allow for exactly its question covers. A  *)
(* deny the endpoint holds for a peer the gate allows some question        *)
(* (NoCrossDeny): that one answer refuses every new session of the peer,   *)
(* and the check that gave it closed every live one, so a refusal of one   *)
(* protocol would end the sessions of another the hook allows. A session   *)
(* decided on answers the gate would not give now (DecideFresh): the       *)
(* endpoint's answer for its peer is whether the gate allows the peer      *)
(* anything, and the session is taken up exactly when the gate allows its  *)
(* own question. A cached answer that is not the gate's now (CacheSound),  *)
(* a remembered allow the gate would not give now (KnownSound: none        *)
(* outlives a revoke, an unrevoke or a hook change). A dial of this node   *)
(* reaching a revoked peer (NoDialRevoked): the peer would hold it as a    *)
(* session until our deny arrives, and its own dial after the lift would   *)
(* ride it and fail.                                                       *)
(*                                                                         *)
(* Rust: crates/vinc/src/engine.rs `Core::{session_up, session_admitted,   *)
(* admits_other}` and the `AcpCheck` arm of `on_event`;                    *)
(* crates/vinc/src/engine/gate.rs `Known::{covers, remember, forget}`,     *)
(* `direction`; crates/vinc/src/engine/ops.rs `Core::{revoke, unrevoke,    *)
(* forget_access, listen}`; crates/vinc-core/src/commands.rs               *)
(* `Command::AcpForget`; crates/vinc-core/src/acp.rs `start_acp`,          *)
(* `ask_acp`, `acp_answer`; crates/vinc-node/src/node.rs                   *)
(* `Node::{revoke, unrevoke, forget_access}`; crates/vinc/src/endpoint.rs  *)
(* `Endpoint::{revoke, unrevoke, connect, admission_changed}`.             *)
(* Lean counterpart: Vinc/FacadeAcpForget.lean (`inv_reach`,               *)
(* `noCrossAllow_reach`, `noCrossDeny_reach`, `noForgetOnLift_bad`,        *)
(* `noForgetOnRevoke_bad`, `noRefuseDial_bad`, `noForgetOnChange_bad`,     *)
(* `perPeer_bad`, `noAny_bad`, `unlisted_bad`).                            *)
(*                                                                         *)
(* Witnesses (scripts/proofs.sh witness_tlc): ForgetOnLift = FALSE is the  *)
(* code before the unrevoke fix: a peer that dialed while revoked is still *)
(* refused after unrevoke, on the cached deny. ForgetOnRevoke = FALSE      *)
(* keeps the cached answer across a revoke: the endpoint lets the revoked  *)
(* peer's session through without asking. Both break DecideFresh.          *)
(* RefuseDial = FALSE lets a dial to a revoked peer go out: NoDialRevoked  *)
(* fails. ForgetOnChange = FALSE is a host that edits its hook without     *)
(* telling the endpoint: the peer it just allowed is refused on the cached *)
(* deny, and DecideFresh fails. AskEach = FALSE with AnswerAny = FALSE is  *)
(* the rule before #440: the endpoint gets the hook's answer for the       *)
(* session that raised the check and no session is asked on its own, so a *)
(* protocol the hook refuses comes up on an allow given for another:       *)
(* NoCrossAllow fails. AnswerAny = FALSE alone tells the endpoint the      *)
(* asking session's own refusal: a peer the hook allows on another         *)
(* protocol is refused on it, NoCrossDeny fails.                           *)
(*                                                                         *)
(* Found (FacadeAcpForget_unlisted, Dialed not empty): the "allowed        *)
(* something" answer asks only about the listed protocols, and a recheck   *)
(* of a session this node dialed asks the inbound question. So an          *)
(* outbound session on a protocol this node dials without listing it is    *)
(* closed at its recheck, about 25 s in, when the hook refuses that        *)
(* protocol inbound and every listed one; and a refused session of a      *)
(* listed protocol gets the endpoint the same deny, which closes such a    *)
(* session and refuses this node's dials on that protocol for 30 s.        *)
(* NoCrossDeny fails. The code's configuration lists every protocol a      *)
(* session uses (Dialed = {}).                                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Peers,           \* the peers sessions are with
    Listed,          \* the protocols the facade lists (the builder's and those registered since): sessions either way
    Dialed,          \* protocols this node dials without listing them: outbound sessions only ({} in the code's config)
    ForgetOnLift,    \* TRUE: unrevoke drops the peer's answers (FALSE: a witness config)
    ForgetOnRevoke,  \* TRUE: revoke drops the peer's answers (FALSE: a witness config)
    RefuseDial,      \* TRUE: a dial to a revoked peer is refused before anything is sent (FALSE: a witness config)
    ForgetOnChange,  \* TRUE: the host calls admission_changed when the hook's answer changes (FALSE: a witness config)
    AskEach,         \* TRUE: each session is decided on its own question (FALSE: the rule before #440, a witness)
    AnswerAny        \* TRUE: the endpoint is told whether the peer is allowed anything (FALSE: a witness config)

ASSUME Listed \cap Dialed = {}

VARIABLES
    hook,     \* the questions the application's hook allows now, per peer; the host edits it
    revoked,  \* the gate's revoked set
    cache,    \* the endpoint's answer per peer: "none", "allow" or "deny"
    known,    \* the facade's remembered allow per peer: {} or {q}, the one question it covers
    last,     \* the last decision: [done, peer, q, ep, up, gate, any, cov] (see Decide)
    out       \* the peers a dial of this node has reached and that hold its session

vars == <<hook, revoked, cache, known, last, out>>

Dirs == {"in", "out"}
\* Every question the hook may be asked: a protocol and a direction.
AllQs == (Listed \cup Dialed) \X Dirs
\* The questions of sessions: a listed protocol either way, a dialed one outbound.
Qs == (Listed \X Dirs) \cup (Dialed \X {"out"})
\* The questions the facade asks about for the endpoint's per-peer answer (`admits_other`).
ListedQs == Listed \X Dirs

\* Some peer and some question, to fill fields that are not used yet.
AnyPeer == CHOOSE p \in Peers : TRUE
AnyQ == CHOOSE q \in Qs : TRUE

\* The gate's answer: a revoked peer is refused, any other gets the hook's answer for the question.
Gate(p, q) == p \notin revoked /\ q \in hook[p]

\* Whether the gate allows `p` some protocol and direction a session may have.
Any(p) == \E q \in Qs : Gate(p, q)

\* The endpoint's answer for a check of `p` that asked `a`: the gate's answer for `a`, or, with the fix, also an allow
\* when the gate allows the peer another listed question.
Told(p, a) == Gate(p, a) \/ (AnswerAny /\ \E q \in ListedQs \ {a} : Gate(p, q))

\* What the facade remembers after a check of `p` that asked `a`: an allow for exactly `a`, never a refusal.
KnownAfter(p, a) == IF AskEach /\ Gate(p, a) THEN {a} ELSE {}

\* The questions a check raised by a session with question `q` may ask (see the header); `again` for a recheck.
Asked(q, again) == IF ~again /\ q[2] = "out" THEN {q} ELSE {<<q[1], d>> : d \in Dirs}

\* Every variable has the shape it should.
TypeOK ==
    /\ hook \in [Peers -> SUBSET AllQs]
    /\ revoked \subseteq Peers
    /\ cache \in [Peers -> {"none", "allow", "deny"}]
    /\ known \in [Peers -> SUBSET AllQs] /\ \A p \in Peers : Cardinality(known[p]) <= 1
    /\ last.done \in BOOLEAN /\ last.peer \in Peers /\ last.q \in Qs
    /\ {last.ep, last.up, last.gate, last.any, last.cov} \subseteq BOOLEAN
    /\ out \subseteq Peers

\* The start: any hook, nobody revoked, nothing cached or remembered, nothing decided, nothing dialed.
Init ==
    /\ hook \in [Peers -> SUBSET AllQs]
    /\ revoked = {}
    /\ cache = [p \in Peers |-> "none"]
    /\ known = [p \in Peers |-> {}]
    /\ last = [done |-> FALSE, peer |-> AnyPeer, q |-> AnyQ, ep |-> FALSE, up |-> FALSE, gate |-> FALSE, any |-> FALSE,
               cov |-> FALSE]
    /\ out = {}

\* A session of `p` with question `q` comes up at the endpoint and is decided. With no answer for `p` the endpoint
\* raises a check, which asks `a` (answered inside the event, so asking and caching are one step); then the endpoint
\* lets the session through on its answer `ep`, and the facade takes it up (`up`) unless the peer is revoked, the hook
\* asked about `q` itself when the remembered allow is not for `q`. The rule before #440 took up whatever the endpoint
\* let through, with the revoked check only. Recorded: what the gate says now about `q` (`gate`) and about the peer
\* (`any`), and whether the remembered allow covered the session (`cov`).
Decide(p, q, a) ==
    LET ask == cache[p] = "none"
        ep  == IF ask THEN Told(p, a) ELSE cache[p] = "allow"
        kn  == IF ask THEN KnownAfter(p, a) ELSE known[p]
        up  == ep /\ p \notin revoked /\ (~AskEach \/ q \in kn \/ q \in hook[p])
    IN /\ a \in Asked(q, FALSE)
       /\ cache' = [cache EXCEPT ![p] = IF ep THEN "allow" ELSE "deny"]
       /\ known' = [known EXCEPT ![p] = kn]
       /\ last' = [done |-> TRUE, peer |-> p, q |-> q, ep |-> ep, up |-> up, gate |-> Gate(p, q), any |-> Any(p),
                   cov |-> q \in kn]
       /\ UNCHANGED <<revoked, out>>

\* A live session of `p` with question `q` asks again while its peer's allow stands; the check asks `a`, and a deny
\* closes every session of `p` (the endpoint's `acp_answer`).
Recheck(p, q, a) ==
    /\ cache[p] = "allow"
    /\ a \in Asked(q, TRUE)
    /\ cache' = [cache EXCEPT ![p] = IF Told(p, a) THEN "allow" ELSE "deny"]
    /\ known' = [known EXCEPT ![p] = KnownAfter(p, a)]
    /\ UNCHANGED <<revoked, last, out>>

\* The application revokes `p`; the fix drops its answers in the same call, and every session with `p` ends.
Revoke(p) ==
    /\ revoked' = revoked \cup {p}
    /\ cache' = IF ForgetOnRevoke THEN [cache EXCEPT ![p] = "none"] ELSE cache
    /\ known' = IF ForgetOnRevoke THEN [known EXCEPT ![p] = {}] ELSE known
    /\ out' = out \ {p}
    /\ UNCHANGED last

\* The application lifts the revocation of `p`; the fix drops its answers in the same call.
Lift(p) ==
    /\ revoked' = revoked \ {p}
    /\ cache' = IF ForgetOnLift THEN [cache EXCEPT ![p] = "none"] ELSE cache
    /\ known' = IF ForgetOnLift THEN [known EXCEPT ![p] = {}] ELSE known
    /\ UNCHANGED <<last, out>>

\* The endpoint's answer for `p` lapses after its 30 s.
Expire(p) ==
    /\ cache[p] # "none"
    /\ cache' = [cache EXCEPT ![p] = "none"]
    /\ UNCHANGED <<revoked, known, last, out>>

\* The remembered allow of `p` lapses, or the bounded table drops it.
Lapse(p) ==
    /\ known[p] # {}
    /\ known' = [known EXCEPT ![p] = {}]
    /\ UNCHANGED <<revoked, cache, last, out>>

\* The full table is cleared (`Known::remember` when no entry has run out): allowed at any time.
Clear ==
    /\ known' = [p \in Peers |-> {}]
    /\ UNCHANGED <<revoked, cache, last, out>>

\* This node dials `p`: refused before anything is sent while `p` is revoked, else the session reaches `p`.
Dial(p) ==
    /\ out' = IF RefuseDial /\ p \in revoked THEN out ELSE out \cup {p}
    /\ UNCHANGED <<revoked, cache, known, last>>

\* A session this node dialed ends for another reason.
Hangup(p) ==
    /\ p \in out
    /\ out' = out \ {p}
    /\ UNCHANGED <<revoked, cache, known, last>>

\* The host edits its hook's answer for `p` on `q` and, with the fix, calls admission_changed for `p`, which drops
\* both answers of `p`.
Rehook(p, q) ==
    /\ hook' = [hook EXCEPT ![p] = IF q \in hook[p] THEN hook[p] \ {q} ELSE hook[p] \cup {q}]
    /\ cache' = IF ForgetOnChange THEN [cache EXCEPT ![p] = "none"] ELSE cache
    /\ known' = IF ForgetOnChange THEN [known EXCEPT ![p] = {}] ELSE known
    /\ UNCHANGED <<revoked, last, out>>

\* Any of the actions, for any peer and question; every action but Rehook leaves the hook as it is.
Next ==
    \/ /\ \/ \E p \in Peers, q \in Qs, a \in AllQs : Decide(p, q, a) \/ Recheck(p, q, a)
          \/ \E p \in Peers : Revoke(p) \/ Lift(p) \/ Expire(p) \/ Lapse(p) \/ Dial(p) \/ Hangup(p)
          \/ Clear
       /\ UNCHANGED hook
    \/ \E p \in Peers, q \in AllQs : Rehook(p, q)

\* The behaviours: start at Init, then take Next steps (or stutter).
Spec == Init /\ [][Next]_vars

\* Every session is decided with the answers the gate gives at that moment: the endpoint's for its peer is whether the
\* gate allows the peer anything, and the session is taken up exactly when the gate allows its own question.
DecideFresh == last.done => (last.ep = last.any /\ last.up = last.gate)
\* Every cached answer is the one the gate would give now: whether it allows the peer anything.
CacheSound == \A p \in Peers : cache[p] # "none" => ((cache[p] = "allow") = Any(p))
\* Every remembered allow is one the gate gives now, for exactly that question.
KnownSound == \A p \in Peers : \A q \in known[p] : Gate(p, q)
\* No revoked peer holds a session this node dialed.
NoDialRevoked == out \cap revoked = {}
\* No session is taken up on an allow given for another protocol or direction: the gate allows its own question at
\* that moment, or the remembered allow is for exactly its question.
NoCrossAllow == (last.done /\ last.up) => (last.gate \/ last.cov)
\* The endpoint holds a deny only for a peer the gate allows no protocol and direction a session may have, so a
\* refusal of one protocol never refuses or closes a session of another the hook allows.
NoCrossDeny == \A p \in Peers : cache[p] = "deny" => \A q \in Qs : ~Gate(p, q)
=============================================================================
