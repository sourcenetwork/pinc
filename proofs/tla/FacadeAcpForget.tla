--------------------------- MODULE FacadeAcpForget ---------------------------
(***************************************************************************)
(* The facade's access decisions: the hook asked for the protocol and      *)
(* direction of each session, the endpoint's one answer per peer, and      *)
(* revoke, unrevoke and hook changes against both.                         *)
(*                                                                         *)
(* Who acts. Peers dial this node and this node dials them; a session has  *)
(* a protocol and a direction, the question the hook is asked about it.    *)
(* The endpoint keeps one answer per peer (30 s in the code, here until an *)
(* Expire step): a session of a peer with an answer is decided on it, else *)
(* the endpoint raises a check. The facade asks the hook about the check's *)
(* question, remembers an allow for exactly that question (Known, the same *)
(* 30 s, here until a Lapse step or a Clear of the whole table) and tells  *)
(* the endpoint "allow" when the gate allows the peer that question or any *)
(* other it asks about: those of the sessions and unfinished dials this    *)
(* node holds with the peer (sess), whatever their protocol, and every     *)
(* listed protocol in both directions. A session the endpoint lets through *)
(* comes up at the facade (session_admitted): refused while its peer is    *)
(* revoked, else taken up if the remembered allow is for its own question  *)
(* or the hook allows that question now. A session asks again before its   *)
(* peer's answer runs out (Recheck), and a deny then closes every session  *)
(* of the peer. This node dials (Dial): the dial is held from that moment, *)
(* and a dial the gate allows drops a refusal the endpoint holds for its   *)
(* peer, so the session of that dial asks with its own question. The       *)
(* application revokes peers, lifts revocations and edits its hook (one    *)
(* answer at a time), telling the endpoint through admission_changed.      *)
(*                                                                         *)
(* The question a check asks: the code asks outbound while a dial of that  *)
(* protocol to the peer waits, else inbound. So the first check of a       *)
(* session this node dialed asks its own question, the first check of an   *)
(* accepted session asks inbound or outbound, and a later check asks       *)
(* inbound or outbound (the dial of a live session no longer waits). The   *)
(* hub's protocol, asked with the gossip direction, is one more listed     *)
(* question.                                                               *)
(*                                                                         *)
(* What must never happen. A session taken up on an allow the hook gave    *)
(* for another protocol or direction (NoCrossAllow, issue #440): every     *)
(* session taken up is one the gate allows for its own question at that    *)
(* moment, or one the remembered allow for exactly its question covers. A  *)
(* deny the endpoint holds for a peer while the gate allows it a listed    *)
(* question or the question of a session or dial held with it              *)
(* (NoCrossDeny): that one answer refuses every new session of the peer. A *)
(* refusal that closes a session the gate allows at that moment (NoCut). A *)
(* session decided on answers the gate would not give now (DecideFresh):   *)
(* it is taken up exactly when the gate allows its own question, let       *)
(* through by the endpoint only for a peer the gate allows something, and  *)
(* refused by it only when the gate allows none of the questions a refusal *)
(* must not stand against, its own among them. A cached allow for a peer   *)
(* the gate allows nothing (CacheSound), a remembered allow the gate would *)
(* not give now (KnownSound: none outlives a revoke, an unrevoke or a hook *)
(* change). A dial of this node reaching a revoked peer (NoDialRevoked):   *)
(* the peer would hold it as a session until our deny arrives, and its own *)
(* dial after the lift would ride it and fail.                             *)
(*                                                                         *)
(* Rust: crates/vinc/src/engine.rs `Core::{session_up, session_admitted,   *)
(* admits_other}` and the `AcpCheck` arm of `on_event`;                    *)
(* crates/vinc/src/engine/gate.rs `Known::{covers, remember, forget}`,     *)
(* `direction`; crates/vinc/src/engine/ops.rs `Core::{connect_start,       *)
(* revoke, unrevoke, forget_access, listen}`; crates/vinc-                 *)
(* core/src/commands.rs `Command::AcpForget`, `Query::PeerSession`,        *)
(* `Query::Access`; crates/vinc-core/src/acp.rs `start_acp`, `ask_acp`,    *)
(* `acp_answer`; crates/vinc-node/src/node.rs `Node::{revoke, unrevoke,    *)
(* forget_access}`; crates/vinc/src/endpoint.rs `Endpoint::{revoke,        *)
(* unrevoke, connect, admission_changed}`. Lean counterpart:               *)
(* Vinc/FacadeAcpForget.lean (the model), Vinc/FacadeAcpForgetThm.lean     *)
(* (`inv_reach`, `noCrossAllow_reach`, `noCrossDeny_reach`, `noCut_reach`) *)
(* and Vinc/FacadeAcpForgetBad.lean (`noForgetOnLift_bad`,                 *)
(* `noForgetOnRevoke_bad`, `noRefuseDial_bad`, `noForgetOnChange_bad`,     *)
(* `perPeer_bad`, `noAny_bad`, `unlisted_bad`, `noDialAsk_bad`).           *)
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
(* session that raised the check and no session is asked on its own, so a  *)
(* protocol the hook refuses comes up on an allow given for another:       *)
(* NoCrossAllow fails. AnswerAny = FALSE alone tells the endpoint the      *)
(* asking session's own refusal: a peer the hook allows on another         *)
(* protocol is refused on it, NoCrossDeny fails. AskHeld = FALSE works the *)
(* answer out over the listed protocols only, as the first part of #440    *)
(* did: a session or a dial on a protocol this node dials without listing  *)
(* it, which the hook allows, is closed by the refusal of a listed         *)
(* protocol or by its own later check, which asks the inbound question:    *)
(* NoCut fails. DialAsks = FALSE keeps a refusal across a dial the hook    *)
(* allows: the refusal stands against that dial, NoCrossDeny fails.        *)
(*                                                                         *)
(* Not modelled exactly, each on the side of more behaviours: a later      *)
(* check may be raised by any session or dial held with the peer; a        *)
(* session the endpoint or the facade refused stays held until an End      *)
(* step; the endpoint's decision and the facade's are one step.            *)
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
    AnswerAny,       \* TRUE: the endpoint is told whether the peer is allowed anything (FALSE: a witness config)
    AskHeld,         \* TRUE: "anything" covers the questions of the peer's sessions and dials (FALSE: a witness config)
    DialAsks         \* TRUE: a dial the gate allows drops a refusal held for its peer (FALSE: a witness config)

ASSUME Listed \cap Dialed = {}

VARIABLES
    hook,     \* the questions the application's hook allows now, per peer; the host edits it
    revoked,  \* the gate's revoked set
    cache,    \* the endpoint's answer per peer: "none", "allow" or "deny"
    known,    \* the facade's remembered allow per peer: {} or {q}, the one question it covers
    last,     \* the last decision: [done, peer, q, ep, up, gate, any, held, cov] (see Decide)
    out,      \* the peers a dial of this node has reached and that hold its session
    sess,     \* the questions of the sessions and unfinished dials this node holds with each peer
    cut       \* a refusal closed a session whose question the gate allowed at that moment

vars == <<hook, revoked, cache, known, last, out, sess, cut>>

Dirs == {"in", "out"}
\* Every question the hook may be asked: a protocol and a direction.
AllQs == (Listed \cup Dialed) \X Dirs
\* The questions of sessions: a listed protocol either way, a dialed one outbound.
Qs == (Listed \X Dirs) \cup (Dialed \X {"out"})
\* The questions of the listed protocols, which the facade always asks about for the endpoint's per-peer answer.
ListedQs == Listed \X Dirs
\* The questions of the sessions this node dials.
OutQs == (Listed \cup Dialed) \X {"out"}
\* The questions a refusal held for `p` must not stand against: the listed ones and those of its sessions and dials.
Held(p) == ListedQs \cup sess[p]
\* The other questions the facade asks about when a check of `p` raised by a session with question `q` is refused
\* (`admits_other`): those of the peer's sessions and dials, the asking session among them, then every listed one.
Others(p, q) == ListedQs \cup (IF AskHeld THEN sess[p] \cup {q} ELSE {})

\* Some peer and some question, to fill fields that are not used yet.
AnyPeer == CHOOSE p \in Peers : TRUE
AnyQ == CHOOSE q \in Qs : TRUE

\* The gate's answer: a revoked peer is refused, any other gets the hook's answer for the question.
Gate(p, q) == p \notin revoked /\ q \in hook[p]

\* Whether the gate allows `p` some protocol and direction a session may have.
Any(p) == \E q \in Qs : Gate(p, q)

\* The endpoint's answer for a check of `p` that asked `a`, raised by a session with question `q`: the gate's answer
\* for `a`, or, with the fix, also an allow when the gate allows the peer another of the questions it asks about.
Told(p, a, q) == Gate(p, a) \/ (AnswerAny /\ \E r \in Others(p, q) \ {a} : Gate(p, r))

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
    /\ {last.ep, last.up, last.gate, last.any, last.held, last.cov} \subseteq BOOLEAN
    /\ out \subseteq Peers
    /\ sess \in [Peers -> SUBSET Qs]
    /\ cut \in BOOLEAN

\* The start: any hook, nobody revoked, nothing cached or remembered, nothing decided, nothing dialed.
Init ==
    /\ hook \in [Peers -> SUBSET AllQs]
    /\ revoked = {}
    /\ cache = [p \in Peers |-> "none"]
    /\ known = [p \in Peers |-> {}]
    /\ last = [done |-> FALSE, peer |-> AnyPeer, q |-> AnyQ, ep |-> FALSE, up |-> FALSE, gate |-> FALSE, any |-> FALSE,
               held |-> FALSE, cov |-> FALSE]
    /\ out = {}
    /\ sess = [p \in Peers |-> {}]
    /\ cut = FALSE

\* A session of `p` with question `q` comes up at the endpoint and is decided; one this node dialed comes up only after
\* its dial (Dial). With no answer for `p` the endpoint raises a check, which asks `a` (answered inside the event, so
\* asking and caching are one step); then the endpoint lets the session through on its answer `ep`, and the facade
\* takes it up (`up`) unless the peer is revoked, the hook asked about `q` itself when the remembered allow is not for
\* `q`. The rule before #440 took up whatever the endpoint let through, with the revoked check only. A session taken
\* up is held; a fresh refusal closes every session and dial of the peer; a session refused on a held answer, or by the
\* facade, ends when the model says so (End). Recorded: what the gate says now about `q` (`gate`), about the peer
\* (`any`) and about the questions a refusal must not stand against, `q` among them (`held`), and whether the
\* remembered allow covered the session (`cov`).
Decide(p, q, a) ==
    LET ask == cache[p] = "none"
        ep  == IF ask THEN Told(p, a, q) ELSE cache[p] = "allow"
        kn  == IF ask THEN KnownAfter(p, a) ELSE known[p]
        up  == ep /\ p \notin revoked /\ (~AskEach \/ q \in kn \/ q \in hook[p])
    IN /\ a \in Asked(q, FALSE)
       /\ q[2] = "out" => q \in sess[p]
       /\ cache' = [cache EXCEPT ![p] = IF ep THEN "allow" ELSE "deny"]
       /\ known' = [known EXCEPT ![p] = kn]
       /\ sess' = [sess EXCEPT ![p] = IF ask /\ ~ep THEN {} ELSE IF up THEN @ \cup {q} ELSE @]
       /\ cut' = (cut \/ (ask /\ ~ep /\ \E r \in sess[p] \cup {q} : Gate(p, r)))
       /\ last' = [done |-> TRUE, peer |-> p, q |-> q, ep |-> ep, up |-> up, gate |-> Gate(p, q), any |-> Any(p),
                   held |-> \E r \in Held(p) \cup {q} : Gate(p, r), cov |-> q \in kn]
       /\ UNCHANGED <<revoked, out>>

\* A session of `p` with question `q` asks again while its peer's allow stands; the check asks `a`, and a deny closes
\* every session of `p` (the endpoint's `acp_answer`).
Recheck(p, q, a) ==
    /\ cache[p] = "allow"
    /\ q \in sess[p]
    /\ a \in Asked(q, TRUE)
    /\ cache' = [cache EXCEPT ![p] = IF Told(p, a, q) THEN "allow" ELSE "deny"]
    /\ known' = [known EXCEPT ![p] = KnownAfter(p, a)]
    /\ sess' = IF Told(p, a, q) THEN sess ELSE [sess EXCEPT ![p] = {}]
    /\ cut' = (cut \/ (~Told(p, a, q) /\ \E r \in sess[p] : Gate(p, r)))
    /\ UNCHANGED <<revoked, last, out>>

\* The application revokes `p`; the fix drops its answers in the same call, and every session with `p` ends.
Revoke(p) ==
    /\ revoked' = revoked \cup {p}
    /\ cache' = IF ForgetOnRevoke THEN [cache EXCEPT ![p] = "none"] ELSE cache
    /\ known' = IF ForgetOnRevoke THEN [known EXCEPT ![p] = {}] ELSE known
    /\ out' = out \ {p}
    /\ sess' = [sess EXCEPT ![p] = {}]
    /\ UNCHANGED <<last, cut>>

\* The application lifts the revocation of `p`; the fix drops its answers in the same call.
Lift(p) ==
    /\ revoked' = revoked \ {p}
    /\ cache' = IF ForgetOnLift THEN [cache EXCEPT ![p] = "none"] ELSE cache
    /\ known' = IF ForgetOnLift THEN [known EXCEPT ![p] = {}] ELSE known
    /\ UNCHANGED <<last, out, sess, cut>>

\* The endpoint's answer for `p` lapses after its 30 s.
Expire(p) ==
    /\ cache[p] # "none"
    /\ cache' = [cache EXCEPT ![p] = "none"]
    /\ UNCHANGED <<revoked, known, last, out, sess, cut>>

\* The remembered allow of `p` lapses, or the bounded table drops it.
Lapse(p) ==
    /\ known[p] # {}
    /\ known' = [known EXCEPT ![p] = {}]
    /\ UNCHANGED <<revoked, cache, last, out, sess, cut>>

\* The full table is cleared (`Known::remember` when no entry has run out): allowed at any time.
Clear ==
    /\ known' = [p \in Peers |-> {}]
    /\ UNCHANGED <<revoked, cache, last, out, sess, cut>>

\* This node dials `p` with question `q`: refused before anything is sent while `p` is revoked, else the dial is held
\* and the session reaches `p`. The endpoint keeps one answer per peer, and a refusal it holds was given for other
\* questions: with the fix a dial the gate allows drops it (and the remembered allow with it), so the session of this
\* dial asks with its own question (`connect_start`).
Dial(p, q) ==
    LET go   == ~(RefuseDial /\ p \in revoked)
        drop == DialAsks /\ go /\ cache[p] = "deny" /\ Gate(p, q)
    IN /\ q \in OutQs
       /\ out' = IF go THEN out \cup {p} ELSE out
       /\ sess' = IF go THEN [sess EXCEPT ![p] = @ \cup {q}] ELSE sess
       /\ cache' = IF drop THEN [cache EXCEPT ![p] = "none"] ELSE cache
       /\ known' = IF drop THEN [known EXCEPT ![p] = {}] ELSE known
       /\ UNCHANGED <<revoked, last, cut>>

\* A session this node dialed ends for another reason.
Hangup(p) ==
    /\ p \in out
    /\ out' = out \ {p}
    /\ UNCHANGED <<revoked, cache, known, last, sess, cut>>

\* A session or a dial with `p` ends: closed by either side, refused, or given up.
End(p, q) ==
    /\ q \in sess[p]
    /\ sess' = [sess EXCEPT ![p] = @ \ {q}]
    /\ UNCHANGED <<revoked, cache, known, last, out, cut>>

\* The host edits its hook's answer for `p` on `q` and, with the fix, calls admission_changed for `p`, which drops
\* both answers of `p`.
Rehook(p, q) ==
    /\ hook' = [hook EXCEPT ![p] = IF q \in hook[p] THEN hook[p] \ {q} ELSE hook[p] \cup {q}]
    /\ cache' = IF ForgetOnChange THEN [cache EXCEPT ![p] = "none"] ELSE cache
    /\ known' = IF ForgetOnChange THEN [known EXCEPT ![p] = {}] ELSE known
    /\ UNCHANGED <<revoked, last, out, sess, cut>>

\* Any of the actions, for any peer and question; every action but Rehook leaves the hook as it is.
Next ==
    \/ /\ \/ \E p \in Peers, q \in Qs, a \in AllQs : Decide(p, q, a) \/ Recheck(p, q, a)
          \/ \E p \in Peers : Revoke(p) \/ Lift(p) \/ Expire(p) \/ Lapse(p) \/ Hangup(p)
          \/ \E p \in Peers, q \in Qs : Dial(p, q) \/ End(p, q)
          \/ Clear
       /\ UNCHANGED hook
    \/ \E p \in Peers, q \in AllQs : Rehook(p, q)

\* The behaviours: start at Init, then take Next steps (or stutter).
Spec == Init /\ [][Next]_vars

\* Every session is decided with the answers the gate gives at that moment: it is taken up exactly when the gate
\* allows its own question, the endpoint lets it through only for a peer the gate allows something, and refuses it
\* only when the gate allows none of the questions a refusal must not stand against, its own among them. With every
\* protocol listed the two are one: the endpoint's answer is whether the gate allows the peer anything.
DecideFresh == last.done => (last.up = last.gate /\ (last.ep => last.any) /\ (~last.ep => ~last.held))
\* Every cached allow is for a peer the gate allows something now (a cached deny: NoCrossDeny).
CacheSound == \A p \in Peers : cache[p] = "allow" => Any(p)
\* Every remembered allow is one the gate gives now, for exactly that question.
KnownSound == \A p \in Peers : \A q \in known[p] : Gate(p, q)
\* No revoked peer holds a session this node dialed.
NoDialRevoked == out \cap revoked = {}
\* No session is taken up on an allow given for another protocol or direction: the gate allows its own question at
\* that moment, or the remembered allow is for exactly its question.
NoCrossAllow == (last.done /\ last.up) => (last.gate \/ last.cov)
\* The endpoint holds a deny only for a peer the gate allows none of the listed questions and none of the questions of
\* the sessions and dials this node holds with it, so a refusal of one protocol never refuses a session or a dial of
\* another the hook allows.
NoCrossDeny == \A p \in Peers : cache[p] = "deny" => \A q \in Held(p) : ~Gate(p, q)
\* No refusal closed a session whose question the gate allowed at that moment.
NoCut == ~cut
=============================================================================
