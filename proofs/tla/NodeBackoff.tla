------------------------------ MODULE NodeBackoff ------------------------------
(***************************************************************************)
(* The node's table of failed dials and its table of dials in progress     *)
(* (pinc-node io.rs, duties.rs, events.rs), over every interleaving of     *)
(* dials, connections, failed dials, sessions the full session table shed, *)
(* closed sessions and the prune at any times from a small set (a clock    *)
(* that steps back and times at the top of the u64 range included), at     *)
(* small sizes (NodeBackoffOps.tla has the operators).                     *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - each table stays within MAXT entries, whatever fails (Bounded);      *)
(*  - every wait is at least BACKOFF_FIRST (2 s), at most DENY_CAP (900 s) *)
(*    and never past the time of its entry: no wraparound (Waits);         *)
(*  - a dial is made only for a peer with no session, no dial in progress, *)
(*    not revoked, and outside its backoff window (`now < until`), and a   *)
(*    dial is refused only for one of those reasons (Right);               *)
(*  - a failed dial waits BACKOFF_FIRST the first time and then twice the  *)
(*    wait of its entry up to the cap (16 s for a hub, 60 s for any other  *)
(*    node), and the wait is at most the cap; a refusal waits DENY_FIRST   *)
(*    or, from an entry of at least that, twice up to DENY_CAP (Right);    *)
(*  - a full table refuses an entry for a peer it has none for and         *)
(*    changes nothing: it never evicts; every other entry is kept (Right); *)
(*  - the entry's time is the time of the failure plus its wait,           *)
(*    saturating at u64::MAX (Right);                                      *)
(*  - a closed session forgets the entry of its peer when it lived at      *)
(*    least 5 s, is a failed dial when it lived less, and is a refusal     *)
(*    when the peer refused us (Right);                                    *)
(*  - a dial whose session came up and that the full session table shed   *)
(*    (events.rs `hub_connected`: `admit` refuses it and closes it) is a   *)
(*    failed dial: it makes the entry a failed dial makes, so the peer is  *)
(*    redialed after the wait and not at every duty pass (Right);          *)
(*  - the prune lets go of exactly the entries whose time plus 3600 s      *)
(*    (saturating) is not after now (Right);                               *)
(*  - a peer is never in the dials in progress and in a session at once    *)
(*    (Disjoint).                                                          *)
(* IGNORE_WINDOW is a dial that skips the window check. The witness        *)
(* NodeBackoff_window sets it and Right fails. SHED_FREE is the rule       *)
(* before issue 367: a shed session leaves the table as it was, so the hub *)
(* is redialed at the next duty pass. The witness NodeBackoff_shedfree     *)
(* sets it and Right fails. The other witnesses are reachability: a table  *)
(* that fills, a new peer refused by it, an entry at the cap, an entry     *)
(* saturated at u64::MAX, a reset, a prune, a shed.                        *)
(* The session table is not in the state: a shed may come for any peer at  *)
(* any time, also for one that has a session (our dial came up while a     *)
(* session the peer opened was already in use).                           *)
(* Known limitation (low severity, filed): once the table is full a        *)
(* newly failing or shed peer has no entry and is redialed at every duty   *)
(* pass.                                                                   *)
(* Lean counterpart: proofs/lean/Pinc/NodeBackoff*.lean.                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Nanos
CONSTANTS MAXT, PEERS, HUBS, REV, TIMES, IGNORE_WINDOW, SHED_FREE
VARIABLES F, C, op, right, seen
vars == <<F, C, op, right, seen>>

INSTANCE NodeBackoffOps

TimesDef == {Zero, Sec(70), U!Max64}

Conn == {p \in PEERS : op[p] # None}
Hub(p) == p \in HUBS

Init == F = Tab0(PEERS) /\ C = {} /\ op = [p \in PEERS |-> None] /\ right = TRUE /\ seen = {}

\* ---- what each rule must give, stated on exact words ----
Sat(a, b) == LET s == U!Add(a, b) IN IF U!Fits(s) THEN s ELSE U!Max64
Twice(b, cap) == LET d == U!Add(b, b) IN IF Lt(cap, d) THEN cap ELSE d

\* a failed dial of p at t that waited `back`, the table before F and after F2
BackoffRight(F1, F2, t, p, back) ==
    LET b == F1[p]
        cap == IF Hub(p) THEN Sec(16) ELSE Sec(60)
        stored == Size(F1) < MAXT \/ b # None
    IN /\ back = IF b = None THEN Sec(2) ELSE Twice(b[2], cap)
       /\ Le(back, cap)
       /\ F2 = IF stored THEN [F1 EXCEPT ![p] = <<Sat(t, back), back>>] ELSE F1

DenyRight(F1, F2, t, p, back) ==
    LET b == F1[p]
        stored == Size(F1) < MAXT \/ b # None
    IN /\ back = IF b # None /\ Le(Sec(60), b[2]) THEN Twice(b[2], Sec(900)) ELSE Sec(60)
       /\ Le(Sec(60), back) /\ Le(back, Sec(900))
       /\ F2 = IF stored THEN [F1 EXCEPT ![p] = <<Sat(t, back), back>>] ELSE F1

Refused(F1, p) == Size(F1) >= MAXT /\ F1[p] = None
Mark(F1, p, name) == IF Refused(F1, p) THEN seen \cup {name, "refused"} ELSE seen \cup {name}

\* ---- the steps ----
DialStep == \E t \in TIMES, p \in PEERS, ok \in BOOLEAN, lv \in BOOLEAN :
    LET open == ~lv /\ p \notin Conn /\ p \notin C /\ p \notin REV
        g == IF IGNORE_WINDOW THEN open ELSE Gate(F, t, p, Conn, C, REV, lv)
        x == Backoff(F, t, p, Hub(p))
    IN /\ right' = (right /\ (g => open /\ ~Window(F, t, p))
                          /\ (open /\ Window(F, t, p) => ~g)
                          /\ (g /\ ~ok => BackoffRight(F, x.f, t, p, x.back)))
       /\ IF g /\ ok THEN C' = Connecting(C, p) /\ F' = F
          ELSE IF g THEN F' = x.f /\ C' = C
          ELSE F' = F /\ C' = C
       /\ seen' = IF g /\ ~ok THEN Mark(F, p, "failed")
                  ELSE IF open /\ Window(F, t, p) /\ ~g THEN seen \cup {"blocked"} ELSE seen
       /\ UNCHANGED op

ConnectedStep == \E t \in TIMES, p \in PEERS \ Conn :
    /\ C' = C \ {p} /\ op' = [op EXCEPT ![p] = t] /\ UNCHANGED <<F, right, seen>>

FailedStep == \E t \in TIMES, p \in C, den \in BOOLEAN :
    LET x == IF den THEN DenyBack(F, t, p) ELSE Backoff(F, t, p, Hub(p))
    IN /\ C' = C \ {p} /\ F' = x.f
       /\ right' = (right /\ IF den THEN DenyRight(F, x.f, t, p, x.back) ELSE BackoffRight(F, x.f, t, p, x.back))
       /\ seen' = Mark(F, p, IF den THEN "deny" ELSE "failed")
       /\ UNCHANGED op

\* our dial of p came up and the full session table shed the session (hub_connected): the dial is over, the peer has
\* no new session, and it is a failed dial
ShedStep == \E t \in TIMES, p \in PEERS :
    LET x == Backoff(F, t, p, Hub(p))
        f2 == IF SHED_FREE THEN F ELSE x.f
    IN /\ C' = C \ {p} /\ F' = f2
       /\ right' = (right /\ BackoffRight(F, f2, t, p, x.back))
       /\ seen' = Mark(F, p, "shed")
       /\ UNCHANGED op

ClosedStep == \E t \in TIMES, p \in Conn : \E den \in (IF Hub(p) THEN BOOLEAN ELSE {FALSE}) :
    LET x == Closed(F, t, p, op[p], den, Hub(p))
        short == Lt(t, U!Add(op[p], Sec(5)))
    IN /\ op' = [op EXCEPT ![p] = None] /\ F' = x.f /\ UNCHANGED C
       /\ right' = (right /\ IF den THEN DenyRight(F, x.f, t, p, x.back)
                             ELSE IF short THEN BackoffRight(F, x.f, t, p, x.back)
                             ELSE x.f = [F EXCEPT ![p] = None])
       /\ seen' = IF den \/ short THEN Mark(F, p, "closed")
                  ELSE IF F[p] # None THEN seen \cup {"reset"} ELSE seen

PruneStep == \E t \in TIMES :
    /\ F' = Prune(F, t)
    /\ right' = (right /\ \A q \in PEERS :
           LET e == F[q]
               s == IF e = None THEN None ELSE U!Add(e[1], KEEP)
               gone == e # None /\ IF U!Fits(s) THEN Le(s, t) ELSE t = U!Max64
           IN F'[q] = IF gone THEN None ELSE e)
    /\ seen' = IF \E q \in PEERS : F[q] # None /\ F'[q] = None THEN seen \cup {"pruned"} ELSE seen
    /\ UNCHANGED <<C, op>>

Next == DialStep \/ ConnectedStep \/ FailedStep \/ ShedStep \/ ClosedStep \/ PruneStep
Spec == Init /\ [][Next]_vars

Bounded == Size(F) <= MAXT /\ Cardinality(C) <= MAXT
Waits == \A p \in Used(F) :
    /\ Le(Sec(2), F[p][2]) /\ Le(F[p][2], Sec(900)) /\ Le(F[p][2], F[p][1])
Disjoint == C \cap Conn = {}
Right == right
Inv == Bounded /\ Waits /\ Disjoint /\ Right

\* reachability witnesses
NoFull == Size(F) < MAXT
NoRefused == "refused" \notin seen
NoCapHit == \A p \in Used(F) : F[p][2] # IF Hub(p) THEN Sec(16) ELSE Sec(60)
NoSaturated == \A p \in Used(F) : F[p][1] # U!Max64
NoReset == "reset" \notin seen
NoPruned == "pruned" \notin seen
NoBlocked == "blocked" \notin seen
NoDenyMax == \A p \in Used(F) : F[p][2] # Sec(900)
NoShed == "shed" \notin seen
=============================================================================
