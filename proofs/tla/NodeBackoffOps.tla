---------------------------- MODULE NodeBackoffOps ----------------------------
(***************************************************************************)
(* The operations of vinc-node on its table of failed dials, step for      *)
(* step: io.rs (`backoff`, `deny_back`, `set_failed`), duties.rs           *)
(* (`dial_peer`, `prune`), events.rs (`hub_closed`, `hub_connect_failed`,  *)
(* and `hub_connected`, whose session the full session table shed: that   *)
(* is `backoff`) and config.rs (the numbers). NodeBackoff.tla checks them  *)
(* over every interleaving at small sizes; TraceNodeBackoff.tla replays    *)
(* the recorded calls of the real code.                                    *)
(*                                                                         *)
(* A time and a wait are Nanos words (Nanos.tla: the u64 of the code on    *)
(* 16-bit limbs, saturating where the code saturates).                     *)
(*                                                                         *)
(* The table F maps each peer to None or <<until, back>>: when the next    *)
(* dial of the peer may start and the wait that was used (the `failed`     *)
(* map of `Io`). The table of dials in progress C is a set of peers (the   *)
(* `connecting` map). MAXT is TABLE_MAX (4096 in the code).                *)
(*                                                                         *)
(* A full table refuses a new entry and never makes room (`set_failed`).   *)
(* The reset of a long session and the prune are the only ways an entry    *)
(* leaves.                                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Nanos

CONSTANT MAXT

None == <<>>

\* config.rs
FIRST == Sec(2)         \* BACKOFF_FIRST
HUBCAP == Sec(16)       \* BACKOFF_HUB_CAP
CAP == Sec(60)          \* BACKOFF_CAP
LIVED == Sec(5)         \* SESSION_LIVED
DFIRST == Sec(60)       \* DENY_FIRST
DCAP == Sec(900)        \* DENY_CAP
KEEP == Sec(3600)       \* FAILED_KEEP (duties.rs)

Tab0(ps) == [p \in ps |-> None]
Used(F) == {p \in DOMAIN F : F[p] # None}
Size(F) == Cardinality(Used(F))

\* b.saturating_mul(2)
Dbl(b) == SatAdd(b, b)

\* set_failed: a full table refuses a peer it has no entry for
SetFailed(F, now, p, back) ==
    IF Size(F) < MAXT \/ F[p] # None
    THEN [F EXCEPT ![p] = <<SatAdd(now, back), back>>]
    ELSE F

\* backoff: the first wait, then double up to the cap of a hub or of any other node
BackWait(F, p, hub) ==
    IF F[p] = None THEN FIRST ELSE Min(Dbl(F[p][2]), IF hub THEN HUBCAP ELSE CAP)
Backoff(F, now, p, hub) == LET b == BackWait(F, p, hub) IN [back |-> b, f |-> SetFailed(F, now, p, b)]

\* deny_back: a wait of at least DENY_FIRST doubles up to DENY_CAP, else DENY_FIRST
DenyWait(F, p) ==
    IF F[p] # None /\ Le(DFIRST, F[p][2]) THEN Min(Dbl(F[p][2]), DCAP) ELSE DFIRST
DenyBack(F, now, p) == LET b == DenyWait(F, p) IN [back |-> b, f |-> SetFailed(F, now, p, b)]

\* the backoff window of dial_peer (and of the frame hand-off): `now < until`
Window(F, now, p) == F[p] # None /\ Lt(now, F[p][1])

\* dial_peer's guard: not leaving, no session, no dial in progress, not revoked, outside the window
Gate(F, now, p, conn, C, rev, lv) ==
    /\ ~lv /\ p \notin conn /\ p \notin C /\ p \notin rev /\ ~Window(F, now, p)

\* the dial reached the transport: the peer joins the dials in progress if there is room
Connecting(C, p) == IF Cardinality(C) < MAXT THEN C \cup {p} ELSE C

\* hub_closed's rule for the closed session of p opened at `opened`: a refusal (den) is deny_back; a session that
\* lived less than SESSION_LIVED is a failure; a longer one forgets the entry
Closed(F, now, p, opened, den, hub) ==
    IF den THEN DenyBack(F, now, p)
    ELSE IF Lt(SatSub(now, opened), LIVED) THEN Backoff(F, now, p, hub)
    ELSE [back |-> None, f |-> [F EXCEPT ![p] = None]]

\* prune: an entry is kept while until + KEEP (saturating) is after now
Prune(F, now) ==
    [p \in DOMAIN F |-> IF F[p] # None /\ Lt(now, SatAdd(F[p][1], KEEP)) THEN F[p] ELSE None]
=============================================================================
