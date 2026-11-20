------------------------- MODULE NodeDtnBackoffOps -------------------------
(***************************************************************************)
(* The backoff of the node's delay-tolerant dials, step for step: the      *)
(* table `lfailed` of io.rs and the one redial time `redial_at` of dtn.rs. *)
(*                                                                         *)
(*  - DtnFailed: layer.rs `layer_failed`, delay-tolerant branch: the wait  *)
(*    is BACKOFF_FIRST, then doubles up to BACKOFF_CAP (no hub cap: it is  *)
(*    `Backoff` of NodeBackoffOps.tla with hub FALSE), the entry           *)
(*    <<now + wait, wait>> (saturating) is stored when the table has room  *)
(*    or holds the peer, and `at`, the end of the wait, is returned even   *)
(*    when the full table refused the entry;                               *)
(*  - Sooner: `d.redial_at = Some(d.redial_at.map_or(at, |t| t.min(at)))`; *)
(*  - RedialDue: dtn.rs `dtn_timeout`, `redial_at.is_some_and(|t| now >= t)`, *)
(*    after which the redial time is None and the contacts are looked at;  *)
(*  - Window: layer.rs `dial_layer`, a delay-tolerant dial waits while     *)
(*    `now < until` (NodeBackoffOps.tla);                                  *)
(*  - Forget: node.rs `service` (a membership event about the peer) and    *)
(*    layer.rs `layer_closed` (our session to the peer lived SESSION_LIVED) *)
(*    remove the entry.                                                    *)
(* A time is a Nanos word; an Option is <<>> or <<w>>. MAXT is TABLE_MAX.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Nanos
CONSTANT MAXT

INSTANCE NodeBackoffOps

DtnFailedN(F, n, now, p) ==
    LET x == BackoffN(F, n, now, p, FALSE) IN [back |-> x.back, f |-> x.f, at |-> SatAdd(now, x.back)]
DtnFailed(F, now, p) == DtnFailedN(F, Size(F), now, p)

Sooner(r, at) == IF r = None THEN <<at>> ELSE <<Min(r[1], at)>>

RedialDue(r, now) == r # None /\ Le(r[1], now)
\* layer.rs `dial_layer` with the N2 fix: a delay-tolerant dial skipped because the peer is still in its window
\* lowers the redial time to that peer's end (`redial_by`, the same two lines as `layer_failed`)
ArmSkipped(r, G, now) ==
    LET S == {G[p][1] : p \in {q \in DOMAIN G : Window(G, now, q)}}
    IN IF S = {} THEN r ELSE Sooner(r, CHOOSE m \in S : \A y \in S : Le(m, y))

Forget(F, p) == [F EXCEPT ![p] = None]
=============================================================================
