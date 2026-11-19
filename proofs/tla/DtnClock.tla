------------------------------ MODULE DtnClock ------------------------------
(***************************************************************************)
(* The hybrid logical clock and the bundle lifetime of pinc-dtn            *)
(* (hlc.rs: `Hlc::tick`, `Hlc::observe`, `Hlc::expires_at`; head.rs:       *)
(* `Head::is_expired`) on the machine integers of U64.tla: the physical    *)
(* part is a u64 and the logical counter a u32 whose `saturating_add(1)`   *)
(* stops at 2^32 - 1; `expires_at` is the saturating u64 sum; a head is    *)
(* expired when `expires_at <= now`.                                       *)
(*                                                                         *)
(* Checked by TLC (DtnClock.cfg) over the boundary values of every input   *)
(* (0, 1, 5, 2^32 - 1, 2^32, u64::MAX - 1, u64::MAX for the clocks and    *)
(* lifetimes, 0, 1, 2^32 - 2, 2^32 - 1 for the counters, and the times     *)
(* around each expiry): the tick has the physical part max(wall, now), is  *)
(* at least the receiver, strictly above it unless the counter is          *)
(* saturated and the clock did not move, and not below `now`; the observe  *)
(* has the physical part max(wall, remote, now), is not below `now`, and   *)
(* is strictly above the receiver (resp. the remote stamp) unless that     *)
(* counter is saturated; the expiry is the exact sum or u64::MAX, never    *)
(* below the creation time; a head is alive strictly before its expiry     *)
(* and expired from it on, and stays expired as time passes.               *)
(*                                                                         *)
(* Lean counterpart (proofs/lean/Pinc/DtnLayoutHlc.lean, unbounded):       *)
(* tick_wall, tick_le, tick_lt, tick_now, observe_wall, observe_now,       *)
(* observe_gt_self, observe_gt_remote, expiresAt_exact, expiresAt_sat,     *)
(* expiresAt_ge_wall, expired_iff, expired_mono.                           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64

Max32 == U!FromLimbs(<<65535, 65535, 0, 0>>)
Sat1(c) == IF c = Max32 THEN c ELSE U!Add(c, U!One)

\* lexicographic order on <<wall, counter>>
LtH(a, b) == U!Lt(a[1], b[1]) \/ (a[1] = b[1] /\ U!Lt(a[2], b[2]))
LeH(a, b) == LtH(a, b) \/ a = b

Tick(h, now) == IF U!Lt(h[1], now) THEN <<now, U!Zero>> ELSE <<h[1], Sat1(h[2])>>

Observe(h, r, now) ==
    LET wall == U!Max(U!Max(h[1], r[1]), now)
    IN <<wall, IF wall = h[1] /\ wall = r[1] THEN Sat1(U!Max(h[2], r[2]))
               ELSE IF wall = h[1] THEN Sat1(h[2])
               ELSE IF wall = r[1] THEN Sat1(r[2])
               ELSE U!Zero>>

ExpiresAt(wall, life) == LET s == U!Add(wall, life) IN IF U!Fits(s) THEN s ELSE U!Max64
IsExpired(wall, life, now) == U!Le(ExpiresAt(wall, life), now)

TickOK(h, now) ==
    LET t == Tick(h, now)
    IN /\ t[1] = U!Max(h[1], now)
       /\ LeH(h, t)
       /\ (U!Lt(h[2], Max32) \/ U!Lt(h[1], now)) => LtH(h, t)
       /\ U!Le(now, t[1])

ObserveOK(h, r, now) ==
    LET o == Observe(h, r, now)
    IN /\ o[1] = U!Max(U!Max(h[1], r[1]), now)
       /\ U!Le(now, o[1])
       /\ U!Lt(h[2], Max32) => LtH(h, o)
       /\ U!Lt(r[2], Max32) => LtH(r, o)

ExpiryOK(wall, life, now) ==
    LET e == ExpiresAt(wall, life)
    IN /\ IF U!Fits(U!Add(wall, life)) THEN e = U!Add(wall, life) ELSE e = U!Max64
       /\ U!Le(wall, e)
       /\ IsExpired(wall, life, now) = U!Le(e, now)
       /\ ~IsExpired(wall, life, now) => U!Lt(now, e)
       /\ \A later \in {U!Max64, U!Add(now, U!One)} : (U!Fits(U!Add(now, U!One)) /\ U!Le(now, later) /\ IsExpired(wall, life, now))
                                                    => IsExpired(wall, life, later)

Walls == {U!Zero, U!One, U!W(5), Max32, U!Add(Max32, U!One), U!Sub(U!Max64, U!One), U!Max64}
Ctrs == {U!Zero, U!One, U!Sub(Max32, U!One), Max32}
Times == {U!Zero, U!One, U!W(5), Max32, U!Sub(U!Max64, U!One), U!Max64}

VARIABLE c
Init == c = [t |-> "root"]
Next ==
    \/ c.t = "root" /\ \E w \in Walls, k \in Ctrs, n \in Times : c' = [t |-> "tick", h |-> <<w, k>>, now |-> n]
    \/ c.t = "root" /\ \E w \in Walls, k \in Ctrs, rw \in Walls, rk \in Ctrs, n \in Times :
         c' = [t |-> "obs", h |-> <<w, k>>, r |-> <<rw, rk>>, now |-> n]
    \/ c.t = "root" /\ \E w \in Walls, l \in Walls : c' = [t |-> "exp", w |-> w, l |-> l]
Spec == Init /\ [][Next]_c

Inv ==
    CASE c.t = "root" -> TRUE
      [] c.t = "tick" -> TickOK(c.h, c.now)
      [] c.t = "obs" -> ObserveOK(c.h, c.r, c.now)
      [] c.t = "exp" ->
            LET e == ExpiresAt(c.w, c.l)
            IN \A n \in Times \cup {e, U!Add(e, U!One), U!Sub(e, U!One)} : ExpiryOK(c.w, c.l, n)
=============================================================================
