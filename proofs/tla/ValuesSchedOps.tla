------------------------------ MODULE ValuesSchedOps ------------------------------
(***************************************************************************)
(* The scheduler arithmetic of pinc-values fetch/sched.rs, as operators     *)
(* shared by the schedule model (ValuesSched.tla) and the trace check       *)
(* (TraceValuesSched.tla): prate, target (ARRIVAL_CURVE), the TAIL_SHRINK    *)
(* cap, the idle test, the eta of a steal candidate, the choice of the      *)
(* victim and the cut (keep) of a steal. Lean counterpart:                  *)
(* proofs/lean/Pinc/ValuesSchedSteal.lean (the same functions on Nat, with  *)
(* the bounds proved for every input).                                      *)
(*                                                                         *)
(* TLC integers are 32 bits, the code is u64. Times are carried as          *)
(* [ms, ns] with ns < 10^6 (the code divides a nanosecond difference by     *)
(* 10^6 and compares it with whole-millisecond thresholds, so the floor of  *)
(* the difference in milliseconds is all that is needed: DiffMs). A product *)
(* that would pass 2^31 is computed by division with remainder (MulDivLe,   *)
(* SatRate) and is exact while the rates are below 20000 bytes per          *)
(* millisecond and a run is shorter than 10^6 ms; RateOk asserts it. The    *)
(* stalled eta, 2^40 in the code, is 2^30 here: only its order relative to  *)
(* the other etas matters, and a real eta is at most the bytes a provider   *)
(* holds (a target plus a group, below 2^21): Lean stalled_eta_max.         *)
(***************************************************************************)
EXTENDS Integers

G == 16384                  \* GROUP
TGT0 == 786432
TGTMAX == 1572864
MINT == 4 * G               \* MIN_TARGET_GROUPS * GROUP
WARMMS == 500               \* RATE_WARMUP in ms
IDLEMS == 2000              \* STEAL_IDLE in ms
STEALMIN == 262144
ETAMS == 800
STALLED == 1073741824       \* STEAL_ETA_STALLED_MS (2^40 in the code)
STRIPE == 1048576           \* STRIPE_CHUNK
NOETA == -1

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

(* floor((a - b) / 1 ms) for a >= b, times being [ms, ns] with ns < 10^6 *)
DiffMs(a, b) == a.ms - b.ms - (IF a.ns < b.ns THEN 1 ELSE 0)

(* ceil(x / G) * G *)
CeilG(x) == ((x + G - 1) \div G) * G

(* floor(b * r / D) for r <= D, without forming b * r: with b = q D + s, it is q r + floor(s r / D) *)
MulDivLe(b, r, D) == LET q == b \div D IN q * r + ((b % D) * r) \div D

(* min(TGT_MAX, floor(pb * 1000 / d)) for d >= 1: the saturating multiply and the division of target() *)
SatRate(pb, d) ==
    LET q == pb \div d
        s == pb % d
    IN IF q >= 2000 THEN TGTMAX ELSE Min(TGTMAX, q * 1000 + (s * 1000) \div d)

(* Fetch::prate: verified bytes per ms, 0 before 500 ms of samples; has = the provider has a first verified group at pt *)
Prate(has, pt, pb, now) ==
    IF ~has THEN 0
    ELSE IF DiffMs(now, pt) < WARMMS THEN 0
    ELSE pb \div Max(DiffMs(now, pt), 1)

(* Fetch::target (ARRIVAL_CURVE): the rate replaces the starting target after the warm-up, or as soon as the provider
   has verified twice the starting target *)
Target(has, pt, pb, now) ==
    IF has /\ (DiffMs(now, pt) >= WARMMS \/ pb >= 2 * TGT0)
    THEN Max(MINT, Min(TGTMAX, SatRate(pb, Max(DiffMs(now, pt), 1))))
    ELSE TGT0

(* TAIL_SHRINK: the cap a top-up puts on `want` with q bytes queued and k holders. The loop sums the queue's span
   lengths until it reaches 4 * STRIPE_CHUNK * k; below that it sums the queue (q); at or above it the cap is not
   below TGT_MAX (Lean tail_shrink_inactive), which `want` never exceeds. *)
TailWant(want, k, q) == IF q >= 4 * STRIPE * k THEN want ELSE Min(want, Max(MINT, q \div (2 * k)))

(* the provider is idle: no verified group (and no work handed over) for STEAL_IDLE; lp = the last such time *)
Idle(hasLp, lp, t0, now) == IF hasLp THEN DiffMs(now, lp) >= IDLEMS ELSE DiffMs(now, t0) >= IDLEMS

(* the eta of a candidate holding m bytes (NOETA if it is skipped): the second idle correction lets an idle provider be
   robbed of less than STEAL_MIN, the first one is that Idle starts when work is handed over *)
EtaOf(idl, m, rq) ==
    IF m = 0 \/ (m < STEALMIN /\ ~idl) THEN NOETA
    ELSE IF idl THEN STALLED
    ELSE IF rq = 0 THEN NOETA
    ELSE m \div rq

(* the bytes the victim keeps: bm.saturating_mul(rq).checked_div(rq + rp) rounded up to a group, rp falling back to rq *)
KeepOf(bm, rq, rp0) ==
    LET rp == IF rp0 = 0 THEN rq ELSE rp0
        D == rq + rp
    IN CeilG(IF D = 0 THEN 0 ELSE MulDivLe(bm, rq, D))

(* Rates: the domain in which the 32-bit evaluation above is exact *)
RateOk(r) == r < 20000
=================================================================================
