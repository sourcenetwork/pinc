--------------------------- MODULE PlatformTimeOps ---------------------------
(***************************************************************************)
(* The time the facade asks of a host's platform, as the code computes it: *)
(* crates/pinc/src/platform.rs (`HostInstant for u64`: `add`, `since`;     *)
(* `ns_to_ms`; `HostInstant for std::time::Instant`: `add`) and            *)
(* crates/pinc/src/drive.rs (`Shared::now`, `Shared::instant`, `T0`).     *)
(*                                                                         *)
(* Instants of the u64 platform are words of U64.tla at a width of BITS    *)
(* bits (64 in the trace check, 4 in the model check), so the saturation   *)
(* at the top of the word is the code's at either width. A Duration is     *)
(* given by its `as_nanos()` (a u128) as a word that may be wider than     *)
(* BITS: `u64::try_from` of it is `Narrow`. T0 is a word (10^10 in the     *)
(* trace check, a small value in the model check).                         *)
(*                                                                         *)
(* The loop of `Instant::add` cannot see the instant's value (std keeps   *)
(* it opaque), so it is written over the answers of `checked_add`: a step  *)
(* fits exactly when it is at most lat, the latest Duration the instant    *)
(* can take (PlatformTime.tla checks that this is what its scaled Instant  *)
(* does; the trace check takes lat from the test). A Duration there is a   *)
(* record [s |-> seconds word, n |-> nanoseconds below NPS]; `Duration / 2` *)
(* is the floor of half the total (seconds halved, an odd second carried   *)
(* as NPS / 2 nanoseconds), `+` and `-` carry and borrow a second; NPS is  *)
(* 10^9 in the trace check and a small even number in the model check.     *)
(* The loop is the decided fix of platform.rs `add` (pinc#731): try d,     *)
(* and when it does not fit, bisect between lo (fits, from zero) and hi    *)
(* (does not fit, from d) with mid = lo + (hi - lo) / 2 until              *)
(* (hi - lo) / 2 is zero, and return self + lo (one more checked_add).     *)
(***************************************************************************)
EXTENDS Integers, Sequences, U64
CONSTANTS BITS, T0, NPS
ASSUME BITS \in 1..64 /\ NPS >= 2 /\ NPS % 2 = 0

\* the latest instant of the word, and whether a word fits it
WMax == Sub(Pw(BITS), One)
InW(a) == Lt(a, Pw(BITS))

\* a.saturating_add(b), a.saturating_sub(b) on the word
SatAddW(a, b) == IF InW(Add(a, b)) THEN Add(a, b) ELSE WMax
SatSubW(a, b) == IF Lt(a, b) THEN Zero ELSE Sub(a, b)

\* u64::try_from(n).unwrap_or(u64::MAX), n the nanoseconds of a Duration (any word below 2^80)
Narrow(n) == IF InW(n) THEN n ELSE WMax

\* `HostInstant for u64`: add(t, d) with n = d.as_nanos(); since(t, e) as nanoseconds (Duration::from_nanos is exact)
UAdd(t, n) == SatAddW(t, Narrow(n))
USince(t, e) == SatSubW(t, e)

\* division and multiplication of a word by a native k below 2^15 (every partial result stays below 2^31)
RECURSIVE DivAt(_, _, _, _)
DivAt(a, k, i, r) ==
    IF i = 0 THEN <<>>
    ELSE LET x == r * B + a[i] IN DivAt(a, k, i - 1, x % k) \o <<x \div k>>
DivSmall(a, k) == DivAt(a, k, 5, 0)
RECURSIVE MulAt(_, _, _, _)
MulAt(a, k, i, c) ==
    IF i > 5 THEN <<>>
    ELSE <<(a[i] * k + c) % B>> \o MulAt(a, k, i + 1, (a[i] * k + c) \div B)
MulSmall(a, k) == MulAt(a, k, 1, 0)

\* `ns_to_ms`: ns / 1_000_000, written as (ns / 2^6) / 15625 (the floor of a floor is the floor)
NsToMs(ns) == DivSmall(Shr(ns, 6), 15625)
\* a * 10^6, exact below 2^80
Mega(a) == Shl(MulSmall(a, 15625), 6)

\* drive.rs: `now()` = T0.saturating_add(u64::try_from(platform.now().since(start).as_nanos()).unwrap_or(MAX))
NowAt(p, s) == SatAddW(T0, Narrow(USince(p, s)))
\* drive.rs: `instant(at)` = start.add(Duration::from_nanos(at.saturating_sub(T0)))
InstAt(at, s) == UAdd(s, SatSubW(at, T0))

\* Durations of the Instant loop
ZeroD == [s |-> Zero, n |-> 0]
IsZeroD(d) == d.s = Zero /\ d.n = 0
Half(d) == [s |-> Shr(d.s, 1), n |-> (d.s[1] % 2) * (NPS \div 2) + d.n \div 2]
LtD(a, b) == Lt(a.s, b.s) \/ (a.s = b.s /\ a.n < b.n)
LeD(a, b) == ~LtD(b, a)
MinD(a, b) == IF LtD(a, b) THEN a ELSE b
\* a + b, and a - b for b <= a (std's Duration `+` and `-` carry and borrow one second)
AddD(a, b) == LET n == a.n + b.n
                  c == IF n >= NPS THEN 1 ELSE 0
              IN [s |-> Add(Add(a.s, b.s), <<c, 0, 0, 0, 0>>), n |-> n - c * NPS]
SubD(a, b) == IF a.n >= b.n THEN [s |-> Sub(a.s, b.s), n |-> a.n - b.n]
              ELSE [s |-> Sub(Sub(a.s, b.s), One), n |-> a.n + NPS - b.n]

\* `HostInstant for std::time::Instant`: add, with lat the latest Duration self can take (checked_add(x) is Some
\* exactly when x <= lat). n is the number of checked_add calls, got the Duration added (zero: self returned). After
\* the bisection the code calls checked_add(lo) once more for the instant it returns (platform.rs, fix F5).
RECURSIVE Bisect(_, _, _, _)
Bisect(lat, lo, hi, k) ==
    LET h == Half(SubD(hi, lo))
    IN IF IsZeroD(h) THEN [n |-> k + 1, got |-> lo]
       ELSE LET mid == AddD(lo, h)
            IN IF LeD(mid, lat) THEN Bisect(lat, mid, hi, k + 1) ELSE Bisect(lat, lo, mid, k + 1)
InstantAdd(lat, d) == IF LeD(d, lat) THEN [n |-> 1, got |-> d] ELSE Bisect(lat, ZeroD, d, 1)
=============================================================================
