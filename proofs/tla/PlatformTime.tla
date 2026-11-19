---------------------------- MODULE PlatformTime ----------------------------
(***************************************************************************)
(* The time a host's platform gives the facade, and how the facade reads   *)
(* it: crates/pinc/src/platform.rs (`HostInstant for u64` `add`, `since`;  *)
(* `ns_to_ms`; `HostInstant for std::time::Instant` `add`, std only) and   *)
(* crates/pinc/src/drive.rs (`Shared::now`, `Shared::instant`, `T0`), with *)
(* the operators of PlatformTimeOps.tla at a word of BITS bits.            *)
(*                                                                         *)
(* The contract a host without `std` keeps (platform.rs, `Platform`), and  *)
(* which this model takes as given unless it says otherwise: a monotonic   *)
(* clock that never goes back; randomness that is unpredictable; an        *)
(* allocator that returns memory or fails cleanly; one thread driving an   *)
(* endpoint. Only the clock enters here; the clock machine below also runs *)
(* with a clock that steps back (BACK), to say what the code does then.    *)
(*                                                                         *)
(* Spec, the cases (each a state of a machine whose root has one successor *)
(* per case, so all workers check them at once):                           *)
(*  - "uadd", "usince": every instant t, e of the word and every Duration  *)
(*    of 0 .. 2^(BITS+1) - 1 nanoseconds (the upper half does not fit u64 *)
(*    and takes the `unwrap_or(MAX)`); checked against plain integers:     *)
(*    UAddOK (add never wraps and is min(t + d, MAX): it saturates at the  *)
(*    latest instant), USinceOK (since is t - e, zero when e is later, and *)
(*    since(add(t, d), t) = d when t + d fits).                            *)
(*  - "ms": `ns_to_ms` on the u64 boundary values (2^j - 1, 2^j, 2^j + 1   *)
(*    for j < 64, k * 10^6 - 1, k * 10^6, k * 10^6 + 1, u64::MAX) at 64    *)
(*    bits: MsOK (ms * 10^6 <= ns < (ms + 1) * 10^6, the truncation of a   *)
(*    Duration's `as_millis`).                                             *)
(*  - "drive": every start s and every x of the word, as the platform's    *)
(*    time p for `now` and as the deadline at for `instant`: NowOK (now is *)
(*    min(T0 + max(p - s, 0), MAX): never below T0, never wraps), InstOK   *)
(*    (instant(at) is min(s + max(at - T0, 0), MAX): never before the      *)
(*    start, never wraps), AgreeOK (`now` and `instant` agree on the       *)
(*    offset: instant(now at p) = p and now at instant(at) = at whenever   *)
(*    nothing saturates), WakeDue (a sleep to instant(at) that ends finds  *)
(*    at due, when instant(at) does not saturate).                         *)
(*  - "iadd": the std Instant at a scaled representable range (seconds     *)
(*    0..IMS, NPS nanoseconds a second; `checked_add` fails past it, as    *)
(*    std's does past its largest Timespec) and every Duration of seconds  *)
(*    below 2^SB, with the loop of the decided fix (pinc#731: try d, then  *)
(*    bisect on the step): FitIsLat (a step fits exactly when it is at     *)
(*    most the latest Duration from t, the assumption PlatformTimeOps      *)
(*    makes of std's Instant), IAddOK (the loop ends after at most KM      *)
(*    checked_add calls, the result is representable so `add` never        *)
(*    panics, it is t + d with one call when that fits), InstantLatest     *)
(*    (what the trait documents for every `add`, "an instant that cannot   *)
(*    be represented is the latest one"; the impl says "the latest instant *)
(*    self + d can reach": the result is self + min(d, latest - self)).    *)
(* PlatformTime_wdue is a witness: a deadline past the latest instant maps *)
(* to the latest instant and a sleep to it ends with the deadline not due. *)
(*                                                                         *)
(* ClockSpec, the platform's clock over time from every start: each step  *)
(* the clock moves forward (or, with BACK, anywhere) and `now` is read:    *)
(* NowExact (now is the formula above at every step: the endpoint's clock  *)
(* goes back with a platform clock that goes back, down to T0 and never    *)
(* below, and never wraps), NowMono (now does not go back when the clock   *)
(* did not). PlatformTime_back is a witness: with a clock that steps back, *)
(* now steps back (NowNotBack fails).                                      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS BITS, NPS, T0N, SB, IMSN, BACK
ASSUME BITS \in 1..8 /\ T0N \in 0..(2 ^ BITS - 1) /\ SB \in 1..8 /\ IMSN \in 0..(2 ^ SB - 1) /\ BACK \in BOOLEAN

\* small native integers as words
Wd(k) == <<k, 0, 0, 0, 0>>
T0W == Wd(T0N)
O == INSTANCE PlatformTimeOps WITH T0 <- T0W
V(a) == O!Val(a)
MaxN == 2 ^ BITS - 1
Mn(a, b) == IF a < b THEN a ELSE b
Mx(a, b) == IF a < b THEN b ELSE a
Words == {Wd(k) : k \in 0..MaxN}

\* the instants of std's Instant at the scaled range: [s |-> seconds word, n |-> nanoseconds]
IMS == Wd(IMSN)
IMax == [s |-> IMS, n |-> NPS - 1]
Instants == {[s |-> Wd(a), n |-> b] : a \in 0..IMSN, b \in 0..(NPS - 1)}
Durs == {[s |-> Wd(a), n |-> b] : a \in 0..(2 ^ SB - 1), b \in 0..(NPS - 1)}
\* Instant::checked_add as std's Timespec adds: nanoseconds with a carry into the seconds, None past IMax
CheckedAddI(t, d) ==
    LET n == t.n + d.n
        c == IF n >= NPS THEN 1 ELSE 0
        s == O!Add(O!Add(t.s, d.s), Wd(c))
    IN IF O!Le(s, IMS) THEN [ok |-> TRUE, v |-> [s |-> s, n |-> n - c * NPS]] ELSE [ok |-> FALSE, v |-> t]
\* the time from t to the latest instant
LatestD(t) == [s |-> O!Sub(IMS, t.s), n |-> NPS - 1 - t.n]
\* enough checked_add calls for every Duration of Durs: one for d, then one per bisection step, each of which at
\* least halves (rounding up) a gap below 2^SB * NPS nanoseconds until it is at most one
KM == SB + 2 + NPS

\* the u64 boundary values for `ns_to_ms` (64 bits whatever BITS is)
U64Max == O!Sub(O!Pw(64), O!One)
Pow2 == {O!Pw(j) : j \in 0..63}
MsCases == Pow2 \cup {O!Sub(w, O!One) : w \in Pow2} \cup {O!Add(w, O!One) : w \in Pow2}
           \cup {O!Mega(Wd(k)) : k \in {1, 2, 999, 1000, 4294, 4295, 65535}}
           \cup {O!Sub(O!Mega(Wd(k)), O!One) : k \in {1, 2, 1000, 4295, 65535}}
           \cup {O!Add(O!Mega(Wd(k)), O!One) : k \in {1, 2, 1000, 4295, 65535}}
           \cup {U64Max, O!Sub(U64Max, O!One)}

Cases == {[k |-> "uadd", t |-> t, x |-> n] : t \in 0..MaxN, n \in 0..(2 * MaxN + 1)}
         \cup {[k |-> "usince", t |-> t, x |-> e] : t \in 0..MaxN, e \in 0..MaxN}
         \cup {[k |-> "ms", w |-> w] : w \in MsCases}
         \cup {[k |-> "drive", t |-> s, x |-> x] : s \in 0..MaxN, x \in 0..MaxN}
         \cup {[k |-> "iadd", i |-> t, d |-> d] : t \in Instants, d \in Durs}

VARIABLES cs, st, pc, pq
vars == <<cs, st, pc, pq>>

\* the cases
Init == cs = [k |-> "root"] /\ st = Wd(0) /\ pc = Wd(0) /\ pq = Wd(0)
Next == cs.k = "root" /\ \E x \in Cases : cs' = x /\ UNCHANGED <<st, pc, pq>>
Spec == Init /\ [][Next]_vars

UAddOK == cs.k = "uadd" =>
    LET r == O!UAdd(Wd(cs.t), Wd(cs.x)) IN O!InW(r) /\ V(r) = Mn(cs.t + cs.x, MaxN)
USinceOK == cs.k = "usince" =>
    /\ V(O!USince(Wd(cs.t), Wd(cs.x))) = Mx(cs.t - cs.x, 0)
    /\ (cs.t + cs.x <= MaxN => V(O!USince(O!UAdd(Wd(cs.t), Wd(cs.x)), Wd(cs.t))) = cs.x)
MsOK == cs.k = "ms" =>
    LET m == O!NsToMs(cs.w) IN O!Le(O!Mega(m), cs.w) /\ O!Lt(cs.w, O!Mega(O!Add(m, O!One)))
NowOK == cs.k = "drive" =>
    LET r == O!NowAt(Wd(cs.x), Wd(cs.t)) IN O!InW(r) /\ V(r) = Mn(T0N + Mx(cs.x - cs.t, 0), MaxN) /\ V(r) >= T0N
InstOK == cs.k = "drive" =>
    LET r == O!InstAt(Wd(cs.x), Wd(cs.t)) IN O!InW(r) /\ V(r) = Mn(cs.t + Mx(cs.x - T0N, 0), MaxN) /\ V(r) >= cs.t
AgreeOK == cs.k = "drive" =>
    /\ (cs.x >= cs.t /\ T0N + (cs.x - cs.t) <= MaxN) => O!InstAt(O!NowAt(Wd(cs.x), Wd(cs.t)), Wd(cs.t)) = Wd(cs.x)
    /\ (cs.x >= T0N /\ cs.t + (cs.x - T0N) <= MaxN) => O!NowAt(O!InstAt(Wd(cs.x), Wd(cs.t)), Wd(cs.t)) = Wd(cs.x)
WakeDue == cs.k = "drive" =>
    (cs.t + Mx(cs.x - T0N, 0) <= MaxN => V(O!NowAt(O!InstAt(Wd(cs.x), Wd(cs.t)), Wd(cs.t))) >= cs.x)
\* the same without the guard: a witness (PlatformTime_wdue), violated when instant(at) saturates
WakeDueAll == cs.k = "drive" => V(O!NowAt(O!InstAt(Wd(cs.x), Wd(cs.t)), Wd(cs.t))) >= cs.x

\* every step the loop can try lies in 0..d, so checking the Durations up to d covers them
FitIsLat == cs.k = "iadd" =>
    \A x \in Durs : O!LeD(x, cs.d) => (CheckedAddI(cs.i, x).ok = O!LeD(x, LatestD(cs.i)))
IAddOK == cs.k = "iadd" =>
    LET r == O!InstantAdd(LatestD(cs.i), cs.d)
    IN /\ r.n \in 1..KM
       /\ CheckedAddI(cs.i, r.got).ok
       /\ (CheckedAddI(cs.i, cs.d).ok => r.got = cs.d /\ r.n = 1)
\* documented (platform.rs lines 8, 25 and 114): the result is self + min(d, latest - self)
InstantLatest == cs.k = "iadd" =>
    O!InstantAdd(LatestD(cs.i), cs.d).got = O!MinD(cs.d, LatestD(cs.i))

\* the clock machine: st the instant the endpoint was built at, pc the platform's clock now, pq before the last read
CInit == cs = [k |-> "clock"] /\ st \in Words /\ pc = st /\ pq = st
CNext == \E q \in Words :
           /\ BACK \/ O!Le(pc, q)
           /\ pc' = q /\ pq' = pc /\ UNCHANGED <<cs, st>>
ClockSpec == CInit /\ [][CNext]_vars

NowExact == LET r == O!NowAt(pc, st) IN O!InW(r) /\ V(r) = Mn(T0N + Mx(V(pc) - V(st), 0), MaxN) /\ V(r) >= T0N
NowMono == O!Le(pq, pc) => O!Le(O!NowAt(pq, st), O!NowAt(pc, st))
\* a witness with BACK (PlatformTime_back): the endpoint's clock goes back
NowNotBack == O!Le(O!NowAt(pq, st), O!NowAt(pc, st))
=============================================================================
