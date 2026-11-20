-------------------------- MODULE TracePlatformTime --------------------------
(***************************************************************************)
(* Trace validation of the platform's time and the endpoint's clock:       *)
(* crates/pinc/src/platform.rs (`HostInstant for u64` `add`, `since`,      *)
(* `ns_to_ms`, `HostInstant for std::time::Instant` `add`) and             *)
(* crates/pinc/src/drive.rs (`Shared::now`, `Shared::instant`), against    *)
(* the operators of PlatformTimeOps.tla at the real width (64 bits,        *)
(* T0 = 10^10, 10^9 nanoseconds a second).                                 *)
(*                                                                         *)
(* The Rust test tests/trace_platform_time.rs (the facade with the cargo   *)
(* feature `trace`, so with `std`) runs the real code on the u64 boundary  *)
(* values and seeded random ones, and real endpoints built on a platform   *)
(* whose u64 clock the test sets (starting at 0, near u64::MAX, and        *)
(* stepping back), reading `now` and `instant` through the probes          *)
(* Endpoint::trace_now and Endpoint::trace_instant. A u64 is written as    *)
(* four 16-bit limbs and a Duration's `as_nanos()` (a u128) as eight (TLC  *)
(* integers are 32 bits wide). Every event must equal the operator's       *)
(* result.                                                                 *)
(*                                                                         *)
(* std's Instant is opaque, so an "iadd" event carries what the code's     *)
(* loop depends on: the latest Duration the instant can take (lat, found   *)
(* by the test with a binary search over `checked_add` and checked there:  *)
(* lat fits and lat + 1 ns does not). The result must be InstantAdd's      *)
(* (the bisecting loop of the decided fix, pinc#731) under the answers     *)
(* "a step fits exactly when it is at most lat", which is the assumption   *)
(* PlatformTime.tla checks of its scaled Instant, and it must be the       *)
(* documented one: t + min(d, lat).                                        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds platform_time.ndjson. *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

O == INSTANCE PlatformTimeOps WITH BITS <- 64, NPS <- 1000000000, T0 <- <<58368, 21515, 2, 0, 0>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/platform_time.ndjson")

\* a u64 from four limbs; a u128 from eight (any value from 2^64 on is one word past u64::MAX, which is all the code
\* asks of it: whether `u64::try_from` fits)
W4(l) == <<l[1], l[2], l[3], l[4], 0>>
W8(l) == IF l[5] = 0 /\ l[6] = 0 /\ l[7] = 0 /\ l[8] = 0 THEN W4(l) ELSE <<0, 0, 0, 0, 1>>
Dur(r) == [s |-> W4(r.s), n |-> r.n]

IAddEv(ev) ==
    LET d == Dur(ev.d)
        lat == Dur(ev.lat)
    IN /\ O!InstantAdd(lat, d).got = Dur(ev.got)
       /\ Dur(ev.got) = O!MinD(d, lat)

EvOK(ev) ==
    CASE ev.op = "uadd" -> O!UAdd(W4(ev.a), W8(ev.d)) = W4(ev.r)
      [] ev.op = "usince" -> O!USince(W4(ev.a), W4(ev.e)) = W8(ev.r)
      [] ev.op = "ms" -> O!NsToMs(W4(ev.a)) = W4(ev.r)
      [] ev.op = "now" -> O!NowAt(W4(ev.a), W4(ev.st)) = W4(ev.r)
      [] ev.op = "inst" -> O!InstAt(W4(ev.a), W4(ev.st)) = W4(ev.r)
      [] ev.op = "iadd" -> IAddEv(ev)
      [] OTHER -> FALSE

Init == c = [t |-> "root"]

(* Every event is an independent call, so the events are the states of one machine: the root state has one successor
   per block of 32 events and a block one per event, which TLC checks on all workers at once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

\* every recorded event equals the specification
EventsOK == c.t = "event" => (Trace[c.i].t = "time" /\ EvOK(Trace[c.i]))
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
