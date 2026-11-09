------------------------------ MODULE TraceLayout ------------------------------
(***************************************************************************)
(* Trace validation of vinc-dag Layout (tree/layout.rs).                   *)
(*                                                                         *)
(* The Rust test tests/trace_tla.rs runs the real `Layout` on lengths up   *)
(* to u64::MAX (the boundary lengths 2^j - 1, 2^j, 2^j + 1, the lengths    *)
(* around k groups of three group sizes, random lengths) and every group   *)
(* log of the boundary set, and records one event per call: `groups`,      *)
(* `depth`, `outboard_size` and `group_size` at the interesting indices    *)
(* (lay), `group_range` over the group edges and the ends of the value     *)
(* (grange), `for_group_bytes` over the sizes around 1024 << log (fgb) and *)
(* `Layout::new` for every log up to 70 (new). Numbers that are u64 are    *)
(* four 16-bit limbs. Each result must equal the operator of Layout.tla,   *)
(* whose properties TLC checks exhaustively in Layout.cfg.                 *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds tla/layout.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

L == INSTANCE Layout WITH SmallLen <- 0, PreN <- 0, c <- 0
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/tla/layout.ndjson")

Init == c = [t |-> "root"]

Ev(ev) ==
    CASE ev.t = "lay" ->
            LET len == U!FromLimbs(ev.len)
            IN /\ L!Groups(len, ev.log) = U!FromLimbs(ev.groups)
               /\ L!Depth(len, ev.log) = ev.depth
               /\ L!OutboardSize(len, ev.log) = U!FromLimbs(ev.ob)
               /\ \A k \in 1..Len(ev.gs) :
                    L!GroupSize(len, ev.log, U!FromLimbs(ev.gs[k][1])) = U!FromLimbs(ev.gs[k][2])
      [] ev.t = "grange" ->
            LET r == L!GroupRange(U!FromLimbs(ev.len), ev.log, U!FromLimbs(ev.s), U!FromLimbs(ev.e))
            IN IF "ok" \in DOMAIN ev
               THEN r = [a |-> U!FromLimbs(ev.ok[1]), b |-> U!FromLimbs(ev.ok[2])]
               ELSE r = [err |-> "range"]
      [] ev.t = "fgb" ->
            LET r == L!ForGroupBytes(U!FromLimbs(ev.gb))
            IN IF "ok" \in DOMAIN ev THEN r = [log |-> ev.ok] ELSE r = [err |-> ev.err]
      [] ev.t = "new" -> L!NewOK(ev.log) = ev.ok

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. TLC's count of distinct states is the number of events plus the blocks plus one. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

(* every recorded event equals the specification *)
EventsOK == c.t = "event" => Ev(Trace[c.i])
=============================================================================
