------------------------------ MODULE TraceDtnLayout ------------------------------
(***************************************************************************)
(* Trace validation of the bundle layout (vinc-dtn/src/layout.rs).         *)
(*                                                                         *)
(* The Rust test tests/trace_dtn_layout.rs runs the real `SliceLayout` on  *)
(* the boundary parameters (k = 0, k + m = 255 and 256, slice logs 0, 3, 4 *)
(* and 5, payloads around every data count and around the largest payload  *)
(* whose sealed length fits a u64, u64::MAX) and records one event per     *)
(* layout: whether `new` accepted it and, when it did, the counts, the     *)
(* padded and sealed lengths and the answers of block_k, block_n,          *)
(* block_start, locate, data_symbol and byte_range at the boundary        *)
(* indices. Numbers that are u64 are four 16-bit limbs. Each recorded      *)
(* answer must equal the operator of DtnLayout.tla, whose properties TLC   *)
(* checks in DtnLayout.cfg.                                                *)
(*                                                                         *)
(* The same file carries the clock events (`hc`): `Hlc::tick`,             *)
(* `Hlc::observe`, `Hlc::expires_at` and `Head::is_expired` on boundary    *)
(* values, equal to the operators of DtnClock.tla.                         *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds dtn_layout.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

D == INSTANCE DtnLayout WITH c <- 0
K == INSTANCE DtnClock WITH c <- 0
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/dtn_layout.ndjson")

Lm(x) == U!FromLimbs(x)

BkRow(ev, r) ==
    LET b == Lm(r[1])
    IN /\ D!BlockK(ev.k, ev.log, Lm(ev.p), b) = Lm(r[2])
       /\ D!BlockN(ev.k, ev.m, ev.log, Lm(ev.p), b) = Lm(r[3])
       /\ D!BlockStart(ev.k, ev.m, b) = Lm(r[4])

LcRow(ev, r) ==
    LET res == D!Locate(ev.k, ev.m, ev.log, Lm(ev.p), Lm(r[1]))
    IN /\ res.ok = r[2]
       /\ res.ok => /\ res.block = Lm(r[3]) /\ res.index = r[4] /\ res.bk = r[5]

DsRow(ev, r) ==
    LET res == D!DataSymbol(ev.k, ev.m, ev.log, Lm(ev.p), Lm(r[1]))
    IN /\ res.ok = r[2]
       /\ res.ok => res.v = Lm(r[3])

BrRow(ev, r) ==
    LET res == D!ByteRange(ev.k, ev.m, ev.log, Lm(ev.p), Lm(r[1]), Lm(r[2]))
    IN IF r[3] THEN res = [s |-> Lm(r[4]), e |-> Lm(r[5])] ELSE res = [err |-> "buffer"]

\* the clock and lifetime events (hc): tick, observe, expires_at and is_expired against DtnClock.tla
ClockEv(ev) ==
    CASE ev.op = "tick" -> K!Tick(<<Lm(ev.w), Lm(ev.c)>>, Lm(ev.now)) = <<Lm(ev.ow), Lm(ev.oc)>>
      [] ev.op = "obs" -> K!Observe(<<Lm(ev.w), Lm(ev.c)>>, <<Lm(ev.rw), Lm(ev.rc)>>, Lm(ev.now)) = <<Lm(ev.ow), Lm(ev.oc)>>
      [] ev.op = "exp" ->
            /\ K!ExpiresAt(Lm(ev.w), Lm(ev.life)) = Lm(ev.e)
            /\ \A i \in 1..Len(ev.pr) : K!IsExpired(Lm(ev.w), Lm(ev.life), Lm(ev.pr[i][1])) = ev.pr[i][2]

LayoutEv(ev) ==
    LET p == Lm(ev.p)
    IN /\ D!NewOK(ev.k, ev.m, ev.log, p) = ev.ok
       /\ ev.ok =>
            /\ D!DataSyms(ev.log, p) = Lm(ev.d)
            /\ D!Blocks(ev.k, ev.log, p) = Lm(ev.bl)
            /\ D!TotalSyms(ev.k, ev.m, ev.log, p) = Lm(ev.ts)
            /\ D!TotalLen(ev.k, ev.m, ev.log, p) = Lm(ev.tl)
            /\ D!PaddedLen(ev.log, p) = Lm(ev.pad)
            /\ \A i \in 1..Len(ev.bk) : BkRow(ev, ev.bk[i])
            /\ \A i \in 1..Len(ev.lc) : LcRow(ev, ev.lc[i])
            /\ \A i \in 1..Len(ev.ds) : DsRow(ev, ev.ds[i])
            /\ \A i \in 1..Len(ev.br) : BrRow(ev, ev.br[i])

Ev(ev) == IF ev.t = "hc" THEN ClockEv(ev) ELSE LayoutEv(ev)

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. *)
Init == c = [t |-> "root"]
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

\* every recorded event equals the specification
EventsOK == c.t = "event" => Ev(Trace[c.i])
=============================================================================
