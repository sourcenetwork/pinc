----------------------------- MODULE TraceDtnRs -----------------------------
(***************************************************************************)
(* Trace validation of pinc-dtn's GF(2^8) arithmetic, slice kernels and    *)
(* Reed-Solomon code (gf256.rs, rs.rs).                                    *)
(*                                                                         *)
(* The Rust test tests/trace_dtn_rs.rs runs the real inv and mul (all 256  *)
(* inverses, every first operand against fixed second operands, random     *)
(* pairs), the kernels xor_into, mul_add and scale on slices around the    *)
(* eight-byte chunk, Rs::new on valid and invalid parameters, and seeded   *)
(* Rs::encode and Rs::reconstruct runs (random erasure patterns, too few   *)
(* symbols, wrong sizes, the two largest solves), and records one event    *)
(* per call. Each recorded result must equal the operator of DtnGfOps.tla  *)
(* or DtnRsOps.tla, whose properties TLC checks in DtnGf.cfg and           *)
(* DtnRs_*.cfg. A block is the flat bytes of its symbols.                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dtn_rs.ndjson.        *)
(***************************************************************************)
EXTENDS DtnRsOps, Json, IOUtils, TraceEnd

VARIABLE c
vars == <<c, tabs>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dtn_rs.ndjson")

Init == TabInit /\ c = [t |-> "root"]

Sym(block, len, s) == SubSeq(block, s * len + 1, (s + 1) * len)
Blk(block, n, len) == [s \in 0..n - 1 |-> Sym(block, len, s)]
RECURSIVE Flat(_, _, _)
Flat(f, s, n) == IF s = n THEN <<>> ELSE f[s] \o Flat(f, s + 1, n)

Ev(ev) ==
    CASE ev.t = "ginv" -> Inv(ev.a) = ev.r
      [] ev.t = "gmul" -> Mul(ev.a, ev.b) = ev.r
      [] ev.t = "gkern" ->
            LET r == CASE ev.op = "muladd" -> MulAddS(ev.dst, ev.src, ev.c)
                       [] ev.op = "xor" -> XorInto(ev.dst, ev.src)
                       [] ev.op = "scale" -> ScaleS(ev.dst, ev.c)
            IN r = ev.out
      [] ev.t = "rsnew" -> Valid(ev.k, ev.m) = ev.ok
      [] ev.t = "rsenc" ->
            LET n == ev.k + ev.m
            IN /\ Valid(ev.k, ev.m)
               /\ IF ev.len = 0 \/ Len(ev.block) # n * ev.len
                  THEN ~ev.ok /\ ev.err = "buffer" /\ ev.out = ev.block
                  ELSE ev.ok /\ ev.out = Flat(EncodeB(ev.k, ev.m, ev.len, Blk(ev.block, n, ev.len)), 0, n)
      [] ev.t = "rsrec" ->
            LET n == ev.k + ev.m
                pr == [s \in 0..n - 1 |-> ev.present[s + 1] = 1]
            IN /\ Valid(ev.k, ev.m)
               /\ IF Len(ev.present) # n \/ ev.len = 0 \/ Len(ev.block) # n * ev.len
                  THEN ~ev.ok /\ ev.err = "buffer" /\ ev.out = ev.block
                  ELSE LET r == Reconstruct(ev.k, ev.m, ev.len, Blk(ev.block, n, ev.len), pr)
                       IN IF r.res = "incomplete"
                          THEN ~ev.ok /\ ev.err = "incomplete" /\ ev.out = ev.block
                          ELSE ev.ok /\ ev.out = Flat(r.blk, 0, n)

(* Every event is an independent call, so the events are the states of one machine: the root state has one
   successor per block of 32 events and a block one per event, which TLC checks on all workers at once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b] /\ UNCHANGED tabs
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k] /\ UNCHANGED tabs

TraceSpec == Init /\ [][Next]_vars

(* every recorded event equals the specification *)
EventsOK == c.t = "event" => Ev(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
