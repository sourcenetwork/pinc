-------------------------- MODULE TraceNodeDtnCodec --------------------------
(***************************************************************************)
(* Trace validation of the byte formats of pinc-node's delay-tolerant      *)
(* layer: the resume records of dtn_save.rs and the frames of dtn_wire.rs. *)
(*                                                                         *)
(* The Rust test tests/trace_node_dtn_codec.rs calls the real writers and  *)
(* readers (through the probes `dtn_save_probe` and `dtn_wire_probe`,      *)
(* built with the cargo feature `trace`) on records made from real signed  *)
(* heads, their proper prefixes, their bytes changed one at a time, runs   *)
(* with bad, unaligned and torn headers, frames of every boundary length,  *)
(* cut and followed by more bytes, and seeded random bytes, and records    *)
(* one event per call: the input and the result. Each result must equal    *)
(* the operator of NodeDtnCodecOps.tla, whose properties TLC checks in the *)
(* NodeDtnCodec_*.cfg configs. The heads that decode and verify are the    *)
(* ones the test made (one "head" event each): any other bytes in the      *)
(* place of a head are refused (ideal signatures, canonical head codec).   *)
(* Numbers over 2^30 are four 16-bit limbs.                                *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dtn_codec_node.ndjson.*)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dtn_codec_node.ndjson")
L(x) == U!FromLimbs(x)

\* the heads that decode and verify
GoodT == {Trace[j].h : j \in {k \in 1..Len(Trace) : Trace[k].op = "head"}}

C == INSTANCE NodeDtnCodecOps WITH HEADS <- GoodT

RunOf(x) == [a |-> L(x[1]), b |-> L(x[2]), data |-> x[3]]
RunsOf(xs) == [j \in 1..Len(xs) |-> RunOf(xs[j])]

ReadEv(ev) ==
    LET x == C!Read(ev.b)
        r == ev.r
    IN /\ x.ok = r.ok
       /\ r.ok => x.k = r.k
       /\ r.ok /\ r.k = "received" => x.expires = L(r.expires)
       /\ r.ok /\ r.k = "held" =>
            /\ x.copies = r.copies /\ x.custody = r.custody /\ x.alg = r.alg /\ x.key = r.key
            /\ x.bytes = L(r.bytes) /\ x.head = r.head
       /\ r.ok /\ r.k = "partial" => x.head = r.head /\ x.runs = r.runs

\* take_runs: whether it took the runs, the length of the torn tail it left, and the slices its held set holds
\* after it (0-based; the bundle is below 2^30 bytes in the trace)
TakeEv(ev) ==
    LET tk == C!TakeRuns(ev.b, L(ev.total), L(ev.slice))
        sl == U!Val(L(ev.slice))
        n == U!Val(L(ev.total)) \div sl
    IN /\ tk.ok = ev.ok
       /\ ev.ok => /\ Len(tk.rest) = ev.rest
                   /\ {k \in 0..(n - 1) :
                         \E j \in 1..Len(tk.runs) : U!Val(tk.runs[j].a) <= k * sl /\ k * sl < U!Val(tk.runs[j].b)}
                      = {ev.held[j] : j \in DOMAIN ev.held}

NextEv(ev) ==
    LET x == C!NextFrame(ev.h, U!W(ev.len))
    IN /\ x.k = ev.r.k
       /\ ev.r.k = "ok" => x.ty = ev.r.ty /\ x.n = U!W(ev.r.n)

U64Ev(ev) ==
    LET x == C!TakeU64(ev.s)
    IN x.ok = ev.ok /\ (ev.ok => x.v = L(ev.v) /\ Len(x.rest) = ev.rest)

U16Ev(ev) ==
    LET x == C!TakeU16(ev.s)
    IN x.ok = ev.ok /\ (ev.ok => x.v = ev.v /\ Len(x.rest) = ev.rest)

Init == c = [t |-> "root"]

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK ==
    c.t = "event" =>
        LET ev == Trace[c.i]
        IN /\ ev.t = "dcodec"
           /\ CASE ev.op = "head" -> C!Read(C!EncPartial(ev.h, <<>>)).ok
                [] ev.op = "read" -> ReadEv(ev)
                [] ev.op = "received" -> C!EncReceived(L(ev.expires)) = ev.b
                [] ev.op = "held" ->
                     C!EncHeld(ev.copies, ev.custody, ev.alg, ev.key, L(ev.bytes), ev.head) = ev.b
                [] ev.op = "partial" -> C!EncPartial(ev.head, RunsOf(ev.runs)) = ev.b
                [] ev.op = "append" -> C!RunsBytes(RunsOf(ev.runs)) = ev.b
                [] ev.op = "check" -> C!CheckRuns(ev.b, L(ev.total), L(ev.slice)) = ev.r
                [] ev.op = "take" -> TakeEv(ev)
                [] ev.op = "frame" -> C!Finish(ev.ty, U!W(ev.body)) = ev.b
                [] ev.op = "next" -> NextEv(ev)
                [] ev.op = "u64" -> U64Ev(ev)
                [] ev.op = "u16" -> U16Ev(ev)
                [] OTHER -> FALSE
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
