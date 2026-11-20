------------------------------ MODULE TraceDtnCodec ------------------------------
(***************************************************************************)
(* Trace validation of the head and acknowledgement codecs (head.rs,       *)
(* custody.rs, endorse.rs).                                                *)
(*                                                                         *)
(* The Rust test tests/trace_dtn_codec.rs encodes real signed heads and    *)
(* custody acknowledgements of every identity algorithm and records them   *)
(* as byte arrays (`enc`), then mutates each (`mut`: one byte replaced),   *)
(* cuts it (`trunc`) and appends to it (`trail`), recording whether the    *)
(* real decoder accepted the result. A trace is a behaviour of this spec   *)
(* when the model of DtnCodec.tla decodes the valid encoding and           *)
(* re-encodes it to the same bytes, and gives for every mutation the same  *)
(* verdict as the code; an accepted mutation must re-encode to the         *)
(* mutated bytes, as it does in the code.                                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dtn_codec.ndjson.     *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

D == INSTANCE DtnCodec WITH s <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dtn_codec.ndjson")

Encs == SelectSeq(Trace, LAMBDA e : e.op = "enc")

Read(kind, bs) == IF kind = "head" THEN D!SignedRead(bs) ELSE D!AckRead(bs)
Enc(kind, v) == IF kind = "head" THEN D!SignedBytes(v) ELSE D!AckBytes(v)

\* the model's verdict on bytes, and the canonical re-encoding of an accepted string
Verdict(kind, bs) == LET r == Read(kind, bs) IN r.ok /\ Enc(kind, r.v) = bs
Rejected(kind, bs) == ~Read(kind, bs).ok

Ev(ev) ==
    LET e == IF ev.op = "enc" THEN ev ELSE Encs[ev.base + 1]
    IN CASE ev.op = "enc" -> Verdict(ev.kind, ev.b)
         [] ev.op = "mut" ->
              LET m == [e.b EXCEPT ![ev.pos + 1] = ev.val]
              IN IF ev.ok THEN Verdict(ev.kind, m) ELSE Rejected(ev.kind, m)
         [] ev.op = "trunc" -> Rejected(ev.kind, SubSeq(e.b, 1, ev.n))
         [] ev.op = "trail" -> Rejected(ev.kind, e.b \o [j \in 1..ev.extra |-> j + 8])

(* Every event is an independent check, so the events are the states of one machine: the root state has one
   successor per block of 64 events and a block one per event, which TLC checks on all workers at once. *)
Init == c = [t |-> "root"]
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 64) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (64 * c.b + 1)..(IF 64 * c.b + 64 < Len(Trace) THEN 64 * c.b + 64 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

\* every recorded verdict equals the model's
EventsOK == c.t = "event" => Ev(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
