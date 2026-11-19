---------------------------- MODULE TraceDagBlock ----------------------------
(***************************************************************************)
(* Trace validation of the blocks of pinc-dag (block/*).                   *)
(*                                                                         *)
(* The Rust test tests/trace_dag_block.rs runs the real BlockRef::parse on *)
(* the hand-built blocks and the mutations of DagBlock.cfg and on seeded   *)
(* random blocks and mutations, and encode_block on the parts of           *)
(* DagBlock.cfg with every buffer size class, and records one event per    *)
(* call. A CBOR input is recorded as the items pinc-wire's                 *)
(* Decoder::next_item yields from it, up to the first error or the end     *)
(* (`end` is TRUE when the bytes end right after the last item); counts    *)
(* and integers above 2^20 are recorded as 2^20. Each event must equal     *)
(* ParseBlock or EncodeBlock of DagBlock.tla, whose properties TLC checks  *)
(* in DagBlock.cfg; an encode event also records the heads and links after *)
(* the call (encode_block sorts them in place).                            *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds tla/dag_block.ndjson.                              *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

B == INSTANCE DagBlock WITH Parts <- {}, CidPool <- {}, c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/tla/dag_block.ndjson")

(* a recorded BlockError against the model's error record *)
ErrOK(m, e) ==
    /\ m.err = e.k
    /\ e.k = "wire" => m.w = e.w /\ (e.w = "small" => m.needed = e.needed)
    /\ e.k = "cid" => m.c = e.c
    /\ e.k \in {"malformed", "unordered"} => m.what = e.what

ParseEv(ev) ==
    LET m == B!ParseBlock(ev.items, ev.end) IN
    IF "ok" \in DOMAIN ev.r
    THEN /\ m.err = "ok"
         /\ m.delta = ev.r.ok.delta
         /\ m.heads = ev.r.ok.heads
         /\ m.links = ev.r.ok.links
         /\ m.sig = ev.r.ok.sig
         /\ m.enc = ev.r.ok.enc
    ELSE ErrOK(m, ev.r.err)

EncEv(ev) ==
    LET p == [d |-> ev.d, dend |-> ev.dend, heads |-> ev.heads, links |-> ev.links, sig |-> ev.sig, enc |-> ev.enc]
        m == B!EncodeBlock(p, ev.cap)
        sorted == B!DeltaOK(ev.d, ev.dend)
    IN /\ IF "ok" \in DOMAIN ev.r
          THEN /\ m.err = "ok"
               /\ m.len = ev.r.ok.len
               /\ m.items = ev.r.ok.items
               /\ ev.r.ok.end
          ELSE ErrOK(m, ev.r.err)
       /\ ev.after.heads = (IF sorted THEN B!SortH(ev.heads) ELSE ev.heads)
       /\ ev.after.links = (IF sorted THEN B!SortL(ev.links) ELSE ev.links)

Init == c = [t |-> "root"]

(* the house machine: the root has one successor per block of 32 events, a block one per event *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK ==
    c.t = "event" =>
        CASE Trace[c.i].t = "parse" -> ParseEv(Trace[c.i])
          [] Trace[c.i].t = "enc" -> EncEv(Trace[c.i])
          [] OTHER -> FALSE
=============================================================================
