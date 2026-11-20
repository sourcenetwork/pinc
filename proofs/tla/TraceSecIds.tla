----------------------------- MODULE TraceSecIds -----------------------------
(***************************************************************************)
(* Trace validation of the identifiers and parameters of pinc-security     *)
(* ids.rs against SecIds.tla.                                              *)
(*                                                                         *)
(* The Rust test tests/trace_sec_ids.rs calls the real ConnId::new,        *)
(* Alpn::new (with as_bytes and ==), AlpnList::new and find, aead_tag,     *)
(* aead_from_tag, AeadSet::from_bits, bits, contains, choose and offer,    *)
(* and LocalIdentity::new with its accessors, on every boundary and on     *)
(* seeded random inputs, and records one event per call with its inputs    *)
(* and its result. Each event must equal the operator of SecIds.tla:       *)
(*   cid, alpn      CidNew, AlpnNew (the bytes back from as_bytes);        *)
(*   cideq, alpneq  equality of two values is equality of their bytes;     *)
(*   list           ListNew and ListFind;                                  *)
(*   tag, tagof     FromTag (aead_from_tag then aead_tag), aead_tag;       *)
(*   bits, has      FromBits, Has;                                         *)
(*   choose, offer  Choose, Offer;                                         *)
(*   ident          IdentNew, and the accessors give back the algorithm,   *)
(*                  the public key and the key handle (a u64, as four      *)
(*                  16-bit limbs compared as they are), and an Ed25519     *)
(*                  node id is the key.                                    *)
(* A missing value is recorded as an empty array or 0 next to ok = false.  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds secids.ndjson.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

S == INSTANCE SecIds WITH x <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/secids.ndjson")

Init == c = [t |-> "root"]

Value(r, ev) == /\ r.ok = ev.ok
                /\ IF ev.ok THEN r.v = ev.v ELSE ev.v = <<>>

Ok(ev) ==
    CASE ev.op = "cid" -> Value(S!CidNew(ev.b), ev)
      [] ev.op = "alpn" -> Value(S!AlpnNew(ev.b), ev)
      [] ev.op = "cideq" -> S!CidNew(ev.a).ok /\ S!CidNew(ev.b).ok /\ ev.r = (ev.a = ev.b)
      [] ev.op = "alpneq" -> S!AlpnNew(ev.a).ok /\ S!AlpnNew(ev.b).ok /\ ev.r = (ev.a = ev.b)
      [] ev.op = "list" ->
           /\ ev.ok = S!ListNew(ev.l)
           /\ IF ev.ok THEN /\ ev.found = S!ListFind(ev.l, ev.w).ok
                            /\ IF ev.found THEN ev.v = ev.w ELSE ev.v = <<>>
              ELSE ~ev.found /\ ev.v = <<>>
      [] ev.op = "tag" -> ev.r = S!FromTag(ev.t)
      [] ev.op = "tagof" -> ev.r = IF ev.a = "chacha" THEN 1 ELSE 2
      [] ev.op = "bits" -> ev.r = S!FromBits(ev.b)
      [] ev.op = "has" -> ev.s \in 1..3 /\ ev.t \in {1, 2} /\ ev.r = S!Has(ev.s, ev.t)
      [] ev.op = "choose" -> ev.a \in 1..3 /\ ev.b \in 1..3 /\ ev.r = S!Choose(ev.a, ev.b)
      [] ev.op = "offer" -> ev.r = S!Offer(ev.hw)
      [] ev.op = "ident" ->
           /\ ev.ok = S!IdentNew(ev.alg, ev.pk)
           /\ IF ev.ok THEN /\ ev.pk2 = ev.pk /\ ev.alg2 = ev.alg /\ ev.key2 = ev.key
                            /\ Len(ev.nid) = 32
                            /\ ev.alg = 1 => ev.nid = ev.pk
              ELSE ev.pk2 = <<>> /\ ev.alg2 = 0 /\ ev.nid = <<>>
      [] OTHER -> FALSE

(* Every event is an independent call of a pure function: the root state has one successor per block of 32 events
   and a block one per event, which TLC checks on all workers at once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => Ok(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
