----------------------------- MODULE TraceDagCid -----------------------------
(***************************************************************************)
(* Trace validation of the CIDs of pinc-dag (cid/*).                       *)
(*                                                                         *)
(* The Rust test tests/trace_dag_cid.rs runs the real CidRef::parse,       *)
(* CidRef::parse_prefix, Cid::new, CidRef::encode_text, Cid::parse_text,   *)
(* cmp_text, CidRef::verify and Cid::for_block on the boundary classes of  *)
(* DagCid.cfg (codecs, hash codes, digest lengths, cuts, rests, header     *)
(* mutations, every byte string of up to 2 bytes, texts over the class     *)
(* alphabet, text mutations) and on seeded random inputs, and records one  *)
(* event per call with the result or the error. The genuine digest of a    *)
(* block under a known hash (SHA2-256, BLAKE3) is computed by the test     *)
(* with the reference crates and recorded as `g`. Each event must equal    *)
(* the operator of DagCid.tla, whose properties TLC checks in DagCid.cfg.  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds tla/dag_cid.ndjson.                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

C == INSTANCE DagCid WITH Parts <- {}, c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/tla/dag_cid.ndjson")

W(l) == C!U!FromLimbs(l)

(* a recorded CidError against the model's error record *)
ErrOK(m, e) ==
    /\ m.err = e.k
    /\ CASE e.k = "version" -> m.v = W(e.v)
         [] e.k = "toolong" -> m.len = W(e.len)
         [] e.k = "mismatch" -> m.hash = W(e.hash) /\ m.len = W(e.len)
         [] e.k = "wire" -> m.w = e.w /\ m.needed = e.needed
         [] e.k = "unsupported" -> m.hash = W(e.hash)
         [] e.k = "text" -> m.why = e.why
         [] e.k = "small" -> m.needed = e.needed
         [] OTHER -> TRUE

(* a recorded CID: its bytes, codec, hash code and digest length *)
CidOK(m, ok) == m.raw = ok.raw /\ m.codec = W(ok.codec) /\ m.hash = W(ok.hash) /\ m.dlen = ok.dlen

ParseEv(ev) ==
    LET m == C!Parse(ev.in) IN
    IF "ok" \in DOMAIN ev.r THEN m.err = "ok" /\ CidOK(m.cid, ev.r.ok) ELSE ErrOK(m, ev.r.err)

PrefixEv(ev) ==
    LET m == C!ParsePrefix(ev.in) IN
    IF "ok" \in DOMAIN ev.r THEN m.err = "ok" /\ CidOK(m.cid, ev.r.ok) /\ m.rest = ev.r.rest ELSE ErrOK(m, ev.r.err)

NewEv(ev) ==
    LET m == C!NewCid(W(ev.codec), W(ev.hash), ev.d) IN
    IF "ok" \in DOMAIN ev.r THEN m.err = "ok" /\ m.cid.raw = ev.r.ok ELSE ErrOK(m, ev.r.err)

ETextEv(ev) ==
    LET m == C!EncodeText(ev.in, ev.cap) IN
    IF "ok" \in DOMAIN ev.r THEN m.err = "ok" /\ m.text = ev.r.ok /\ m.text = C!TextSpec(ev.in) ELSE ErrOK(m, ev.r.err)

PTextEv(ev) ==
    LET m == C!ParseText(ev.in) IN
    IF "ok" \in DOMAIN ev.r THEN m.err = "ok" /\ m.cid.raw = ev.r.ok ELSE ErrOK(m, ev.r.err)

CmpEv(ev) == C!CmpText(ev.a, ev.b) = ev.r

VerifyEv(ev) ==
    LET p == C!Parse(ev.in)
        m == C!Verify(p.cid, ev.g)
    IN p.err = "ok" /\ (IF "ok" \in DOMAIN ev.r THEN m.err = "ok" ELSE ErrOK(m, ev.r.err))

ForBlockEv(ev) ==
    LET m == C!ForBlock(W(ev.codec), W(ev.hash), ev.g) IN
    IF "ok" \in DOMAIN ev.r THEN m.err = "ok" /\ m.cid.raw = ev.r.ok ELSE ErrOK(m, ev.r.err)

Init == c = [t |-> "root"]

(* the house machine: the root has one successor per block of 32 events, a block one per event *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK ==
    c.t = "event" =>
        LET ev == Trace[c.i] IN
        CASE ev.t = "parse" -> ParseEv(ev)
          [] ev.t = "prefix" -> PrefixEv(ev)
          [] ev.t = "new" -> NewEv(ev)
          [] ev.t = "etext" -> ETextEv(ev)
          [] ev.t = "ptext" -> PTextEv(ev)
          [] ev.t = "cmp" -> CmpEv(ev)
          [] ev.t = "verify" -> VerifyEv(ev)
          [] ev.t = "forblock" -> ForBlockEv(ev)
          [] OTHER -> FALSE
=============================================================================
