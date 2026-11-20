---------------------------- MODULE TraceValuesWire ----------------------------
(***************************************************************************)
(* Trace validation of the value wire codecs (pinc-values wire.rs).        *)
(*                                                                         *)
(* The Rust test tests/trace_values_wire.rs runs the real Req::parse,      *)
(* Req::total_len, Req::encode, GroupHeader::parse and encode,             *)
(* ProofFrame::parse and write_head, ProofReq::parse and encode on seeded  *)
(* random valid values, every cut length of valid inputs, mutated inputs   *)
(* (flipped bytes, every type, count and flag byte, a zero length, a       *)
(* proof that is not whole pairs or is too long, non-canonical and broken  *)
(* stream ids, trailing bytes), garbage, and every class-alphabet id of up *)
(* to 3 bytes; and the encoders into buffers of every size around the      *)
(* edges, pre-filled with a sentinel. It records one event per call: the   *)
(* input bytes (or the values to encode and the buffer size), the result   *)
(* (the fields, or the error kind, the reason and the shortfall) and, for  *)
(* an encode, the buffer afterwards. A u64 is four 16-bit limbs (TLC       *)
(* integers are 32 bits wide). Each event must equal the result of the     *)
(* operator of ValuesWire.tla (ReqParse, ReqTotalLen, ReqEncode, GhParse,  *)
(* GhEncode, PfParse, PfHead, PrParse, PrEncode), whose properties TLC     *)
(* checks exhaustively in ValuesWire.cfg.                                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds values_wire.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

W == INSTANCE ValuesWire WITH c <- 0
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/values_wire.ndjson")

Init == c = [t |-> "root"]

Word(l) == U!FromLimbs(l)

(* the model's result against the recorded one: the same refusal (kind, reason, shortfall), or the same success *)
SameErr(r, res) == ~res.ok /\ ~r.ok /\ r.err = res.err /\ r.msg = res.msg /\ r.needed = res.needed

SpansW(ss) == [i \in 1..Len(ss) |-> [off |-> Word(ss[i][1]), len |-> Word(ss[i][2])]]

ReqEv(ev) ==
    LET r == W!ReqParse(ev.in)
        t == W!ReqTotalLen(ev.in)
    IN /\ IF ev.res.ok
          THEN /\ r.ok /\ r.n = ev.res.n /\ r.root = ev.res.root
               /\ W!SpansOf(r.ranges) = SpansW(ev.res.ranges)
          ELSE SameErr(r, ev.res)
       /\ IF ev.tot.ok THEN t.ok /\ t.n = ev.tot.n ELSE SameErr(t, ev.tot)

ReqEncEv(ev) ==
    LET e == W!ReqEncode(ev.root, SpansW(ev.spans), W!Sent(ev.cap))
    IN /\ e.after = ev.after
       /\ IF ev.res.ok THEN e.ok /\ e.n = ev.res.n ELSE SameErr(e, ev.res)

GhEv(ev) ==
    LET r == W!GhParse(ev.in)
    IN IF ev.res.ok
       THEN /\ r.ok /\ r.off = Word(ev.res.off) /\ r.len = Word(ev.res.len) /\ r.plen = ev.res.plen
            /\ r.follows = ev.res.follows
       ELSE SameErr(r, ev.res)

GhEncEv(ev) ==
    W!GhEncode([off |-> Word(ev.off), len |-> Word(ev.len), plen |-> ev.plen, follows |-> ev.follows]) = ev.out

PfEv(ev) ==
    LET r == W!PfParse(ev.in)
    IN IF ev.res.ok
       THEN /\ r.ok /\ r.sid = Word(ev.res.sid) /\ r.glog = ev.res.glog /\ r.start = Word(ev.res.start)
            /\ r.wn = Word(ev.res.wn) /\ r.ln = Word(ev.res.ln) /\ r.proof = ev.res.proof
       ELSE SameErr(r, ev.res)

PfHeadEv(ev) ==
    LET e == W!PfHead(Word(ev.sid), ev.glog, Word(ev.start), Word(ev.wn), Word(ev.ln), W!Sent(ev.cap))
    IN /\ e.after = ev.after
       /\ IF ev.res.ok THEN e.ok /\ e.n = ev.res.n ELSE SameErr(e, ev.res)

PrEv(ev) ==
    LET r == W!PrParse(ev.in)
    IN IF ev.res.ok
       THEN r.ok /\ r.sid = Word(ev.res.sid) /\ r.from = Word(ev.res.from) /\ r.upto = Word(ev.res.upto)
       ELSE SameErr(r, ev.res)

PrEncEv(ev) ==
    LET e == W!PrEncode([sid |-> Word(ev.sid), from |-> Word(ev.from), upto |-> Word(ev.upto)], W!Sent(ev.cap))
    IN /\ e.after = ev.after
       /\ IF ev.res.ok THEN e.ok /\ e.n = ev.res.n ELSE SameErr(e, ev.res)

EventOK(ev) ==
    CASE ev.t = "wreq" -> ReqEv(ev)
      [] ev.t = "wreqenc" -> ReqEncEv(ev)
      [] ev.t = "wgh" -> GhEv(ev)
      [] ev.t = "wghenc" -> GhEncEv(ev)
      [] ev.t = "wpf" -> PfEv(ev)
      [] ev.t = "wpfhead" -> PfHeadEv(ev)
      [] ev.t = "wpr" -> PrEv(ev)
      [] ev.t = "wprenc" -> PrEncEv(ev)

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 64 events and a block one per event, which TLC checks on all workers at
   once. TLC's count of distinct states is the number of events plus the blocks plus one. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 64) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (64 * c.b + 1)..(IF 64 * c.b + 64 < Len(Trace) THEN 64 * c.b + 64 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

(* every recorded event equals the specification *)
EventsOK == c.t = "event" => EventOK(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
