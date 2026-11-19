---------------------------- MODULE TraceConnectCodec ----------------------------
(***************************************************************************)
(* Trace validation of the wire formats of pinc-connect: the carrier       *)
(* frame, the relay datagram, the signed record, the beacon, the sleep     *)
(* notice, the ticket (binary and text) and the candidate list.            *)
(*                                                                         *)
(* The Rust test tests/trace_connect_codec.rs runs the real decoders and   *)
(* encoders on valid values of every kind and boundary, on every proper    *)
(* cut of them, with trailing bytes, with single bytes changed, into       *)
(* buffers of every nearby size and on seeded random garbage behind a      *)
(* valid type byte, and records one event per call: the bytes in and the   *)
(* result, the decoded fields as byte sequences or the tag of the error.   *)
(* Each event must equal what the operators of ConnectCodecOps.tla give,   *)
(* whose properties (RoundTrip, Canon, Strict, Prepare, Text) TLC checks   *)
(* in ConnectCodec.cfg.                                                    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_codec.ndjson. *)
(***************************************************************************)
EXTENDS ConnectCodecOps, Json, IOUtils

VARIABLE c

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_codec.ndjson")

Init == c = [t |-> "root"]

Fld(ev, name) == ev[name]

\* a decode result against the event: the same refusal, or the same fields
Refused(r, ev) == ~r.ok /\ r.e = ev.err
Bytes(r, ev) == r.ok /\ r.v = ev.b
HasErr(ev) == "err" \in DOMAIN ev

FDecOK(ev) == IF HasErr(ev) THEN Refused(Frame(ev.b), ev) ELSE Frame(ev.b) = RdOk([ty |-> ev.ty, fs |-> ev.fs], <<>>)
FEncOK(ev) == LET r == EncodeFrame(ev.cap, [ty |-> ev.ty, fs |-> ev.fs]) IN IF HasErr(ev) THEN Refused(r, ev) ELSE Bytes(r, ev)
DDecOK(ev) == IF HasErr(ev) THEN Refused(Dgram(ev.b), ev) ELSE Dgram(ev.b) = RdOk([ty |-> ev.ty, fs |-> ev.fs], <<>>)
DEncOK(ev) == LET r == EncodeDg(ev.cap, [ty |-> ev.ty, fs |-> ev.fs]) IN IF HasErr(ev) THEN Refused(r, ev) ELSE Bytes(r, ev)

RDecOK(ev) ==
    LET r == RecParse(ev.b) IN
    IF HasErr(ev) THEN Refused(r, ev)
    ELSE r.ok /\ r.v.node = ev.node /\ r.v.home = ev.home /\ r.v.seq = ev.seq /\ r.v.reach = ev.reach
         /\ r.v.addrs = ev.addrs /\ r.v.hints = ev.hints
RPrepOK(ev) ==
    LET r == RecPrepare(ev.cap, [node |-> ev.node, home |-> ev.home, seq |-> ev.seq, reach |-> ev.reach,
                                  addrs |-> ev.addrs, hints |-> ev.hints, pk |-> ev.pk]) IN
    IF HasErr(ev) THEN Refused(r, ev) ELSE Bytes(r, ev)

BDecOK(ev) ==
    LET r == BcnParse(ev.b) IN
    IF HasErr(ev) THEN Refused(r, ev)
    ELSE r.ok /\ r.v.node = ev.node /\ r.v.seq = ev.seq /\ r.v.addrs = ev.addrs /\ r.v.hint = ev.hint
BPrepOK(ev) ==
    LET r == BcnPrepare(ev.cap, [node |-> ev.node, seq |-> ev.seq, addrs |-> ev.addrs, hint |-> ev.hint, pk |-> ev.pk]) IN
    IF HasErr(ev) THEN Refused(r, ev) ELSE Bytes(r, ev)

SDecOK(ev) ==
    LET r == NtcParse(ev.b) IN
    IF HasErr(ev) THEN Refused(r, ev) ELSE r.ok /\ r.v.node = ev.node /\ r.v.ts = ev.ts
SPrepOK(ev) ==
    LET r == NtcPrepare(ev.cap, [node |-> ev.node, ts |-> ev.ts, pk |-> ev.pk]) IN
    IF HasErr(ev) THEN Refused(r, ev) ELSE Bytes(r, ev)
SMsgOK(ev) == SleepMessage(ev.relay, ev.node, ev.ts) = ev.b

TDecOK(ev) ==
    LET r == TkParse(ev.b) IN
    IF HasErr(ev) THEN Refused(r, ev)
    ELSE r.ok /\ r.v.node = ev.node /\ r.v.home = ev.home /\ r.v.addrs = ev.addrs
TEncOK(ev) ==
    LET r == TkEncode(ev.cap, [node |-> ev.node, home |-> ev.home, addrs |-> ev.addrs]) IN
    IF HasErr(ev) THEN Refused(r, ev) ELSE Bytes(r, ev)
TTextOK(ev) ==
    LET r == TkText(ev.cap, [node |-> ev.node, home |-> ev.home, addrs |-> ev.addrs]) IN
    IF HasErr(ev) THEN Refused(r, ev) ELSE Bytes(r, ev)
TFromOK(ev) ==
    LET r == TkFromText(ev.s) IN
    IF HasErr(ev) THEN Refused(r, ev) ELSE r.ok /\ TkBytes(r.v) = ev.b

CDecOK(ev) ==
    LET r == CandsDec(ev.b) IN
    IF HasErr(ev) THEN ~r.ok ELSE r.ok /\ r.v = ev.addrs
CEncOK(ev) ==
    IF HasErr(ev) THEN Len(CandsEnc(ev.addrs)) > ev.cap
    ELSE Len(CandsEnc(ev.addrs)) <= ev.cap /\ CandsEnc(ev.addrs) = ev.b

ConstsOK(ev) ==
    /\ ev.rec = MaxRec /\ ev.pkt = MaxPacket /\ ev.notice = MaxNotice /\ ev.frames = BatchFrames
    /\ ev.bytes = BatchBytes /\ ev.frame = BatchBytes + 2 + BatchFrames * 3 /\ ev.tunnel = MaxTunnel /\ ev.alias = 32
    /\ ev.bcn = 8 + 33 + 8 + 2 + 4 * 19 + 8 + 1984 + 3373 /\ ev.ntc = 33 + 8 + 1984 + 3373

EventOK(ev) ==
    CASE ev.t = "consts" -> ConstsOK(ev)
      [] ev.t = "fdec" -> FDecOK(ev)
      [] ev.t = "fenc" -> FEncOK(ev)
      [] ev.t = "ddec" -> DDecOK(ev)
      [] ev.t = "denc" -> DEncOK(ev)
      [] ev.t = "rdec" -> RDecOK(ev)
      [] ev.t = "rprep" -> RPrepOK(ev)
      [] ev.t = "bdec" -> BDecOK(ev)
      [] ev.t = "bprep" -> BPrepOK(ev)
      [] ev.t = "sdec" -> SDecOK(ev)
      [] ev.t = "sprep" -> SPrepOK(ev)
      [] ev.t = "smsg" -> SMsgOK(ev)
      [] ev.t = "tdec" -> TDecOK(ev)
      [] ev.t = "tenc" -> TEncOK(ev)
      [] ev.t = "ttext" -> TTextOK(ev)
      [] ev.t = "tfrom" -> TFromOK(ev)
      [] ev.t = "cdec" -> CDecOK(ev)
      [] ev.t = "cenc" -> CEncOK(ev)

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => EventOK(Trace[c.i])
=============================================================================
