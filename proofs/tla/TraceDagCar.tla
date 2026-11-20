----------------------------- MODULE TraceDagCar -----------------------------
(***************************************************************************)
(* Trace validation of the CAR v1 archives of pinc-dag (car/...).            *)
(*                                                                         *)
(* The Rust test tests/trace_dag_car.rs builds CARs with the real          *)
(* CarWriter (recording every CarWriter::new and section call with its     *)
(* buffer size, header_len and section_len), reads them, their cuts and    *)
(* the frame classes of DagCar.cfg with CarReader (with and without        *)
(* verify, under several maxima) and drives CarDecoder over them, feeding  *)
(* exactly what it asks and 7 bytes more, recording every decode call; it  *)
(* also does so on seeded random CARs. A header body is recorded as the    *)
(* items pinc-wire's Decoder::next_item yields from it (`hdr`, only when   *)
(* its frame is complete); the genuine digests of the section blocks under *)
(* a known hash, computed with the reference crates, as triples            *)
(* <<code, block, digest>> (`gen`). Each event must equal the operators of *)
(* DagCar.tla, whose properties TLC checks in DagCar.cfg.                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds tla/dag_car.ndjson.                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

M == INSTANCE DagCar WITH Parts <- {}, CidPool <- {}, c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/tla/dag_car.ndjson")

W(l) == M!U!FromLimbs(l)

Gen(ev) == {<<W(ev.gen[i][1]), ev.gen[i][2], ev.gen[i][3]>> : i \in 1..Len(ev.gen)}

(* a recorded CarError against the model's error record *)
ErrOK(m, e) ==
    /\ m.err = e.k
    /\ e.k = "wire" => m.w = e.w /\ (e.w = "small" => m.needed = e.needed)
    /\ e.k = "cid" => m.c = e.c
    /\ e.k = "truncated" => m.needed = W(e.needed)
    /\ e.k = "toolarge" => m.len = W(e.len) /\ m.max = W(e.max)
    /\ e.k = "badheader" => m.why = e.why

SecOK(m, e) == IF "ok" \in DOMAIN e THEN m.err = "ok" /\ m.cid = e.ok.cid /\ m.blk = e.ok.blk ELSE ErrOK(m, e.err)

WNewEv(ev) ==
    LET m == M!WriterNew(ev.roots, ev.cap) IN
    /\ M!HeaderLen(ev.roots) = ev.hl
    /\ IF "ok" \in DOMAIN ev.r THEN m.err = "ok" /\ m.bytes = ev.r.ok.bytes /\ m.pos = ev.r.ok.pos ELSE ErrOK(m, ev.r.err)

WSecEv(ev) ==
    LET m == M!WriterSection(ev.pos, ev.cap, ev.cid, ev.blk) IN
    /\ M!SectionLen(ev.cid, ev.blk) = ev.sl
    /\ IF "ok" \in DOMAIN ev.r
       THEN m.err = "ok" /\ m.app = ev.r.ok.app /\ m.pos = ev.r.ok.pos
       ELSE ErrOK(m, ev.r.err) /\ ev.r.pos = ev.pos

ReadEv(ev) ==
    LET m == M!Read(ev.buf, W(ev.max), ev.verify, ev.hdr, Gen(ev)) IN
    IF "ok" \in DOMAIN ev.r
    THEN /\ m.err = "ok"
         /\ m.roots = ev.r.ok.roots
         /\ Len(m.secs) = Len(ev.r.ok.secs)
         /\ \A i \in 1..Len(m.secs) : SecOK(m.secs[i], ev.r.ok.secs[i])
    ELSE ErrOK(m, ev.r.err)

DecEv(ev) ==
    LET m == M!DecodeStream(ev.done, ev.in, W(ev.max), ev.verify, ev.hdr, Gen(ev)) IN
    CASE "need" \in DOMAIN ev.r -> m.t = "need" /\ m.n = W(ev.r.need)
      [] "hdr" \in DOMAIN ev.r -> m.t = "ok" /\ m.consumed = ev.r.hdr.consumed /\ m.entry = [t |-> "hdr", roots |-> ev.r.hdr.roots]
      [] "sec" \in DOMAIN ev.r ->
            m.t = "ok" /\ m.consumed = ev.r.sec.consumed /\ m.entry = [t |-> "sec", cid |-> ev.r.sec.cid, blk |-> ev.r.sec.blk]
      [] OTHER -> m.t = "err" /\ ErrOK(m.e, ev.r.err)

Init == c = [t |-> "root"]

(* the house machine: the root has one successor per block of 32 events, a block one per event *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK ==
    c.t = "event" =>
        CASE Trace[c.i].t = "wnew" -> WNewEv(Trace[c.i])
          [] Trace[c.i].t = "wsec" -> WSecEv(Trace[c.i])
          [] Trace[c.i].t = "read" -> ReadEv(Trace[c.i])
          [] Trace[c.i].t = "dec" -> DecEv(Trace[c.i])
          [] OTHER -> FALSE
=============================================================================
