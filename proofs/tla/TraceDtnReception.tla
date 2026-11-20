------------------------------ MODULE TraceDtnReception ------------------------------
(***************************************************************************)
(* Trace validation of the reception of a bundle (pinc-dtn/src/bundle.rs   *)
(* `Reception`).                                                           *)
(*                                                                         *)
(* The Rust test tests/trace_dtn_reception.rs drives real receptions of an *)
(* honest sender and of a sender whose parity is not a code word through   *)
(* seeded random calls (intact, damaged, short and padded proof streams    *)
(* into a held set of 2 or 3 intervals, or into a BlockHeld lent as       *)
(* `&mut`, which never refuses and so is the cap of 4; finish, resume)     *)
(* and records after each call its verdict, the whole held set and the answers of `holds`,   *)
(* `is_complete`, `is_decodable` and `next_missing`. Each recorded step    *)
(* must be a step of DtnReception.tla: a feed is FeedResult for an intact  *)
(* stream, a stream with one wrong group, a stream cut short, or a stream  *)
(* with trailing bytes (the number of groups that verified is not          *)
(* recorded, so it is a choice of the check), `finish` agrees with the     *)
(* verdict rules of FinishCorrect (Incomplete exactly when a block is      *)
(* short of k; Ok exactly when the blocks are decodable and every block    *)
(* that is not fully held is rebuilt, at its symbols that are not held, to *)
(* the sender's bytes, which depends on the held set alone because finish  *)
(* never writes a held symbol; Inconsistent otherwise, never for an honest *)
(* sender), a finish with a wrong-sized outboard or scratch is Buffer with *)
(* the held set unchanged, and resume gives the verdict of its checks and  *)
(* the same held set. The                                                  *)
(* answers of the helpers must be the model's on the recorded held set.    *)
(* The step before an event is the held set the previous event recorded.   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dtn_reception.ndjson. *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, RangeOps, TraceEnd

VARIABLE c

R2 == INSTANCE DtnReception WITH G <- 1024, W <- 2, ct <- 0, have <- 0, buf <- 0, res <- 0
R3 == INSTANCE DtnReception WITH G <- 1024, W <- 3, ct <- 0, have <- 0, buf <- 0, res <- 0
\* a BlockHeld never refuses a symbol: the cap of 4 is the most runs 7 symbols can make
R4 == INSTANCE DtnReception WITH G <- 1024, W <- 4, ct <- 0, have <- 0, buf <- 0, res <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dtn_reception.ndjson")
News == SelectSeq(Trace, LAMBDA e : e.op = "new")

H(x) == [k \in 1..Len(x) |-> <<x[k][1], x[k][2]>>]
Pre(i) == IF Trace[i].op = "new" THEN <<>> ELSE H(Trace[i - 1].have)

\* the sender's content: zero data, so zero parity, except that the faulty parity symbols are one off
CtOf(faulty) == [s \in 0..6 |-> IF s \in faulty THEN 1 ELSE 0]

Z(n) == [k \in 1..n |-> 0]
Ct0 == [s \in 0..6 |-> 0]
Buf0 == [s \in 0..6 |-> 9]

Sts(kind, n) ==
    CASE kind = "good" -> {[vals |-> Z(n), extra |-> FALSE]}
      [] kind = "trail" -> {[vals |-> Z(n), extra |-> TRUE]}
      [] kind = "short" -> {[vals |-> Z(j), extra |-> FALSE] : j \in 0..(n - 1)}
      [] kind = "flip" -> {[vals |-> [Z(n) EXCEPT ![p] = 1], extra |-> FALSE] : p \in 1..n}

FR(w, a, b, h, st) ==
    IF w = 2 THEN R2!FeedResult(Ct0, Buf0, h, a, b, st)
    ELSE IF w = 3 THEN R3!FeedResult(Ct0, Buf0, h, a, b, st)
    ELSE R4!FeedResult(Ct0, Buf0, h, a, b, st)

Snap(ev) ==
    LET h2 == H(ev.have)
    IN /\ \A s \in 0..6 : (ev.hold[s + 1] = 1) = R2!Holds(h2, s)
       /\ ev.cmp = R2!IsComplete(h2)
       /\ ev.dec = R2!IsDecodable(h2)
       /\ \A f \in 0..7 : LET r == R2!NextMissing(h2, f)
                          IN IF r.some THEN ev.nm[f + 1] = <<r.a, r.b>> ELSE ev.nm[f + 1] = <<>>

Ev(i) ==
    LET ev == Trace[i]
        pre == Pre(i)
        nw == News[ev.run + 1]
        faulty == {nw.faulty[k] : k \in 1..Len(nw.faulty)}
        ctv == CtOf(faulty)
    IN CASE ev.op = "new" -> ev.have = <<>>
         [] ev.op = "feed" ->
              /\ Snap(ev)
              /\ IF ev.kind = "range"
                 THEN ev.res = "buffer" /\ H(ev.have) = pre
                 ELSE \E st \in Sts(IF ev.a = ev.b THEN "good" ELSE ev.kind, ev.b - ev.a) :
                        LET r == FR(nw.W, ev.a, ev.b, pre, st)
                        IN r.res = ev.res /\ r.h = H(ev.have)
         [] ev.op = "fin" ->
              /\ Snap(ev)
              /\ LET dec == R2!IsDecodable(pre)
                 IN /\ (ev.res = "incomplete") = ~dec
                    /\ (ev.res = "ok") = (dec /\ \A b \in {0, 1} : ~R2!FullyHeld(pre, b) => R2!BlockMatches(ctv, ctv, pre, b))
                    /\ (ev.res = "inconsistent") => faulty # {}
                    /\ ev.res \in {"incomplete", "inconsistent", "ok"}
                    /\ H(ev.have) = IF ev.res = "ok" THEN <<<<0, 7168>>>> ELSE pre
         [] ev.op = "finbuf" ->
              /\ Snap(ev)
              /\ ev.res = "buffer" /\ H(ev.have) = pre
         [] ev.op = "res" ->
              /\ Snap(ev)
              /\ H(ev.have) = pre
              /\ ev.res = CASE ev.case = 0 -> "crypto" [] ev.case = 1 -> "expired" [] ev.case = 2 -> "buffer" [] ev.case = 3 -> "ok"

(* Every event is checked against the held set the previous event recorded, so the events are independent: they are
   the states of one machine, one root, a block of 32 events per successor and one event per block state. *)
Init == c = [t |-> "root"]
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c
EventsOK == c.t = "event" => Ev(c.i)
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
