--------------------------- MODULE TraceDgramQueue ---------------------------
(***************************************************************************)
(* Trace validation of the datagram queues, pinc-transport                 *)
(* stream/datagram.rs (Datagrams), over a real BufferPool.                 *)
(*                                                                         *)
(* The Rust test tests/trace_dgram_queue.rs drives Datagrams<4, 2> and     *)
(* Datagrams<64, 16> over pools of a few chunks: datagrams of 0 bytes, 1,  *)
(* boundary lengths around the chunk size (16384) and seeded random ones,  *)
(* sent and received, taken out, `clear`; and the pool's other users (the  *)
(* test takes and gives back chunks itself) and its budget lowered and     *)
(* raised. Every call must be the step the operators of DgramQueueOps.tla  *)
(* compute, with the result the code gave; after every call the drop       *)
(* counters, the chunks the pool charges and the oldest datagram of each   *)
(* queue ([length, tag], every byte of a datagram is its tag) must be the  *)
(* model's.                                                                *)
(*                                                                         *)
(* DOC = TRUE counts drops as the docs of `send_dropped` and               *)
(* `recv_dropped` say, which the code does with fix T2; before T2 the      *)
(* replay stopped at the first call where the code counted otherwise (the  *)
(* finding, see DgramQueue.tla). DOC = FALSE replays the code before T2.   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dgram_queue.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd
CONSTANT DOC
VARIABLES i, sq, rq, pl, sd, rd, dims
vars == <<i, sq, rq, pl, sd, rd, dims>>
INSTANCE DgramQueueOps

CHUNK == 16384
Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dgram_queue.ndjson")
Ev0 == Trace[i]

Same(s, r, p, a, b, v) == /\ a = v.sd /\ b = v.rd /\ p.used = v.used
                          /\ Front(s) = v.sf /\ Front(r) = v.rf

InitEv == /\ Ev0.op = "init"
          /\ dims' = [q |-> Ev0.q, c |-> Ev0.c, p |-> Ev0.p]
          /\ sq' = QNew(Ev0.c) /\ rq' = QNew(Ev0.c) /\ pl' = PNew(Ev0.p) /\ sd' = 0 /\ rd' = 0
SendEv == LET d == [len |-> Ev0.len, tag |-> Ev0.tag]
              r == Send(sq, pl, sd, d, Ev0.max, dims.q, dims.c, CHUNK, dims.p, DOC)
          IN /\ Ev0.op = "send" /\ r.res = Ev0.res
             /\ (r.res = "toolarge" => Ev0.limit = IF d.len > Ev0.max THEN Ev0.max ELSE CHUNK)
             /\ sq' = r.q /\ pl' = r.pl /\ sd' = r.cnt /\ UNCHANGED <<rq, rd, dims>>
RecvEv == LET d == [len |-> Ev0.len, tag |-> Ev0.tag]
              r == Recv(rq, pl, rd, d, dims.q, dims.c, CHUNK, dims.p, DOC)
          IN /\ Ev0.op = "recv" /\ rq' = r.q /\ pl' = r.pl /\ rd' = r.cnt /\ UNCHANGED <<sq, sd, dims>>
PopSendEv == LET r == Pop(sq, pl, dims.c)
             IN /\ Ev0.op = "pop_send" /\ sq' = r.q /\ pl' = r.pl /\ UNCHANGED <<rq, sd, rd, dims>>
ReleaseEv == LET r == Pop(rq, pl, dims.c)
             IN /\ Ev0.op = "release" /\ rq' = r.q /\ pl' = r.pl /\ UNCHANGED <<sq, sd, rd, dims>>
ClearEv == LET a == Clear(sq, pl, dims.c)
               b == Clear(rq, a.pl, dims.c)
           IN /\ Ev0.op = "clear" /\ sq' = a.q /\ rq' = b.q /\ pl' = b.pl /\ UNCHANGED <<sd, rd, dims>>
TakeEv == LET a == Alloc(pl, dims.p)
          IN /\ Ev0.op = "take" /\ a.ok = Ev0.ok /\ pl' = a.pl /\ UNCHANGED <<sq, rq, sd, rd, dims>>
GiveEv == /\ Ev0.op = "give" /\ pl' = Free(pl) /\ UNCHANGED <<sq, rq, sd, rd, dims>>
BudgetEv == /\ Ev0.op = "budget"
            /\ pl' = [pl EXCEPT !.budget = IF Ev0.b < dims.p THEN Ev0.b ELSE dims.p]
            /\ UNCHANGED <<sq, rq, sd, rd, dims>>

Init == /\ i = 1 /\ sq = QNew(1) /\ rq = QNew(1) /\ pl = PNew(0) /\ sd = 0 /\ rd = 0
        /\ dims = [q |-> 1, c |-> 1, p |-> 0]
Step == /\ i <= Len(Trace) /\ Ev0.t = "dgram"
        /\ (InitEv \/ SendEv \/ RecvEv \/ PopSendEv \/ ReleaseEv \/ ClearEv \/ TakeEv \/ GiveEv \/ BudgetEv)
        /\ Same(sq', rq', pl', sd', rd', Ev0.v)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* each queue within its entries and chunks, no entry straddling a chunk, an empty queue holding no chunk
QOK(x) == /\ Len(x.es) <= dims.q /\ x.clen <= dims.c
          /\ \A j \in 1..Len(x.es) : x.es[j].at + x.es[j].len <= CHUNK
          /\ (x.es = <<>> => x.clen = 0)
Inv == QOK(sq) /\ QOK(rq)
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
