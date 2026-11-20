------------------------------- MODULE TraceTx -------------------------------
(***************************************************************************)
(* Trace validation of the datagrams out: pinc-core tx.rs                  *)
(* (Endpoint::poll_transmit) and the send queues it serves.                *)
(*                                                                         *)
(* The Rust test tests/trace_tx.rs drives a real endpoint (built with the  *)
(* cargo feature `trace`) with sessions to several peers, and records one  *)
(* event per poll_transmit call in tx.ndjson: the caller's buffer length,  *)
(* max_gso, MAX_DATAGRAM, the broadcast flag of every slot, the two queues *)
(* and the kept datagram before the call; the steps the code took, in      *)
(* order (the probe's trace records): a connection asked (its slot, the    *)
(* window, what it wrote: destination, bytes, datagram size, or nothing),  *)
(* a slot found gone, a gate call (destination, bytes, datagrams, the size *)
(* asked of the ledger and its answer), a datagram dropped for a path with *)
(* no address or a buffer too short, a session put on a queue, a reject   *)
(* sent; and the result, the queues and the kept datagram after the call.  *)
(* Each call is replayed through the operators of TxOps.tla with the       *)
(* connections' and the ledger's answers as recorded: the code must ask    *)
(* the session the model asks, with the window the model computes, send   *)
(* to the ledger the size the model computes, join, keep or return as the *)
(* model does, move the sessions as the module doc says, and return what   *)
(* the model returns, with the queues and the kept datagram the model has. *)
(* The calls are independent (each carries its state), so TLC checks them *)
(* as separate steps.                                                      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds tx.ndjson.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE i

T == INSTANCE TxOps WITH OVH <- 28

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/tx.ndjson")

NoStep == [k |-> "end", slot |-> 0, room |-> 0, has |-> FALSE, d |-> 0, len |-> 0, seg |-> 0, segs |-> 0, n |-> 0,
           ok |-> FALSE, q |-> 0]
Nxt(st, steps) == IF st.k <= Len(steps) THEN steps[st.k] ELSE NoStep
Fail(st) == [st EXCEPT !.ph = "fail"]
Done(st, res) == [st EXCEPT !.ph = "done", !.res = res]

(* the sessions the code put on a queue after a settle: each one not waiting, at the back of the queue it names *)
RECURSIVE Marks(_, _)
Marks(st, steps) ==
    LET s == Nxt(st, steps)
    IN IF s.k # "mark" THEN st
       ELSE IF T!Waits(st.qs, s.slot) \/ s.q \notin {0, 1} THEN Fail(st)
       ELSE Marks([st EXCEPT !.qs = T!Enq(@, s.slot, s.q + 1), !.k = @ + 1], steps)

(* session x, first of queue qi, produced a datagram: it goes to the back of the queue of its class (its open has
   left); the code records the move as a mark, except when the session is alone and its class still names its queue,
   and it stays where it is (fix C2: a lone session whose class changed moves, with a mark) *)
Served(st, steps, qi, x) ==
    LET c == IF st.gos[x] THEN 2 ELSE 1
        s == Nxt(st, steps)
    IN IF Len(st.qs[qi]) = 1 /\ c = qi THEN Marks(st, steps)
       ELSE IF s.k = "mark" /\ s.slot = x /\ s.q + 1 = c
       THEN Marks([st EXCEPT !.qs = T!Rotate(@, qi, c), !.k = @ + 1], steps)
       ELSE Fail(st)

GateOK(s, tx) == /\ s.k = "gate" /\ s.d = tx.d /\ s.len = tx.len
                 /\ s.segs = T!Segs(tx.len, tx.seg) /\ s.n = T!GateN(tx.len, s.segs)

RECURSIVE Run(_, _)
Run(st, ev) ==
    LET steps == ev.steps
        s == Nxt(st, steps)
    IN CASE st.ph \in {"done", "fail"} -> st
         [] st.ph = "start" ->
              IF st.stash = <<>> THEN Run([st EXCEPT !.ph = "rej"], ev)
              ELSE LET x == st.stash[1]
                   IN IF x.d = 0 \/ x.len > ev.out
                      THEN IF s.k = "drop" THEN Run([st EXCEPT !.stash = <<>>, !.ph = "rej", !.k = @ + 1], ev)
                           ELSE Fail(st)
                      ELSE IF ~GateOK(s, x) THEN Fail(st)
                      ELSE IF s.ok THEN Done([st EXCEPT !.stash = <<>>, !.k = @ + 1], <<x>>)
                      ELSE Run([st EXCEPT !.stash = <<>>, !.ph = "rej", !.k = @ + 1], ev)
         [] st.ph = "rej" ->
              IF s.k = "reject" THEN Done([st EXCEPT !.k = @ + 1], <<[d |-> s.d, len |-> s.len, seg |-> s.seg]>>)
              ELSE Run([st EXCEPT !.ph = "loop"], ev)
         [] st.ph = "loop" ->
              LET f == T!Front(st.qs)
              IN IF f = <<>> THEN Done(st, <<>>)
                 ELSE IF s.k = "gone" /\ s.slot = f[2] THEN Run([st EXCEPT !.qs = T!Pop(@, f[1]), !.k = @ + 1], ev)
                 ELSE IF s.k # "conn" \/ s.slot # f[2] \/ s.room # ev.out THEN Fail(st)
                 ELSE IF ~s.has THEN Run(Marks([st EXCEPT !.qs = T!Pop(@, f[1]), !.k = @ + 1], steps), ev)
                 ELSE IF s.len > s.room \/ s.seg < 1 \/ s.len < 1 THEN Fail(st)
                 ELSE LET tx == [d |-> s.d, len |-> s.len, seg |-> s.seg]
                          st1 == Served([st EXCEPT !.k = @ + 1], steps, f[1], f[2])
                          s1 == Nxt(st1, steps)
                      IN IF st1.ph = "fail" THEN st1
                         ELSE IF tx.d = 0
                         THEN IF s1.k = "drop" /\ s1.slot = f[2] THEN Run([st1 EXCEPT !.k = @ + 1], ev) ELSE Fail(st1)
                         ELSE IF ~GateOK(s1, tx) THEN Fail(st1)
                         ELSE IF s1.ok THEN Run([st1 EXCEPT !.k = @ + 1, !.ph = "batch", !.buf = T!NewBuf(tx)], ev)
                         ELSE Run([st1 EXCEPT !.k = @ + 1], ev)
         [] st.ph = "batch" ->
              LET f == T!Front(st.qs)
                  room == T!Room(st.buf, ev.out, ev.md)
              IN IF ~T!Cont(st.buf, ev.lim, ev.out) \/ f = <<>> THEN Done(st, <<T!BufRes(st.buf)>>)
                 ELSE IF s.k = "gone" /\ s.slot = f[2] THEN Run([st EXCEPT !.qs = T!Pop(@, f[1]), !.k = @ + 1], ev)
                 ELSE IF s.k # "conn" \/ s.slot # f[2] \/ s.room # room THEN Fail(st)
                 ELSE IF ~s.has
                 THEN IF room < ev.md THEN Done([st EXCEPT !.k = @ + 1], <<T!BufRes(st.buf)>>)
                      ELSE Run(Marks([st EXCEPT !.qs = T!Pop(@, f[1]), !.k = @ + 1], steps), ev)
                 ELSE IF s.len > s.room \/ s.seg < 1 \/ s.len < 1 THEN Fail(st)
                 ELSE LET tx == [d |-> s.d, len |-> s.len, seg |-> s.seg]
                          st1 == Served([st EXCEPT !.k = @ + 1], steps, f[1], f[2])
                          s1 == Nxt(st1, steps)
                      IN IF st1.ph = "fail" THEN st1
                         ELSE IF ~T!Joins(st1.buf, tx, ev.lim)
                         THEN Done([st1 EXCEPT !.stash = <<tx>>], <<T!BufRes(st1.buf)>>)
                         ELSE IF ~GateOK(s1, tx) THEN Fail(st1)
                         ELSE IF ~s1.ok THEN Run([st1 EXCEPT !.k = @ + 1], ev)
                         ELSE LET st2 == [st1 EXCEPT !.k = @ + 1, !.buf = T!Join(@, tx)]
                              IN IF T!Full(st1.buf, tx) THEN Run(st2, ev) ELSE Done(st2, <<T!BufRes(st2.buf)>>)
         [] OTHER -> Fail(st)

Start(ev) == [qs |-> <<ev.q0, ev.q1>>, gos |-> [x \in 0..(Len(ev.gos) - 1) |-> ev.gos[x + 1]], stash |-> ev.stash,
              ph |-> "start", buf |-> T!NoBuf, k |-> 1, res |-> <<>>]

(* each session waits at most once, in one queue *)
WF(q0, q1) == /\ \A j, k \in 1..Len(q0) : q0[j] = q0[k] => j = k
              /\ \A j, k \in 1..Len(q1) : q1[j] = q1[k] => j = k
              /\ \A j \in 1..Len(q0) : ~T!InQ(q1, q0[j])

(* only broadcast sessions wait in the broadcast queue: a session that stops being one, or in which an open is
   queued, is promoted to the ordinary queue at once (dirty_promote, fix C2); the open's flag is not recorded, so a
   broadcast session with an open waiting in the broadcast queue is not seen here *)
BcastOnly(st, q1) == \A j \in 1..Len(q1) : q1[j] \in DOMAIN st.gos /\ st.gos[q1[j]]

CallOK(ev) ==
    LET r == Run(Start(ev), ev)
    IN /\ ev.t = "tx"
       /\ WF(ev.q0, ev.q1) /\ WF(ev.q0a, ev.q1a)
       /\ BcastOnly(Start(ev), ev.q1) /\ BcastOnly(Start(ev), ev.q1a)
       /\ r.ph = "done"
       /\ r.k = Len(ev.steps) + 1
       /\ r.res = ev.res
       /\ r.qs = <<ev.q0a, ev.q1a>>
       /\ r.stash = ev.stasha
       \* a buffer returned holds at most max_gso datagrams and fits the caller's buffer
       /\ \A j \in 1..Len(r.res) : r.res[j].len <= ev.out /\ T!Segs(r.res[j].len, r.res[j].seg) <= ev.lim

Init == i = 1
Step == i <= Len(Trace) /\ CallOK(Trace[i]) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED i
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_i

Inv == i \in 1..(Len(Trace) + 1)
=============================================================================
