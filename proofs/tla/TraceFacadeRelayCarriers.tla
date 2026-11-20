----------------------- MODULE TraceFacadeRelayCarriers -----------------------
(***************************************************************************)
(* Trace validation of the carriers of a node that carries the relay      *)
(* role: relay/part.rs Part::poll over the real core, with a host whose    *)
(* Carriers the test controls.                                             *)
(*                                                                         *)
(* The Rust test tests/trace_facade_relay_carriers.rs builds a part with   *)
(* RelayHost::builder().build_part and a Carriers of its own that records  *)
(* every submit_accept, submit_read, submit_write and close and hands back *)
(* at most one completion per poll, chosen by the test: a stream of a      *)
(* member (real carrier handshakes and frames, TCP or WebSocket framing),  *)
(* an accept error, a read (bytes of a member, junk, end of stream), a     *)
(* write written whole, in part or not at all, and operations of closed   *)
(* streams. Each line is one poll, one timer run, a stop or an end; the    *)
(* line must be the step FacadeRelayCarriersOps.tla computes: the accept,  *)
(* the reads and writes started (a write from its offset or not), the      *)
(* streams closed, every counter and the session count.                    *)
(*                                                                         *)
(* A conn's tag in the trace is id * 65536 + slot with slot from 0, the    *)
(* model's slot less one; streams are numbered in accept order, as the     *)
(* model's handles. Whether a read queued a reply, and on which conn a     *)
(* slow close fell, is not visible to the test: those are chosen here and  *)
(* pinned by the writes started in the same poll and by the counters.      *)
(* Times are milliseconds since the start of the test. Needs the TLA+      *)
(* CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the directory that *)
(* holds relay-carriers.ndjson.                                            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
CONSTANTS HS, CAP, BL, HSD, IDL, PAUSE, CHK, NODES
VARIABLES i, m
vars == <<i, m>>
INSTANCE FacadeRelayCarriersOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/relay-carriers.ndjson")
E == Trace[i]
Rng(f) == {f[j] : j \in DOMAIN f}
Conn(x) == x.id * 65536 + x.slot - 1

\* the operation the test handed back
OpOf(d) ==
    IF d.k = "acc" THEN AccOp
    ELSE [k |-> d.k, id |-> d.conn \div 65536, slot |-> d.conn % 65536 + 1,
          h |-> LET c == {x \in m.o : x.k = d.k /\ Conn(x) = d.conn} IN IF c = {} THEN 0 ELSE (CHOOSE x \in c : TRUE).h]

New(m1, k) == {x \in m1.o \ m.o : x.k = k}
Closed(m1) == {h \in 1..Len(m1.ends) : h > Len(m.ends) \/ m1.ends[h] > m.ends[h]}

Counted(m1, e) ==
    /\ m1.c.cnt = [opened |-> e.cnt.opened, closed |-> e.cnt.closed, full |-> e.cnt.full, hsfull |-> e.cnt.hsfull,
                   proto |-> e.cnt.proto, slow |-> e.cnt.slow, tout |-> e.cnt.tout, accerr |-> e.cnt.accerr]
    /\ Sessions(m1) = e.sess

PollEv ==
    /\ E.op = "poll"
    /\ WantAccept(m, E.now) = E.acc
    /\ E.done.k # "none" => OpOf(E.done) \in m.o
    /\ \E reply, slow, tslow \in BOOLEAN :
         LET d == IF E.done.k = "none" THEN NoDone
                  \* a write written in part leaves one unit unsent here: the test cannot see the bytes left, and
                  \* the slow closes are read from the counters, so the units unsent pin nothing in the trace
                  ELSE [op |-> OpOf(E.done), x |-> E.done.x, n |-> IF E.done.k = "wr" THEN 1 ELSE E.done.n,
                        kind |-> E.done.kind,
                        reply |-> reply, slow |-> slow, to |-> E.done.to, tslow |-> tslow]
             m1 == Poll(m, E.now, d, TRUE)
         IN /\ {Conn(x) : x \in New(m1, "rd")} = Rng(E.rd)
            /\ {[conn |-> Conn(x), part |-> m1.c.cs[x.slot].off] : x \in New(m1, "wr")} = Rng(E.wr)
            /\ Closed(m1) = Rng(E.close)
            /\ Counted(m1, E)
            /\ m' = m1

TimeoutEv ==
    /\ E.op = "timeout"
    /\ \E slow \in [Slots(m) -> BOOLEAN] :
         LET m1 == Timeout(m, E.now, slow) IN Counted(m1, E) /\ m' = m1

StopEv == E.op = "stop" /\ m' = Stop(m)

EndEv == E.op = "end" /\ m' = End(m) /\ Counted(m', E)

Init == i = 1 /\ m = Sys0(0)
Step == /\ i <= Len(Trace)
        /\ \/ PollEv \/ TimeoutEv \/ StopEv \/ EndEv
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* what the model checks, on the real run
Inv == /\ m.c.hs = Cardinality({k \in Live(m) : m.c.cs[k].node = 0}) /\ m.c.hs <= HS
       /\ Sessions(m) <= CAP
       /\ \A h \in 1..Len(m.ends) : m.ends[h] <= 1 /\ ~(h \in m.drop /\ m.ends[h] > 0)
       /\ \A k \in Live(m) : m.ends[m.c.cs[k].h] = 0 /\ m.c.cs[k].h \notin m.drop
=============================================================================
