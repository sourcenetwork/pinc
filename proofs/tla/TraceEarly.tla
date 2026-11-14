----------------------------- MODULE TraceEarly ------------------------------
(***************************************************************************)
(* Trace validation of the buffer of packets that arrive before their      *)
(* keys: vinc-transport conn/recv.rs, drive.rs, life.rs and                *)
(* stream/datagram.rs.                                                     *)
(*                                                                         *)
(* The Rust test tests/trace_early.rs records two kinds of event.          *)
(* "txea": the real buffer (EarlyData) with a pool of one to eight chunks, *)
(* pushed packets of many sizes (some refused for want of room, one too    *)
(* large), popped and cleared. "txeb": real connections, a server or a     *)
(* client, in their handshake, handed junk 0-RTT and 1-RTT packets (more   *)
(* than the buffer holds), then established, handed more, closed and       *)
(* handed more. Every step must be the one the operators of EarlyOps.tla   *)
(* compute and the state recorded must be the model's: the packets held,   *)
(* the phase, the keys, and the counters early_buffered, early_dropped,    *)
(* undecryptable and bytes_received. The junk never opens, so every        *)
(* packet held fails when it is tried. The bytes counted between the last  *)
(* junk packet and the establishment (the handshake messages the pair      *)
(* itself exchanged) are the "real" of the est event.                      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds early.ndjson.         *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, c, cap
vars == <<i, c, cap>>
INSTANCE EarlyOps

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/early.ndjson")
Ev0 == Trace[i]

\* the buffer alone
Front(x) == IF x.q = <<>> THEN -1 ELSE x.q[1].id
SameA(x, v) == /\ Len(x.q) = v.n /\ x.nd = v.nd /\ Front(x) = v.front
Phase(n) == IF n = 0 THEN "hs" ELSE IF n = 1 THEN "up" ELSE "closed"
\* a connection
SameB(x, v) == /\ x.ph = Phase(v.ph) /\ x.er = v.er /\ x.rv = v.rv /\ Len(x.q) = v.n
               /\ x.nb = v.nb /\ x.nd = v.nd /\ x.nu = v.nu /\ x.rx = v.rx
Junk(id, kind) == [id |-> id, kind |-> kind, fate |-> "fail"]

InitA == /\ Ev0.op = "init" /\ cap' = Ev0.cap /\ c' = Early0(FALSE) /\ SameA(c', Ev0.v)
PushA == LET x == HoldPkt(c, cap, Ev0.room, Junk(Ev0.id, "s"))
         IN /\ Ev0.op = "push" /\ (x.out = "held") = Ev0.ok /\ c' = x.c /\ SameA(c', Ev0.v) /\ UNCHANGED cap
PopA == /\ Ev0.op = "pop" /\ c' = [c EXCEPT !.q = IF c.q = <<>> THEN <<>> ELSE Tail(c.q)]
        /\ SameA(c', Ev0.v) /\ UNCHANGED cap
ClearA == /\ Ev0.op = "clear" /\ c' = [c EXCEPT !.q = <<>>] /\ SameA(c', Ev0.v) /\ UNCHANGED cap

\* the handshake messages the pair exchanged before the first junk packet are in rx already
InitB == /\ Ev0.op = "init" /\ cap' = Ev0.cap /\ c' = [Early0(Ev0.client) EXCEPT !.rx = Ev0.v.rx] /\ SameB(c', Ev0.v)
RxB == LET x == Recv(c, cap, TRUE, Junk(i, Ev0.kind), Ev0.dlen)
       IN /\ Ev0.op = "rx" /\ x.out = Ev0.out /\ c' = x.c /\ SameB(c', Ev0.v) /\ UNCHANGED cap
EstB == LET x == Established(c)
        IN /\ Ev0.op = "est" /\ c.ph = "hs"
           /\ c' = [x.c EXCEPT !.rx = x.c.rx + Ev0.real] /\ SameB(c', Ev0.v) /\ UNCHANGED cap
CloseB == /\ Ev0.op = "close" /\ c' = Shut(c) /\ SameB(c', Ev0.v) /\ UNCHANGED cap

Init == i = 1 /\ c = Early0(FALSE) /\ cap = 0
Step == /\ i <= Len(Trace)
        /\ \/ Ev0.t = "txea" /\ (InitA \/ PushA \/ PopA \/ ClearA)
           \/ Ev0.t = "txeb" /\ (InitB \/ RxB \/ EstB \/ CloseB)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == Len(c.q) <= cap \/ cap = 0
=============================================================================
