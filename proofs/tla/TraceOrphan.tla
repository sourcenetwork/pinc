----------------------------- MODULE TraceOrphan -----------------------------
(***************************************************************************)
(* Trace validation of the endpoint's table of held first-flight           *)
(* fragments: pinc-core orphan.rs.                                         *)
(*                                                                         *)
(* The Rust test tests/trace_orphan.rs drives real tables (built with the  *)
(* cargo feature `trace`) with seeded calls: datagrams of every length up  *)
(* to the bound and past it, held for a few messages from a few addresses, *)
(* taken for the same message and for one that differs in the id, the      *)
(* length or the address, and expired, at times that step forward, stand   *)
(* still, step back and land on the edge of a datagram's lifetime. Every   *)
(* call must be the step the operators of OrphanOps.tla compute, with the  *)
(* result the code returned, and the entries and counters recorded must be *)
(* the model's. The tag of a datagram is read back from the bytes the      *)
(* table holds and from the bytes it gives out.                            *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds orphan.ndjson.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
VARIABLES i, o, max, life
vars == <<i, o, max, life>>
INSTANCE OrphanOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/orphan.ndjson")
Ev0 == Trace[i]
\* the recorded table: the entries as sequences, an empty one for a free entry
Same(y, v) == /\ DOMAIN y.slots = 1..Len(v.slots)
              /\ \A k \in DOMAIN y.slots : y.slots[k] = v.slots[k]
              /\ y.order = v.order /\ y.held = v.held /\ y.replayed = v.replayed
              /\ y.expired = v.expired /\ y.evicted = v.evicted

InitEv == /\ Ev0.op = "init" /\ max' = Ev0.max /\ life' = Ev0.life /\ o' = Orphan0(Ev0.n) /\ Same(o', Ev0.v)
HoldEv == LET x == Hold(o, max, life, Ev0.now, Ev0.key, Ev0.loc, Ev0.len, Ev0.tag)
          IN /\ Ev0.op = "hold" /\ x.ok = Ev0.ok /\ o' = x.o /\ Same(o', Ev0.v) /\ UNCHANGED <<max, life>>
TakeEv == LET x == Take(o, life, Ev0.now, Ev0.key)
              out == IF x.out = None THEN <<>> ELSE <<x.out[4], x.out[5], x.out[6]>>
          IN /\ Ev0.op = "take" /\ out = Ev0.out /\ o' = x.o /\ Same(o', Ev0.v) /\ UNCHANGED <<max, life>>
ExpireEv == /\ Ev0.op = "expire" /\ o' = Expire(o, life, Ev0.now) /\ Same(o', Ev0.v) /\ UNCHANGED <<max, life>>

Init == i = 1 /\ o = Orphan0(1) /\ max = 0 /\ life = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "coor" /\ (InitEv \/ HoldEv \/ TakeEv \/ ExpireEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the table never grows, and the counters balance
Inv == /\ o.held = o.replayed + o.expired + o.evicted + Waiting(o)
       /\ \A k \in DOMAIN o.slots : o.slots[k] = None \/ o.slots[k][5] <= max
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
