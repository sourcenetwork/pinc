------------------------------ MODULE TraceCid -------------------------------
(***************************************************************************)
(* Trace validation of the connection id tables: pinc-transport conn/cid.rs.*)
(*                                                                         *)
(* The Rust test tests/trace_cid.rs drives real tables (built with the     *)
(* cargo feature `trace`) through seeded runs: the peer's first id learned,*)
(* the secret installed, packets authenticated for ids near the highest    *)
(* index seen (skipping, repeating, outside the lookahead, below the       *)
(* highest, index 0), ids taken for new paths, some of the ids taken        *)
(* confirmed, and queries of the ids accepted. After every call the table  *)
(* shows its slots; every event must be the step the operators of          *)
(* CidOps.tla compute from the state before it, and the state the model    *)
(* computes must be the state recorded.                                    *)
(*                                                                         *)
(* The first event of a run records, for each index it reaches, the least  *)
(* index whose derived id is the same (0: the first id); that is Id for    *)
(* the run. Runs with ids of four bytes have no collision; runs with ids   *)
(* of one byte have many, with each other and with the first id, and two   *)
(* runs at the code's sizes have the single collisions of the witnesses of *)
(* #398. An index past the recorded ones is an error of the check, never a *)
(* pass. The trace's probe of an index past 0 before the secret is         *)
(* installed is false (it has no id to derive).                            *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds cid.ndjson.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

CONSTANTS SLOTS, LOOK, FIXED, SKIP, BUMP
VARIABLES i, c, ids
vars == <<i, c, ids>>

\* the id of index j in the run being replayed, as its first event recorded it
Id(j) == ids[j + 1]

INSTANCE CidOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/cid.ndjson")
Ev0 == Trace[i]

\* the view does not show the count of ids handed out again (ru): the model carries it, and a wrong count shows as
\* a wrong index at the next claim past the window
COf(v, ru) == [ent |-> [s \in 1..SLOTS |-> [idx |-> v.ent[s][1], used |-> v.ent[s][2], seen |-> v.ent[s][3]]],
               hi |-> v.hi, tick |-> v.tick, ns |-> v.ns, cf |-> v.cf, ru |-> ru, sec |-> v.sec, fr |-> v.fr]
Same(y, v) == COf(v, y.ru) = y /\ v.epoch = Epoch(y)
\* the trace's probe of index p: index 0 is the first id; a derived id exists once the secret is installed
Probe(y, p) == p = 0 \/ (y.sec /\ IsLocal(y, p))

InitEv == /\ Ev0.op = "init" /\ c' = Init0 /\ ids' = Ev0.ids /\ Same(c', Ev0.v)
FremEv == /\ Ev0.op = "frem" /\ c' = SetFirstRemote(c) /\ Same(c', Ev0.v) /\ UNCHANGED ids
InstallEv == LET r == Install(c) IN /\ Ev0.op = "install" /\ c' = r.c /\ Same(c', Ev0.v) /\ UNCHANGED ids
AuthEv == LET r == Auth(c, Ev0.k) IN /\ Ev0.op = "auth" /\ c' = r.c /\ Same(c', Ev0.v) /\ UNCHANGED ids
ClaimEv == LET r == Claim(c) IN /\ Ev0.op = "claim" /\ r.k = Ev0.k /\ c' = r.c /\ Same(c', Ev0.v) /\ UNCHANGED ids
ConfEv == /\ Ev0.op = "conf" /\ c' = Confirm(c, Ev0.k) /\ Same(c', Ev0.v) /\ UNCHANGED ids
QueryEv == /\ Ev0.op = "query" /\ c' = c /\ Same(c, Ev0.v) /\ UNCHANGED ids
           /\ Ev0.lc = 1 + Cardinality(Held(c))
           /\ \A k \in 1..Len(Ev0.has) : Ev0.has[k][2] = Probe(c, Ev0.has[k][1])
           /\ \A k \in 1..Len(Ev0.usable) : Ev0.usable[k][2] = RemoteUsable(c, Ev0.usable[k][1])

Init == i = 1 /\ c = Init0 /\ ids = <<0>>
Step == /\ i <= Len(Trace) /\ Ev0.t = "txcid"
        /\ (InitEv \/ FremEv \/ InstallEv \/ AuthEv \/ ClaimEv \/ ConfEv \/ QueryEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the run's indices have ids of their own: no two share one and none has the first id
NoColl == \A j \in 2..Len(ids) : ids[j] = j - 1
\* Lookahead and WindowAccepted of Cid.tla, and HeldAhead in a run with no collision
Inv == /\ c.sec => \A j \in (c.hi - LOOK + 1)..(c.hi + LOOK) : j >= 1 => IsLocal(c, j)
       /\ NoColl => (c.sec => \A j \in (c.hi + 1)..(c.hi + LOOK) : Has(c, j))
       /\ (c.cf = 0 \/ c.cf < c.ns)
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
