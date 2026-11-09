------------------------------ MODULE TraceCid -------------------------------
(***************************************************************************)
(* Trace validation of the connection id tables: vinc-transport conn/cid.rs.*)
(*                                                                         *)
(* The Rust test tests/trace_cid.rs drives real tables (built with the     *)
(* cargo feature `trace`) through seeded runs: the peer's first id learned,*)
(* the secret installed, packets authenticated for ids near the highest    *)
(* index seen (skipping, repeating, outside the lookahead, below the       *)
(* highest, index 0), ids taken for new paths, and queries of the ids      *)
(* accepted. After every call the table shows its slots; every event must  *)
(* be the step the operators of CidOps.tla compute from the state before   *)
(* it, and the state the model computes must be the state recorded.        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds cid.ndjson.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

CONSTANTS SLOTS, LOOK, FIXED
VARIABLES i, c
vars == <<i, c>>

INSTANCE CidOps

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/cid.ndjson")
Ev0 == Trace[i]

COf(v) == [ent |-> [s \in 1..SLOTS |-> [idx |-> v.ent[s][1], used |-> v.ent[s][2], seen |-> v.ent[s][3]]],
           hi |-> v.hi, tick |-> v.tick, ns |-> v.ns, sec |-> v.sec, fr |-> v.fr]
Same(y, v) == COf(v) = y /\ v.epoch = Epoch(y)

InitEv == /\ Ev0.op = "init" /\ c' = Init0 /\ Same(c', Ev0.v)
FremEv == /\ Ev0.op = "frem" /\ c' = SetFirstRemote(c) /\ Same(c', Ev0.v)
InstallEv == LET r == Install(c) IN /\ Ev0.op = "install" /\ c' = r.c /\ Same(c', Ev0.v)
AuthEv == LET r == Auth(c, Ev0.k) IN /\ Ev0.op = "auth" /\ c' = r.c /\ Same(c', Ev0.v)
ClaimEv == LET r == Claim(c) IN /\ Ev0.op = "claim" /\ r.k = Ev0.k /\ c' = r.c /\ Same(c', Ev0.v)
QueryEv == /\ Ev0.op = "query" /\ c' = c /\ Same(c, Ev0.v)
           /\ Ev0.lc = 1 + Cardinality(Held(c))
           /\ \A k \in 1..Len(Ev0.has) : Ev0.has[k][2] = IsLocal(c, Ev0.has[k][1])

Init == i = 1 /\ c = Init0
Step == /\ i <= Len(Trace) /\ Ev0.t = "txcid"
        /\ (InitEv \/ FremEv \/ InstallEv \/ AuthEv \/ ClaimEv \/ QueryEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == c.sec => \A j \in (c.hi + 1)..(c.hi + LOOK) : Has(c, j)
=============================================================================
