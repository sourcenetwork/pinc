-------------------------- MODULE TraceConnectTable --------------------------
(***************************************************************************)
(* Trace validation of the bounded tables: pinc-connect relay/table.rs.    *)
(*                                                                         *)
(* The Rust test tests/trace_connect_table.rs runs the real Table and      *)
(* Cache of small capacities, with node ids whose buckets collide, wrap    *)
(* around the end of the array and fill it. It records the bucket of every *)
(* key (bucket_of) first, then each insert, remove, retain, cache put and  *)
(* get with its answer, and after every table operation the entries in     *)
(* slot order. Every event must be the step the operators of               *)
(* ConnectTableOps.tla compute with those buckets: the same answer, the    *)
(* same keys visited by retain, and the same entries in the same slots     *)
(* order.                                                                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_table.ndjson. *)
(***************************************************************************)
EXTENDS ConnectTableOps, Json, IOUtils, TraceEnd

VARIABLES i, n, bk, t, c
vars == <<i, n, bk, t, c>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_table.ndjson")
Ev == Trace[i]

Init == i = 1 /\ n = 1 /\ bk = [x \in {} |-> 0] /\ t = NewTable(1) /\ c = NewCache(1)

Same(e) == /\ Len(e.s) = Len(Entries(n, t, 0))
           /\ \A j \in 1..Len(e.s) : Entries(n, t, 0)[j].k = e.s[j][1] /\ Entries(n, t, 0)[j].v = e.s[j][2]

Next1 == /\ i' = i + 1 /\ UNCHANGED <<n, bk, t, c>>

NewT == /\ Ev.t = "tbnew" /\ n' = Ev.n /\ bk' = [x \in {} |-> 0] /\ t' = NewTable(Ev.n) /\ c' = c /\ i' = i + 1
NewC == /\ Ev.t = "knew" /\ n' = Ev.n /\ bk' = [x \in {} |-> 0] /\ c' = NewCache(Ev.n) /\ t' = t /\ i' = i + 1
Bucket == /\ Ev.t = "tbk"
          /\ bk' = [x \in DOMAIN bk \cup {Ev.k} |-> IF x = Ev.k THEN Ev.b ELSE bk[x]]
          /\ i' = i + 1 /\ UNCHANGED <<n, t, c>>
Ins == /\ Ev.t = "tins"
       /\ LET r == Insert(n, bk, t, Ev.k, Ev.v) IN
          /\ r.res = Ev.res /\ (Ev.res = "ok" => r.old = Ev.old)
          /\ t' = r.t
       /\ i' = i + 1 /\ UNCHANGED <<n, bk, c>>
Rem == /\ Ev.t = "trem"
       /\ LET r == Remove(n, bk, t, Ev.k) IN
          /\ r.found = Ev.found /\ (Ev.found => r.v = Ev.v)
          /\ t' = r.t
       /\ i' = i + 1 /\ UNCHANGED <<n, bk, c>>
Ret == /\ Ev.t = "tret"
       /\ LET r == RetainOdd(n, bk, t) IN
          /\ r.vis = {Ev.vis[j] : j \in 1..Len(Ev.vis)}
          /\ t' = r.t
       /\ i' = i + 1 /\ UNCHANGED <<n, bk, c>>
Slots == /\ Ev.t = "tslots" /\ Same(Ev) /\ Next1
CPut == /\ Ev.t = "kput" /\ c' = CachePut(c, bk, Ev.k, Ev.v) /\ i' = i + 1 /\ UNCHANGED <<n, bk, t>>
CGet == /\ Ev.t = "kget" /\ CacheHit(c, bk, Ev.k) = Ev.hit /\ (Ev.hit => c[bk[Ev.k]].v = Ev.v) /\ Next1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (NewT \/ NewC \/ Bucket \/ Ins \/ Rem \/ Ret \/ Slots \/ CPut \/ CGet)) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of ConnectTableOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
Inv == TRUE
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
