--------------------------- MODULE TraceFacadeBufs ---------------------------
(***************************************************************************)
(* Trace validation of the facade's buffer pools: crates/pinc/src/         *)
(* drive.rs `pools` (both shapes), `pooled`, `Buf::drop`, `POOLED` = 8,    *)
(* against the operators of FacadeBufsOps.tla at the real POOLED.          *)
(*                                                                         *)
(* The unit test `drive::tests::trace_facade_bufs` runs in both builds of  *)
(* the crate `pinc` (with `std`: facade_bufs_std.ndjson; without:          *)
(* facade_bufs_nostd.ndjson). Each run, on a thread of its own so the std  *)
(* pools start empty, builds the receive pools of two endpoints            *)
(* (`pools(L, L).0`, twice) and drives holders of either endpoint through  *)
(* `pooled` and the drop of the `Buf`. A buffer is named by a u32 tag the  *)
(* test writes into its first four bytes when it is handed out (a new      *)
(* buffer reads 0; the reserved buffers of the build without std are       *)
(* tagged 1 and 2), so the trace sees which buffer `pooled` popped.        *)
(*                                                                         *)
(* Every event must be the model's step (the take or give of that holder,  *)
(* the popped buffer the model's top of the pool) and the recorded pools   *)
(* and holders must be the model's state. Without std the recorded         *)
(* capacity of each pool's Vec is the one of the build (at least POOLED)   *)
(* at every step: no buffer that goes back allocates (the model's NoGrow). *)
(* With std the capacity is std's growth, not compared; only that it holds *)
(* the pool.                                                               *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds both files.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
VARIABLES i, st, cf
vars == <<i, st, cf>>

P == INSTANCE FacadeBufsOps WITH POOLED <- 8

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/facade_bufs_std.ndjson")
         \o ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/facade_bufs_nostd.ndjson")
Ev0 == Trace[i]

\* the endpoint of holder h in the run (holders 1..h1 are endpoint 1's)
Ep(c, h) == IF h <= c.h1 THEN 1 ELSE 2

\* the recorded pools and holders are the model's
SameBuf(b, r) == b.id = r[1] /\ b.len = r[2]
Same(s, c, v) ==
    /\ \A q \in 1..2 : Len(v.pools[q]) = Len(s.pools[q])
                       /\ \A k \in 1..Len(s.pools[q]) : SameBuf(s.pools[q][k], v.pools[q][k])
    /\ Len(v.held) = Cardinality(DOMAIN s.held)
    /\ \A h \in DOMAIN s.held : SameBuf(s.held[h], v.held[h])
    /\ IF c.std THEN v.cap[1] >= Len(v.pools[1])
       ELSE v.cap = c.cap0 /\ s.cap = <<8, 8>>

InitEv ==
    /\ Ev0.op = "init"
    /\ Ev0.h1 \in 1..(Ev0.hs - 1)
    /\ cf' = [std |-> Ev0.std, h1 |-> Ev0.h1, lens |-> Ev0.lens, cap0 |-> Ev0.v.cap]
    /\ st' = P!Built(Ev0.std, 1..Ev0.hs, Ev0.lens)
    /\ ~Ev0.std => (Ev0.v.cap[1] >= 8 /\ Ev0.v.cap[2] >= 8)
    /\ Same(st', cf', Ev0.v)

TakeEv ==
    LET h == Ev0.h
        e == Ep(cf, h)
    IN /\ Ev0.op = "take"
       /\ h \in DOMAIN st.held /\ st.held[h] = P!NoBuf
       /\ Ev0.e = e /\ Ev0.len = cf.lens[e]
       /\ Ev0.got = IF P!Popped(cf.std, st, e) THEN P!TopOf(cf.std, st, e).id ELSE 0
       /\ st' = P!Take(cf.std, st, h, e, cf.lens[e])
       /\ UNCHANGED cf
       /\ Same(st', cf, Ev0.v)

GiveEv ==
    LET h == Ev0.h
        e == Ep(cf, h)
    IN /\ Ev0.op = "give"
       /\ h \in DOMAIN st.held /\ st.held[h] # P!NoBuf
       /\ Ev0.e = e
       /\ st' = P!Give(cf.std, st, h, e)
       /\ UNCHANGED cf
       /\ Same(st', cf, Ev0.v)

Init == /\ i = 1
        /\ st = P!Built(FALSE, {}, <<4, 4>>)
        /\ cf = [std |-> FALSE, h1 |-> 0, lens |-> <<4, 4>>, cap0 |-> <<0, 0>>]
\* the first event of the trace is an init (a take or give before one finds no holder and deadlocks)
Step == /\ i <= Len(Trace) /\ Ev0.t = "bufs" /\ (InitEv \/ TakeEv \/ GiveEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* along the trace: no pool holds more than POOLED, a held buffer has its endpoint's length
Inv == /\ \A q \in 1..2 : Len(st.pools[q]) <= 8
       /\ \A h \in DOMAIN st.held : st.held[h] # P!NoBuf => st.held[h].len = cf.lens[Ep(cf, h)]
=============================================================================
