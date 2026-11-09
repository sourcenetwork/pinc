---------------------------- MODULE TraceDtnStore ----------------------------
(***************************************************************************)
(* Trace validation of the charged store (vinc-dtn/src/store.rs).           *)
(*                                                                          *)
(* The Rust test tests/trace_dtn_store.rs drives the real Ledger through the*)
(* public API with seeded random admissions, expiries, releases and        *)
(* reclasses over ledgers of one to four slots, two spaces and both classes,*)
(* and records every call. Each recorded call must be the step of          *)
(* DtnStoreOps.tla (Admit, Expire, Release, Reclass), and what the code    *)
(* returned must be what the operator returns: the error of an admission,   *)
(* the evicted entries in the order the callback saw them, the entry        *)
(* released, whether a reclass found its key, and after every call the kept *)
(* entries in slot order and the bytes charged. The admission number of an  *)
(* entry is not observable: the model carries it, and the order of the      *)
(* evictions is what checks it.                                             *)
(*                                                                          *)
(* The saturation maximum is 2^30 - 1 here (TLC integers are 32 bits); the  *)
(* recorded sizes are at most 12. The runs with sizes around u64::MAX are   *)
(* in dtn_store_edge.ndjson and are replayed by Lean only (exact u64).      *)
(*                                                                          *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment      *)
(* variable VINC_TRACE_DIR, the directory that holds dtn_store.ndjson.     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES i, L
vars == <<i, L>>

O == INSTANCE DtnStoreOps WITH MaxU <- 1073741823

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/dtn_store.ndjson")

\* a recorded entry without its (unobservable) admission number
Ent(j) == [key |-> <<j.s, j.i>>, bytes |-> j.b, cls |-> IF j.c = 0 THEN "custody" ELSE "transit", exp |-> j.x]
Proj(e) == [key |-> e.key, bytes |-> e.bytes, cls |-> e.cls, exp |-> e.exp]
Ents(js) == [k \in 1..Len(js) |-> Ent(js[k])]
EvProj(es) == [k \in 1..Len(es) |-> Proj(es[k])]

RECURSIVE Kept(_, _)
Kept(slots, k) == IF k > Len(slots) THEN <<>>
                  ELSE IF slots[k].full THEN <<Proj(slots[k])>> \o Kept(slots, k + 1) ELSE Kept(slots, k + 1)

\* after every call: the kept entries in slot order and the bytes charged
Seen(L2, ev) == /\ Kept(L2.slots, 1) = Ents(ev.snap) /\ L2.used = ev.used

Init == i = 1 /\ L = O!New(0, 0)

ErrOf(e) == IF e = "cust" THEN "custody" ELSE e

DNew == /\ Trace[i].t = "dl_new"
        /\ L' = O!New(Trace[i].budget, Trace[i].n)
        /\ i' = i + 1

DAdm == /\ Trace[i].t = "dl_adm"
        /\ \A r \in {O!Admit(L, <<Trace[i].s, Trace[i].i>>, Trace[i].b, IF Trace[i].c = 0 THEN "custody" ELSE "transit",
                              Trace[i].x, Trace[i].now)} :
              /\ r.err = ErrOf(Trace[i].err)
              /\ EvProj(r.ev) = Ents(Trace[i].ev)
              /\ Seen(r.L, Trace[i])
              /\ L' = r.L
        /\ i' = i + 1

DExp == /\ Trace[i].t = "dl_exp"
        /\ \A r \in {O!Expire(L, Trace[i].now)} :
              /\ EvProj(r.ev) = Ents(Trace[i].ev)
              /\ Seen(r.L, Trace[i])
              /\ L' = r.L
        /\ i' = i + 1

DRel == /\ Trace[i].t = "dl_rel"
        /\ \A r \in {O!Release(L, <<Trace[i].s, Trace[i].i>>)} :
              /\ r.got = Trace[i].got
              /\ r.got => Proj(r.e) = Ent(Trace[i].e)
              /\ Seen(r.L, Trace[i])
              /\ L' = r.L
        /\ i' = i + 1

DRec == /\ Trace[i].t = "dl_rec"
        /\ \A r \in {O!Reclass(L, <<Trace[i].s, Trace[i].i>>, IF Trace[i].c = 0 THEN "custody" ELSE "transit")} :
              /\ r.ok = Trace[i].ok
              /\ Seen(r.L, Trace[i])
              /\ L' = r.L
        /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (DNew \/ DAdm \/ DExp \/ DRel \/ DRec)) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of DtnStoreOps
TraceAccepted == <>(i = Len(Trace) + 1)
=============================================================================
