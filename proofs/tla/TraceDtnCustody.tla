--------------------------- MODULE TraceDtnCustody ---------------------------
(***************************************************************************)
(* Trace validation of custody (pinc-dtn/src/custody.rs) on the shared     *)
(* ledger (store.rs).                                                       *)
(*                                                                          *)
(* The Rust test tests/trace_dtn_custody.rs drives the real CustodyBook on a *)
(* Ledger through the public API with seeded random acceptances, offers,     *)
(* acknowledgements (valid, stale ones naming the right node and another   *)
(* offer id, from the wrong node, for an unknown bundle, with a signature   *)
(* that does not verify), deliveries and expiries, and with the            *)
(* host's own admissions, expiries and releases on the ledger, and records   *)
(* every call. Each recorded call must be the step of DtnCustodyOps.tla     *)
(* (Accept, Offer, OnAck, Delivered, BExpire) or of DtnStoreOps.tla (the     *)
(* host's calls), and what the code returned must be what the operator       *)
(* returns: the error, the evicted entries in order, and after every call the*)
(* kept entries in slot order, the bytes charged, the held bundles with the  *)
(* node each ack is owed to, and the book's length. The node an offer was    *)
(* made to is not observable: the model carries it, and the outcome of the   *)
(* later acknowledgements is what checks it.                                 *)
(*                                                                          *)
(* The signature check of an acknowledgement is the recorded boolean (the    *)
(* signature scheme is assumed, as in the Lean model). Needs the TLA+       *)
(* CommunityModules (Json, IOUtils) and the environment variable            *)
(* PINC_TRACE_DIR, the directory that holds dtn_custody.ndjson.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES i, B, L, nx
vars == <<i, B, L, nx>>

C == INSTANCE DtnCustodyOps WITH MaxU <- 1073741823

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dtn_custody.ndjson")

Ent(j) == [key |-> <<j.s, j.i>>, bytes |-> j.b, cls |-> IF j.c = 0 THEN "custody" ELSE "transit", exp |-> j.x]
Proj(e) == [key |-> e.key, bytes |-> e.bytes, cls |-> e.cls, exp |-> e.exp]
Ents(js) == [k \in 1..Len(js) |-> Ent(js[k])]
EvProj(es) == [k \in 1..Len(es) |-> Proj(es[k])]

RECURSIVE Kept(_, _)
Kept(slots, k) == IF k > Len(slots) THEN <<>>
                  ELSE IF slots[k].full THEN <<Proj(slots[k])>> \o Kept(slots, k + 1) ELSE Kept(slots, k + 1)

LedgerSeen(L2, ev) == Kept(L2.slots, 1) = Ents(ev.snap) /\ L2.used = ev.used

BookSeen(B2, ev) ==
    /\ {<<ev.held[k][1], ev.held[k][2]>> : k \in 1..Len(ev.held)} = {<<B2[q].bundle, B2[q].prev>> : q \in C!RIdx(B2)}
    /\ Len(ev.held) = Cardinality(C!RIdx(B2))
    /\ ev.blen = Cardinality(C!RIdx(B2))

Seen(B2, L2, ev) == LedgerSeen(L2, ev) /\ BookSeen(B2, ev)

ErrOf(e) == IF e = "cap" THEN "capacity" ELSE IF e = "cust" THEN "custody" ELSE e

Init == i = 1 /\ B = <<>> /\ L = C!New(0, 0) /\ nx = 0

CNew == /\ Trace[i].t = "cu_new"
        /\ B' = [k \in 1..Trace[i].n |-> C!BNone] /\ L' = C!New(Trace[i].budget, Trace[i].ln) /\ nx' = 0
        /\ i' = i + 1

CAcc == /\ Trace[i].t = "cu_acc"
        /\ \A r \in {C!Accept(B, L, Trace[i].b, Trace[i].by, Trace[i].x, Trace[i].p, Trace[i].o, Trace[i].now)} :
              /\ r.err = ErrOf(Trace[i].err)
              /\ Trace[i].due = (r.err = "ok")
              /\ (r.err = "ok") => (r.prev = Trace[i].ap /\ r.offer = Trace[i].ao)
              /\ EvProj(r.ev) = Ents(Trace[i].ev)
              /\ Seen(r.B, r.L, Trace[i])
              /\ B' = r.B /\ L' = r.L
        /\ UNCHANGED nx /\ i' = i + 1

COff == /\ Trace[i].t = "cu_off"
        /\ \A r \in {C!Offer(B, nx, Trace[i].b, Trace[i].to)} :
              /\ r.err = Trace[i].err
              /\ r.id = Trace[i].id
              /\ nx' = r.nx
              /\ BookSeen(r.B, Trace[i]) /\ LedgerSeen(L, Trace[i])
              /\ B' = r.B
        /\ UNCHANGED L /\ i' = i + 1

CAck == /\ Trace[i].t = "cu_ack"
        /\ \A r \in {C!OnAck(B, L, Trace[i].b, Trace[i].c, Trace[i].o, Trace[i].v)} :
              /\ r.err = ErrOf(Trace[i].err)
              /\ Seen(r.B, r.L, Trace[i])
              /\ B' = r.B /\ L' = r.L
        /\ UNCHANGED nx /\ i' = i + 1

CDel == /\ Trace[i].t = "cu_del"
        /\ \A r \in {C!Delivered(B, L, Trace[i].b)} :
              /\ r.err = Trace[i].err
              /\ Seen(r.B, r.L, Trace[i])
              /\ B' = r.B /\ L' = r.L
        /\ UNCHANGED nx /\ i' = i + 1

CExp == /\ Trace[i].t = "cu_exp"
        /\ \A r \in {C!BExpire(B, L, Trace[i].now)} :
              /\ EvProj(r.ev) = Ents(Trace[i].ev)
              /\ Seen(r.B, r.L, Trace[i])
              /\ B' = r.B /\ L' = r.L
        /\ UNCHANGED nx /\ i' = i + 1

HAdm == /\ Trace[i].t = "cu_hadm"
        /\ \A r \in {C!Admit(L, <<Trace[i].s, Trace[i].i>>, Trace[i].b, IF Trace[i].c = 0 THEN "custody" ELSE "transit",
                               Trace[i].x, Trace[i].now)} :
              /\ r.err = ErrOf(Trace[i].err)
              /\ EvProj(r.ev) = Ents(Trace[i].ev)
              /\ Seen(B, r.L, Trace[i])
              /\ L' = r.L
        /\ UNCHANGED <<B, nx>> /\ i' = i + 1

HExp == /\ Trace[i].t = "cu_hexp"
        /\ \A r \in {C!Expire(L, Trace[i].now)} :
              /\ EvProj(r.ev) = Ents(Trace[i].ev)
              /\ Seen(B, r.L, Trace[i])
              /\ L' = r.L
        /\ UNCHANGED <<B, nx>> /\ i' = i + 1

HRel == /\ Trace[i].t = "cu_hrel"
        /\ \A r \in {C!Release(L, <<Trace[i].s, Trace[i].i>>)} :
              /\ r.got = Trace[i].got
              /\ r.got => Proj(r.e) = Ent(Trace[i].e)
              /\ Seen(B, r.L, Trace[i])
              /\ L' = r.L
        /\ UNCHANGED <<B, nx>> /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (CNew \/ CAcc \/ COff \/ CAck \/ CDel \/ CExp \/ HAdm \/ HExp \/ HRel)) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of DtnCustodyOps
TraceAccepted == <>(i = Len(Trace) + 1)
=============================================================================
