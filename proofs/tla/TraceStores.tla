------------------------------ MODULE TraceStores ------------------------------
(***************************************************************************)
(* Trace validation of the ticket stores and the prekey cache              *)
(* (pinc-security/src/tickets.rs and cache.rs).                            *)
(*                                                                         *)
(* The Rust test tests/trace_stores.rs drives the real ClientTickets,      *)
(* ServerTickets and PrekeyCache through the public API with seeded        *)
(* random operations and records every call. Each recorded step must be a *)
(* step of the operators of Tickets.tla (AcceptSeq, Take, Export, Restore, *)
(* IssueBatch) or PrekeyCache.tla (ImplGet, ImplInsert), and what the      *)
(* code returned must be what the operator returns: the ticket a take      *)
(* returned, the exported tickets, the count a restore reported and        *)
(* whether it accepted the bytes, the batch an issue returned and whether  *)
(* it failed for lack of an unused id (the draws of the generator are      *)
(* recorded), whether a cache get hit and the key it returned, and after   *)
(* every call the length of the store. After every client call the whole   *)
(* content of the store, read back with export, must equal the model's     *)
(* slots in the order of the stamps. Byte strings are ids (the idef lines  *)
(* only matter to the Lean replay); times are the code's nanoseconds, a    *)
(* lifetime of L seconds is L * 10^9.                                      *)
(*                                                                         *)
(* An export that fails (buffer too small) leaves the store unchanged, and *)
(* the byte-level size is checked in Lean (TicketsExport.exportBytes); the *)
(* TLA model checks the content.                                           *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds stores.ndjson.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

VARIABLES i, cl, sv, pcc
vars == <<i, cl, sv, pcc>>

TK == INSTANCE Tickets WITH Unit <- 1000000000, Attempts <- 8, MaxBatch <- 4, Peers <- {}, Alpns <- {}, Tids <- {},
          Psks <- {}, AeadVals <- {}, CreditVals <- {}, ExpVals <- {}, Nows <- {}, Ids <- {}, NC <- 0, NS <- 0,
          MaxClock <- 0, Mode <- "client", TicketSet <- {}, Batches <- {}, Streams <- {}, cl <- 0, sv <- 0
PC == INSTANCE PrekeyCache WITH N <- 0, Hashes <- {}, Vals <- {}, MaxClock <- 0, c <- 0, L <- 0, out <- 0

Raw == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/stores.ndjson")
Trace == SelectSeq(Raw, LAMBDA l : l.t # "idef")

Tk(j) == [full |-> TRUE, peer |-> j.p, alpn |-> j.a, tid |-> j.t, psk |-> j.s, aead |-> j.ae, exp |-> j.x, credit |-> j.cr]
Tks(s) == [k \in 1..Len(s) |-> Tk(s[k])]

Init == i = 1 /\ cl = TK!EmptyStore(0) /\ sv = TK!EmptyStore(0) /\ pcc = [slots |-> <<>>, clock |-> 0]

\* after a client call the store holds exactly the recorded tickets, oldest first, and its length
ClientSeen(c2, ev) ==
    /\ TK!Export(c2.slots, 0, Len(c2.slots)) = Tks(ev.snap)
    /\ Cardinality(TK!Occ(c2.slots)) = ev.len

CNew == /\ Trace[i].t = "cnew"
        /\ cl' = TK!EmptyStore(Trace[i].n)
        /\ i' = i + 1 /\ UNCHANGED <<sv, pcc>>

CAcc == /\ Trace[i].t = "cacc"
        /\ \A k \in 1..Len(Trace[i].b) : Trace[i].b[k].x = TK!Exp(Trace[i].now, Trace[i].b[k].lf)
        /\ cl' = TK!AcceptSeq(cl, Tks(Trace[i].b), Trace[i].now)
        /\ ClientSeen(cl', Trace[i])
        /\ i' = i + 1 /\ UNCHANGED <<sv, pcc>>

CBad == /\ Trace[i].t = "cbad"
        /\ ClientSeen(cl, Trace[i])
        /\ i' = i + 1 /\ UNCHANGED <<cl, sv, pcc>>

CTake == /\ Trace[i].t = "ctake"
         /\ \A r \in {TK!Take(cl, Trace[i].p, Trace[i].a, Trace[i].now)} :
                /\ r.got.full = Trace[i].got
                /\ Trace[i].got => r.got = Tk(Trace[i].e)
                /\ cl' = r.cl
         /\ ClientSeen(cl', Trace[i])
         /\ i' = i + 1 /\ UNCHANGED <<sv, pcc>>

CExp == /\ Trace[i].t = "cexp"
        /\ Trace[i].ok => TK!Export(cl.slots, Trace[i].now, Trace[i].max) = Tks(Trace[i].b)
        /\ ClientSeen(cl, Trace[i])
        /\ i' = i + 1 /\ UNCHANGED <<cl, sv, pcc>>

Blob(ev) == [ver |-> ev.ver, ents |-> Tks(ev.b) \o (IF ev.bad THEN <<TK!Bad>> ELSE <<>>), trailing |-> ev.trail]

CRes == /\ Trace[i].t = "cres"
        /\ \A r \in {TK!Restore(cl, Blob(Trace[i]), Trace[i].now)} :
               /\ TK!Wellformed(Blob(Trace[i])) = Trace[i].ok
               /\ r.n = Trace[i].n
               /\ cl' = r.cl
        /\ ClientSeen(cl', Trace[i])
        /\ i' = i + 1 /\ UNCHANGED <<sv, pcc>>

SNew == /\ Trace[i].t = "snew"
        /\ sv' = TK!EmptyStore(Trace[i].n)
        /\ i' = i + 1 /\ UNCHANGED <<cl, pcc>>

SIss == /\ Trace[i].t = "siss"
        /\ \A r \in {TK!IssueBatch(sv, Trace[i].draws, Trace[i].now, Trace[i].lf, Trace[i].cnt)} :
               /\ (r.res = "ok") = Trace[i].ok
               /\ Trace[i].ok => r.batch = Trace[i].batch
               /\ r.res # "rand"
               /\ sv' = r.sv
               /\ Cardinality(TK!Occ(r.sv.slots)) = Trace[i].len
        /\ i' = i + 1 /\ UNCHANGED <<cl, pcc>>

PNew == /\ Trace[i].t = "pnew"
        /\ pcc' = [slots |-> [k \in 1..Trace[i].n |-> PC!None], clock |-> 0]
        /\ i' = i + 1 /\ UNCHANGED <<cl, sv>>

PGet == /\ Trace[i].t = "pget"
        /\ \A r \in {PC!ImplGet(pcc, Trace[i].h)} :
               /\ r.hit = Trace[i].hit
               /\ r.hit => r.val = Trace[i].v
               /\ pcc' = r.c
               /\ Cardinality(PC!Occ(r.c.slots)) = Trace[i].len
        /\ i' = i + 1 /\ UNCHANGED <<cl, sv>>

PIns == /\ Trace[i].t = "pins"
        /\ pcc' = PC!ImplInsert(pcc, Trace[i].h, Trace[i].v)
        /\ Cardinality(PC!Occ(pcc'.slots)) = Trace[i].len
        /\ i' = i + 1 /\ UNCHANGED <<cl, sv>>

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (CNew \/ CAcc \/ CBad \/ CTake \/ CExp \/ CRes \/ SNew \/ SIss \/ PNew \/ PGet \/ PIns))
         \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of Tickets.tla and PrekeyCache.tla
TraceAccepted == <>(i = Len(Trace) + 1)
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=================================================================================
