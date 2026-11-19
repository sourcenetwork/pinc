--------------------------- MODULE TraceBroadcastAuth2 ---------------------------
(***************************************************************************)
(* Trace validation of version 2 signing: pinc-broadcast auth2.rs `sign2`  *)
(* and `verify2`.                                                          *)
(*                                                                         *)
(* The Rust test tests/trace_broadcast_auth2.rs holds 8 keys (key k has    *)
(* algorithm tag KeyAlg(k): two of each algorithm). It signs fields with   *)
(* each key (its own origin, another key's origin, an origin no key owns,  *)
(* fields of another algorithm, fields that make no statement, an output   *)
(* buffer one byte short) and verifies heads built from every signature:  *)
(* unchanged, with each field changed alone (algorithm, origin, the        *)
(* incarnation, the sequence number, the topic, the wall time, the        *)
(* counter, the flags, the parents, the body), with the key of another     *)
(* node or junk bytes in the head, with another signature, plus seeded    *)
(* random mixes. Byte strings are named by small ids: an origin by `oid`   *)
(* (k for key k's node id, 8 and up for other bytes), a head key by `pki`  *)
(* (k for key k's public key, 100 and up for other bytes, -1 when absent),  *)
(* a signature by `sig`, a body by `bid`, a content id by `cid`; ids are   *)
(* assigned per distinct byte string, so equal ids are equal bytes.        *)
(*                                                                         *)
(* The checker keeps the signatures made (a `sign` event that succeeded)   *)
(* and decides itself, with Verify of BroadcastAuth2.tla (crypto ideal)    *)
(* and Encode of BroadcastStatement.tla (which fields make a statement),   *)
(* whether each sign succeeds and each verify returns an id, and that the  *)
(* id returned is the content id the signer got.                           *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds bcast/auth2.ndjson.                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLES i, orc
vars == <<i, orc>>

KeyAlg(n) == IF n \in 0..7 THEN <<1, 2, 3, 4, 1, 2, 3, 4>>[n + 1] ELSE 0
SigLen(t) == CASE t = 1 -> 64 [] t = 2 -> 64 [] t = 3 -> 3309 [] t = 4 -> 3373

A == INSTANCE BroadcastAuth2 WITH Honest <- 0..7, Byz <- {}, Algs <- 1..4, KeyCheck <- TRUE, MaxSig <- 0,
                                  Cover <- {"alg", "origin", "inc", "seq", "topic", "wall", "ctr", "flags", "parents", "body"},
                                  AlgOf <- KeyAlg, made <- {}, dlv <- 0
S == INSTANCE BroadcastStatement WITH IdW <- 32, DigW <- 32, MaxParents <- 8, MaxTopic <- 255, Wide <- TRUE, f <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/bcast/auth2.ndjson")
Ev == Trace[i]

\* the fields as the statement codec sees them (origin and body bytes do not decide a refusal: zeros stand in)
EncF(ev) == [alg |-> ev.alg, origin |-> [j \in 1..32 |-> 0], inc |-> ev.inc, seq |-> ev.seq, topic |-> ev.topic,
             wall |-> ev.wall, ctr |-> ev.ctr, flags |-> ev.flags, parents |-> ev.parents, body |-> [j \in 1..32 |-> 0]]
\* the message as BroadcastAuth2 sees it: nodes are key indices, the body is its id
Fl(ev) == [alg |-> ev.alg, origin |-> ev.oid, inc |-> ev.inc, seq |-> ev.seq, topic |-> ev.topic, wall |-> ev.wall,
           ctr |-> ev.ctr, flags |-> ev.flags, parents |-> ev.parents, body |-> ev.bid]
Msg(ev) == [x \in A!FieldNames \union {"pk"} |-> IF x = "pk" THEN ev.pki ELSE Fl(ev)[x]]

Init == i = 1 /\ orc = {}

SignEv ==
    /\ Ev.op = "sign"
    /\ LET ok == KeyAlg(Ev.k) = Ev.alg /\ S!Encode(EncF(Ev)).ok /\ Ev.cap >= SigLen(Ev.alg)
       IN IF ok THEN /\ "sig" \in DOMAIN Ev
                     /\ orc' = orc \union {[sig |-> Ev.sig, k |-> Ev.k, st |-> A!Stmt(Fl(Ev)), cid |-> Ev.cid]}
                ELSE /\ "none" \in DOMAIN Ev
                     /\ UNCHANGED orc

VerifyEv ==
    /\ Ev.op = "verify"
    /\ LET good == {o \in orc : o.sig = Ev.sig /\ S!Encode(EncF(Ev)).ok /\ A!Verify(Msg(Ev), <<o.k, o.st>>)}
       IN IF good = {} THEN "none" \in DOMAIN Ev ELSE "id" \in DOMAIN Ev /\ \E o \in good : Ev.id = o.cid
    /\ UNCHANGED orc

Step == /\ i <= Len(Trace) /\ Ev.t = "a2" /\ (SignEv \/ VerifyEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* one signature is one signer over one statement (ideal crypto), and the content id is a function of the statement
\* that no two statements share (an injective encoding, a collision-free hash)
OneSigner == \A o, p \in orc : /\ o.sig = p.sig => o = p
                               /\ o.st = p.st <=> o.cid = p.cid
=============================================================================
