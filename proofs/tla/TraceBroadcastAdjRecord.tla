------------------------- MODULE TraceBroadcastAdjRecord -------------------------
(***************************************************************************)
(* Trace validation of the adjacency record: pinc-broadcast                *)
(* reach/record.rs `parse`, `verify` and `digest`, and the writer reach.rs *)
(* `Topics::adj_frame` (through `set_adjacent`).                           *)
(*                                                                         *)
(* The Rust test tests/trace_broadcast_adj_record.rs (pinc-broadcast built *)
(* with the cargo feature `trace`, whose probe `Topics::adj_probe` returns *)
(* what parse read and whether verify passed) takes the records real nodes *)
(* of every algorithm write (with 0, 1, 3 peers, peers given out of order, *)
(* repeated, naming the node itself, and more than ADJ_MAX), and parses    *)
(* them as written, every proper cut of some, with a byte appended, with   *)
(* single bytes changed (the tag, the count, a peer, the signature), with  *)
(* the peers reordered or repeated or naming the origin and signed again   *)
(* by the origin's key, signed by another key, with another node's key in  *)
(* the head, and seeded random bytes. Events: `key` (a key's algorithm,    *)
(* node id and public key), `sign` (a key signed the digest of these       *)
(* signed bytes, giving this signature: the oracle), `write` (a node wrote *)
(* this record for these given peers), `parse` (bytes in, what the probe   *)
(* returned).                                                              *)
(*                                                                         *)
(* Each parse must equal Parse of BroadcastAdjRecord.tla at the code's     *)
(* widths (32, 8, count 2, ADJ_MAX 1024, the key and signature lengths of  *)
(* each algorithm), its signed length the model's, and verify must pass    *)
(* exactly when the oracle holds a signature of those signed bytes by the  *)
(* key the origin names (crypto ideal). Each written record must parse,    *)
(* write back to its bytes, name its writer, and hold the given peers      *)
(* without the writer (the ADJ_MAX smallest when there are more).          *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds bcast/adj_record.ndjson.                           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES i, keys, orc
vars == <<i, keys, orc>>

KeyLen(t) == CASE t = 1 -> 32 [] t = 2 -> 33 [] t = 3 -> 1952 [] t = 4 -> 1984
SigLen(t) == CASE t = 1 -> 64 [] t = 2 -> 64 [] t = 3 -> 3309 [] t = 4 -> 3373
AdjMax == 1024

\* Sym is empty: the model's ASSUME ranges over no record at these widths (BroadcastAdjRecord.cfg checks it)
R == INSTANCE BroadcastAdjRecord WITH Sym <- {}, MaxLen <- 0, OrgW <- 32, IntW <- 8, CntW <- 2, AdjMax <- AdjMax,
                                      Tags <- 1..4, PkW <- KeyLen, SigW <- SigLen, x <- <<>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/bcast/adj_record.ndjson")
Ev == Trace[i]
Range(s) == {s[j] : j \in 1..Len(s)}

\* verify: a signature of exactly these signed bytes by a key whose node id is the origin, of the record's
\* algorithm, and (unless Ed25519, whose id is the key) whose public key is the record's
Verified(r) == \E g \in orc, kk \in keys :
    /\ g.signed = r.signed /\ g.sig = r.sig /\ g.k = kk.k
    /\ kk.id = r.origin /\ kk.alg = r.alg /\ (r.alg # 1 => kk.pk = r.pk)

Init == i = 1 /\ keys = {} /\ orc = {}

KeyEv == /\ Ev.op = "key"
         /\ keys' = keys \union {[k |-> Ev.k, alg |-> Ev.alg, id |-> Ev.id, pk |-> Ev.pk]}
         /\ UNCHANGED orc

SignEv == /\ Ev.op = "sign"
          /\ \E kk \in keys : kk.k = Ev.k /\ Len(Ev.sig) = SigLen(kk.alg)
          /\ orc' = orc \union {[k |-> Ev.k, signed |-> Ev.signed, sig |-> Ev.sig]}
          /\ UNCHANGED keys

ParseEv == /\ Ev.op = "parse"
           /\ LET r == R!Parse(Ev.b)
              IN IF "none" \in DOMAIN Ev THEN ~r.ok
                 ELSE /\ r.ok
                      /\ r.origin = Ev.origin /\ r.alg = Ev.alg /\ r.pk = Ev.pk /\ r.inc = Ev.inc /\ r.seq = Ev.seq
                      /\ r.peers = Ev.peers /\ r.sig = Ev.sig /\ Len(r.signed) = Ev.slen
                      /\ Ev.ver = Verified(r)
           /\ UNCHANGED <<keys, orc>>

\* a node wrote its record: it parses, writes back to itself, names the writer, and holds the given peers
WriteEv == /\ Ev.op = "write"
           /\ LET r == R!Parse(Ev.b)
                  G == {g \in Range(Ev.given) : g # r.origin}
              IN /\ r.ok
                 /\ R!Encode(r) = Ev.b
                 /\ \E kk \in keys : /\ kk.k = Ev.k /\ kk.id = r.origin /\ kk.alg = r.alg
                                     /\ r.pk = IF r.alg = 1 THEN <<>> ELSE kk.pk
                 /\ IF Cardinality(G) <= AdjMax THEN Range(r.peers) = G
                    ELSE /\ Len(r.peers) = AdjMax /\ Range(r.peers) \subseteq G
                         /\ \A a \in Range(r.peers), b \in G \ Range(r.peers) : R!LexLt(a, b)
                 /\ orc' = orc \union {[k |-> Ev.k, signed |-> r.signed, sig |-> r.sig]}
           /\ UNCHANGED keys

Step == /\ i <= Len(Trace) /\ Ev.t = "adj" /\ (KeyEv \/ SignEv \/ ParseEv \/ WriteEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* one key per index, and one node id per key
KeysOK == \A a, b \in keys : a.k = b.k <=> a = b
=============================================================================
