---------------------------- MODULE BroadcastAdjRecord ----------------------------
(***************************************************************************)
(* The adjacency record of pinc-broadcast reach/record.rs: `parse` (and   *)
(* the signed prefix `verify` checks) and its writer, reach.rs             *)
(* `Topics::adj_frame` (the part after the frame header).                  *)
(*                                                                         *)
(* The layout is the code's: origin alg1 [public key] inc seq count peers  *)
(* signature, big endian, the key absent for tag 1 (Ed25519). The widths   *)
(* are parameters (the code: 32, 8, 2 for the count, ADJ_MAX 1024, the key *)
(* and signature lengths of each algorithm). parse gives nothing (None)    *)
(* for a cut record, an unknown tag, a count above AdjMax, trailing bytes, *)
(* peers not strictly ascending (which also refuses repeats) or peers that *)
(* name the origin; the signed bytes are the record up to the signature.   *)
(*                                                                         *)
(* Checked over every byte string up to MaxLen symbols: WellFormed (a      *)
(* parsed record has its peers ascending, without the origin, at most      *)
(* AdjMax), Canonical (writing a parsed record gives the same bytes),      *)
(* Strict (no proper prefix and no one-symbol extension parses),          *)
(* SignedBinds (the signed prefix alone decides every field but the        *)
(* signature: any signature after it parses to the same origin,           *)
(* algorithm, key, incarnation, sequence number and peers, so a signature *)
(* over the digest of the signed bytes binds all of them). As an ASSUME    *)
(* over every well-formed record of the alphabet: RoundTrip. Witness:      *)
(* BroadcastAdjRecord_peers.cfg (a record with two peers parses).          *)
(* Crypto ideal, not modelled (the digest is collision free, a signature   *)
(* is the named key's). TraceBroadcastAdjRecord.tla checks the real        *)
(* parse, verify and writer.                                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Sym, MaxLen, OrgW, IntW, CntW, AdjMax, Tags, PkW(_), SigW(_)

Ed == 1
PkSmall(t) == 1
SigSmall(t) == 1
KeyW(t) == IF t = Ed THEN 0 ELSE PkW(t)
Sl(b, p, n) == SubSeq(b, p, p + n - 1)
RECURSIVE Val(_)
Val(s) == IF s = <<>> THEN 0 ELSE Val(SubSeq(s, 1, Len(s) - 1)) * 256 + s[Len(s)]
\* k <= 4 only
BE(n, k) == [i \in 1..k |-> (n \div (256 ^ (k - i))) % 256]
RECURSIVE Cat(_)
Cat(s) == IF s = <<>> THEN <<>> ELSE Head(s) \o Cat(Tail(s))
LexLt(a, b) == \E k \in 1..Len(a) : a[k] < b[k] /\ \A j \in 1..(k - 1) : a[j] = b[j]
Ascending(ps) == \A i \in 1..(Len(ps) - 1) : LexLt(ps[i], ps[i + 1])
None == [ok |-> FALSE]

\* record.rs parse
Parse(b) ==
    IF Len(b) < OrgW + 1 THEN None
    ELSE IF b[OrgW + 1] \notin Tags THEN None
    ELSE LET t == b[OrgW + 1]
             pc == OrgW + 2 + KeyW(t) + 2 * IntW
         IN IF Len(b) < pc + CntW - 1 THEN None
            ELSE IF Val(Sl(b, pc, CntW)) > AdjMax THEN None
            ELSE LET n == Val(Sl(b, pc, CntW))
                     pp == pc + CntW
                     ps == pp + n * OrgW
                     origin == Sl(b, 1, OrgW)
                     peers == [j \in 1..n |-> Sl(b, pp + (j - 1) * OrgW, OrgW)]
                 IN IF Len(b) # ps - 1 + SigW(t) THEN None
                    ELSE IF ~Ascending(peers) \/ (\E j \in 1..n : peers[j] = origin) THEN None
                    ELSE [ok |-> TRUE, origin |-> origin, alg |-> t, pk |-> Sl(b, OrgW + 2, KeyW(t)),
                          inc |-> Sl(b, OrgW + 2 + KeyW(t), IntW), seq |-> Sl(b, OrgW + 2 + KeyW(t) + IntW, IntW),
                          peers |-> peers, signed |-> SubSeq(b, 1, ps - 1), sig |-> Sl(b, ps, SigW(t))]

\* adj_frame: me, the tag, the key unless Ed25519, inc, seq, the count, the peers, then the signature
Encode(v) == v.origin \o <<v.alg>> \o v.pk \o v.inc \o v.seq \o BE(Len(v.peers), CntW) \o Cat(v.peers) \o v.sig

Ids == [1..OrgW -> Sym]
ViewsOf(t) == {[origin |-> o, alg |-> t, pk |-> k, inc |-> n, seq |-> n, peers |-> p, sig |-> g] :
                 o \in Ids, k \in [1..KeyW(t) -> Sym], n \in [1..IntW -> Sym], g \in [1..SigW(t) -> Sym],
                 p \in {q \in UNION {[1..m -> Ids] : m \in 0..AdjMax} : Ascending(q) /\ \A j \in 1..Len(q) : q[j] # o}}
Views == UNION {ViewsOf(t) : t \in Tags}
RoundTrip == \A v \in Views :
    LET r == Parse(Encode(v))
    IN /\ r.ok /\ r.origin = v.origin /\ r.alg = v.alg /\ r.pk = v.pk /\ r.inc = v.inc /\ r.seq = v.seq
       /\ r.peers = v.peers /\ r.sig = v.sig
ASSUME RoundTrip

VARIABLE x
Init == x \in UNION {[1..n -> Sym] : n \in 0..MaxLen}
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

WellFormed == LET r == Parse(x)
              IN r.ok => Ascending(r.peers) /\ Len(r.peers) <= AdjMax /\ \A j \in 1..Len(r.peers) : r.peers[j] # r.origin

Canonical == Parse(x).ok => Encode(Parse(x)) = x

Strict == Parse(x).ok => /\ \A k \in 0..(Len(x) - 1) : ~Parse(SubSeq(x, 1, k)).ok
                         /\ \A s \in Sym : ~Parse(x \o <<s>>).ok

SignedBinds == LET r == Parse(x)
               IN r.ok => /\ r.signed \o r.sig = x
                          /\ \A g \in [1..SigW(r.alg) -> Sym] :
                                LET q == Parse(r.signed \o g)
                                IN q.ok /\ q.origin = r.origin /\ q.alg = r.alg /\ q.pk = r.pk /\ q.inc = r.inc
                                   /\ q.seq = r.seq /\ q.peers = r.peers

\* witness (must be violated): a record with two peers parses
NoTwoPeers == Parse(x).ok => Len(Parse(x).peers) < 2
=============================================================================
