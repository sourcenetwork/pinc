---------------------------- MODULE IntegrationCodecs ----------------------------
(***************************************************************************)
(* The properties of the three round trips of IntegrationCodecsOps.tla,    *)
(* over small domains (IntegrationCodecs.cfg: octets of 2 bits, tags of up *)
(* to 2 bytes; IntegrationCodecs_tag64.cfg: the real tag limit;            *)
(* IntegrationCodecs_sid.cfg: the real widths of the varint, a buffer of   *)
(* 12 bytes).                                                              *)
(*                                                                         *)
(*   RelayRT      relay_parts (relay_addr (v6, r, p)) = (r, p) in the same *)
(*                family, for every slot and peer;                         *)
(*   RelayInv     every address relay_parts accepts is the one relay_addr  *)
(*                builds from the parts (every address over the alphabet); *)
(*   RelayNone    an address it refuses is none relay_addr builds;         *)
(*   TagRT        read_tag (write_tag t ++ rest) = t with rest unread;     *)
(*   TagWriteRange write_tag refuses exactly the tags of 0 and over MAXTAG;*)
(*   TagReadOK    for every byte string: an accepted tag is 1 to MAXTAG    *)
(*                bytes, the input is exactly its length byte, the tag and *)
(*                the rest, and write_tag writes the same bytes (one       *)
(*                encoding, nothing read past the length); a refused       *)
(*                length byte leaves everything after it unread; eof       *)
(*                happens only on a short stream;                          *)
(*   SidRT, SidOK  with_sid replaces the head with the varint of the new   *)
(*                id and copies the rest unchanged, refuses what does not  *)
(*                fit, replacing an id by itself changes nothing, and      *)
(*                head_sid reads the one canonical encoding.               *)
(***************************************************************************)
EXTENDS IntegrationCodecsOps

VARIABLE x
Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

(* ---- relay ---- *)
Seg == 0..4
Addrs == {[v6 |-> FALSE, s |-> f] : f \in [1..4 -> 0..(B - 1)]} \cup {[v6 |-> TRUE, s |-> f] : f \in [1..8 -> Seg]}
Built == {RelayAddr(v, r, p) : v \in BOOLEAN, r \in 0..(B - 1), p \in 0..(B * B - 1)}

RelayRT ==
    \A v \in BOOLEAN, r \in 0..(B - 1), p \in 0..(B * B - 1) :
        /\ RelayParts(RelayAddr(v, r, p)) = [ok |-> TRUE, relay |-> r, peer |-> p]
        /\ RelayAddr(v, r, p).v6 = v
        /\ Len(RelayAddr(v, r, p).s) = IF v THEN 8 ELSE 4

RelayInv ==
    \A a \in Addrs :
        LET q == RelayParts(a) IN
        q.ok => /\ q.relay < B /\ q.peer < B * B
                /\ RelayAddr(a.v6, q.relay, q.peer) = a

RelayNone == \A a \in Addrs : ~RelayParts(a).ok => a \notin Built

(* ---- tag ---- *)
TagStrs == UNION {[1..n -> 0..(B - 1)] : n \in 0..(MAXTAG + 3)}
Edge == ({0, 1, 2, MAXTAG - 1, MAXTAG, MAXTAG + 1, B - 1}) \cap (0..(B - 1))
BTags == {[i \in 1..n |-> (i * 7 + n) % B] : n \in 0..(MAXTAG + 2)}
BInputs == {<<n>> \o [i \in 1..k |-> (i * 5 + n) % B] : n \in Edge, k \in 0..(MAXTAG + 3)}
Rests == {<<>>, <<0>>, <<B - 1, 1>>}

TagReadOK(b) ==
    LET r == TagRead(b) IN
    IF r.ok
    THEN /\ Len(r.tag) >= 1 /\ Len(r.tag) <= MAXTAG
         /\ b = <<Len(r.tag)>> \o r.tag \o r.rest
         /\ TagWrite(r.tag) = [ok |-> TRUE, b |-> <<Len(r.tag)>> \o r.tag]
         /\ Len(b) - Len(r.rest) = 1 + Len(r.tag)
    ELSE IF r.e = "config"
         THEN /\ Len(b) >= 1 /\ (b[1] = 0 \/ b[1] > MAXTAG) /\ r.rest = Tail(b)
         ELSE b = <<>> \/ (b[1] >= 1 /\ b[1] <= MAXTAG /\ Len(b) - 1 < b[1])

TagRT(T) ==
    \A t \in T, rest \in Rests :
        LET w == TagWrite(t) IN
        w.ok => TagRead(w.b \o rest) = [ok |-> TRUE, tag |-> t, rest |-> rest]

TagWriteRange(T) == \A t \in T : TagWrite(t).ok = (Len(t) >= 1 /\ Len(t) <= MAXTAG)

TagAll == TagRT(TagStrs) /\ TagWriteRange(TagStrs) /\ \A b \in TagStrs : TagReadOK(b)
TagBoundary == TagRT(BTags) /\ TagWriteRange(BTags) /\ \A b \in BInputs : TagReadOK(b)

(* ---- sid ---- *)
Wd == {0, 6, 7, 8, 13, 14, 15, 21, 28, 35, 56, 62, 63, 64}
Ids == UNION {{V!EdgeVal(j, d) : d \in {e \in -1..1 : V!EdgeOK(j, e)}} : j \in Wd}
Olds == {V!EdgeVal(j, 0) : j \in {0, 7, 14, 28, 56, 62}} \cup {V!EdgeVal(63, -1)}
SRests == {[i \in 1..n |-> 5] : n \in 0..(EXTMAX + 1)} \cup {<<255, 1, 2>>}
Junk == {<<>>, <<128>>, <<128, 0>>, <<129, 0>>, <<0, 0>>, <<127, 128>>, [i \in 1..8 |-> 255], [i \in 1..9 |-> 255],
         [i \in 1..10 |-> 128]}
Bodies == {V!Encode(o, 16).bytes \o r : o \in Olds, r \in SRests} \cup Junk

SidOK(b, sid) ==
    LET h == HeadSid(b)
        w == WithSid(b, sid)
        e == V!Encode(sid, EXTMAX)
    IN /\ (h.ok => /\ SubSeq(b, 1, Len(V!Encode(h.v, 16).bytes)) = V!Encode(h.v, 16).bytes
                   /\ (Len(b) <= EXTMAX => WithSid(b, h.v) = [ok |-> TRUE, out |-> b]))
       /\ (w.ok => /\ h.ok /\ e.kind = "ok" /\ Len(w.out) <= EXTMAX
                   /\ HeadSid(w.out) = [ok |-> TRUE, v |-> sid]
                   /\ w.out = e.bytes \o SubSeq(b, Len(V!Encode(h.v, 16).bytes) + 1, Len(b)))
       /\ (~w.ok <=> (~h.ok \/ e.kind # "ok"
                       \/ Len(e.bytes) + Len(SubSeq(b, Len(V!Encode(h.v, 16).bytes) + 1, Len(b))) > EXTMAX))

SidRT ==
    \A o \in Olds, sid \in Ids, r \in SRests :
        LET e == V!Encode(sid, EXTMAX)
            w == WithSid(V!Encode(o, 16).bytes \o r, sid)
        IN IF e.kind = "ok" /\ Len(e.bytes) + Len(r) <= EXTMAX
           THEN w = [ok |-> TRUE, out |-> e.bytes \o r]
           ELSE ~w.ok

SidAll == \A b \in Bodies, sid \in Ids : SidOK(b, sid)

(* the invariants of the configs: a constant property is checked on the one state, so TLC names it as violated *)
cRelayRT == x = 0 /\ RelayRT
cRelayInv == x = 0 /\ RelayInv
cRelayNone == x = 0 /\ RelayNone
cTagAll == x = 0 /\ TagAll
cTagBoundary == x = 0 /\ TagBoundary
cSidRT == x = 0 /\ SidRT
cSidAll == x = 0 /\ SidAll
=============================================================================
