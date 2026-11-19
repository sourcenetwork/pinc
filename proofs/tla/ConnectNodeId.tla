---------------------------- MODULE ConnectNodeId ----------------------------
(***************************************************************************)
(* Model check of the wire form of a node id: pinc-connect                 *)
(* carrier/node.rs, `read`, `write` and NODE_ID_LEN, over a systematic     *)
(* domain: every tag class (0, each known tag 1..4, 5, 127, 255) with      *)
(* three identifier bodies (all 0, 1..32, all 255), every cut of 0 to 33   *)
(* bytes, the whole id with 0, 1 and 2 bytes after it, and writes of every *)
(* id into every room from 0 to 40 bytes.                                  *)
(*                                                                         *)
(* Checked for every case (the module doc's invariants: a node id is       *)
(* exactly NODE_ID_LEN bytes, an unknown tag is refused and never mapped   *)
(* to a default; the doc of `read`: nothing is consumed on failure):       *)
(*  - ReadClass: a read succeeds exactly on 33 or more bytes with a known  *)
(*    tag and then consumes exactly 33; an unknown tag on 33 or more bytes *)
(*    is the tag error; fewer than 33 bytes are Truncated; a failed read   *)
(*    consumes nothing;                                                    *)
(*  - Canon: the 33 bytes an accepted read consumed are what `write`       *)
(*    writes for the id it returned, so an id has one encoding;            *)
(*  - WriteExact: a write succeeds exactly when 33 bytes of room are left  *)
(*    and writes 33 bytes; otherwise it writes nothing and names the       *)
(*    shortfall;                                                           *)
(*  - RoundTrip: reading what `write` wrote, followed by any bytes, gives  *)
(*    back the id and consumes 33.                                         *)
(* The cases are the successors of one root state, so all workers check    *)
(* them at once. No witness: every refusal is a case of the domain itself. *)
(* Assumption: IdentityAlg::tag and from_tag are inverse on 1..4 (the      *)
(* enum's discriminants, pinc-crypto identity.rs).                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, ConnectNodeIdOps

VARIABLE x

RTAGS == {0, 1, 2, 3, 4, 5, 127, 255}
BODIES == {[i \in 1..32 |-> 0], [i \in 1..32 |-> i], [i \in 1..32 |-> 255]}
RESTS == {<<>>, <<0>>, <<9, 255>>}

ReadIns == {SubSeq(<<t>> \o bd, 1, k) : t \in RTAGS, bd \in BODIES, k \in 0..33}
           \cup {(<<t>> \o bd) \o r : t \in RTAGS, bd \in BODIES, r \in RESTS}
WriteIns == [alg : TAGS, bytes : BODIES, room : 0..40]

Init == x = [t |-> "root"]
Next == /\ x.t = "root"
        /\ \/ \E b \in ReadIns : x' = [t |-> "rd", in |-> b]
           \/ \E w \in WriteIns : x' = [t |-> "wr", w |-> w]
Spec == Init /\ [][Next]_x

Known(b) == Len(b) >= NODEIDLEN /\ b[1] \in TAGS

ReadClass == x.t = "rd" =>
    LET b == x.in
        r == NodeRead(b)
    IN /\ (r.kind = "ok") = Known(b)
       /\ (r.kind = "tag") = (Len(b) >= NODEIDLEN /\ ~Known(b))
       /\ (r.kind = "trunc") = (Len(b) < NODEIDLEN)
       /\ r.kind = "ok" => r.used = NODEIDLEN
       /\ r.kind # "ok" => r.used = 0

Canon == x.t = "rd" =>
    LET r == NodeRead(x.in)
    IN r.kind = "ok" => NodeWrite(r.alg, r.bytes, NODEIDLEN).out = SubSeq(x.in, 1, NODEIDLEN)

WriteExact == x.t = "wr" =>
    LET w == NodeWrite(x.w.alg, x.w.bytes, x.w.room)
    IN /\ (w.kind = "ok") = (x.w.room >= NODEIDLEN)
       /\ w.kind = "ok" => Len(w.out) = NODEIDLEN
       /\ w.kind = "small" => w.out = <<>> /\ w.needed = NODEIDLEN - x.w.room

RoundTrip == x.t = "wr" =>
    LET w == NodeWrite(x.w.alg, x.w.bytes, x.w.room)
    IN w.kind = "ok" =>
         \A r \in RESTS : LET d == NodeRead(w.out \o r)
                          IN d.kind = "ok" /\ d.alg = x.w.alg /\ d.bytes = x.w.bytes /\ d.used = NODEIDLEN
=============================================================================
