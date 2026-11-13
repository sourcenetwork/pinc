---------------------------- MODULE ConnectCarrier ----------------------------
(***************************************************************************)
(* The protected carrier of vinc-connect carrier/session.rs over every     *)
(* interleaving, at small sizes (ConnectCarrierOps.tla has the operators). *)
(*                                                                         *)
(* Two carriers: the acceptor A, whose reader is checked, and the dialer   *)
(* D, open from the start, which seals records toward A. A also seals (its *)
(* records can be reflected back to it). The stream into A is built by an  *)
(* adversary from units: the two handshake messages (in any order, any     *)
(* number of times), D's sealed records (in order, replayed, dropped,      *)
(* reordered, with a flipped bit), A's own records, units with a junk      *)
(* length (0, between the handshake and the record limit, over every       *)
(* limit) and a body of any shorter length, and the first bytes of a       *)
(* record cut short and followed by more units. A's host offers the stream *)
(* in reads of one byte or of all it has (so every split of the stream is  *)
(* reached, polls coming between any two bytes, and the bounded buffer     *)
(* pushes back), polls, answers key requests, transmits and seals, in      *)
(* every order.                                                            *)
(*                                                                         *)
(* A byte of the stream is named <<unit, index>>; two units with the same  *)
(* bytes are the same unit (a replay appends the same unit again). The     *)
(* reader splits the stream by the values of the length bytes (base Base, *)
(* 256 in the code and small here, so that a length read across a cut     *)
(* unit can be any length). A record authenticates exactly when the bytes *)
(* the reader takes are the bytes D sealed at the packet number the reader *)
(* opens with, its length bytes included (a perfect AEAD whose associated *)
(* data is the length); A's own records were sealed under the other       *)
(* direction's key and never open (the key schedule gives the two          *)
(* directions different secrets). The handshake machine of A is a step     *)
(* that yields keys: the Initial raises a key request, the answer queues  *)
(* the reply, the Finish establishes; any other unit fails it, except a   *)
(* repeated Initial after the reply, which queues the reply again (as the *)
(* responder does, which is how the handshake output fills up).            *)
(*                                                                         *)
(* Checked, in every reachable state:                                      *)
(*  - the reader takes whole units in stream order: while A lives, the     *)
(*    next unit it reads starts at a unit boundary of the stream, so the   *)
(*    units it processed are exactly the units before it (Aligned),       *)
(*    whatever the split of the stream into reads;                         *)
(*  - the records A delivers are D's records in the order D sealed them,  *)
(*    each once, none dropped, none of its own (InOrder), and none before  *)
(*    the handshake completed (NoFrameBeforeOpen);                         *)
(*  - every seal of D or A uses the packet number that counts its earlier *)
(*    successful seals (PnCount, PnUsed) and no (key, nonce) pair is used *)
(*    twice by the two carriers together (NoNonceReuse, through Record's  *)
(*    SealOp, which the carrier calls);                                    *)
(*  - the buffers are bounded and a full input buffer always holds a      *)
(*    whole unit or a refused length, so the host is never stuck (Bounds, *)
(*    NoStall);                                                            *)
(* and of the next call from every reachable state:                        *)
(*  - a length of 0 or over the stage's limit is refused (the carrier      *)
(*    ends with UnitSize) as soon as its two bytes are in (EarlyRefusal); *)
(*  - every call that ends A (a refused length, a record of at most a     *)
(*    tag, a record that does not open, a failed handshake step, a full    *)
(*    handshake output, a key limit) delivers nothing, opens nothing and   *)
(*    leaves both packet numbers as they were (EndChangesNothing);         *)
(*  - on an ended carrier every call leaves it ended and delivers, opens  *)
(*    and seals nothing (EndedStays);                                      *)
(*  - the next record D sealed, intact and whole in the buffer of an open *)
(*    carrier, is accepted (InOrderAccepted), unless the receive key is   *)
(*    at its failed-open limit (KeyLimit) or the packet number is past    *)
(*    MaxPn (Record), which end the carrier (LimitEnds).                   *)
(* Lean counterparts (proofs/lean/Vinc/ConnectCarrier*.lean):              *)
(*   Aligned, EarlyRefusal   ConnectCarrier.run_ref, split_invariance,     *)
(*                           poll_idle_iff, poll_bad_len, poll_extend      *)
(*   InOrder, InOrderAccepted, NoFrameBeforeOpen                           *)
(*                           procRec_ok, procRec_auth, poll_frame_open     *)
(*   PnCount, PnUsed, NoNonceReuse                                         *)
(*                           carrier_pns, carrier_no_nonce_reuse,          *)
(*                           sealIn_ok, sealIn_never_not_increasing        *)
(*   EndChangesNothing, EndedStays, LimitEnds                              *)
(*                           ends_change_nothing, ended_stays, sealIn_limit*)
(*   Bounds, NoStall         receive_bound, idle_has_room                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS TAG, MAXF, MAXM, MaxPn, Sat, AEAD, AesLimit, ChachaLimit, WMAX, SMAX, StartOpen, WrongMax,
          JunkLens, ReadSizes, Base
VARIABLES a, d, w, U, sd, sa, logs, del, hsn
vars == <<a, d, w, U, sd, sa, logs, del, hsn>>

INSTANCE ConnectCarrierOps

Mx(x, y) == IF x > y THEN x ELSE y
MAXU == MAXF + TAG
(* WrongMax: the deliberately wrong rule of the witness config, a reader that keeps the handshake limit for records *)
K == [inl |-> 2 + Mx(MAXU, MAXM), maxm |-> MAXM, maxu |-> IF WrongMax THEN MAXM ELSE MAXU, tag |-> TAG,
      outn |-> 2 * (2 + MAXM), maxf |-> MAXF, aead |-> AEAD, aesLim |-> AesLimit, chachaLim |-> ChachaLimit]

SecD == 1    \* D's send secret, A's receive secret
SecA == 2    \* A's send secret, D's receive secret

(* the units that exist from the start: the two handshake messages, then one junk unit per junk length *)
JunkSeq == CHOOSE s \in [1..Cardinality(JunkLens) -> JunkLens] : \A i, j \in DOMAIN s : i < j => s[i] < s[j]
Unit(kd, h, src, pn, ok, fok) == [kind |-> kd, hdr |-> h, src |-> src, pn |-> pn, ok |-> ok, fok |-> fok]
U0 == <<Unit("hs1", MAXM, "D", -1, TRUE, FALSE), Unit("hs2", MAXM, "D", -1, TRUE, FALSE)>>
      \o [i \in DOMAIN JunkSeq |-> Unit("junk", JunkSeq[i], "X", -1, FALSE, FALSE)]

(* ---- the stream into A ---- *)
B(o) == w[o + 1]
Val(b) == LET x == U[b.u] IN
          IF b.i = 0 THEN x.hdr \div Base ELSE IF b.i = 1 THEN x.hdr % Base
          ELSE IF x.kind = "rec" THEN 1 ELSE IF x.kind = "junk" THEN 3 ELSE 2
Hdr(o) == Val(B(o)) * Base + Val(B(o + 1))
Whole(o, len) == o + 2 + len <= Len(w) /\ \A j \in 0..(len + 1) : B(o + j) = [u |-> B(o).u, i |-> j]
Opens(o, pn) == LET x == U[B(o).u] IN x.kind = "rec" /\ x.src = "D" /\ x.ok /\ x.pn = pn /\ Whole(o, x.hdr)
Fok(o) == U[B(o).u].fok
HsUnit(o) == LET x == U[B(o).u] IN IF x.kind \in {"hs1", "hs2"} /\ Whole(o, x.hdr) THEN x.kind ELSE "junk"

Hs(herr, outs, kreq) == [herr |-> herr, outs |-> outs, kreq |-> kreq, sb |-> SecA, rb |-> SecD]
Reply == <<[o |-> "send", m |-> MAXM]>>
(* A's handshake machine: what handle() of the unit at o does *)
HsOut(o) ==
    LET x == HsUnit(o) IN
    IF hsn = 0 /\ x = "hs1" THEN Hs(FALSE, <<>>, TRUE)
    ELSE IF hsn = 2 /\ x = "hs1" THEN Hs(FALSE, Reply, FALSE)
    ELSE IF hsn = 2 /\ x = "hs2" THEN Hs(FALSE, <<[o |-> "est", kok |-> TRUE]>>, FALSE)
    ELSE Hs(TRUE, <<>>, FALSE)
AnsOut == IF hsn = 1 THEN Hs(FALSE, Reply, FALSE) ELSE Hs(TRUE, <<>>, FALSE)

(* the unit boundaries of the stream: offset 0, then after each unit by the value of its length bytes *)
RECURSIVE BndsFrom(_, _)
BndsFrom(o, n) == IF n = 0 \/ o + 2 > Len(w) \/ Hdr(o) = 0 THEN {o} ELSE {o} \cup BndsFrom(o + 2 + Hdr(o), n - 1)
Bnds == BndsFrom(0, Len(w))
UnitBytes(u) == 2 + U[u].hdr

OpenA == [C0("open") EXCEPT !.sk = NewKey(K, SecA), !.rk = NewKey(K, SecD)]
Init == /\ a = IF StartOpen THEN OpenA ELSE C0("hs")
        /\ d = [C0("open") EXCEPT !.sk = NewKey(K, SecD), !.rk = NewKey(K, SecA)]
        /\ w = <<>> /\ U = U0 /\ sd = <<>> /\ sa = <<>> /\ logs = <<>> /\ del = <<>>
        /\ hsn = (IF StartOpen THEN 3 ELSE 0)

(* ---- the adversary appends to A's stream ---- *)
AppendOld(u, nb) == Len(w) + nb <= WMAX /\ w' = w \o [j \in 1..nb |-> [u |-> u, i |-> j - 1]]
Adv == /\ \/ \E u \in DOMAIN U0 : /\ (StartOpen => U[u].kind = "junk")
                                   /\ \/ AppendOld(u, UnitBytes(u))
                                      \/ ~StartOpen /\ U[u].kind = "junk" /\ U[u].hdr > 0 /\ AppendOld(u, 3)
          \/ \E j \in 1..Len(sd) : AppendOld(sd[j], UnitBytes(sd[j]))
          \/ \E j \in 1..Len(sd) : AppendOld(sd[j] + 1, UnitBytes(sd[j]))      \* its twin with a flipped bit
          \/ \E j \in 1..Len(sa) : AppendOld(sa[j], UnitBytes(sa[j]))
          \/ \E j \in 1..Len(sd), c \in 1..4 : c < UnitBytes(sd[j]) /\ AppendOld(sd[j], c)
       /\ UNCHANGED <<a, d, U, sd, sa, logs, del, hsn>>

(* ---- A's host ---- *)
ARecv == \E n \in ReadSizes :
           LET off == Mn(n, Len(w) - Release(a).wr) IN
           /\ off > 0
           /\ a' = Receive(K, a, off).c
           /\ UNCHANGED <<d, w, U, sd, sa, logs, del, hsn>>

PollA == LET a1 == Release(a) IN Poll(K, a, Hdr, Opens, Fok, HsOut(a1.rd))
APoll == LET a1 == Release(a)
             p == PollA
         IN /\ a' = p.c
            /\ del' = IF p.r \in {"frame", "Frame"} THEN Append(del, B(a1.rd).u) ELSE del
            /\ hsn' = IF a1.st = "hs" /\ p.r = "kreq" THEN 1
                      ELSE IF a1.st = "hs" /\ p.r = "open" THEN 3 ELSE hsn
            /\ UNCHANGED <<d, w, U, sd, sa, logs>>
AnsA == AnswerSoft(K, a, AnsOut)
AAns == /\ a' = AnsA.c
        /\ hsn' = IF a.st = "hs" /\ hsn = 1 /\ AnsA.r = "hs" THEN 2 ELSE hsn
        /\ UNCHANGED <<d, w, U, sd, sa, logs, del>>
ATx == \E cap \in {1, K.outn} : /\ a' = Transmit(a, cap).c
                                /\ UNCHANGED <<d, w, U, sd, sa, logs, del, hsn>>

(* a seal of carrier c by the frame or bytes path *)
SealCall(c, how, plen, cap) == IF how = "frame" THEN SealFrame(K, c, plen, cap, IF cap >= 2 + plen THEN "ok" ELSE "wire")
                               ELSE SealBytes(K, c, plen, cap)
Cap(plen, short) == IF short THEN 2 + plen ELSE 2 + plen + TAG
(* a successful seal adds the unit and its twin with a flipped bit *)
Sealed(s, src, plen, fok) ==
    <<Unit("rec", plen + TAG, src, s.pn, TRUE, fok), Unit("rec", plen + TAG, src, s.pn, FALSE, fok)>>

(* D seals an encoded frame (it decodes), or bytes that are not a frame, of every length around the limits, into an
   output buffer that holds the unit or one that is a tag short *)
DSeal == \E how \in {"frame", "bytes"}, plen \in 0..(MAXF + 1), short \in BOOLEAN :
          /\ Len(sd) < SMAX
          /\ (how = "frame" => plen \in 1..MAXF)
          /\ (how = "bytes" => ~short)
          /\ LET s == SealCall(d, how, plen, Cap(plen, short)) IN
             /\ d' = s.c
             /\ IF s.r = "ok" THEN /\ U' = U \o Sealed(s, "D", plen, how = "frame")
                                   /\ sd' = Append(sd, Len(U) + 1)
                                   /\ logs' = Append(logs, <<SecD, s.pn>>)
                ELSE UNCHANGED <<U, sd, logs>>
          /\ UNCHANGED <<a, w, sa, del, hsn>>
ASealA(plen, short) == SealCall(a, "frame", plen, Cap(plen, short))
ASeal == \E plen \in 1..MAXF, short \in BOOLEAN :
          /\ Len(sa) < 1
          /\ LET s == ASealA(plen, short) IN
             /\ a' = s.c
             /\ IF s.r = "ok" THEN /\ U' = U \o Sealed(s, "A", plen, TRUE)
                                   /\ sa' = Append(sa, Len(U) + 1)
                                   /\ logs' = Append(logs, <<SecA, s.pn>>)
                ELSE UNCHANGED <<U, sa, logs>>
          /\ UNCHANGED <<d, w, sd, del, hsn>>

Next == Adv \/ ARecv \/ APoll \/ AAns \/ ATx \/ DSeal \/ ASeal
Spec == Init /\ [][Next]_vars

(* ---- properties of every reachable state ---- *)
Opened == hsn = 3
Bounds == /\ 0 <= a.cons /\ a.cons <= InLen(a) /\ InLen(a) <= K.inl /\ a.rd <= a.wr /\ a.wr <= Len(w)
          /\ a.out <= K.outn
Next0 == a.rd + a.cons    \* the offset of the next unit the reader takes
Aligned == a.st # "ended" => Next0 \in Bnds
InOrder == /\ Len(del) <= Len(sd)
           /\ \A i \in 1..Len(del) : del[i] = sd[i]
NoFrameBeforeOpen == Len(del) > 0 => Opened
PnCount == /\ a.rpn = Len(del) /\ d.spn = Len(sd) /\ a.spn = Len(sa)
PnUsed == /\ \A j \in 1..Len(sd) : U[sd[j]].pn = j - 1
          /\ \A j \in 1..Len(sa) : U[sa[j]].pn = j - 1
NoNonceReuse == \A i, j \in 1..Len(logs) : i # j => logs[i] # logs[j]
MaxOf(st) == IF st = "open" THEN K.maxu ELSE K.maxm
NoStall == LET a1 == Release(a) IN
           (a1.st # "ended" /\ InLen(a1) = K.inl) => UnitLen(a1, Hdr, MaxOf(a1.st)).k # "idle"

(* ---- properties of the next call from every reachable state ---- *)
Delivers(r) == r \in {"frame", "Frame", "open"}
(* every call of A's host: the poll, the key answer, a seal (frame or short), a read, a transmit *)
Calls == {[c |-> PollA.c, r |-> PollA.r], [c |-> AnsA.c, r |-> AnsA.r]}
         \cup {[c |-> ASealA(p, s).c, r |-> ASealA(p, s).r] : p \in 1..MAXF, s \in BOOLEAN}
         \cup {[c |-> Receive(K, a, n).c, r |-> "recv"] : n \in ReadSizes}
         \cup {[c |-> Transmit(a, n).c, r |-> "tx"] : n \in {1, K.outn}}
EarlyRefusal == LET a1 == Release(a) IN
                (a1.st # "ended" /\ InLen(a1) >= 2 /\ (Hdr(a1.rd) = 0 \/ Hdr(a1.rd) > MaxOf(a1.st)))
                => (PollA.c.st = "ended" /\ PollA.r = "UnitSize")
EndChangesNothing == a.st # "ended" =>
                     \A x \in Calls : x.c.st = "ended" =>
                        (~Delivers(x.r) /\ x.r # "ok" /\ x.c.rpn = a.rpn /\ x.c.spn = a.spn
                         /\ x.c.sk = NoKey /\ x.c.rk = NoKey)
EndedStays == a.st = "ended" =>
              \A x \in Calls : x.c.st = "ended" /\ ~Delivers(x.r) /\ x.r # "ok" /\ x.c.rpn = a.rpn /\ x.c.spn = a.spn
(* (below the receive key's limits: a ChaCha20-Poly1305 key at its failed-open limit, or a packet number past
   MAX_PACKET_NUMBER, ends the carrier instead, KeyLimit and Record) *)
InOrderAccepted == LET a1 == Release(a) IN
                   (a1.st = "open" /\ InLen(a1) >= 2 /\ Opens(a1.rd, a1.rpn) /\ a1.wr >= a1.rd + 2 + Hdr(a1.rd)
                    /\ a1.rpn <= MaxPn /\ ~(a1.rk.aead = "chacha" /\ a1.rk.failed >= a1.rk.chachaLim))
                   => PollA.r \in {"frame", "Frame"}
LimitEnds == LET a1 == Release(a) IN
             (a1.st = "open" /\ InLen(a1) >= 2 /\ Hdr(a1.rd) > TAG /\ Hdr(a1.rd) <= K.maxu
              /\ a1.wr >= a1.rd + 2 + Hdr(a1.rd))
             => /\ a1.rpn > MaxPn => PollA.r = "Record"
                /\ (a1.rpn <= MaxPn /\ a1.rk.aead = "chacha" /\ a1.rk.failed >= a1.rk.chachaLim) => PollA.r = "KeyLimit"
Inv == Bounds /\ Aligned /\ InOrder /\ NoFrameBeforeOpen /\ PnCount /\ PnUsed /\ NoNonceReuse /\ NoStall
       /\ EarlyRefusal /\ EndChangesNothing /\ EndedStays /\ InOrderAccepted /\ LimitEnds

(* reachability witness (ConnectCarrier_reach.cfg, which TLC must violate): a record is delivered after a handshake
   over the stream *)
NoRecordAfterHandshake == ~(~StartOpen /\ Opened /\ Len(del) > 0)
=============================================================================
