---------------------------- MODULE ConnectCarrier ----------------------------
(***************************************************************************)
(* The protected carrier of pinc-connect carrier/session.rs over every     *)
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
(*    and seals nothing (EndedStays), and every call that can fail answers *)
(*    Closed, before anything else is looked at (EndedAnswersClosed);      *)
(*  - an error is fatal (CarrierError::is_fatal) exactly when the call     *)
(*    ended the carrier, or found it ended (FatalIffEnded);                *)
(*  - a key answer while no key request is outstanding answers            *)
(*    NoKeyRequest and changes nothing: an open carrier stays open         *)
(*    (NoRequestNoChange);                                                 *)
(*  - a seal before the handshake completes answers NotOpen and changes   *)
(*    nothing, whatever its size or buffer (SealStageFirst); bytes that    *)
(*    are empty or longer than a frame are refused as a frame on an open   *)
(*    carrier, which lives on (BytesRefusedLive);                          *)
(*  - free() is what a read takes when it offers more (FreeIsReceive):     *)
(*    the unit the last poll took counts as room;                          *)
(*  - the next record D sealed, intact and whole in the buffer of an open *)
(*    carrier, is accepted (InOrderAccepted), unless the receive key is   *)
(*    at its failed-open limit (KeyLimit) or the packet number is past    *)
(*    MaxPn (Record), which end the carrier (LimitEnds).                   *)
(* Lean counterparts (proofs/lean/Pinc/ConnectCarrier*.lean):              *)
(*   Aligned, EarlyRefusal   ConnectCarrier.run_ref, split_invariance,     *)
(*                           poll_idle_iff, poll_bad_len, poll_extend      *)
(*   InOrder, InOrderAccepted, NoFrameBeforeOpen                           *)
(*                           procRec_ok, procRec_auth, poll_frame_open     *)
(*   PnCount, PnUsed, NoNonceReuse                                         *)
(*                           carrier_pns, carrier_no_nonce_reuse,          *)
(*                           sealIn_ok, sealIn_never_not_increasing        *)
(*   EndChangesNothing, EndedStays, LimitEnds, EndedAnswersClosed          *)
(*                           ends_change_nothing, ended_stays, sealIn_limit*)
(*   NoRequestNoChange, SealStageFirst, BytesRefusedLive, FreeIsReceive    *)
(*                           keyResponse_no_request, seal_not_open,        *)
(*                           sealBytes_size, receive_takes_free            *)
(*   FatalIffEnded           TLC only                                      *)
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

(* A value an action uses more than once is bound with `\E x \in {e}`, not a LET: TLC evaluates a LET of an action
   again at each use. *)
PollA == LET a1 == Release(a) IN Poll(K, a, Hdr, Opens, Fok, HsOut(a1.rd))
APoll == \E a1 \in {Release(a)} : \E p \in {Poll(K, a, Hdr, Opens, Fok, HsOut(a1.rd))} :
            /\ a' = p.c
            /\ del' = IF p.r \in {"frame", "Frame"} THEN Append(del, B(a1.rd).u) ELSE del
            /\ hsn' = IF a1.st = "hs" /\ p.r = "kreq" THEN 1
                      ELSE IF a1.st = "hs" /\ p.r = "open" THEN 3 ELSE hsn
            /\ UNCHANGED <<d, w, U, sd, sa, logs>>
AnsA == AnswerSoft(K, a, AnsOut)
AAns == \E an \in {AnsA} :
        /\ a' = an.c
        /\ hsn' = IF a.st = "hs" /\ hsn = 1 /\ an.r = "hs" THEN 2 ELSE hsn
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
          /\ \E s \in {SealCall(d, how, plen, Cap(plen, short))} :
             /\ d' = s.c
             /\ IF s.r = "ok" THEN /\ U' = U \o Sealed(s, "D", plen, how = "frame")
                                   /\ sd' = Append(sd, Len(U) + 1)
                                   /\ logs' = Append(logs, <<SecD, s.pn>>)
                ELSE UNCHANGED <<U, sd, logs>>
          /\ UNCHANGED <<a, w, sa, del, hsn>>
ASealA(plen, short) == SealCall(a, "frame", plen, Cap(plen, short))
ASeal == \E plen \in 1..MAXF, short \in BOOLEAN :
          /\ Len(sa) < 1
          /\ \E s \in {ASealA(plen, short)} :
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
(* every call of A's host: the poll, the key answer, a seal (frame or short, or bytes of every length around the
   limits), a read, a transmit *)
BytesCap(p) == 2 + p + TAG
(* The properties of the next call take the calls as parameters (the poll p, the key answer an, every call cs), so Inv
   computes each call once per state; a zero-argument definition such as PollA is evaluated again at each use. *)
CR(x) == [c |-> x.c, r |-> x.r]
SealCalls == {CR(ASealA(p, s)) : p \in 1..MAXF, s \in BOOLEAN}
             \cup {CR(SealBytes(K, a, p, BytesCap(p))) : p \in 0..(MAXF + 1)}
CallsOf(p, an) == {CR(p), CR(an)}
                  \cup SealCalls
                  \cup {[c |-> Receive(K, a, n).c, r |-> "recv"] : n \in ReadSizes}
                  \cup {[c |-> Transmit(a, n).c, r |-> "tx"] : n \in {1, K.outn}}
Calls == CallsOf(PollA, AnsA)
EarlyRefusalOf(p) == LET a1 == Release(a) IN
                     (a1.st # "ended" /\ InLen(a1) >= 2 /\ (Hdr(a1.rd) = 0 \/ Hdr(a1.rd) > MaxOf(a1.st)))
                     => (p.c.st = "ended" /\ p.r = "UnitSize")
EarlyRefusal == EarlyRefusalOf(PollA)
EndChangesNothingIn(cs) == a.st # "ended" =>
                           \A x \in cs : x.c.st = "ended" =>
                              (~Delivers(x.r) /\ x.r # "ok" /\ x.c.rpn = a.rpn /\ x.c.spn = a.spn
                               /\ x.c.sk = NoKey /\ x.c.rk = NoKey)
EndChangesNothing == EndChangesNothingIn(Calls)
EndedStaysIn(cs) == a.st = "ended" =>
                    \A x \in cs : x.c.st = "ended" /\ ~Delivers(x.r) /\ x.r # "ok" /\ x.c.rpn = a.rpn /\ x.c.spn = a.spn
EndedStays == EndedStaysIn(Calls)
(* (below the receive key's limits: a ChaCha20-Poly1305 key at its failed-open limit, or a packet number past
   MAX_PACKET_NUMBER, ends the carrier instead, KeyLimit and Record) *)
InOrderAcceptedOf(p) == LET a1 == Release(a) IN
                       (a1.st = "open" /\ InLen(a1) >= 2 /\ Opens(a1.rd, a1.rpn) /\ a1.wr >= a1.rd + 2 + Hdr(a1.rd)
                        /\ a1.rpn <= MaxPn /\ ~(a1.rk.aead = "chacha" /\ a1.rk.failed >= a1.rk.chachaLim))
                       => p.r \in {"frame", "Frame"}
InOrderAccepted == InOrderAcceptedOf(PollA)
LimitEndsOf(p) == LET a1 == Release(a) IN
                  (a1.st = "open" /\ InLen(a1) >= 2 /\ Hdr(a1.rd) > TAG /\ Hdr(a1.rd) <= K.maxu
                   /\ a1.wr >= a1.rd + 2 + Hdr(a1.rd))
                  => /\ a1.rpn > MaxPn => p.r = "Record"
                     /\ (a1.rpn <= MaxPn /\ a1.rk.aead = "chacha" /\ a1.rk.failed >= a1.rk.chachaLim) => p.r = "KeyLimit"
LimitEnds == LimitEndsOf(PollA)
(* the answers of the calls, as the table of the code has them *)
Errs == {"Handshake", "UnitSize", "Authentication", "KeyLimit", "OutputFull", "Record", "Closed",
         "NotOpen", "NoKeyRequest", "NoRoom", "Frame"}
Fatal(r) == r \in {"Handshake", "UnitSize", "Authentication", "KeyLimit", "OutputFull", "Record", "Closed"}
FatalIffEndedIn(cs) == \A x \in cs : x.r \in Errs => (Fatal(x.r) <=> x.c.st = "ended")
FatalIffEnded == FatalIffEndedIn(Calls)
EndedAnswersClosedIn(cs) == a.st = "ended" => \A x \in cs : x.r \in Errs => x.r = "Closed"
EndedAnswersClosed == EndedAnswersClosedIn(Calls)
NoRequestNoChangeOf(an) == (a.st # "ended" /\ ~(a.st = "hs" /\ a.kr)) => (an.r = "NoKeyRequest" /\ an.c = a)
NoRequestNoChange == NoRequestNoChangeOf(AnsA)
SealStageFirst == a.st = "hs" => \A x \in SealCalls : x.r = "NotOpen" /\ x.c = a
BytesRefusedLive == a.st = "open" =>
    \A p \in {0, MAXF + 1} : SealBytes(K, a, p, BytesCap(p)).r = "Frame" /\ SealBytes(K, a, p, BytesCap(p)).c = a
FreeIsReceive == Receive(K, a, K.inl + 1).took = Free(K, a)
Inv == LET p == PollA
           an == AnsA
           cs == CallsOf(p, an)
       IN /\ Bounds /\ Aligned /\ InOrder /\ NoFrameBeforeOpen /\ PnCount /\ PnUsed /\ NoNonceReuse /\ NoStall
          /\ EarlyRefusalOf(p) /\ EndChangesNothingIn(cs) /\ EndedStaysIn(cs) /\ InOrderAcceptedOf(p) /\ LimitEndsOf(p)
          /\ FatalIffEndedIn(cs) /\ EndedAnswersClosedIn(cs) /\ NoRequestNoChangeOf(an) /\ SealStageFirst
          /\ BytesRefusedLive /\ FreeIsReceive

(* reachability witness (ConnectCarrier_reach.cfg, which TLC must violate): a record is delivered after a handshake
   over the stream *)
NoRecordAfterHandshake == ~(~StartOpen /\ Opened /\ Len(del) > 0)
=============================================================================
