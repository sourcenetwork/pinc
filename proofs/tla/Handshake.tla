------------------------------ MODULE Handshake ------------------------------
(***************************************************************************)
(* Model of the pinc-security handshake: the Initiator and Responder       *)
(* state machines at the message level, running against a network that an  *)
(* attacker controls. The step functions are in HsOps.tla, shared with the *)
(* trace check; this module adds the honest nodes' sessions, the shared    *)
(* stores and the attacker.                                                *)
(*                                                                         *)
(* Nodes: the honest set H and the attacker's node A. Each honest node     *)
(* runs up to NI initiator sessions and up to NR responder sessions; a     *)
(* responder node keeps a prekey cache and a ticket store of TK slots, and *)
(* an initiator node a store of CK tickets (one per peer) that it can      *)
(* export and restore. Seed adds one ticket per ordered pair of honest     *)
(* nodes issued by an earlier session that is not modelled, so resumption  *)
(* can be checked with few sessions.                                       *)
(*                                                                         *)
(* The network is the set of every message ever sent; any message in it    *)
(* can be delivered to any session any number of times in any order (drop, *)
(* reorder, duplicate, replay). The attacker can also inject a message it  *)
(* can build: a message seen on the network or of its own making, or a     *)
(* seen one with one field replaced (version, ALPN, connection ids, offer, *)
(* credit record, length, public values, ticket id, binder, ...), a blob  *)
(* or tag it can make only when it knows the key (Known), or a signature   *)
(* of its own identity or one an honest node made. It owns the secrets of  *)
(* the node A; it never learns an honest node's long-term keys or an       *)
(* honest ephemeral secret. Key requests (decapsulate, sign) are answered  *)
(* by separate steps, any time later, or fail. The random generator is the *)
(* environment: every ticket id is drawn from the pool POOL by the         *)
(* adversary of the model, collisions with stored ids included; the code   *)
(* must (and does) refuse them.                                            *)
(*                                                                         *)
(* The loss timers are real steps: the initiator's retransmit (the short   *)
(* Initial carries the full prekey on sends 3, 6, 9; an unanswered Hello   *)
(* gives way to an Initial under the same destination id on its third     *)
(* send), the responder's retransmit while it waits for the Finish, and    *)
(* shed on both sides. Ticket expiry (Expire, ExpireC), the client store's *)
(* export and restore and its restart are steps too.                       *)
(*                                                                         *)
(* The hybrid: BX and BK of HsOps break the X25519 or the ML-KEM half for  *)
(* the attacker (Known); its forgeries then also mix an honest Reply's     *)
(* public value or ciphertext with its own half (MixBases). With one half  *)
(* broken every property holds (Handshake_xbroken, _kbroken and the store  *)
(* configs): secrecy rests on the other half, agreement and authentication *)
(* on the signatures, which stay ideal. With both broken Secrecy fails     *)
(* (Handshake_bothbroken). A resumed session runs no ML-KEM: its chain key *)
(* is the ticket's key and one X25519 secret (ResumedAsPsk); a stolen      *)
(* ticket alone does not reveal the keys of a resumption an honest peer    *)
(* answered (Handshake_pskleak), with X25519 broken it does                *)
(* (Handshake_pskleak_xbroken).                                            *)
(*                                                                         *)
(* Not modelled: the prekey cache's capacity (see PrekeyCache.tla), the    *)
(* transport (padding, 1-RTT data), and a ticket store that survives a     *)
(* responder restart (it cannot: the code has no way to persist it).       *)
(***************************************************************************)
EXTENDS HsOps

CONSTANTS H1, H2, \* the two honest nodes
          ISess,  \* the initiator sessions <<node, k>>, k = 1.. in order
          RSess,  \* the responder sessions <<node, k>>
          Short,  \* TRUE: an initiator may try the short Initial
          Accept, \* TRUE: finished sessions hand their tickets to the node's store
          Seed,   \* TRUE: one ticket from an earlier session for each ordered pair of honest nodes
          Second, \* the message types a responder session beyond the first receives (a subset of {"Init", "Hello"})
          Retr,   \* TRUE: the loss timers fire (retransmit)
          Forge,  \* TRUE: the attacker also builds Initials, Replies and Hellos of its own; FALSE keeps only the injections the
                  \* store, resend and late-reply checks need (a bad binder for a stored ticket, copied connection ids, a forged late reply)
          Persist,\* TRUE: a client store is exported, restored and restarted
          Alps,   \* the ALPNs an initiator may dial
          POOL,   \* the ticket ids the generator may return
          TK, CK  \* slots of a responder's ticket store and of a client store, at least 1

VARIABLES ist,    \* initiator sessions
          rst,    \* responder sessions
          sto,    \* per responder node: prekey cache (hashes) and ticket slots
          cli,    \* per node: the client store (slots)
          snap,   \* per node: the last exported client state
          net,    \* every message sent
          signed, \* every signature an honest node made: <<id, label, transcript>>
          issued  \* every ticket a responder issued: [tid, psk, peer, al, ad, cr]
vars == <<ist, rst, sto, cli, snap, net, signed, issued>>

(* session sets for the configs, selected with <- in the .cfg *)
H == {H1, H2}
Ids == H \cup {A}
ISess_a == {<<H1, 1>>}
RSess_a == {<<H2, 1>>}
ISess_b == {<<H1, 1>>}
RSess_b == {<<H2, 1>>, <<H2, 2>>}
ISess_d == {<<H1, 1>>, <<H1, 2>>}
RSess_d == {<<H2, 1>>, <<H2, 2>>}
ISess_e == {<<H1, 1>>}
RSess_e == {<<H2, 1>>, <<H2, 2>>}
ISess_c == H \X {1}
RSess_c == H \X {1}
SecInit == {"Init"}
SecHello == {"Hello"}
AlpsOne == {Alp(1)}
AlpsTwo == {Alp(1), Alp(2)}
PoolOne == {1}
PoolTwo == {1, 2}

Draws == [1..NT -> [1..ATT -> POOL]]
Draw0 == [j \in 1..NT |-> [k \in 1..ATT |-> Min(POOL)]]

AttX == <<"i", A, 0>>
AttCoin == <<"m", A, 0>>
AttPub == Pub(AttX)
AttCid == Cid("a", A, 0)
AttCr == Cr(A)
AttOf == Off(A)
AttLens == {1}
BadT == <<"bad">>
BadAd == <<"aeadbad", 0>>
SigOK(id, lab, th) == id = A \/ <<id, lab, th>> \in signed

Other(n) == CHOOSE o \in H : o # n
SeedTid(i, r) == <<"tid0", i, r>>
SeedAd(i, r) == Ac(Off(i), r)
SeedRes(i, r) == <<"seed", i, r>>
SeedPsk(i, r) == Psk(SeedRes(i, r), SeedTid(i, r), Cr(r))
SrvSeed(i, r) == [occ |-> TRUE, tid |-> SeedTid(i, r), psk |-> SeedPsk(i, r), peer |-> i, al |-> Alp(1), ad |-> SeedAd(i, r),
                  cr |-> Cr(r), exp |-> FALSE, stamp |-> 1]
CliSeed(i, r) == [occ |-> TRUE, tid |-> SeedTid(i, r), psk |-> SeedPsk(i, r), peer |-> r, al |-> Alp(1), ad |-> SeedAd(i, r),
                  cr |-> Cr(r), exp |-> FALSE, stamp |-> 1]

Init ==
    /\ ist = [s \in ISess |-> INil]
    /\ rst = [s \in RSess |-> RNil]
    /\ sto = [r \in H |-> [pkc |-> {},
                           tks |-> [i \in 1..TK |-> IF Seed /\ i = 1 THEN SrvSeed(Other(r), r) ELSE NoSlot]]]
    /\ cli = [i \in H |-> [j \in 1..CK |-> IF Seed /\ j = 1 THEN CliSeed(i, Other(i)) ELSE NoSlot]]
    /\ snap = [i \in H |-> <<>>]
    /\ net = {}
    /\ signed = {}
    /\ issued = IF Seed THEN {[tid |-> SeedTid(i, Other(i)), psk |-> SeedPsk(i, Other(i)), peer |-> i, al |-> Alp(1), ad |-> SeedAd(i, Other(i)),
                               cr |-> Cr(Other(i))] : i \in H}
                ELSE {}

(* ---- what the attacker can inject ---- *)
NetInit == {m \in net : m.ty = "Init"}
NetHello == {m \in net : m.ty = "Hello"}
IPubs == {AttPub} \cup {m.e : m \in NetInit \cup NetHello}
CidPool == {AttCid}
CrPool == {AttCr}
TidPool == {NIL} \cup {m.tid : m \in NetHello}
           \cup UNION {{m.tids[j] : j \in DOMAIN m.tids} : m \in {x \in net : x.ty = "RReply"}}
           \cup {t.tid : t \in {x \in issued : x.peer = A}}

(* tickets the attacker was issued, by tid: it knows their pre-shared keys *)
OwnTickets == {t \in issued : t.peer = A /\ Known(t.psk)}

AttInit == M([ty |-> "Init", form |-> "full", ver |-> "ok", al |-> Alp(1), dc |-> AttCid, sc |-> AttCid, of |-> AttOf,
              cr |-> AttCr, len |-> LF, e |-> AttPub, pk |-> EK(A)])

(* An Initial the attacker can deliver: a base (its own or one seen) with the public value and prekey replaced, or a
   canonical message that fails a check the responder makes (version, ALPN, offer: one failing message stands for
   every message that fails that check). Messages seen are replayed from the network. The other fields (connection
   ids, credit record, length) the code only absorbs; the attacker's values for them are in its own Initial, and the
   single-field changes of a seen message are covered by the trace check and by the Lean attacker, who may send
   any value. *)
InitForgeries(b) ==
    {[b EXCEPT !.e = e, !.form = f, !.pk = IF f = "full" THEN EK(A) ELSE Hash(EK(A)), !.len = IF f = "full" THEN LF ELSE LS] :
        e \in IPubs, f \in {"full", "short"}}
    \cup {[b EXCEPT !.e = AttPub, !.form = f, !.pk = IF f = "full" THEN EK(x) ELSE Hash(EK(x)), !.len = IF f = "full" THEN LF ELSE LS] :
        x \in H, f \in {"full", "short"}}
InitBad == {[AttInit EXCEPT !.ver = "bad"], [AttInit EXCEPT !.al = BadAlp], [AttInit EXCEPT !.of = BadOff]}
(* a resumed responder answers an Initial under its connection ids: the attacker copies them from the Hello *)
InitSameIds(st) == {[AttInit EXCEPT !.dc = st.dc, !.sc = st.sc, !.len = l] : l \in {1, LS, LF}}

HelloBase(t) ==
    LET thh == ThH("ok", t.al, AttCid, AttCid, t.ad, t.tid, AttPub, AttCr)
    IN M([ty |-> "Hello", ver |-> "ok", al |-> t.al, dc |-> AttCid, sc |-> AttCid, ad |-> t.ad, tid |-> t.tid, e |-> AttPub,
          cr |-> AttCr, len |-> LH, binder |-> Binder(t.psk, thh)])
HelloForgeries(b) ==
    {b, [b EXCEPT !.ver = "bad"], [b EXCEPT !.al = BadAlp]}

(* A message the attacker has no way to make valid is, to the receiver, one canonical failing message: the bad ones
   below stand for every such message (any other bad field only changes what an immediate fatal failure reports, or,
   for a Reply, which check drops it). *)
ForgedToR(s) ==
    LET st == rst[s]
    IN (IF Forge THEN InitForgeries(AttInit) \cup InitBad ELSE {})
       \cup (IF st.ph = "resumed" THEN InitSameIds(st) ELSE {})
       \cup (IF Forge THEN UNION {HelloForgeries(b) : b \in NetHello \cup {HelloBase(t) : t \in OwnTickets}} ELSE {})
       \cup {M([ty |-> "Hello", ver |-> "ok", al |-> Alp(1), dc |-> AttCid, sc |-> AttCid, ad |-> Ac(AttOf, A), tid |-> t,
                e |-> AttPub, cr |-> AttCr, len |-> LH, binder |-> BadT]) : t \in TidPool \ {NIL}}
       \cup {M([ty |-> "Fin"])}
       \cup (IF st.ph = "finish" /\ Known(st.hsi)
             THEN {M([ty |-> "Fin", sealed |-> [k |-> st.hsi, ad |-> st.th3, id |-> x, sig |-> Sig(x, "initiator", Th4(st.th3, x)),
                                                cr |-> NIL]]) :
                       x \in {y \in Ids : SigOK(y, "initiator", Th4(st.th3, y))}}
             ELSE {})

ReplyBlobs(st, n, m) ==
    LET th1 == Th1(st.th0, m.sc, m.ad, m.e, m.ct)
        hsr == Hs(Ck1(IF m.ct[1] = "ct" /\ m.ct[3] = EK(n) THEN Kem(m.ct[2], m.ct[3]) ELSE <<"junk", n, m.ct>>,
                       Dh(st.x, AtomOf(m.e))), "R", th1)
    IN {BadBlob} \cup (IF Known(hsr)
                       THEN {[k |-> hsr, ad |-> th1, id |-> st.peer, sig |-> Sig(st.peer, "responder", Th2(th1, st.peer, cr)), cr |-> cr] :
                                 cr \in CrPool \cup {NIL}} ELSE {})
(* a blob that opens but holds no credit record, another identity or a signature that does not verify is dropped by
   the initiator exactly as BadBlob is (IKey), so BadBlob stands for it *)
ReplyBlobsOK(st, n, m) == {b \in ReplyBlobs(st, n, m) : b = BadBlob \/ SigOK(st.peer, "responder", Th2(Th1(st.th0, m.sc, m.ad, m.e, m.ct), st.peer, b.cr))}

(* a forged resumption reply against the Hello secrets x, thh, binder, ckpsk *)
RReplyForgeries(x, thh, binder, ckpsk) ==
    LET thr == ThR(thh, binder, AttCid, AttPub, AttCr)
        cfk == CfkK(Ck2(Ck1R(ckpsk, Dh(x, AtomOf(AttPub))), thr), thr)
        b == M([ty |-> "RReply", sc |-> AttCid, e |-> AttPub, tids |-> <<>>, cr |-> AttCr, len |-> LR])
    IN {[b EXCEPT !.conf = BadT]}
       \cup (IF Known(cfk) THEN {[b EXCEPT !.conf = Conf(cfk, ThT(thr, <<>>))]} ELSE {})

(* with a broken half the attacker can also pair an honest Reply's public value (X25519 broken) or ciphertext (ML-KEM
   broken) with its own other half: it then knows the chain key the initiator derives *)
MixBases(base) ==
    LET rs == {m \in net : m.ty = "Reply"}
    IN (IF BX THEN {[base EXCEPT !.e = r.e] : r \in rs} ELSE {}) \cup (IF BK THEN {[base EXCEPT !.ct = r.ct] : r \in rs} ELSE {})

ForgedToI(s) ==
    LET st == ist[s]
        n == s[1]
        ct == Ct(AttCoin, EK(n))
        base == M([ty |-> "Reply", sc |-> AttCid, ad |-> Ac(st.of, A), e |-> AttPub, ct |-> ct])
    IN (IF Forge THEN {[base EXCEPT !.ad = BadAd]} ELSE {})
       \cup (IF ~Forge \/ st.ph # "reply" THEN {}
             ELSE UNION {{[m EXCEPT !.sealed = b] : b \in ReplyBlobsOK(st, n, m)} :
                            m \in {base} \cup {[base EXCEPT !.sc = c] : c \in CidPool} \cup MixBases(base)})
       \cup (IF st.ph # "resume" THEN {} ELSE RReplyForgeries(st.x, st.thh, st.binder, st.ckpsk))
       \cup (IF st.late.on /\ st.ph \in {"reply", "decap", "sign"}
             THEN RReplyForgeries(st.late.x, st.late.thh, st.late.binder, st.late.ckpsk) ELSE {})
       \cup {M([ty |-> "PRej", echo |-> ist[o].th0, gap |-> g]) : o \in {x \in ISess : ist[x].ph = "reply"}, g \in BOOLEAN}
       \cup {M([ty |-> "RRej", echo |-> ist[o].thh]) : o \in {x \in ISess : ist[x].thh # NIL}}

IPool(s) == {m \in net : m.ty \in {"Reply", "PRej", "RReply", "RRej"}} \cup ForgedToI(s)
(* a responder session beyond the first only receives the Initials and Hellos seen and forged Hellos: it stands for
   the second node-level connection a replayed Hello, or the full Initial of a fallback, can reach *)
RPool(s) == IF s[2] > 1 THEN {m \in net : m.ty \in Second} \cup {m \in ForgedToR(s) : m.ty \in Second /\ m.ty = "Hello"}
            ELSE {m \in net : m.ty \in {"Init", "Hello", "Fin"}} \cup ForgedToR(s)

(* ---- initiator steps ---- *)
IFirst(s) == IF s[2] = 1 THEN TRUE ELSE ist[<<s[1], s[2] - 1>>].ph # "none"

(* Initiator::new: the host may take a ticket of the peer for the ALPN from its store first *)
IStart(s) ==
    /\ ist[s].ph = "none" /\ IFirst(s)
    /\ \E peer \in Ids \ {s[1]}, al \in Alps, short \in IF Short THEN BOOLEAN ELSE {FALSE}, take \in BOOLEAN :
        LET c == IF take THEN CTake(cli[s[1]], peer, al) ELSE [sl |-> cli[s[1]], tk |-> NoTk]
            r == INew(s[1], s[2], peer, al, short, c.tk)
        IN /\ ist' = [ist EXCEPT ![s] = r.st]
           /\ cli' = [cli EXCEPT ![s[1]] = c.sl]
           /\ net' = net \cup r.out
    /\ UNCHANGED <<rst, sto, snap, signed, issued>>

IRecv(s) ==
    /\ \E m \in IPool(s) :
        LET r == IHandle(ist[s], s[1], m)
        IN /\ ist' = [ist EXCEPT ![s] = r.st]
           /\ net' = net \cup r.out
    /\ UNCHANGED <<rst, sto, cli, snap, signed, issued>>

IAnswer(s) ==
    /\ ist[s].ph \in {"decap", "sign"}
    /\ \E kind \in {"ok", "fail"} :
        LET r == IKey(ist[s], s[1], kind)
        IN /\ ist' = [ist EXCEPT ![s] = r.st]
           /\ net' = net \cup r.out
           /\ signed' = signed \cup r.sg
    /\ UNCHANGED <<rst, sto, cli, snap, issued>>

IRetrans(s) ==
    /\ Retr
    /\ ist[s].ph # "none"
    /\ LET r == IRetransmit(s[1], ist[s])
       IN /\ ist' = [ist EXCEPT ![s] = r.st]
          /\ net' = net \cup r.out
    /\ UNCHANGED <<rst, sto, cli, snap, signed, issued>>

IShedS(s) ==
    /\ Retr
    /\ ist[s].ph # "none"
    /\ ist' = [ist EXCEPT ![s] = IShed(ist[s])]
    /\ UNCHANGED <<rst, sto, cli, snap, net, signed, issued>>

(* the tickets of a finished session reach the node's store over the protected channel *)
IAccept(s) ==
    LET st == ist[s]
    IN /\ Accept /\ st.ph = "done" /\ ~st.acc /\ st.peer \in H
       /\ \E tids \in IF st.resumed THEN {st.tids}
                      ELSE {rst[r].mytids : r \in {x \in RSess : x[1] = st.peer /\ rst[x].ph = "done" /\ rst[x].thf = st.thf}} :
            cli' = [cli EXCEPT ![s[1]] = CInsertAll(@, [j \in DOMAIN tids |->
                       [tid |-> tids[j], psk |-> Psk(st.res, tids[j], st.pcr), peer |-> st.peer, al |-> st.al,
                        ad |-> st.ad, cr |-> st.pcr]])]
       /\ ist' = [ist EXCEPT ![s].acc = TRUE]
       /\ UNCHANGED <<rst, sto, snap, net, signed, issued>>

(* ---- responder steps ---- *)
RFirst(s) == IF s[2] = 1 THEN TRUE ELSE rst[<<s[1], s[2] - 1>>].ph # "idle"

RRecv(s) ==
    /\ RFirst(s)
    /\ \E m \in RPool(s) : \E cs \in IF m.ty \in {"Fin", "Hello"} THEN Draws ELSE {Draw0} :
        LET r == RHandle(rst[s], s, sto[s[1]], m, cs)
        IN /\ rst' = [rst EXCEPT ![s] = r.st]
           /\ sto' = [sto EXCEPT ![s[1]] = r.sto]
           /\ net' = net \cup r.out
           /\ issued' = issued \cup r.iss
    /\ UNCHANGED <<ist, cli, snap, signed>>

RAnswer(s) ==
    /\ rst[s].ph = "sign"
    /\ \E kind \in {"ok", "fail"} :
        LET r == RKey(rst[s], s, sto[s[1]], kind)
        IN /\ rst' = [rst EXCEPT ![s] = r.st]
           /\ net' = net \cup r.out
           /\ signed' = signed \cup r.sg
    /\ UNCHANGED <<ist, sto, cli, snap, issued>>

RRetrans(s) ==
    /\ Retr /\ rst[s].ph = "finish"
    /\ net' = net \cup RRetransmit(rst[s], sto[s[1]]).out
    /\ UNCHANGED <<ist, rst, sto, cli, snap, signed, issued>>

RShedS(s) ==
    /\ Retr
    /\ rst' = [rst EXCEPT ![s] = RShed(rst[s])]
    /\ UNCHANGED <<ist, sto, cli, snap, net, signed, issued>>

Expire(n, i) ==
    /\ sto[n].tks[i].occ /\ ~sto[n].tks[i].exp
    /\ sto' = [sto EXCEPT ![n].tks[i].exp = TRUE]
    /\ UNCHANGED <<ist, rst, cli, snap, net, signed, issued>>

ExpireC(n, i) ==
    /\ cli[n][i].occ /\ ~cli[n][i].exp
    /\ cli' = [cli EXCEPT ![n][i].exp = TRUE]
    /\ UNCHANGED <<ist, rst, sto, snap, net, signed, issued>>

(* ClientTickets::export of the newest tickets that have not expired *)
Export(n) ==
    /\ Persist
    /\ snap' = [snap EXCEPT ![n] = CExport(cli[n], CK)]
    /\ UNCHANGED <<ist, rst, sto, cli, net, signed, issued>>

(* ClientTickets::restore: every entry that has not expired by now is stored as accept_batch stores tickets; time
   may have passed since the export, so any subset of the entries has expired *)
Restore(n) ==
    /\ Persist
    /\ \E drop \in SUBSET DOMAIN snap[n] : cli' = [cli EXCEPT ![n] = CInsertAll(@, KeepSeq(snap[n], drop, 1))]
    /\ UNCHANGED <<ist, rst, sto, snap, net, signed, issued>>

(* the process restarts: the client store is empty *)
Restart(n) ==
    /\ Persist
    /\ cli' = [cli EXCEPT ![n] = NoSlots(CK)]
    /\ UNCHANGED <<ist, rst, sto, snap, net, signed, issued>>

Next ==
    \/ \E s \in ISess : IStart(s) \/ IRecv(s) \/ IAnswer(s) \/ IRetrans(s) \/ IShedS(s) \/ IAccept(s)
    \/ \E s \in RSess : RRecv(s) \/ RAnswer(s) \/ RRetrans(s) \/ RShedS(s)
    \/ \E n \in H : Export(n) \/ Restore(n) \/ Restart(n)
    \/ \E n \in H, i \in 1..TK : Expire(n, i)
    \/ \E n \in H, i \in 1..CK : ExpireC(n, i)

Spec == Init /\ [][Next]_vars

(* ---- properties ---- *)
PrivateOK(t) == ~Known(t)
Done(r) == rst[r].est   \* established (done or resumed)

(* Agreement: two finished sessions with the same final transcript hold the same keys, name each other as peer,
   resumed alike, and agree on the ALPN, the AEAD and the credit records of both sides *)
Agreement ==
    \A i \in ISess, r \in RSess :
        (ist[i].ph = "done" /\ Done(r) /\ ist[i].thf = rst[r].thf) =>
            /\ ist[i].send = rst[r].recv /\ ist[i].recv = rst[r].send /\ ist[i].res = rst[r].res /\ ist[i].cid = rst[r].cid
            /\ ist[i].peer = r[1] /\ rst[r].peer = i[1]
            /\ ist[i].resumed = rst[r].resumed
            /\ ist[i].al = rst[r].al /\ ist[i].ad = rst[r].ad
            /\ ist[i].pcr = RCr(r) /\ rst[r].pcr = Cr(i[1])
            /\ ist[i].rcr = rst[r].rcr

(* Authentication of the responder to the initiator: it completes with an honest peer X only if X ran a responder
   session that signed (full) or accepted the Hello of (resumed, also a late reply) the same transcript *)
AuthI ==
    \A i \in ISess :
        (ist[i].ph = "done" /\ ist[i].peer \in H) =>
            \E r \in RSess : r[1] = ist[i].peer /\ rst[r].sgn /\ rst[r].ath = ist[i].ath

(* Authentication of the initiator to the responder: it completes with an honest peer Y only if Y signed the
   transcript (full) or sent the Hello (resumed) *)
AuthR ==
    \A r \in RSess :
        (Done(r) /\ rst[r].peer \in H) =>
            \E i \in ISess :
                /\ i[1] = rst[r].peer
                /\ IF rst[r].resumed THEN ist[i].thh = rst[r].thh
                   ELSE ist[i].ph = "done" /\ ist[i].th4 = rst[r].th4

(* Secrecy: the keys of a finished session with an honest peer are not known to the attacker *)
Secrecy ==
    /\ \A i \in ISess : (ist[i].est /\ ist[i].peer \in H) =>
            PrivateOK(ist[i].send) /\ PrivateOK(ist[i].recv) /\ PrivateOK(ist[i].res) /\ PrivateOK(ist[i].cid)
    /\ \A r \in RSess : (rst[r].est /\ rst[r].peer \in H) =>
            PrivateOK(rst[r].send) /\ PrivateOK(rst[r].recv) /\ PrivateOK(rst[r].res) /\ PrivateOK(rst[r].cid)
    /\ \A i \in ISess : (ist[i].early # NIL /\ ist[i].peer \in H) => PrivateOK(ist[i].early)
    /\ \A r \in RSess : (rst[r].early # NIL /\ rst[r].peer \in H) => PrivateOK(rst[r].early)

(* A resumed session runs no ML-KEM: the chain key of its keys is ck1r(the ticket's key, one X25519 secret), so its keys
   are known exactly when the ticket's pre-shared key and that X25519 secret are; with X25519 broken (BX), exactly
   when the pre-shared key is. The keys are <<"app" | "res" | "cids", ck2, ...>> with ck2 = <<"ck2", ck1, th>>. *)
Ck1Of(k) == k[2][2]
AsPsk(keys, ckp) ==
    \A k \in keys : /\ Ck1Of(k)[1] = "ck1r" /\ Ck1Of(k)[2] = ckp /\ Ck1Of(k)[3][1] = "dh"
                    /\ (Known(k) <=> (Known(ckp) /\ Known(Ck1Of(k)[3])))
                    /\ (BX => (Known(k) <=> Known(ckp)))
ResumedAsPsk ==
    /\ \A i \in ISess : (ist[i].est /\ ist[i].resumed) => AsPsk({ist[i].send, ist[i].recv, ist[i].res, ist[i].cid}, ist[i].ckpsk)
    /\ \A r \in RSess : (rst[r].est /\ rst[r].resumed) =>
           AsPsk({rst[r].send, rst[r].recv, rst[r].res, rst[r].cid}, CkPsk(rst[r].tpsk))

(* The keys of a resumption that an honest responder answered (both sides established with the same final transcript)
   are secret. The early keys are not claimed: they derive from the pre-shared key alone. With the ticket's pre-shared
   key stolen (SeedLeak) this holds, by the X25519 exchange of the resumption; with X25519 broken as well it fails. *)
ResumedSecret ==
    \A i \in ISess, r \in RSess :
        (ist[i].est /\ ist[i].resumed /\ rst[r].est /\ rst[r].resumed /\ ist[i].thf = rst[r].thf) =>
            \A k \in {ist[i].send, ist[i].recv, ist[i].res, ist[i].cid, rst[r].send, rst[r].recv, rst[r].res, rst[r].cid} :
                PrivateOK(k)

(* No early acceptance: Established and the early keys only after the peer was authenticated, and the responder's
   early keys come from a ticket it issued *)
NoEarly ==
    /\ \A i \in ISess : ist[i].est => ist[i].auth
    /\ \A r \in RSess : rst[r].est => rst[r].auth
    /\ \A r \in RSess : rst[r].early # NIL =>
            /\ rst[r].auth
            /\ \E t \in issued : t.tid = rst[r].tid /\ t.psk = rst[r].tpsk /\ Early(CkPsk(t.psk), rst[r].thh) = rst[r].early

(* 0-RTT at most once per ticket: no two responder sessions accepted a Hello with the same ticket (same pre-shared key) *)
ZeroRttOnce ==
    \A r1, r2 \in RSess : (r1 # r2 /\ rst[r1].early # NIL /\ rst[r2].early # NIL) => rst[r1].tpsk # rst[r2].tpsk

(* The prekey cache only holds hashes of prekeys whose initiator finished a handshake *)
CacheAuthenticated ==
    \A n \in H : \A h \in sto[n].pkc : \E r \in RSess : r[1] = n /\ rst[r].ph = "done" /\ rst[r].hpk = h

(* Rejects: a reject delivered to an initiator never authenticates or establishes it and never changes whom it
   dialed. A prekey reject leaves a session that waits for a Reply as it was (same transcript, same form of its
   resends), but for noting that a full Initial went out for a reject; a resume reject moves a resumption to a fresh
   full handshake. A responder's reject leaves its state unchanged. (Before the resend rules of the reject gap, a
   prekey reject moved a short Initial to the full form for good; it no longer does.) *)
RejectsOnlyFallback ==
    /\ \A s \in ISess : \A m \in IPool(s) :
        m.ty \in {"PRej", "RRej"} =>
            LET r == IHandle(ist[s], s[1], m).st
            IN \/ r = ist[s]
               \/ (/\ ist[s].ph = "reply" /\ r = [ist[s] EXCEPT !.rgap = TRUE] /\ ~r.est /\ ~r.auth)
               \/ (/\ ist[s].ph = "resume" /\ r.ph = "reply" /\ r.fell /\ r.peer = ist[s].peer /\ ~r.est /\ ~r.auth
                   /\ ~ist[s].est)
    /\ \A s \in RSess : \A m \in RPool(s) :
        LET r == RHandle(rst[s], s, sto[s[1]], m, Draw0)
        IN (\E o \in r.out : o.ty = "PRej") => (r.st = rst[s] /\ r.sto = sto[s[1]])

TypeOK ==
    /\ \A s \in ISess : ist[s].ph \in {"none", "reply", "resume", "decap", "sign", "done", "failed"}
    /\ \A s \in RSess : rst[s].ph \in {"idle", "sign", "finish", "resumed", "done", "failed"}
    /\ \A n \in H : Len(sto[n].tks) = TK /\ Cardinality(Occ(sto[n].tks)) <= TK
    /\ \A n \in H : Len(cli[n]) = CK /\ Cardinality(Occ(cli[n])) <= CK
    /\ \A r \in RSess : rst[r].spent <= SpentCap

(* a ticket in a server slot was issued *)
TicketsIssued ==
    \A n \in H : \A i \in Occ(sto[n].tks) : \E t \in issued : t.tid = sto[n].tks[i].tid /\ t.psk = sto[n].tks[i].psk

(* the code makes the stored ticket ids of a store pairwise distinct, whatever the generator returns *)
UniqueIds ==
    \A n \in H : \A i, j \in Occ(sto[n].tks) : sto[n].tks[i].tid = sto[n].tks[j].tid => i = j

(* a client store holds at most one ticket per peer, and only tickets some node issued for that session *)
ClientOnePerPeer ==
    \A n \in H : \A i, j \in Occ(cli[n]) : cli[n][i].peer = cli[n][j].peer => i = j
ClientTicketsIssued ==
    \A n \in H : \A i \in Occ(cli[n]) :
        cli[n][i].peer \in H => \E t \in issued : t.tid = cli[n][i].tid /\ t.psk = cli[n][i].psk /\ t.peer = n

(* A19: a Hello that gave way to a full Initial kept its destination id *)
FallbackKeepsDcid ==
    \A s \in ISess : ist[s].late.on => ist[s].dc = Cid("d", s[1], s[2])

(* A21: a resumed responder sends its Reply again only within the byte budgets: a repeated Hello of the same
   transcript while the bytes it was sent total at most RB, and an Initial under the same ids only when the Reply is
   at most three times its size and the bytes total at most LB *)
ResendWithinBudget ==
    \A s \in RSess : rst[s].ph = "resumed" =>
        \A m \in RPool(s) :
            LET r == RHandle(rst[s], s, sto[s[1]], m, Draw0)
            IN rst[s].reply \in r.out =>
                \/ /\ m.ty = "Hello" /\ r.st.thh = rst[s].thh /\ r.st.spent <= RB
                \/ /\ m.ty = "Init" /\ m.dc = rst[s].dc /\ m.sc = rst[s].sc
                   /\ rst[s].reply.len <= 3 * m.len /\ r.st.spent <= LB

=============================================================================
