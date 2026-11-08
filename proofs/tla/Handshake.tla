------------------------------ MODULE Handshake ------------------------------
(***************************************************************************)
(* Model of the vinc-security handshake: the Initiator and Responder       *)
(* state machines at the message level, running against a network that an  *)
(* attacker controls. The step functions are in HsOps.tla, shared with the *)
(* trace check; this module adds the honest nodes' sessions, the shared    *)
(* stores and the attacker.                                                *)
(*                                                                         *)
(* Nodes: the honest set H and the attacker's node A. Each honest node     *)
(* runs up to NI initiator sessions and up to NR responder sessions; a     *)
(* responder node keeps a prekey cache and a ticket store of TK slots      *)
(* (tickets.rs), and an initiator node a store of the tickets it was       *)
(* handed. Seed adds one ticket per ordered pair of honest nodes issued by *)
(* an earlier session that is not modelled, so resumption can be checked   *)
(* with few sessions.                                                      *)
(*                                                                         *)
(* The network is the set of every message ever sent; any message in it    *)
(* can be delivered to any session any number of times in any order (drop, *)
(* reorder, duplicate, replay). The attacker can also inject a message it  *)
(* can build: every field is a public value (prekeys, ephemeral publics    *)
(* seen on the network or its own, identities, ticket ids it saw or was    *)
(* issued), a blob or tag it can make only when it knows the key (Known),  *)
(* or a signature of its own identity or one an honest node made. It owns  *)
(* the secrets of the node A; it never learns an honest node's long-term   *)
(* keys or an honest ephemeral secret. Key requests (decapsulate, sign)    *)
(* are answered by separate steps, any time later, or fail.                *)
(*                                                                         *)
(* Retransmission timers add no behaviour beyond redelivery, except for    *)
(* the short Initial that every third retransmission replaces by the full  *)
(* one (IRetransmitFull). Not modelled: the prekey cache's capacity,       *)
(* ticket lifetimes beyond the nondeterministic Expire step, the client    *)
(* store's capacity, and the transport (padding, connection ids, 1-RTT     *)
(* data). Several tickets per session are covered by the Lean model of the *)
(* store; here a session issues one.                                       *)
(***************************************************************************)
EXTENDS HsOps

CONSTANTS H1, H2, \* the two honest nodes
          ISess,  \* the initiator sessions <<node, k>>, k = 1.. in order
          RSess,  \* the responder sessions <<node, k>>
          Short,  \* TRUE: an initiator may try the short Initial
          Accept, \* TRUE: finished sessions hand their tickets to the node's store
          Seed    \* TRUE: one ticket from an earlier session for each ordered pair of honest nodes

VARIABLES ist,    \* initiator sessions
          rst,    \* responder sessions
          sto,    \* per responder node: prekey cache, ticket slots, stamp clock
          cli,    \* per node: the tickets it holds to resume with
          net,    \* every message sent
          signed, \* every signature an honest node made: <<id, label, transcript>>
          issued  \* every ticket a responder issued: [tid, psk, peer]
vars == <<ist, rst, sto, cli, net, signed, issued>>

(* session sets for the configs, selected with <- in the .cfg *)
H == {H1, H2}
Ids == H \cup {A}
ISess_a == {<<H1, 1>>}
RSess_a == {<<H2, 1>>}
ISess_b == {<<H1, 1>>}
RSess_b == {<<H2, 1>>, <<H2, 2>>}
ISess_d == {<<H1, 1>>, <<H1, 2>>}
RSess_d == {<<H2, 1>>, <<H2, 2>>}
ISess_c == H \X {1}
RSess_c == H \X {1}
AttX == <<"i", A, 0>>
AttCoin == <<"m", A, 0>>
AttPub == Pub(AttX)
BadT == <<"bad">>
SigOK(id, lab, th) == id = A \/ <<id, lab, th>> \in signed

Other(n) == CHOOSE o \in H : o # n
SeedTid(i, r) == <<"tid0", i, r>>
SeedPsk(i, r) == Psk(<<"seed", i, r>>, SeedTid(i, r))
SrvSeed(i, r) == [occ |-> TRUE, tid |-> SeedTid(i, r), psk |-> SeedPsk(i, r), peer |-> i, exp |-> FALSE, stamp |-> 1]

Init ==
    /\ ist = [s \in ISess |-> INil]
    /\ rst = [s \in RSess |-> RNil]
    /\ sto = [r \in H |-> [pkc |-> {}, clk |-> IF Seed THEN 1 ELSE 0,
                           tks |-> [i \in Slots |-> IF Seed /\ i = 1 THEN SrvSeed(Other(r), r) ELSE NoSlot]]]
    /\ cli = [i \in H |-> IF Seed THEN {[tid |-> SeedTid(i, Other(i)), psk |-> SeedPsk(i, Other(i)),
                                         peer |-> Other(i)]} ELSE {}]
    /\ net = {}
    /\ signed = {}
    /\ issued = IF Seed THEN {[tid |-> SeedTid(i, Other(i)), psk |-> SeedPsk(i, Other(i)), peer |-> i] :
                              i \in H}
                ELSE {}

(* ---- what the attacker can inject ---- *)
IPubs == {AttPub} \cup {m.e : m \in {x \in net : x.ty \in {"Init", "Hello"}}}
TidPool == {NIL} \cup {m.tid : m \in {x \in net : x.ty = "Hello"}}
           \cup UNION {{m.tids[j] : j \in DOMAIN m.tids} : m \in {x \in net : x.ty = "RReply"}}
           \cup {t.tid : t \in {x \in issued : x.peer = A}}

(* tickets the attacker was issued, by tid: it knows their pre-shared keys *)
OwnPsk(tid) == {t.psk : t \in {x \in issued : x.tid = tid /\ Known(x.psk)}}

(* A message the attacker has no way to make valid is, to the receiver, one canonical failing message: the bad ones
   below stand for every such message (any other bad field only changes what an immediate fatal failure reports).
   The attacker's valid or accepted-without-proof messages are built from the public values it can reach. *)
ForgedToR(s) ==
    LET st == rst[s]
    IN {M([ty |-> "Init", prm |-> "bad", form |-> "full", e |-> AttPub, pk |-> EK(A)])}
       \cup {M([ty |-> "Init", form |-> f, e |-> e, pk |-> IF f = "full" THEN EK(A) ELSE Hash(EK(A))]) :
                  e \in IPubs, f \in {"full", "short"}}
       \cup {M([ty |-> "Init", form |-> f, e |-> AttPub, pk |-> IF f = "full" THEN EK(x) ELSE Hash(EK(x))]) :
                  x \in H, f \in {"full", "short"}}
       \cup UNION {{M([ty |-> "Hello", e |-> AttPub, tid |-> t, binder |-> b]) :
                        b \in {BadT} \cup {Binder(p, ThH("ok", t, AttPub)) : p \in OwnPsk(t)}} : t \in TidPool}
       \cup {M([ty |-> "Fin"])}
       \cup (IF st.ph = "finish" /\ Known(st.hsi)
             THEN {M([ty |-> "Fin", sealed |-> [k |-> st.hsi, ad |-> st.th3, id |-> x, sig |-> Sig(x, "initiator", Th4(st.th3, x))]]) :
                       x \in {y \in Ids : SigOK(y, "initiator", Th4(st.th3, y))}}
             ELSE {})

ReplyBlobs(st, n, e, ct) ==
    LET ssk == IF ct[3] = EK(n) THEN Kem(ct[2], ct[3]) ELSE <<"junk", n, ct>>
        th1 == Th1(st.th0, "ok", e, ct)
        hsr == Hs(Ck1(ssk, Dh(st.x, AtomOf(e))), "R", th1)
    IN {BadBlob} \cup (IF Known(hsr) /\ SigOK(st.peer, "responder", Th2(th1, st.peer))
                       THEN {[k |-> hsr, ad |-> th1, id |-> st.peer, sig |-> Sig(st.peer, "responder", Th2(th1, st.peer))]}
                       ELSE {})

ForgedToI(s) ==
    LET st == ist[s]
        n == s[1]
        ct == Ct(AttCoin, EK(n))
    IN {M([ty |-> "Reply", rprm |-> "bad", e |-> AttPub, ct |-> ct])}
       \cup (IF st.ph # "reply" THEN {}
             ELSE {M([ty |-> "Reply", e |-> AttPub, ct |-> ct, sealed |-> b]) : b \in ReplyBlobs(st, n, AttPub, ct)})
       \cup (IF st.ph # "resume" THEN {}
             ELSE LET thr == ThR(st.thh, st.binder, "ok", AttPub)
                      cfk == CfkK(Ck2(Ck1R(st.ckpsk, Dh(st.x, AtomOf(AttPub))), thr), thr)
                  IN {M([ty |-> "RReply", e |-> AttPub, tids |-> <<>>, conf |-> BadT])}
                     \cup (IF Known(cfk) THEN {M([ty |-> "RReply", e |-> AttPub, tids |-> <<>>, conf |-> Conf(cfk, ThT(thr, <<>>))])}
                           ELSE {}))
       \cup {M([ty |-> "PRej", echo |-> ist[o].th0]) : o \in {x \in ISess : ist[x].ph = "reply"}}
       \cup {M([ty |-> "RRej", echo |-> ist[o].thh]) : o \in {x \in ISess : ist[x].thh # NIL}}

IPool(s) == {m \in net : m.ty \in {"Reply", "PRej", "RReply", "RRej"}} \cup ForgedToI(s)
(* a responder session beyond the first only receives Hellos: it stands for the second node-level connection a
   replayed Hello can reach *)
RPool(s) == IF s[2] > 1 THEN {m \in net : m.ty = "Hello"} \cup {m \in ForgedToR(s) : m.ty = "Hello"}
            ELSE {m \in net : m.ty \in {"Init", "Hello", "Fin"}} \cup ForgedToR(s)

(* ---- initiator steps ---- *)
IFirst(s) == IF s[2] = 1 THEN TRUE ELSE ist[<<s[1], s[2] - 1>>].ph # "none"

IStartFull(s) ==
    /\ ist[s].ph = "none" /\ IFirst(s)
    /\ \E peer \in Ids \ {s[1]}, short \in IF Short THEN BOOLEAN ELSE {FALSE} :
        LET r == IBeginFull(s[1], <<"i", s[1], s[2]>>, peer, short, NIL, NIL)
        IN /\ ist' = [ist EXCEPT ![s] = r.st]
           /\ net' = net \cup r.out
    /\ UNCHANGED <<rst, sto, cli, signed, issued>>

IStartResume(s) ==
    /\ ist[s].ph = "none" /\ IFirst(s)
    /\ \E tk \in cli[s[1]] :
        LET r == IBeginResume(s[1], <<"i", s[1], s[2]>>, tk)
        IN /\ ist' = [ist EXCEPT ![s] = r.st]
           /\ cli' = [cli EXCEPT ![s[1]] = @ \ {tk}]
           /\ net' = net \cup r.out
    /\ UNCHANGED <<rst, sto, signed, issued>>

IRecv(s) ==
    /\ \E m \in IPool(s) :
        LET r == IHandle(ist[s], s[1], m)
        IN /\ ist' = [ist EXCEPT ![s] = r.st]
           /\ net' = net \cup r.out
    /\ UNCHANGED <<rst, sto, cli, signed, issued>>

IAnswer(s) ==
    /\ ist[s].ph \in {"decap", "sign"}
    /\ \E kind \in {"ok", "fail"} :
        LET r == IKey(ist[s], s[1], kind)
        IN /\ ist' = [ist EXCEPT ![s] = r.st]
           /\ net' = net \cup r.out
           /\ signed' = signed \cup r.sg
    /\ UNCHANGED <<rst, sto, cli, issued>>

IRetransmitFull(s) ==
    /\ ist[s].ph = "reply" /\ ist[s].short
    /\ net' = net \cup {M([ty |-> "Init", form |-> "full", e |-> Pub(ist[s].x), pk |-> EK(s[1])])}
    /\ UNCHANGED <<ist, rst, sto, cli, signed, issued>>

(* the tickets of a finished session reach the node's store over the protected channel *)
IAccept(s) ==
    LET st == ist[s]
    IN /\ Accept /\ st.ph = "done" /\ ~st.acc /\ st.peer \in H
       /\ \E tid \in IF st.resumed THEN {st.tids[j] : j \in DOMAIN st.tids}
                     ELSE {rst[r].mytid : r \in {x \in RSess : x[1] = st.peer /\ rst[x].ph = "done" /\ rst[x].thf = st.thf}} :
            cli' = [cli EXCEPT ![s[1]] = @ \cup {[tid |-> tid, psk |-> Psk(st.res, tid), peer |-> st.peer]}]
       /\ ist' = [ist EXCEPT ![s].acc = TRUE]
       /\ UNCHANGED <<rst, sto, net, signed, issued>>

(* ---- responder steps ---- *)
RFirst(s) == IF s[2] = 1 THEN TRUE ELSE rst[<<s[1], s[2] - 1>>].ph # "idle"

RRecv(s) ==
    /\ RFirst(s)
    /\ \E m \in RPool(s) :
        LET r == RHandle(rst[s], s, sto[s[1]], m)
        IN /\ rst' = [rst EXCEPT ![s] = r.st]
           /\ sto' = [sto EXCEPT ![s[1]] = r.sto]
           /\ net' = net \cup r.out
           /\ issued' = issued \cup r.iss
    /\ UNCHANGED <<ist, cli, signed>>

RAnswer(s) ==
    /\ rst[s].ph = "sign"
    /\ \E kind \in {"ok", "fail"} :
        LET r == RKey(rst[s], s, sto[s[1]], kind)
        IN /\ rst' = [rst EXCEPT ![s] = r.st]
           /\ net' = net \cup r.out
           /\ signed' = signed \cup r.sg
    /\ UNCHANGED <<ist, sto, cli, issued>>

Expire(n, i) ==
    /\ sto[n].tks[i].occ /\ ~sto[n].tks[i].exp
    /\ sto' = [sto EXCEPT ![n].tks[i].exp = TRUE]
    /\ UNCHANGED <<ist, rst, cli, net, signed, issued>>

Next ==
    \/ \E s \in ISess : IStartFull(s) \/ IStartResume(s) \/ IRecv(s) \/ IAnswer(s) \/ IRetransmitFull(s) \/ IAccept(s)
    \/ \E s \in RSess : RRecv(s) \/ RAnswer(s)
    \/ \E n \in H, i \in Slots : Expire(n, i)

Spec == Init /\ [][Next]_vars

(* ---- properties ---- *)
PrivateOK(t) == ~Known(t)

(* Agreement: two finished sessions with the same final transcript hold the same keys, name each other as peer and resumed alike *)
Agreement ==
    \A i \in ISess, r \in RSess :
        (ist[i].ph = "done" /\ rst[r].ph = "done" /\ ist[i].thf = rst[r].thf) =>
            /\ ist[i].send = rst[r].recv /\ ist[i].recv = rst[r].send /\ ist[i].res = rst[r].res
            /\ ist[i].peer = r[1] /\ rst[r].peer = i[1]
            /\ ist[i].resumed = rst[r].resumed

(* Authentication of the responder to the initiator: it completes with an honest peer X only if X ran a responder
   session that signed (full) or accepted the Hello of (resumed) the same transcript *)
AuthI ==
    \A i \in ISess :
        (ist[i].ph = "done" /\ ist[i].peer \in H) =>
            \E r \in RSess : r[1] = ist[i].peer /\ rst[r].sgn /\ rst[r].ath = ist[i].ath

(* Authentication of the initiator to the responder: it completes with an honest peer Y only if Y signed the
   transcript (full) or sent the Hello (resumed) *)
AuthR ==
    \A r \in RSess :
        (rst[r].ph = "done" /\ rst[r].peer \in H) =>
            \E i \in ISess :
                /\ i[1] = rst[r].peer
                /\ IF rst[r].resumed THEN ist[i].thh = rst[r].thh
                   ELSE ist[i].ph = "done" /\ ist[i].th4 = rst[r].th4

(* Secrecy: the keys of a finished session with an honest peer are not known to the attacker *)
Secrecy ==
    /\ \A i \in ISess : (ist[i].est /\ ist[i].peer \in H) =>
            PrivateOK(ist[i].send) /\ PrivateOK(ist[i].recv) /\ PrivateOK(ist[i].res)
    /\ \A r \in RSess : (rst[r].est /\ rst[r].peer \in H) =>
            PrivateOK(rst[r].send) /\ PrivateOK(rst[r].recv) /\ PrivateOK(rst[r].res)
    /\ \A i \in ISess : (ist[i].early # NIL /\ ist[i].peer \in H) => PrivateOK(ist[i].early)
    /\ \A r \in RSess : (rst[r].early # NIL /\ rst[r].peer \in H) => PrivateOK(rst[r].early)

(* No early acceptance: Established and the early keys only after the peer was authenticated, and the responder's
   early keys come from a ticket it issued *)
NoEarly ==
    /\ \A i \in ISess : ist[i].est => ist[i].auth
    /\ \A r \in RSess : rst[r].est => rst[r].auth
    /\ \A r \in RSess : rst[r].early # NIL =>
            /\ rst[r].auth
            /\ \E t \in issued : t.tid = rst[r].tid /\ Early(CkPsk(t.psk), rst[r].thh) = rst[r].early

(* 0-RTT at most once per ticket: no two responder sessions accepted a Hello with the same ticket id *)
ZeroRttOnce ==
    \A r1, r2 \in RSess : (r1 # r2 /\ rst[r1].early # NIL /\ rst[r2].early # NIL) => rst[r1].tid # rst[r2].tid

(* The prekey cache only holds hashes of prekeys whose initiator finished a handshake *)
CacheAuthenticated ==
    \A n \in H : \A h \in sto[n].pkc : \E r \in RSess : r[1] = n /\ rst[r].ph = "done" /\ rst[r].hpk = h

(* Rejects: a reject delivered to an initiator never authenticates or establishes it and never changes whom it
   dialed; it only moves a short Initial to the full form (same transcript) or a resumption to a fresh full
   handshake. A responder's reject leaves its state unchanged. *)
RejectsOnlyFallback ==
    /\ \A s \in ISess : \A m \in IPool(s) :
        m.ty \in {"PRej", "RRej"} =>
            LET r == IHandle(ist[s], s[1], m).st
            IN r = ist[s]
               \/ (/\ r.ph = "reply" /\ ~r.short /\ r.peer = ist[s].peer /\ ~r.est /\ ~r.auth /\ ~ist[s].est
                   /\ (ist[s].ph = "reply" => r.th0 = ist[s].th0)
                   /\ (ist[s].ph = "resume" => r.fell))
    /\ \A s \in RSess : \A m \in RPool(s) :
        LET r == RHandle(rst[s], s, sto[s[1]], m)
        IN (\E o \in r.out : o.ty = "PRej") => (r.st = rst[s] /\ r.sto = sto[s[1]])

TypeOK ==
    /\ \A s \in ISess : ist[s].ph \in {"none", "reply", "resume", "decap", "sign", "done", "failed"}
    /\ \A s \in RSess : rst[s].ph \in {"idle", "sign", "finish", "done", "failed"}
    /\ \A n \in H : Cardinality(Occ(sto[n].tks)) <= TK

(* a ticket that was removed by a Hello is not found again: its id occurs in a slot only if it was issued *)
TicketsIssued ==
    \A n \in H : \A i \in Slots : sto[n].tks[i].occ => \E t \in issued : t.tid = sto[n].tks[i].tid

=============================================================================
