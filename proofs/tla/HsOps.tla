------------------------------- MODULE HsOps -------------------------------
(***************************************************************************)
(* The pure core of the vinc-security handshake: the symbolic terms, the   *)
(* attacker's knowledge of them, and the step function of each state       *)
(* machine (Initiator in initiator.rs, Responder in responder.rs, the      *)
(* ticket store in tickets.rs). Shared by the model (Handshake.tla) and    *)
(* by the trace check (TraceHandshake.tla), so both use one definition of  *)
(* every step.                                                             *)
(*                                                                         *)
(* Symbolic crypto (perfect primitives, a stated assumption): a hash, a    *)
(* key derivation or a MAC is a tuple tagged with its purpose whose        *)
(* arguments are the inputs, so two values are equal iff their inputs are  *)
(* (collision resistance), and a key is known to the attacker only if it   *)
(* can be computed from the attacker's own secrets (Known). A Diffie-      *)
(* Hellman secret is known if either secret is the attacker's; a KEM       *)
(* secret if the encapsulation coin or the key owner is the attacker's;    *)
(* the chain key of the hybrid schedule needs both. A sealed blob is a     *)
(* record of the key it was sealed under, its associated data and its      *)
(* plaintext; opening checks the key and the data. A signature is a term   *)
(* only the signer (or anyone, for the attacker's own identity) can make.  *)
(* Secrets are atoms <<tag, node, k>>, and a node is the attacker's iff    *)
(* it is A.                                                                *)
(*                                                                         *)
(* A step returns [st, out, ev, err, sg] (the responder also stores and    *)
(* iss): the new local state, the messages sent, the events raised         *)
(* ("early", "est", "rejected", "failed"), "ok" / "drop" (the input is     *)
(* dropped and nothing changes) / "fatal" (the machine stopped), and the   *)
(* signatures made. Fields that are only compared for equality by the      *)
(* machines (version, ALPN, AEAD offer and choice, token, connection ids)  *)
(* are folded into the parameter values prm (the initiator's) and rprm     *)
(* (the responder's): "ok" passes the checks of the receiver, any other    *)
(* value fails them, and both are absorbed into the transcript.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS A,    \* the attacker's node id
          TK    \* the capacity of a responder's ticket store, at least 1

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

NIL == <<"nil">>

(* ---- terms ---- *)
Pub(x) == <<"pub", x>>
AtomOf(p) == p[2]
EK(n) == <<"ek", n>>                    \* the prekey (ML-KEM encapsulation key) of node n
Hash(ek) == <<"h", ek>>                 \* the hash of a prekey
Ct(coin, ek) == <<"ct", coin, ek>>      \* a KEM ciphertext made with coin to ek
Dh(x, y) == <<"dh", {x, y}>>
Kem(coin, ek) == <<"kem", coin, ek>>
Ck1(ssk, ssx) == <<"ck1", ssk, ssx>>    \* extract(ck0, ss_K || ss_X)
Ck1R(ckp, ssx) == <<"ck1r", ckp, ssx>>  \* extract(extract(ck0, psk), ss_X)
Hs(ck1, dir, th1) == <<"hs", ck1, dir, th1>>
Ck2(ck1, th) == <<"ck2", ck1, th>>
AppK(ck2, dir, th) == <<"app", ck2, dir, th>>
ResK(ck2, th) == <<"res", ck2, th>>
CfkK(ck2, th) == <<"cfk", ck2, th>>
Psk(res, tid) == <<"psk", res, tid>>
CkPsk(psk) == <<"ckpsk", psk>>
Early(ckp, thh) == <<"early", ckp, thh>>
Binder(psk, thh) == <<"binder", psk, thh>>
Conf(cfk, tht) == <<"conf", cfk, tht>>
Sig(id, lab, th) == <<"sig", id, lab, th>>
(* transcripts, in the order schedule.rs builds them *)
Th0(prm, e, hpk) == <<"th0", prm, e, hpk>>
Th1(th0, rprm, e, ct) == <<"th1", th0, rprm, e, ct>>
Th2(th1, id) == <<"th2", th1, id>>
Th3(th2, sig) == <<"th3", th2, sig>>
Th4(th3, id) == <<"th4", th3, id>>
Th5(th4, sig) == <<"th5", th4, sig>>
ThH(prm, tid, e) == <<"thH", prm, tid, e>>
ThR(thh, binder, rprm, e) == <<"thR", thh, binder, rprm, e>>
ThT(thr, tids) == <<"thT", thr, tids>>

(* the attacker can compute t from its own secrets *)
RECURSIVE Known(_)
Known(t) ==
    CASE t[1] = "dh" -> \E x \in t[2] : x[2] = A
      [] t[1] = "kem" -> t[2][2] = A \/ t[3][2] = A
      [] t[1] = "seed" -> t[2] = A \/ t[3] = A
      [] t[1] = "junk" -> FALSE
      [] t[1] \in {"ck1", "ck1r"} -> Known(t[2]) /\ Known(t[3])
      [] OTHER -> Known(t[2])

(* ---- messages: one record shape, unused fields are NIL ---- *)
BadBlob == [k |-> NIL, ad |-> NIL, id |-> NIL, sig |-> NIL]
MNil == [ty |-> "nil", form |-> "nil", prm |-> "ok", e |-> NIL, pk |-> NIL, rprm |-> "ok", ct |-> NIL,
         sealed |-> BadBlob, tid |-> NIL, binder |-> NIL, tids |-> <<>>, conf |-> NIL, echo |-> NIL]
M(r) == r @@ MNil

(* ---- the initiator ---- *)
INil == [ph |-> "none", peer |-> NIL, x |-> NIL, short |-> FALSE, th0 |-> NIL, mode |-> "nil",
         ckpsk |-> NIL, thh |-> NIL, binder |-> NIL, early |-> NIL, tid |-> NIL,
         reply |-> MNil, th1 |-> NIL, ssx |-> NIL,
         hsi |-> NIL, ck1 |-> NIL, th2 |-> NIL, th3 |-> NIL, th4 |-> NIL,
         send |-> NIL, recv |-> NIL, res |-> NIL, ath |-> NIL, thf |-> NIL, tids |-> <<>>,
         auth |-> FALSE, est |-> FALSE, resumed |-> FALSE, fell |-> FALSE, acc |-> FALSE]

Res(st, out, ev, err) == [st |-> st, out |-> out, ev |-> ev, err |-> err, sg |-> {}]
Drop(st) == Res(st, {}, {}, "drop")
Fatal(st) == Res([st EXCEPT !.ph = "failed"], {}, {"failed"}, "fatal")
Ok(st, out, ev) == Res(st, out, ev, "ok")

(* Initiator::begin_full: a fresh ephemeral x, the short or the full Initial *)
IBeginFull(n, x, peer, short, thh, early) ==
    LET e == Pub(x)
        hpk == Hash(EK(n))
    IN Ok([INil EXCEPT !.ph = "reply", !.peer = peer, !.x = x, !.short = short, !.th0 = Th0("ok", e, hpk),
                       !.mode = IF short THEN "short" ELSE "full", !.thh = thh, !.early = early],
          {IF short THEN M([ty |-> "Init", form |-> "short", e |-> e, pk |-> hpk])
                    ELSE M([ty |-> "Init", form |-> "full", e |-> e, pk |-> EK(n)])},
          {})

(* Initiator::begin_resume with a ticket tk = [tid, psk, peer] *)
IBeginResume(n, x, tk) ==
    LET e == Pub(x)
        thh == ThH("ok", tk.tid, e)
        b == Binder(tk.psk, thh)
        ckp == CkPsk(tk.psk)
    IN Ok([INil EXCEPT !.ph = "resume", !.peer = tk.peer, !.x = x, !.mode = "resume", !.ckpsk = ckp,
                       !.thh = thh, !.binder = b, !.early = Early(ckp, thh), !.tid = tk.tid],
          {M([ty |-> "Hello", e |-> e, tid |-> tk.tid, binder |-> b])},
          {"early"})

(* Initiator::handle for a message m received by node n *)
IHandle(st, n, m) ==
    IF st.ph = "failed" THEN Drop(st)
    ELSE CASE m.ty = "Reply" ->
            IF st.ph # "reply" THEN Drop(st)
            ELSE IF m.rprm # "ok" THEN Fatal(st)
            ELSE Ok([st EXCEPT !.ph = "decap", !.reply = m, !.th1 = Th1(st.th0, m.rprm, m.e, m.ct),
                               !.ssx = Dh(st.x, AtomOf(m.e))], {}, {})
      [] m.ty = "PRej" ->
            IF ~(st.ph = "reply" /\ st.short) \/ m.echo # st.th0 THEN Drop(st)
            ELSE Ok([st EXCEPT !.short = FALSE], {M([ty |-> "Init", form |-> "full", e |-> Pub(st.x), pk |-> EK(n)])}, {})
      [] m.ty = "RReply" ->
            IF st.ph # "resume" THEN Drop(st)
            ELSE LET thr == ThR(st.thh, st.binder, m.rprm, m.e)
                     ck2 == Ck2(Ck1R(st.ckpsk, Dh(st.x, AtomOf(m.e))), thr)
                 IN IF m.conf # Conf(CfkK(ck2, thr), ThT(thr, m.tids)) THEN Fatal(st)
                    ELSE Ok([st EXCEPT !.ph = "done", !.send = AppK(ck2, "I", thr), !.recv = AppK(ck2, "R", thr),
                                       !.res = ResK(ck2, thr), !.ath = thr, !.thf = thr, !.tids = m.tids,
                                       !.auth = TRUE, !.est = TRUE, !.resumed = TRUE], {}, {"est"})
      [] m.ty = "RRej" ->
            IF st.ph # "resume" \/ m.echo # st.thh THEN Drop(st)
            ELSE LET b == IBeginFull(n, <<"f", st.x[2], st.x[3]>>, st.peer, FALSE, st.thh, NIL)
                 IN Ok([b.st EXCEPT !.mode = "fallback", !.fell = TRUE], b.out, {"rejected"})
      [] OTHER -> Drop(st)

(* Initiator::on_key_response with the answer to the outstanding request: "ok" is the host's success *)
IKey(st, n, kind) ==
    IF st.ph = "decap" /\ kind = "ok" THEN
        LET ct == st.reply.ct
            ssk == IF ct[3] = EK(n) THEN Kem(ct[2], ct[3]) ELSE <<"junk", n, ct>>
            ck1 == Ck1(ssk, st.ssx)
            b == st.reply.sealed
            th2 == Th2(st.th1, b.id)
        IN IF b.k # Hs(ck1, "R", st.th1) \/ b.ad # st.th1 THEN Fatal(st)
           ELSE IF b.id # st.peer THEN Fatal(st)
           ELSE IF b.sig # Sig(b.id, "responder", th2) THEN Fatal(st)
           ELSE Ok([st EXCEPT !.ph = "sign", !.hsi = Hs(ck1, "I", st.th1), !.ck1 = ck1, !.th2 = th2,
                              !.th3 = Th3(th2, b.sig), !.th4 = Th4(Th3(th2, b.sig), n), !.ath = th2,
                              !.auth = TRUE], {}, {})
    ELSE IF st.ph = "sign" /\ kind = "ok" THEN
        LET sig == Sig(n, "initiator", st.th4)
            th5 == Th5(st.th4, sig)
            ck2 == Ck2(st.ck1, th5)
        IN [Ok([st EXCEPT !.ph = "done", !.send = AppK(ck2, "I", th5), !.recv = AppK(ck2, "R", th5),
                          !.res = ResK(ck2, th5), !.thf = th5, !.est = TRUE],
               {M([ty |-> "Fin", sealed |-> [k |-> st.hsi, ad |-> st.th3, id |-> n, sig |-> sig]])},
               {"est"}) EXCEPT !.sg = {<<n, "initiator", st.th4>>}]
    ELSE IF st.ph \in {"decap", "sign"} /\ kind = "fail" THEN Fatal(st)
    ELSE Drop(st)

(* ---- the responder and its stores ---- *)
RNil == [ph |-> "idle", th0 |-> NIL, hpk |-> NIL, ek |-> NIL, fresh |-> FALSE, ct |-> NIL,
         th1 |-> NIL, th2 |-> NIL, th3 |-> NIL, hsr |-> NIL, hsi |-> NIL, ck1 |-> NIL, reply |-> MNil,
         send |-> NIL, recv |-> NIL, res |-> NIL, ath |-> NIL, thf |-> NIL, th4 |-> NIL, peer |-> NIL,
         tid |-> NIL, thh |-> NIL, early |-> NIL, mytid |-> NIL,
         sgn |-> FALSE, auth |-> FALSE, est |-> FALSE, resumed |-> FALSE]

(* The shared state of one responder node: the prekey cache (hashes), the ticket slots and the stamp clock. *)
NoSlot == [occ |-> FALSE, tid |-> NIL, psk |-> NIL, peer |-> NIL, exp |-> FALSE, stamp |-> 0]
Slots == 1..TK
Occ(tks) == {i \in Slots : tks[i].occ}

(* ServerTickets victim: the first empty slot, else the first expired one, else the oldest *)
Victim(tks) ==
    IF \E i \in Slots : ~tks[i].occ THEN Min({i \in Slots : ~tks[i].occ})
    ELSE IF \E i \in Slots : tks[i].exp THEN Min({i \in Slots : tks[i].exp})
    ELSE CHOOSE i \in Slots : \A j \in Slots : tks[i].stamp <= tks[j].stamp

(* issue_batch for one ticket *)
IssueTicket(sto, tid, psk, peer) ==
    LET i == Victim(sto.tks)
        tk == [occ |-> TRUE, tid |-> tid, psk |-> psk, peer |-> peer, exp |-> FALSE, stamp |-> sto.clk + 1]
    IN [sto EXCEPT !.tks[i] = tk, !.clk = sto.clk + 1]

RemoveSlot(sto, i) == [sto EXCEPT !.tks[i] = NoSlot]

RRes(st, out, ev, err, sto, iss, sg) ==
    [st |-> st, out |-> out, ev |-> ev, err |-> err, sto |-> sto, iss |-> iss, sg |-> sg]
RDrop(st, sto) == RRes(st, {}, {}, "drop", sto, {}, {})
RFatal(st, sto) == RRes([st EXCEPT !.ph = "failed"], {}, {"failed"}, "fatal", sto, {}, {})
ROk(st, out, ev, sto) == RRes(st, out, ev, "ok", sto, {}, {})

(* Responder::on_initial for session s, given the cache of its node *)
RInitial(st, s, sto, m) ==
    LET n == s[1]
        hpk == IF m.form = "full" THEN Hash(m.pk) ELSE m.pk
        th0 == Th0(m.prm, m.e, hpk)
        y == <<"r", s[1], s[2]>>
        ek == IF m.form = "full" THEN m.pk ELSE hpk[2]
        coin == <<"m", s[1], s[2]>>
        eR == Pub(y)
        ct == Ct(coin, ek)
        th1 == Th1(th0, "ok", eR, ct)
        ck1 == Ck1(Kem(coin, ek), Dh(y, AtomOf(m.e)))
    IN IF st.ph = "failed" THEN RDrop(st, sto)
       ELSE IF st.ph = "finish" THEN
            (IF st.th0 = th0 THEN ROk(st, {st.reply}, {}, sto) ELSE RDrop(st, sto))
       ELSE IF st.ph # "idle" THEN RDrop(st, sto)
       ELSE IF m.prm # "ok" THEN RFatal(st, sto)
       ELSE IF m.form = "short" /\ hpk \notin sto.pkc
            THEN ROk(st, {M([ty |-> "PRej", echo |-> th0])}, {}, sto)
       ELSE ROk([st EXCEPT !.ph = "sign", !.th0 = th0, !.hpk = hpk, !.ek = ek, !.fresh = (m.form = "full"),
                           !.ct = ct, !.th1 = th1, !.th2 = Th2(th1, n), !.ath = Th2(th1, n),
                           !.hsr = Hs(ck1, "R", th1), !.hsi = Hs(ck1, "I", th1), !.ck1 = ck1], {}, {}, sto)

(* Responder::on_key_response: the host's signature of the Reply *)
RKey(st, s, sto, kind) ==
    LET n == s[1]
        y == <<"r", s[1], s[2]>>
        sig == Sig(n, "responder", st.th2)
        reply == M([ty |-> "Reply", e |-> Pub(y), ct |-> st.ct,
                    sealed |-> [k |-> st.hsr, ad |-> st.th1, id |-> n, sig |-> sig]])
    IN IF st.ph = "sign" /\ kind = "ok"
       THEN RRes([st EXCEPT !.ph = "finish", !.th3 = Th3(st.th2, sig), !.reply = reply, !.sgn = TRUE], {reply}, {}, "ok", sto,
                 {}, {<<n, "responder", st.th2>>})
       ELSE IF st.ph = "sign" /\ kind = "fail" THEN RFatal(st, sto)
       ELSE RDrop(st, sto)

(* Responder::on_finish *)
RFinish(st, s, sto, m) ==
    LET n == s[1]
        b == m.sealed
        th4 == Th4(st.th3, b.id)
        th5 == Th5(th4, b.sig)
        ck2 == Ck2(st.ck1, th5)
        res == ResK(ck2, th5)
        tid == <<"tid", s[1], s[2]>>
        sto1 == IssueTicket(sto, tid, Psk(res, tid), b.id)
        sto2 == IF st.fresh THEN [sto1 EXCEPT !.pkc = @ \cup {st.hpk}] ELSE sto1
    IN IF st.ph = "failed" THEN RDrop(st, sto)
       ELSE IF st.ph # "finish" THEN RDrop(st, sto)
       ELSE IF b.k # st.hsi \/ b.ad # st.th3 THEN RFatal(st, sto)
       ELSE IF b.sig # Sig(b.id, "initiator", th4) THEN RFatal(st, sto)
       ELSE RRes([st EXCEPT !.ph = "done", !.peer = b.id, !.th4 = th4, !.send = AppK(ck2, "R", th5),
                            !.recv = AppK(ck2, "I", th5), !.res = res, !.thf = th5, !.mytid = tid,
                            !.auth = TRUE, !.est = TRUE],
                 {}, {"est"}, "ok", sto2,
                 {[tid |-> tid, psk |-> Psk(res, tid), peer |-> b.id]}, {})

(* Responder::on_hello *)
RHello(st, s, sto, m) ==
    LET n == s[1]
        y == <<"r", s[1], s[2]>>
        thh == ThH(m.prm, m.tid, m.e)
        found == {i \in Slots : sto.tks[i].occ /\ sto.tks[i].tid = m.tid}
        i0 == Min(found)
        t == sto.tks[i0]
        usable == found # {} /\ ~t.exp /\ Binder(t.psk, thh) = m.binder
        ckp == CkPsk(t.psk)
        eR == Pub(y)
        thr == ThR(thh, m.binder, "ok", eR)
        ck2 == Ck2(Ck1R(ckp, Dh(y, AtomOf(m.e))), thr)
        tid == <<"tid", s[1], s[2]>>
        sto1 == IssueTicket(RemoveSlot(sto, i0), tid, Psk(ResK(ck2, thr), tid), t.peer)
        stoRej == IF found # {} /\ t.exp THEN RemoveSlot(sto, i0) ELSE sto
    IN IF st.ph = "failed" THEN RDrop(st, sto)
       ELSE IF st.ph # "idle" THEN RDrop(st, sto)
       ELSE IF m.prm # "ok" THEN RFatal(st, sto)
       ELSE IF ~usable THEN ROk(st, {M([ty |-> "RRej", echo |-> thh])}, {}, stoRej)
       ELSE RRes([st EXCEPT !.ph = "done", !.peer = t.peer, !.tid = m.tid, !.thh = thh,
                            !.early = Early(ckp, thh), !.send = AppK(ck2, "R", thr), !.recv = AppK(ck2, "I", thr),
                            !.res = ResK(ck2, thr), !.ath = thr, !.thf = thr, !.mytid = tid, !.sgn = TRUE,
                            !.auth = TRUE, !.est = TRUE, !.resumed = TRUE],
                 {M([ty |-> "RReply", e |-> eR, tids |-> <<tid>>,
                     conf |-> Conf(CfkK(ck2, thr), ThT(thr, <<tid>>))])},
                 {"early", "est"}, "ok", sto1,
                 {[tid |-> tid, psk |-> Psk(ResK(ck2, thr), tid), peer |-> t.peer]}, {})

(* Responder::handle *)
RHandle(st, s, sto, m) ==
    IF st.ph = "failed" THEN RDrop(st, sto)
    ELSE CASE m.ty \in {"Init"} -> RInitial(st, s, sto, m)
           [] m.ty = "Fin" -> RFinish(st, s, sto, m)
           [] m.ty = "Hello" -> RHello(st, s, sto, m)
           [] OTHER -> RDrop(st, sto)

=============================================================================
