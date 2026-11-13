------------------------------- MODULE HsOps -------------------------------
(***************************************************************************)
(* The pure core of the vinc-security handshake: the symbolic terms, the   *)
(* attacker's knowledge of them, and the step function of each state       *)
(* machine (Initiator in initiator.rs, Responder in responder.rs, the      *)
(* ticket stores in tickets.rs). Shared by the model (Handshake.tla) and   *)
(* by the trace check (TraceHandshake.tla), so both use one definition of  *)
(* every step.                                                             *)
(*                                                                         *)
(* Symbolic crypto (perfect primitives, a stated assumption of the         *)
(* dependencies): a hash, a key derivation or a MAC is a tuple tagged with *)
(* its purpose whose arguments are the inputs, so two values are equal iff *)
(* their inputs are (collision resistance), and a key is known to the      *)
(* attacker only if it can be computed from the attacker's own secrets     *)
(* (Known). A Diffie-Hellman secret is known if either secret is the      *)
(* attacker's; a KEM secret if the encapsulation coin or the key owner is  *)
(* the attacker's; the chain key of the hybrid schedule needs both. Either *)
(* half of the hybrid can be broken by a constant, as DtnSeal.tla does it: *)
(* with BX the attacker learns the Diffie-Hellman secret of every exchange *)
(* (it sees every public value on the network), with BK the KEM secret of  *)
(* every ciphertext and the implicit-rejection value of every malformed    *)
(* one; signatures, hashes and the AEAD stay ideal. A resumption secret    *)
(* seeded from an earlier, unmodelled full handshake is known if a party   *)
(* is the attacker, if both halves are broken (the earlier session was a   *)
(* full handshake: Handshake_xbroken and Handshake_kbroken show that one   *)
(* broken half leaves its resumption secret secret), or if the ticket      *)
(* store leaked (SeedLeak). A sealed blob is a record of the key it was    *)
(* sealed under, its associated data and its plaintext; opening checks the *)
(* key and the data. A signature is a term only the signer (or anyone, for *)
(* the attacker's own identity) can make. Secrets are atoms <<tag, node,   *)
(* k>>, and a node is the attacker's iff it is A.                          *)
(*                                                                         *)
(* Every field of every message is its own field of the message and its    *)
(* own argument of the transcript terms: version (ver), ALPN (al),         *)
(* connection ids (dc, sc), credit record (cr), AEAD offer (of) and choice *)
(* (ad), and the byte length of the message (len), exactly as the code     *)
(* absorbs them. The checks the code makes on them are the checks below:   *)
(* the responder refuses a version other than "ok", an ALPN it does not    *)
(* serve (Served) and an offer without a common AEAD (Choose), the         *)
(* initiator refuses an AEAD outside its offer (InOffer). Anything else is *)
(* absorbed and so authenticated through the transcript.                   *)
(*                                                                         *)
(* A step returns [st, out, ev, err] (the responder also sto and iss, the  *)
(* initiator also sg): the new local state, the messages sent, the events  *)
(* raised ("early", "est", "rejected", "failed"), "ok" / "drop" (the input *)
(* is dropped: a non-fatal error; the state changes only where the code    *)
(* changes it) / "fatal" (the machine stopped), and the signatures made.   *)
(*                                                                         *)
(* Three abstractions keep the state space finite and change no behaviour: *)
(* the retransmission count of an initiator is kept modulo 3 (the code     *)
(* reads it only as "is a multiple of 3" and, in the resume state,         *)
(* "reached 3"), the bytes a resumed responder has answered are saturated  *)
(* one above the larger budget (the code only compares them with the       *)
(* budgets), and store stamps are renumbered densely after every           *)
(* operation (only their order is read).                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS A,    \* the attacker's node id
          NT,   \* tickets a session issues (tickets_per_session), 1..4
          ATT,  \* the draws one ticket id may take (ID_ATTEMPTS)
          LF, LS, LH, LR,   \* byte lengths: full Initial, short Initial, resume Hello, resume Reply
          RB, LB,           \* RESEND_BUDGET and LATE_INITIAL_BUDGET
          BX, BK,           \* X25519 / ML-KEM-768 broken (the attacker learns every DH / KEM shared secret)
          SeedLeak          \* the attacker holds the resumption secrets of the seeded earlier sessions

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max2(a, b) == IF a > b THEN a ELSE b
SpentCap == Max2(RB, LB) + 1
Sat(x) == IF x > SpentCap THEN SpentCap ELSE x

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
CidK(ck2, th) == <<"cids", ck2, th>>    \* the connection id secret (CID_SECRET)
Psk(res, tid, cr) == <<"psk", res, tid, cr>>   \* expand(resume, "ticket", H(tid, credit.encode()))
CkPsk(psk) == <<"ckpsk", psk>>
Early(ckp, thh) == <<"early", ckp, thh>>
Binder(psk, thh) == <<"binder", psk, thh>>
Conf(cfk, tht) == <<"conf", cfk, tht>>
Sig(id, lab, th) == <<"sig", id, lab, th>>

(* the field values: honest nodes use the first of each kind, the attacker the others *)
Cid(role, n, k) == <<"cid", role, n, k>>   \* a connection id (random in the code, one per session and role)
Off(n) == <<"off", n>>                     \* the AEAD offer of node n
BadOff == <<"offbad", 0>>                  \* an offer that shares no AEAD with the responder
Alp(i) == <<"alpn", i>>                    \* an ALPN the responders serve (i = 1, 2)
BadAlp == <<"alpnbad", 0>>                  \* an ALPN no responder serves
Cr(n) == <<"cr", n>>                       \* the credit record of node n
Ac(of, r) == <<"aead", of, r>>             \* the AEAD node r chose from the offer of
Served(al) == al \in {Alp(1), Alp(2)}
Choose(of, r) == IF of = BadOff THEN NIL ELSE Ac(of, r)
InOffer(of, ad) == ad[1] = "aead" /\ ad[2] = of
TidT(c) == <<"tid", c>>                    \* a ticket id drawn from the generator

(* transcripts, in the order schedule.rs builds them *)
Th0(v, al, dc, sc, cr, of, e, hpk) == <<"th0", v, al, dc, sc, cr, of, e, hpk>>
Th1(th0, rsc, ad, e, ct) == <<"th1", th0, rsc, ad, e, ct>>
Th2(th1, id, rcr) == <<"th2", th1, id, rcr>>
Th3(th2, sig) == <<"th3", th2, sig>>
Th4(th3, id) == <<"th4", th3, id>>
Th5(th4, sig) == <<"th5", th4, sig>>
ThH(v, al, dc, sc, ad, tid, e, cr) == <<"thH", v, al, dc, sc, ad, tid, e, cr>>
ThR(thh, binder, rsc, e, rcr) == <<"thR", thh, binder, rsc, e, rcr>>
ThT(thr, tids) == <<"thT", thr, tids>>

(* the attacker can compute t from its own secrets (and from the public values, with a broken half) *)
RECURSIVE Known(_)
Known(t) ==
    CASE t[1] = "dh" -> BX \/ \E x \in t[2] : x[2] = A
      [] t[1] = "kem" -> BK \/ t[2][2] = A \/ t[3][2] = A
      [] t[1] = "seed" -> (BX /\ BK) \/ SeedLeak \/ t[2] = A \/ t[3] = A
      [] t[1] = "junk" -> BK
      [] t[1] \in {"ck1", "ck1r"} -> Known(t[2]) /\ Known(t[3])
      [] OTHER -> Known(t[2])

(* ---- messages: one record shape, unused fields are NIL ---- *)
BadBlob == [k |-> NIL, ad |-> NIL, id |-> NIL, sig |-> NIL, cr |-> NIL]
MNil == [ty |-> "nil", form |-> "nil", ver |-> "ok", al |-> Alp(1), dc |-> NIL, sc |-> NIL, of |-> NIL, ad |-> NIL,
         cr |-> NIL, len |-> 0, e |-> NIL, pk |-> NIL, ct |-> NIL, sealed |-> BadBlob, tid |-> NIL,
         binder |-> NIL, tids |-> <<>>, conf |-> NIL, echo |-> NIL]
M(r) == r @@ MNil

(* ---- the stores (tickets.rs): a store is a sequence of slots ---- *)
NoSlot == [occ |-> FALSE, tid |-> NIL, psk |-> NIL, peer |-> NIL, al |-> NIL, ad |-> NIL, cr |-> NIL, exp |-> FALSE,
           stamp |-> 0]

NoSlots(k) == [i \in 1..k |-> NoSlot]

EmptyIdx(sl) == LET S == {i \in 1..Len(sl) : ~sl[i].occ} IN IF S = {} THEN 0 ELSE Min(S)
ExpiredIdx(sl) == LET S == {i \in 1..Len(sl) : sl[i].occ /\ sl[i].exp} IN IF S = {} THEN 0 ELSE Min(S)
OldestIdx(sl) ==
    LET S == {i \in 1..Len(sl) : sl[i].occ}
        lo == Min({sl[i].stamp : i \in S})
    IN Min({i \in S : sl[i].stamp = lo})

(* tickets.rs victim: the first empty slot, else the first expired one, else the oldest; 0 for a store without slots *)
Victim(sl) ==
    IF sl = <<>> THEN 0
    ELSE IF EmptyIdx(sl) # 0 THEN EmptyIdx(sl)
    ELSE IF ExpiredIdx(sl) # 0 THEN ExpiredIdx(sl)
    ELSE OldestIdx(sl)

(* renumber the stamps densely, keeping their order *)
Rank(sl, i) == Cardinality({j \in 1..Len(sl) : sl[j].occ /\ sl[j].stamp <= sl[i].stamp})
Norm(sl) == [i \in 1..Len(sl) |-> IF sl[i].occ THEN [sl[i] EXCEPT !.stamp = Rank(sl, i)] ELSE sl[i]]
Clk(sl) == Cardinality({i \in 1..Len(sl) : sl[i].occ})

Put(sl, i, x) == IF i = 0 THEN sl ELSE [sl EXCEPT ![i] = x]
Occ(tks) == {i \in 1..Len(tks) : tks[i].occ}
FindTid(sl, tid) == LET S == {i \in 1..Len(sl) : sl[i].occ /\ sl[i].tid = tid} IN IF S = {} THEN 0 ELSE Min(S)

(* ---- ServerTickets ---- *)
StoredIds(sl) == {sl[i].tid : i \in Occ(sl)}
(* fresh_id: the first of the ATT draws c[1..ATT] that no stored ticket has, or NIL (Failure::TicketId) *)
RECURSIVE FreshFrom(_, _, _)
FreshFrom(sl, c, j) == IF j > ATT THEN NIL ELSE IF TidT(c[j]) \notin StoredIds(sl) THEN TidT(c[j]) ELSE FreshFrom(sl, c, j + 1)

(* one ticket of issue_batch: [ok, sl, tid] *)
IssueOne(sl, c, res, cr, peer, al, ad) ==
    LET tid == FreshFrom(sl, c, 1)
        slot == [occ |-> TRUE, tid |-> tid, psk |-> Psk(res, tid, cr), peer |-> peer, al |-> al, ad |-> ad, cr |-> cr,
                 exp |-> FALSE, stamp |-> Clk(sl) + 1]
        at == Victim(sl)
    IN IF tid = NIL THEN [ok |-> FALSE, sl |-> sl, tid |-> NIL]
       ELSE [ok |-> TRUE, sl |-> Norm(Put(sl, at, slot)), tid |-> IF at = 0 THEN NIL ELSE tid]

(* issue_batch for the Len(cs) tickets asked for; cs[j] is the draw sequence of ticket j; the tickets that did get stored
   are in tids *)
RECURSIVE IssueAll(_, _, _, _, _, _, _, _, _)
IssueAll(sl, cs, j, res, cr, peer, al, ad, tids) ==
    IF j > Len(cs) THEN [ok |-> TRUE, sl |-> sl, tids |-> tids]
    ELSE LET r == IssueOne(sl, cs[j], res, cr, peer, al, ad)
         IN IF ~r.ok THEN [ok |-> FALSE, sl |-> r.sl, tids |-> tids]
            ELSE IssueAll(r.sl, cs, j + 1, res, cr, peer, al, ad, IF r.tid = NIL THEN tids ELSE Append(tids, r.tid))
Issue(sl, cs, res, cr, peer, al, ad) == IssueAll(sl, cs, 1, res, cr, peer, al, ad, <<>>)

(* the tickets an issue produced, for the ledger *)
IssuedOf(tids, res, cr, peer, al, ad) ==
    {[tid |-> tids[j], psk |-> Psk(res, tids[j], cr), peer |-> peer, al |-> al, ad |-> ad, cr |-> cr] : j \in DOMAIN tids}

(* ---- ClientTickets ---- *)
CFindPeer(sl, peer) == LET S == {i \in 1..Len(sl) : sl[i].occ /\ sl[i].peer = peer} IN IF S = {} THEN 0 ELSE Min(S)

(* insert: the peer's slot is replaced; else the victim *)
CInsert(sl, tk) ==
    LET same == CFindPeer(sl, tk.peer)
        slot == [occ |-> TRUE, tid |-> tk.tid, psk |-> tk.psk, peer |-> tk.peer, al |-> tk.al, ad |-> tk.ad, cr |-> tk.cr,
                 exp |-> FALSE, stamp |-> Clk(sl) + 1]
        at == IF same # 0 THEN same ELSE Victim(sl)
    IN Norm(Put(sl, at, slot))

(* accept_batch: each ticket of the batch in order, so the last of a peer is the one kept *)
RECURSIVE CInsertAll(_, _)
CInsertAll(sl, tks) == IF tks = <<>> THEN sl ELSE CInsertAll(CInsert(sl, Head(tks)), Tail(tks))

RECURSIVE KeepSeq(_, _, _)
KeepSeq(sq, drop, j) == IF j > Len(sq) THEN <<>> ELSE (IF j \in drop THEN <<>> ELSE <<sq[j]>>) \o KeepSeq(sq, drop, j + 1)

NoTk == [none |-> TRUE]

(* take: expired tickets are dropped, then the peer's ticket for the ALPN is removed and returned (or NIL) *)
CDropExpired(sl) == [i \in 1..Len(sl) |-> IF sl[i].occ /\ sl[i].exp THEN NoSlot ELSE sl[i]]
CFind(sl, peer, al) == LET S == {i \in 1..Len(sl) : sl[i].occ /\ sl[i].peer = peer /\ sl[i].al = al} IN IF S = {} THEN 0 ELSE Min(S)
TicketOf(slot) == [tid |-> slot.tid, psk |-> slot.psk, peer |-> slot.peer, al |-> slot.al, ad |-> slot.ad, cr |-> slot.cr]
CTake(sl, peer, al) ==
    LET d == CDropExpired(sl)
        at == CFind(d, peer, al)
    IN IF at = 0 THEN [sl |-> Norm(d), tk |-> NoTk]
       ELSE [sl |-> Norm(Put(d, at, NoSlot)), tk |-> TicketOf(d[at])]

(* export: the newest at most mx unexpired tickets, oldest first *)
Live(sl) == {i \in 1..Len(sl) : sl[i].occ /\ ~sl[i].exp}
RECURSIVE SortByStamp(_, _)
SortByStamp(sl, S) ==
    IF S = {} THEN <<>>
    ELSE LET i == CHOOSE i \in S : \A j \in S : sl[i].stamp <= sl[j].stamp
         IN <<TicketOf(sl[i])>> \o SortByStamp(sl, S \ {i})
CExport(sl, mx) ==
    LET all == SortByStamp(sl, Live(sl))
        keep == IF Len(all) > mx THEN mx ELSE Len(all)
    IN SubSeq(all, Len(all) - keep + 1, Len(all))

(* ---- the initiator ---- *)
NoLate == [on |-> FALSE, x |-> NIL, thh |-> NIL, binder |-> NIL, ckpsk |-> NIL, rcr |-> NIL, ad |-> NIL]
INil == [ph |-> "none", peer |-> NIL, x |-> NIL, short |-> FALSE, th0 |-> NIL, mode |-> "nil",
         al |-> NIL, dc |-> NIL, sc |-> NIL, of |-> NIL, cr |-> NIL, sends |-> 0,
         ckpsk |-> NIL, thh |-> NIL, binder |-> NIL, early |-> NIL, tid |-> NIL, late |-> NoLate,
         reply |-> MNil, th1 |-> NIL, ssx |-> NIL,
         hsi |-> NIL, ck1 |-> NIL, th2 |-> NIL, th3 |-> NIL, th4 |-> NIL, fin |-> MNil,
         send |-> NIL, recv |-> NIL, res |-> NIL, cid |-> NIL, ath |-> NIL, thf |-> NIL, tids |-> <<>>,
         ad |-> NIL, pcr |-> NIL, rcr |-> NIL,
         auth |-> FALSE, est |-> FALSE, resumed |-> FALSE, fell |-> FALSE, acc |-> FALSE]

Res(st, out, ev, err) == [st |-> st, out |-> out, ev |-> ev, err |-> err, sg |-> {}]
Drop(st) == Res(st, {}, {}, "drop")
Fatal(st) == Res([st EXCEPT !.ph = "failed"], {}, {"failed"}, "fatal")
Ok(st, out, ev) == Res(st, out, ev, "ok")

(* the Initial of an initiator in the short or the full form (write_initial) *)
IInitMsg(n, st, short) ==
    M([ty |-> "Init", form |-> IF short THEN "short" ELSE "full", ver |-> "ok", al |-> st.al, dc |-> st.dc, sc |-> st.sc,
       of |-> st.of, cr |-> st.cr, len |-> IF short THEN LS ELSE LF, e |-> Pub(st.x),
       pk |-> IF short THEN Hash(EK(n)) ELSE EK(n)])

(* Initiator::begin_full: a fresh ephemeral x (and destination id dcid), the short or the full Initial; st0 holds the
   parameters of the dial (peer, ALPN, source id, offer, credit) *)
IBeginFull(n, st0, x, dcid, short, thh) ==
    LET st == [st0 EXCEPT !.ph = "reply", !.x = x, !.dc = dcid, !.short = short,
                          !.th0 = Th0("ok", st0.al, dcid, st0.sc, st0.cr, st0.of, Pub(x), Hash(EK(n))),
                          !.mode = IF short THEN "short" ELSE "full", !.thh = thh, !.early = NIL, !.sends = 1]
    IN Ok(st, {IInitMsg(n, st, short)}, {})

(* Initiator::begin_resume with a ticket tk = [tid, psk, peer, al, ad, cr] *)
IBeginResume(n, st0, x, dcid, tk) ==
    LET e == Pub(x)
        thh == ThH("ok", st0.al, dcid, st0.sc, tk.ad, tk.tid, e, st0.cr)
        b == Binder(tk.psk, thh)
        ckp == CkPsk(tk.psk)
    IN Ok([st0 EXCEPT !.ph = "resume", !.x = x, !.dc = dcid, !.mode = "resume", !.ckpsk = ckp, !.thh = thh,
                      !.binder = b, !.early = Early(ckp, thh), !.tid = tk.tid, !.ad = tk.ad, !.rcr = tk.cr, !.sends = 1],
          {M([ty |-> "Hello", ver |-> "ok", al |-> st0.al, dc |-> dcid, sc |-> st0.sc, ad |-> tk.ad, tid |-> tk.tid,
              e |-> e, binder |-> b, cr |-> st0.cr, len |-> LH])},
          {"early"})

(* Initiator::new: the dial parameters, and a ticket (NoTk for none) *)
INew(n, k, peer, al, short, tk) ==
    LET st0 == [INil EXCEPT !.peer = peer, !.al = al, !.sc = Cid("i", n, k), !.of = Off(n), !.cr = Cr(n)]
        x == <<"i", n, k>>
        dcid == Cid("d", n, k)
    IN IF tk # NoTk THEN IBeginResume(n, st0, x, dcid, tk) ELSE IBeginFull(n, st0, x, dcid, short, NIL)

(* the resumption reply as the initiator computes it, from the secrets of a Hello (x, thh, binder, ckpsk) *)
RrThr(thh, binder, m) == ThR(thh, binder, m.sc, m.e, m.cr)
RrCk2(x, ckpsk, thr, m) == Ck2(Ck1R(ckpsk, Dh(x, AtomOf(m.e))), thr)
RrConfOK(x, ckpsk, thh, binder, m) ==
    LET thr == RrThr(thh, binder, m)
        ck2 == RrCk2(x, ckpsk, thr, m)
    IN m.conf = Conf(CfkK(ck2, thr), ThT(thr, m.tids))

(* finish_resume: the established session of a resumption whose reply authenticated *)
IResumed(st, x, ckpsk, thh, binder, rcr, ad, m) ==
    LET thr == RrThr(thh, binder, m)
        ck2 == RrCk2(x, ckpsk, thr, m)
    IN [st EXCEPT !.ph = "done", !.send = AppK(ck2, "I", thr), !.recv = AppK(ck2, "R", thr), !.res = ResK(ck2, thr),
                  !.cid = CidK(ck2, thr), !.ath = thr, !.thf = thr, !.tids = m.tids, !.pcr = m.cr, !.rcr = rcr,
                  !.ad = ad, !.fin = MNil, !.late = NoLate, !.auth = TRUE, !.est = TRUE, !.resumed = TRUE]

(* Initiator::handle for a message m received by node n *)
IHandle(st, n, m) ==
    IF st.ph = "failed" THEN Drop(st)
    ELSE CASE m.ty = "Reply" ->
            IF st.ph # "reply" THEN Drop(st)
            ELSE IF ~InOffer(st.of, m.ad) THEN Fatal(st)
            ELSE Ok([st EXCEPT !.ph = "decap", !.reply = m, !.ad = m.ad, !.th1 = Th1(st.th0, m.sc, m.ad, m.e, m.ct),
                               !.ssx = Dh(st.x, AtomOf(m.e))], {}, {})
      [] m.ty = "PRej" ->
            IF ~(st.ph = "reply" /\ st.short) \/ m.echo # st.th0 THEN Drop(st)
            ELSE Ok([st EXCEPT !.short = FALSE, !.mode = "full"], {IInitMsg(n, st, FALSE)}, {})
      [] m.ty = "RReply" ->
            IF st.ph = "resume" THEN
                (* a reply that does not confirm is dropped; the Hello is still outstanding *)
                IF ~RrConfOK(st.x, st.ckpsk, st.thh, st.binder, m) THEN Drop(st)
                ELSE Ok(IResumed(st, st.x, st.ckpsk, st.thh, st.binder, st.rcr, st.ad, m), {}, {"est"})
            ELSE IF st.ph \in {"reply", "decap", "sign"} /\ st.late.on THEN
                (* the Hello was given up for a full handshake: its reply counts only if it authenticates against
                   the Hello's own transcript; a forgery changes nothing *)
                IF ~RrConfOK(st.late.x, st.late.ckpsk, st.late.thh, st.late.binder, m) THEN Drop(st)
                ELSE Ok(IResumed(st, st.late.x, st.late.ckpsk, st.late.thh, st.late.binder, st.late.rcr, st.late.ad, m),
                        {}, {"est"})
            ELSE Drop(st)
      [] m.ty = "RRej" ->
            IF st.ph # "resume" \/ m.echo # st.thh THEN Drop(st)
            ELSE LET b == IBeginFull(n, [st EXCEPT !.late = NoLate], <<"f", st.x[2], st.x[3]>>, Cid("r", n, st.x[3]),
                                     FALSE, st.thh)
                 IN Ok([b.st EXCEPT !.mode = "fallback", !.fell = TRUE], b.out, {"rejected"})
      [] OTHER -> Drop(st)

(* Initiator::retransmit: the host's loss timer fired *)
IRetransmit(n, st) ==
    IF st.ph = "reply" /\ st.short THEN
        LET s1 == (st.sends + 1) % 3
        IN Ok([st EXCEPT !.sends = s1], {IInitMsg(n, st, s1 # 0)}, {})
    ELSE IF st.ph = "resume" THEN
        IF st.sends + 1 >= 3 THEN
            (* fall_back: a full Initial under the same destination id; a late resume reply still counts *)
            LET late == [on |-> TRUE, x |-> st.x, thh |-> st.thh, binder |-> st.binder, ckpsk |-> st.ckpsk,
                         rcr |-> st.rcr, ad |-> st.ad]
                b == IBeginFull(n, [st EXCEPT !.late = late], <<"f", st.x[2], st.x[3]>>, st.dc, FALSE, st.thh)
            IN Ok([b.st EXCEPT !.mode = "fallback", !.fell = TRUE], b.out, {"rejected"})
        ELSE Ok([st EXCEPT !.sends = st.sends + 1],
                {M([ty |-> "Hello", ver |-> "ok", al |-> st.al, dc |-> st.dc, sc |-> st.sc, ad |-> st.ad, tid |-> st.tid,
                    e |-> Pub(st.x), binder |-> st.binder, cr |-> st.cr, len |-> LH])}, {})
    ELSE IF st.ph = "reply" THEN Ok(st, {IInitMsg(n, st, FALSE)}, {})
    ELSE IF st.ph = "done" /\ st.fin # MNil THEN Ok(st, {st.fin}, {})
    ELSE Ok(st, {}, {})

(* Initiator::shed: the transport knows the peer has the session *)
IShed(st) == [st EXCEPT !.late = NoLate, !.fin = MNil]

(* Initiator::on_key_response with the answer to the outstanding request: "ok" is the host's success *)
IKey(st, n, kind) ==
    IF st.ph = "decap" /\ kind = "ok" THEN
        LET ct == st.reply.ct
            ssk == IF ct[1] = "ct" /\ ct[3] = EK(n) THEN Kem(ct[2], ct[3]) ELSE <<"junk", n, ct>>
            ck1 == Ck1(ssk, st.ssx)
            b == st.reply.sealed
            th2 == Th2(st.th1, b.id, b.cr)
        IN IF b.k # Hs(ck1, "R", st.th1) \/ b.ad # st.th1 THEN
               (* the Reply does not open: it is dropped and the initiator waits for the next one (st.ad keeps the
                  refused Reply's value; the next accepted Reply overwrites it) *)
               Res([st EXCEPT !.ph = "reply", !.reply = MNil, !.th1 = NIL, !.ssx = NIL], {}, {}, "drop")
           ELSE IF b.cr = NIL THEN Fatal(st)
           ELSE IF b.id # st.peer THEN Fatal(st)
           ELSE IF b.sig # Sig(b.id, "responder", th2) THEN Fatal(st)
           ELSE Ok([st EXCEPT !.ph = "sign", !.hsi = Hs(ck1, "I", st.th1), !.ck1 = ck1, !.th2 = th2,
                              !.th3 = Th3(th2, b.sig), !.th4 = Th4(Th3(th2, b.sig), n), !.ath = th2, !.pcr = b.cr,
                              !.auth = TRUE], {}, {})
    ELSE IF st.ph = "sign" /\ kind = "ok" THEN
        LET sig == Sig(n, "initiator", st.th4)
            th5 == Th5(st.th4, sig)
            ck2 == Ck2(st.ck1, th5)
            fin == M([ty |-> "Fin", sealed |-> [k |-> st.hsi, ad |-> st.th3, id |-> n, sig |-> sig, cr |-> NIL]])
        IN [Ok([st EXCEPT !.ph = "done", !.send = AppK(ck2, "I", th5), !.recv = AppK(ck2, "R", th5),
                          !.res = ResK(ck2, th5), !.cid = CidK(ck2, th5), !.thf = th5, !.fin = fin, !.rcr = NIL, !.est = TRUE],
               {fin}, {"est"}) EXCEPT !.sg = {<<n, "initiator", st.th4>>}]
    ELSE IF st.ph \in {"decap", "sign"} /\ kind = "fail" THEN Fatal(st)
    ELSE Drop(st)

(* ---- the responder and its stores ---- *)
RNil == [ph |-> "idle", th0 |-> NIL, hpk |-> NIL, ek |-> NIL, fresh |-> FALSE, ct |-> NIL,
         th1 |-> NIL, th2 |-> NIL, th3 |-> NIL, hsr |-> NIL, hsi |-> NIL, ck1 |-> NIL, reply |-> MNil,
         send |-> NIL, recv |-> NIL, res |-> NIL, cid |-> NIL, ath |-> NIL, thf |-> NIL, th4 |-> NIL, peer |-> NIL,
         tid |-> NIL, tpsk |-> NIL, thh |-> NIL, early |-> NIL, mytids |-> <<>>,
         al |-> NIL, ad |-> NIL, dc |-> NIL, sc |-> NIL, pcr |-> NIL, rcr |-> NIL, spent |-> 0, nre |-> 0,
         sgn |-> FALSE, auth |-> FALSE, est |-> FALSE, resumed |-> FALSE]

(* The shared state of one responder node: sto.pkc, the prekey cache (hashes), and sto.tks, the ticket slots. *)
RemoveSlot(sto, i) == [sto EXCEPT !.tks = Norm(Put(sto.tks, i, NoSlot))]

RRes(st, out, ev, err, sto, iss, sg) ==
    [st |-> st, out |-> out, ev |-> ev, err |-> err, sto |-> sto, iss |-> iss, sg |-> sg]
RDrop(st, sto) == RRes(st, {}, {}, "drop", sto, {}, {})
RFatal(st, sto) == RRes([st EXCEPT !.ph = "failed"], {}, {"failed"}, "fatal", sto, {}, {})
ROk(st, out, ev, sto) == RRes(st, out, ev, "ok", sto, {}, {})

(* the responder's own connection id and credit record for a session s = <<node, k>> *)
RCid(s) == Cid("r", s[1], s[2])
RCr(s) == Cr(s[1])

(* Responder::on_initial for session s, given the cache of its node *)
RInitial(st, s, sto, m) ==
    LET n == s[1]
        hpk == IF m.form = "full" THEN Hash(m.pk) ELSE m.pk
        th0 == Th0(m.ver, m.al, m.dc, m.sc, m.cr, m.of, m.e, hpk)
        y == <<"r", s[1], s[2]>>
        ek == IF m.form = "full" THEN m.pk ELSE hpk[2]
        coin == <<"m", s[1], s[2]>>
        eR == Pub(y)
        ct == Ct(coin, ek)
        ad == Choose(m.of, n)
        th1 == Th1(th0, RCid(s), ad, eR, ct)
        ck1 == Ck1(Kem(coin, ek), Dh(y, AtomOf(m.e)))
        sp == Sat(st.spent + m.len)
        st1 == [st EXCEPT !.spent = sp]
    IN IF st.ph = "failed" THEN RDrop(st, sto)
       ELSE IF st.ph = "finish" THEN
            (IF st.th0 = th0 THEN ROk(st, {st.reply}, {}, sto) ELSE RDrop(st, sto))
       ELSE IF st.ph = "resumed" THEN
            (* the initiator gave up on its Hello and started a full handshake under the same ids: send the Reply
               again, but never answer more than it was asked; the bytes count either way *)
            (IF st.dc = m.dc /\ st.sc = m.sc
             THEN (IF st.reply.len <= 3 * m.len /\ sp <= LB
                   THEN ROk([st1 EXCEPT !.nre = @ + 1], {st.reply}, {}, sto)
                   ELSE RRes(st1, {}, {}, "drop", sto, {}, {}))
             ELSE RDrop(st, sto))
       ELSE IF st.ph # "idle" THEN RDrop(st, sto)
       ELSE IF m.ver # "ok" THEN RFatal(st, sto)
       ELSE IF ~Served(m.al) THEN RFatal(st, sto)
       ELSE IF ad = NIL THEN RFatal(st, sto)
       ELSE IF m.form = "short" /\ hpk \notin sto.pkc
            THEN ROk(st, {M([ty |-> "PRej", echo |-> th0])}, {}, sto)
       ELSE ROk([st EXCEPT !.ph = "sign", !.th0 = th0, !.hpk = hpk, !.ek = ek, !.fresh = (m.form = "full"),
                           !.ct = ct, !.th1 = th1, !.th2 = Th2(th1, n, RCr(s)), !.ath = Th2(th1, n, RCr(s)),
                           !.hsr = Hs(ck1, "R", th1), !.hsi = Hs(ck1, "I", th1), !.ck1 = ck1,
                           !.al = m.al, !.ad = ad, !.dc = m.dc, !.sc = m.sc, !.pcr = m.cr], {}, {}, sto)

(* Responder::on_key_response: the host's signature of the Reply *)
RKey(st, s, sto, kind) ==
    LET n == s[1]
        y == <<"r", s[1], s[2]>>
        sig == Sig(n, "responder", st.th2)
        reply == M([ty |-> "Reply", sc |-> RCid(s), ad |-> st.ad, e |-> Pub(y), ct |-> st.ct,
                    sealed |-> [k |-> st.hsr, ad |-> st.th1, id |-> n, sig |-> sig, cr |-> RCr(s)]])
    IN IF st.ph = "sign" /\ kind = "ok"
       THEN RRes([st EXCEPT !.ph = "finish", !.th3 = Th3(st.th2, sig), !.reply = reply, !.sgn = TRUE], {reply}, {}, "ok", sto,
                 {}, {<<n, "responder", st.th2>>})
       ELSE IF st.ph = "sign" /\ kind = "fail" THEN RFatal(st, sto)
       ELSE RDrop(st, sto)

(* Responder::on_finish; cs are the id draws of issue_batch *)
RFinish(st, s, sto, m, cs) ==
    LET n == s[1]
        b == m.sealed
        th4 == Th4(st.th3, b.id)
        th5 == Th5(th4, b.sig)
        ck2 == Ck2(st.ck1, th5)
        res == ResK(ck2, th5)
        is == Issue(sto.tks, cs, res, RCr(s), b.id, st.al, st.ad)
        sto1 == [sto EXCEPT !.tks = is.sl]
        sto2 == IF st.fresh THEN [sto1 EXCEPT !.pkc = @ \cup {st.hpk}] ELSE sto1
        iss == IssuedOf(is.tids, res, RCr(s), b.id, st.al, st.ad)
    IN IF st.ph = "failed" THEN RDrop(st, sto)
       ELSE IF st.ph # "finish" THEN RDrop(st, sto)
       ELSE IF b.k # st.hsi \/ b.ad # st.th3 THEN RDrop(st, sto)  \* a Finish that does not open is dropped
       ELSE IF b.sig # Sig(b.id, "initiator", th4) THEN RFatal(st, sto)
       ELSE IF ~is.ok THEN RRes([st EXCEPT !.ph = "failed"], {}, {"failed"}, "fatal", sto1, iss, {})
       ELSE RRes([st EXCEPT !.ph = "done", !.peer = b.id, !.th4 = th4, !.send = AppK(ck2, "R", th5),
                            !.recv = AppK(ck2, "I", th5), !.res = res, !.cid = CidK(ck2, th5), !.thf = th5,
                            !.mytids = is.tids, !.auth = TRUE, !.est = TRUE],
                 {}, {"est"}, "ok", sto2, iss, {})

(* Responder::on_repeated_hello: a repeat of the Hello answered; the Reply goes out again within the byte budget.
   The bytes count whether or not the Reply goes out. *)
RRepeat(st, sto, m) ==
    LET thh == ThH(m.ver, m.al, m.dc, m.sc, m.ad, m.tid, m.e, m.cr)
        sp == Sat(st.spent + m.len)
        st1 == [st EXCEPT !.spent = sp]
    IN IF st.thh # thh \/ sp > RB THEN RRes(st1, {}, {}, "drop", sto, {}, {})
       ELSE RRes([st1 EXCEPT !.nre = @ + 1], {st.reply}, {}, "ok", sto, {}, {})

(* Responder::on_hello; cs are the id draws of issue_batch *)
RHello(st, s, sto, m, cs) ==
    LET y == <<"r", s[1], s[2]>>
        thh == ThH(m.ver, m.al, m.dc, m.sc, m.ad, m.tid, m.e, m.cr)
        i0 == FindTid(sto.tks, m.tid)
        t == IF i0 = 0 THEN NoSlot ELSE sto.tks[i0]
        usable == i0 # 0 /\ ~t.exp /\ t.al = m.al /\ t.ad = m.ad /\ Binder(t.psk, thh) = m.binder
        ckp == CkPsk(t.psk)
        eR == Pub(y)
        thr == ThR(thh, m.binder, RCid(s), eR, RCr(s))
        ck2 == Ck2(Ck1R(ckp, Dh(y, AtomOf(m.e))), thr)
        stoR == RemoveSlot(sto, i0)
        is == Issue(stoR.tks, cs, ResK(ck2, thr), RCr(s), t.peer, m.al, t.ad)
        sto1 == [stoR EXCEPT !.tks = is.sl]
        stoRej == IF i0 # 0 /\ t.exp THEN stoR ELSE sto
        reply == M([ty |-> "RReply", sc |-> RCid(s), e |-> eR, tids |-> is.tids, cr |-> RCr(s), len |-> LR,
                    conf |-> Conf(CfkK(ck2, thr), ThT(thr, is.tids))])
        iss == IssuedOf(is.tids, ResK(ck2, thr), RCr(s), t.peer, m.al, t.ad)
    IN IF st.ph = "failed" THEN RDrop(st, sto)
       ELSE IF st.ph = "resumed" THEN RRepeat(st, sto, m)
       ELSE IF st.ph # "idle" THEN RDrop(st, sto)
       ELSE IF m.ver # "ok" THEN RFatal(st, sto)
       ELSE IF ~Served(m.al) THEN RFatal(st, sto)
       ELSE IF ~usable THEN ROk(st, {M([ty |-> "RRej", echo |-> thh])}, {}, stoRej)
       ELSE IF ~is.ok THEN RRes([st EXCEPT !.ph = "failed"], {}, {"failed"}, "fatal", sto1, iss, {})
       ELSE RRes([st EXCEPT !.ph = "resumed", !.peer = t.peer, !.tid = m.tid, !.tpsk = t.psk, !.thh = thh,
                            !.early = Early(ckp, thh), !.send = AppK(ck2, "R", thr), !.recv = AppK(ck2, "I", thr),
                            !.res = ResK(ck2, thr), !.cid = CidK(ck2, thr), !.ath = thr, !.thf = thr,
                            !.mytids = is.tids, !.al = m.al, !.ad = t.ad, !.dc = m.dc, !.sc = m.sc, !.pcr = m.cr,
                            !.rcr = t.cr, !.reply = reply, !.spent = 0, !.sgn = TRUE, !.auth = TRUE, !.est = TRUE,
                            !.resumed = TRUE],
                 {reply}, {"early", "est"}, "ok", sto1, iss, {})

(* Responder::retransmit: the loss timer fired while waiting for the Finish *)
RRetransmit(st, sto) ==
    IF st.ph = "finish" THEN ROk(st, {st.reply}, {}, sto) ELSE RDrop(st, sto)

(* Responder::shed: the transport knows the peer has the session *)
RShed(st) == IF st.ph = "resumed" THEN [st EXCEPT !.ph = "done"] ELSE st

(* Responder::handle *)
RHandle(st, s, sto, m, cs) ==
    IF st.ph = "failed" THEN RDrop(st, sto)
    ELSE CASE m.ty = "Init" -> RInitial(st, s, sto, m)
           [] m.ty = "Fin" -> RFinish(st, s, sto, m, cs)
           [] m.ty = "Hello" -> RHello(st, s, sto, m, cs)
           [] OTHER -> RDrop(st, sto)

=============================================================================
