---------------------------- MODULE TraceHandshake ----------------------------
(***************************************************************************)
(* Trace validation of vinc-security Initiator and Responder.              *)
(*                                                                         *)
(* The Rust test tests/trace_handshake.rs drives real handshakes in        *)
(* memory (full, short Initial with hit and miss and the full prekey on    *)
(* the third send, resumption with a ticket, 0-RTT replays, unanswered     *)
(* Hellos that give way to a full Initial under the same destination id,   *)
(* late resume replies, repeated Hellos and Initials answered by a resumed *)
(* responder, rejects, tampered and cut messages, an attacker identity as  *)
(* the dialed peer and as the dialing node, key requests answered late or  *)
(* failing, ticket expiry, store eviction, export and restore of the       *)
(* client store) and records one line per step of either machine: the      *)
(* input message with its length, the outcome (ok, dropped, fatal), the    *)
(* messages sent, the key request raised, the events and the fingerprints  *)
(* of the keys. Every public value, transcript hash prefix and key is an   *)
(* id: one id per distinct byte string.                                    *)
(*                                                                         *)
(* Each recorded world must be a behaviour of Handshake.tla's machines:    *)
(* every step is replayed through the SAME step functions (INew,           *)
(* IHandle, IKey, IRetransmit, IShed, RHandle, RKey, RRetransmit, RShed,   *)
(* CTake, CInsertAll, CExport of HsOps.tla), and                           *)
(*  - the outcome, the events, the messages sent (with their lengths) and  *)
(*    the key request must be the model's;                                 *)
(*  - an input is the model message of an earlier output (a replay,        *)
(*    found by message id), or that message with the recorded field        *)
(*    replaced by a value the attacker made (a tampered message);          *)
(*  - the oracle om is a bijection between the symbolic terms the code     *)
(*    hashes or derives (ephemeral publics, prekey hash, ciphertexts,      *)
(*    transcript hashes, keys) and their recorded ids: equal ids must be   *)
(*    equal terms and equal terms equal ids, so the code absorbs into each *)
(*    transcript exactly the fields the model does, and both sides derive  *)
(*    the same keys exactly when the model says so;                        *)
(*  - ticket ids are the recorded ids themselves (the generator is the     *)
(*    environment), so a repeated id in a store would make the model fail  *)
(*    where the code did not;                                              *)
(*  - the tickets of a client store, its export and its restore are those  *)
(*    of the sessions that finished.                                       *)
(* A world starts from empty stores (the begin line, which also gives the  *)
(* store sizes and whether the dialing node is the attacker's); sessions   *)
(* are numbered by the test.                                               *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds handshake.ndjson.     *)
(***************************************************************************)
EXTENDS HsOps, Json, IOUtils

CONSTANTS INODE, R1, R2   \* the honest initiator node and the two honest responder nodes of a world
MaxS == 40

VARIABLES ist, rst, sto, cli, snap, msgs, om, i, inode
vars == <<ist, rst, sto, cli, snap, msgs, om, i, inode>>

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/handshake.ndjson")

RNode(rn) == CASE rn = 1 -> R1 [] rn = 2 -> R2 [] OTHER -> A
PeerNode(c) == CASE c = "R1" -> R1 [] c = "R2" -> R2 [] OTHER -> A
EmptySto(tk) == [pkc |-> {}, tks |-> NoSlots(tk)]

Init ==
    /\ i = 1
    /\ ist = [s \in 1..MaxS |-> INil]
    /\ rst = [x \in {1, 2, 3} \X (1..MaxS) |-> RNil]
    /\ sto = [rn \in {1, 2, 3} |-> EmptySto(1)]
    /\ cli = NoSlots(1)
    /\ snap = <<>>
    /\ msgs = {}
    /\ om = {}
    /\ inode = INODE

(* ---- the oracle: a bijection between terms and ids ---- *)
Consistent(o, t, id) ==
    IF \E p \in o : p[1] = t \/ p[2] = id THEN <<t, id>> \in o ELSE TRUE

(* fold a sequence of <<term, id>> pairs into the oracle; ok is FALSE if one contradicts it *)
RECURSIVE FoldOm(_, _)
FoldOm(o, sq) ==
    IF sq = <<>> THEN [ok |-> TRUE, om |-> o]
    ELSE IF sq[1][2] < 0 THEN FoldOm(o, Tail(sq))
    ELSE IF Consistent(o, sq[1][1], sq[1][2]) THEN FoldOm(o \cup {sq[1]}, Tail(sq))
    ELSE [ok |-> FALSE, om |-> o]

(* the ids the code recorded for a message it sent, paired with the model terms; tickets are checked, not paired *)
HpkOf(m) == IF m.form = "full" THEN Hash(m.pk) ELSE m.pk
MPairs(m, rec) ==
    <<<<m.e, rec.e>>, <<m.ct, rec.ct>>, <<m.echo, rec.echo>>>>
    \o (IF m.ty = "Init" THEN <<<<HpkOf(m), rec.hpk>>, <<m.pk, rec.pk>>>> ELSE <<>>)
TidsOK(tids, ids) == Len(tids) = Len(ids) /\ \A j \in DOMAIN ids : tids[j] = TidT(ids[j])
MsgOK(m, rec) ==
    /\ rec.ty = m.ty
    /\ (m.ty \in {"Init", "Hello", "RReply"} => m.len = rec.len)
    /\ (m.tid # NIL => m.tid = TidT(rec.tid))
    /\ (m.ty = "RReply" => TidsOK(m.tids, rec.tids))

(* ---- messages ---- *)
MsgOf(mid) == (CHOOSE p \in msgs : p[1] = mid)[2]
Forge(b, fld, mid) ==
    CASE fld = "ver" -> [b EXCEPT !.ver = "bad"]
      [] fld = "al" -> [b EXCEPT !.al = BadAlp]
      [] fld = "dc" -> [b EXCEPT !.dc = Cid("x", A, mid)]
      [] fld = "sc" -> [b EXCEPT !.sc = Cid("x", A, mid)]
      [] fld = "of" -> [b EXCEPT !.of = Off(A)]
      [] fld = "cr" -> [b EXCEPT !.cr = Cr(A)]
      [] fld = "e" -> [b EXCEPT !.e = Pub(<<"x", A, mid>>)]
      [] fld = "pk" -> [b EXCEPT !.pk = IF b.form = "full" THEN EK(<<"x", A, mid>>) ELSE Hash(EK(<<"x", A, mid>>))]
      [] fld = "ct" -> [b EXCEPT !.ct = Ct(<<"m", A, mid>>, EK(A))]
      [] fld = "sealed" -> [b EXCEPT !.sealed = BadBlob]
      [] fld = "tid" -> [b EXCEPT !.tid = TidT(1000000 + mid)]
      [] fld = "binder" -> [b EXCEPT !.binder = <<"bad">>]
      [] fld = "conf" -> [b EXCEPT !.conf = <<"bad">>]
      [] fld = "tids" -> [b EXCEPT !.tids = <<TidT(1000000 + mid)>>]
      [] fld = "echo" -> [b EXCEPT !.echo = <<"bad">>]
InputMsg(ev) ==
    IF ev.ibase = -1 THEN MsgOf(ev.imid) ELSE Forge(MsgOf(ev.ibase), ev.ifld, ev.imid)
InputKnown(ev) ==
    \/ ev.imal
    \/ (ev.ibase = -1 /\ \E p \in msgs : p[1] = ev.imid)
    \/ (ev.ibase # -1 /\ \E p \in msgs : p[1] = ev.ibase)

(* the input is of the type and (for the messages whose length the model keeps) of the length that was delivered *)
InputShape(ev) ==
    IF ev.imal THEN TRUE
    ELSE LET m == InputMsg(ev)
         IN /\ m.ty = ev.ity
            /\ (m.ty \in {"Init", "Hello", "RReply"} => m.len = ev.ilen)

(* ---- the checks common to every step ---- *)
EvSet(ev) == {ev.evs[j] : j \in DOMAIN ev.evs}

ReqOf(who, old, new) ==
    IF who = "I"
    THEN (IF new.ph = "decap" /\ old.ph # "decap" THEN "decap"
          ELSE IF new.ph = "sign" /\ old.ph # "sign" THEN "sign" ELSE "none")
    ELSE (IF new.ph = "sign" /\ old.ph # "sign" THEN "sign" ELSE "none")

StepPairs(ev, who, old, r) ==
    LET new == r.st
    IN (IF ev.outs = <<>> \/ r.out = {} THEN <<>> ELSE MPairs(CHOOSE m \in r.out : TRUE, ev.outs[1]))
       \o (IF ReqOf(who, old, new) = "sign"
           THEN <<<<IF who = "I" THEN new.th4 ELSE new.th2, ev.rth>>>> ELSE <<>>)
       \o (IF "est" \in r.ev
           THEN <<<<new.send, ev.send>>, <<new.recv, ev.recv>>, <<new.res, ev.rsm>>, <<new.cid, ev.cid>>>> ELSE <<>>)
       \o (IF "early" \in r.ev THEN <<<<new.early, ev.early>>>> ELSE <<>>)

(* the step is the model's: outcome, events, outputs, request, established session, oracle and message table *)
StepOK(ev, who, old, r, peer) ==
    LET new == r.st
        fo == FoldOm(om, StepPairs(ev, who, old, r))
    IN /\ ev.res = r.err
       /\ EvSet(ev) = r.ev
       /\ Len(ev.outs) = Cardinality(r.out)
       /\ ev.req = ReqOf(who, old, new)
       /\ ("est" \in r.ev) =>
            /\ new.est /\ new.peer = peer /\ new.resumed = ev.resumed
            /\ TidsOK(IF who = "I" THEN new.tids ELSE new.mytids, ev.etids)
            /\ ev.alpn = new.al[2]
       /\ ("est" \in r.ev) => ev.peer = IF who = "I" THEN "R" ELSE "I"
       /\ (~("est" \in r.ev) /\ ev.op # "start") => ev.peer = "none"
       /\ fo.ok
       /\ om' = fo.om
       /\ IF r.out = {} THEN msgs' = msgs
          ELSE LET m == CHOOSE x \in r.out : TRUE
                   mid == ev.outs[1].mid
               IN /\ MsgOK(m, ev.outs[1])
                  /\ \A p \in msgs : (p[1] = mid) = (p[2] = m)
                  /\ msgs' = msgs \cup {<<mid, m>>}

(* the slot table of the ticket store of the responder's node after a step, as the code holds it: slot by slot, the
   ticket id and whether the code's clock passed its expiry (the expiry in seconds sx against the time ts of the step)
   must be the model's; an empty slot is -1 *)
SlotsOK(sl, ev) ==
    /\ Len(ev.slots) = Len(sl) /\ Len(ev.sx) = Len(sl)
    /\ \A j \in 1..Len(sl) :
         IF sl[j].occ
         THEN sl[j].tid = TidT(ev.slots[j]) /\ (sl[j].exp = (ev.sx[j] < ev.ts))
         ELSE ev.slots[j] = -1 /\ ev.sx[j] = -1

(* a resumed responder bounds the Reply it sends again for a full Initial under the answered ids by this many times
   the Initial's length (RInitial of HsOps.tla); the code records the bound it computed, and -1 for any other message *)
ResendFactor == 3
CapOK(ev, old) ==
    IF ev.imal THEN ev.rcap = -1
    ELSE LET m == InputMsg(ev)
         IN IF m.ty = "Init" /\ old.ph = "resumed" /\ old.dc = m.dc /\ old.sc = m.sc
            THEN ev.rcap = ResendFactor * ev.ilen
            ELSE ev.rcap = -1

Guard == i <= Len(Trace)

(* ---- steps ---- *)
Begin ==
    /\ Guard
    /\ Trace[i].op = "begin"
    /\ LET ev == Trace[i] IN
       /\ ist' = [s \in 1..MaxS |-> INil]
       /\ rst' = [x \in {1, 2, 3} \X (1..MaxS) |-> RNil]
       /\ sto' = [rn \in {1, 2, 3} |-> EmptySto(ev.tk)]
       /\ cli' = NoSlots(ev.ck)
       /\ inode' = IF ev.ia THEN A ELSE INODE
    /\ snap' = <<>> /\ msgs' = {} /\ om' = {}
    /\ i' = i + 1

StartI ==
    /\ Guard
    /\ LET ev == Trace[i]
           peer == PeerNode(ev.peer)
           al == Alp(ev.alpn)
           c == IF ev.take THEN CTake(cli, peer, al) ELSE [sl |-> cli, tk |-> NoTk]
           r == INew(inode, ev.s, peer, al, ev.mode = "short", c.tk)
       IN /\ ev.op = "start"
          /\ ist[ev.s].ph = "none"
          /\ (ev.mode = "resume") = (c.tk # NoTk)
          /\ (c.tk # NoTk => c.tk.tid = TidT(ev.tid))
          /\ StepOK(ev, "I", INil, r, peer)
          /\ ist' = [ist EXCEPT ![ev.s] = r.st]
          /\ cli' = c.sl
          /\ UNCHANGED <<rst, sto, snap, inode>>
          /\ i' = i + 1

RecvI ==
    /\ Guard
    /\ LET ev == Trace[i]
           old == ist[ev.s]
           r == IF ev.imal THEN Drop(old) ELSE IHandle(old, inode, InputMsg(ev))
       IN /\ ev.op = "recv" /\ ev.who = "I"
          /\ InputKnown(ev)
          /\ InputShape(ev)
          /\ StepOK(ev, "I", old, r, old.peer)
          /\ ist' = [ist EXCEPT ![ev.s] = r.st]
          /\ UNCHANGED <<rst, sto, cli, snap, inode>>
          /\ i' = i + 1

KeyI ==
    /\ Guard
    /\ LET ev == Trace[i]
           old == ist[ev.s]
           r == IKey(old, inode, IF ev.kind = "ok" THEN "ok" ELSE "fail")
       IN /\ ev.op = "key" /\ ev.who = "I"
          /\ StepOK(ev, "I", old, r, old.peer)
          /\ ist' = [ist EXCEPT ![ev.s] = r.st]
          /\ UNCHANGED <<rst, sto, cli, snap, inode>>
          /\ i' = i + 1

RetxI ==
    /\ Guard
    /\ LET ev == Trace[i]
           old == ist[ev.s]
           r == IRetransmit(inode, old)
       IN /\ ev.op = "retx" /\ ev.who = "I"
          /\ StepOK(ev, "I", old, r, old.peer)
          /\ ist' = [ist EXCEPT ![ev.s] = r.st]
          /\ UNCHANGED <<rst, sto, cli, snap, inode>>
          /\ i' = i + 1

ShedI ==
    /\ Guard
    /\ LET ev == Trace[i] IN
       /\ ev.op = "shed" /\ ev.who = "I"
       /\ ist' = [ist EXCEPT ![ev.s] = IShed(ist[ev.s])]
    /\ UNCHANGED <<rst, sto, cli, snap, msgs, om, inode>>
    /\ i' = i + 1

(* the id draws of the ticket batch an established responder session issued: the recorded ids *)
DrawsOf(ev) == [j \in DOMAIN ev.etids |-> <<ev.etids[j]>>]

RecvR ==
    /\ Guard
    /\ LET ev == Trace[i]
           old == rst[<<ev.rn, ev.s>>]
           r == IF ev.imal THEN RDrop(old, sto[ev.rn])
                ELSE RHandle(old, <<RNode(ev.rn), ev.s>>, sto[ev.rn], InputMsg(ev), DrawsOf(ev))
       IN /\ ev.op = "recv" /\ ev.who = "R"
          /\ InputKnown(ev)
          /\ InputShape(ev)
          /\ StepOK(ev, "R", old, r, inode)
          /\ SlotsOK(r.sto.tks, ev)
          /\ CapOK(ev, old)
          /\ rst' = [rst EXCEPT ![<<ev.rn, ev.s>>] = r.st]
          /\ sto' = [sto EXCEPT ![ev.rn] = r.sto]
          /\ UNCHANGED <<ist, cli, snap, inode>>
          /\ i' = i + 1

KeyR ==
    /\ Guard
    /\ LET ev == Trace[i]
           old == rst[<<ev.rn, ev.s>>]
           r == RKey(old, <<RNode(ev.rn), ev.s>>, sto[ev.rn], IF ev.kind = "ok" THEN "ok" ELSE "fail")
       IN /\ ev.op = "key" /\ ev.who = "R"
          /\ StepOK(ev, "R", old, r, inode)
          /\ SlotsOK(r.sto.tks, ev)
          /\ rst' = [rst EXCEPT ![<<ev.rn, ev.s>>] = r.st]
          /\ sto' = [sto EXCEPT ![ev.rn] = r.sto]
          /\ UNCHANGED <<ist, cli, snap, inode>>
          /\ i' = i + 1

RetxR ==
    /\ Guard
    /\ LET ev == Trace[i]
           old == rst[<<ev.rn, ev.s>>]
           r == RRetransmit(old, sto[ev.rn])
       IN /\ ev.op = "retx" /\ ev.who = "R"
          /\ StepOK(ev, "R", old, r, inode)
          /\ SlotsOK(r.sto.tks, ev)
          /\ UNCHANGED <<ist, rst, sto, cli, snap, inode>>
          /\ i' = i + 1

ShedR ==
    /\ Guard
    /\ LET ev == Trace[i] IN
       /\ ev.op = "shed" /\ ev.who = "R"
       /\ rst' = [rst EXCEPT ![<<ev.rn, ev.s>>] = RShed(rst[<<ev.rn, ev.s>>])]
    /\ UNCHANGED <<ist, sto, cli, snap, msgs, om, inode>>
    /\ i' = i + 1

(* the client takes the tickets of a finished session: a resumed session's own, or the batch of the responder
   session of a full handshake, whose final transcript the client must share *)
AcceptT ==
    /\ Guard
    /\ LET ev == Trace[i]
           st == ist[ev.s]
           rr == rst[<<ev.rn, ev.rs>>]
           tids == IF st.resumed THEN st.tids ELSE rr.mytids
       IN /\ ev.op = "accept"
          /\ st.ph = "done" /\ (st.resumed \/ (rr.ph \in {"done", "resumed"} /\ rr.thf = st.thf))
          /\ TidsOK(tids, ev.tids)
          /\ cli' = CInsertAll(cli, [j \in DOMAIN tids |->
                       [tid |-> tids[j], psk |-> Psk(st.res, tids[j], st.pcr), peer |-> st.peer, al |-> st.al,
                        ad |-> st.ad, cr |-> st.pcr]])
          /\ UNCHANGED <<ist, rst, sto, snap, msgs, om, inode>>
          /\ i' = i + 1

(* time passes: the ticket with this id expires in the store of the responder node or in the client store *)
MarkExpired(sl, tid) ==
    [j \in 1..Len(sl) |-> IF sl[j].occ /\ sl[j].tid = TidT(tid) THEN [sl[j] EXCEPT !.exp = TRUE] ELSE sl[j]]
ExpireT ==
    /\ Guard
    /\ LET ev == Trace[i] IN
       /\ ev.op = "expire"
       /\ IF ev.scope = "srv"
          THEN /\ sto' = [sto EXCEPT ![ev.rn].tks = MarkExpired(@, ev.tid)]
               /\ UNCHANGED cli
          ELSE /\ cli' = MarkExpired(cli, ev.tid)
               /\ UNCHANGED sto
    /\ UNCHANGED <<ist, rst, snap, msgs, om, inode>>
    /\ i' = i + 1

ExportT ==
    /\ Guard
    /\ LET ev == Trace[i]
           out == CExport(cli, ev.max)
       IN /\ ev.op = "export"
          /\ TidsOK([j \in DOMAIN out |-> out[j].tid], ev.tids)
          /\ snap' = out
    /\ UNCHANGED <<ist, rst, sto, cli, msgs, om, inode>>
    /\ i' = i + 1

RECURSIVE DropIdx(_, _, _)
DropIdx(sq, kept, j) ==
    IF j > Len(sq) THEN {}
    ELSE (IF sq[j].tid \in {TidT(k) : k \in kept} THEN {} ELSE {j}) \cup DropIdx(sq, kept, j + 1)

RestoreT ==
    /\ Guard
    /\ LET ev == Trace[i]
           kept == {ev.kept[j] : j \in DOMAIN ev.kept}
           drop == DropIdx(snap, kept, 1)
       IN /\ ev.op = "restore"
          /\ IF ev.ok
             THEN /\ ev.stored = Len(ev.kept)
                  /\ Len(snap) - Cardinality(drop) = Len(ev.kept)
                  /\ cli' = CInsertAll(cli, KeepSeq(snap, drop, 1))
             ELSE cli' = cli
    /\ UNCHANGED <<ist, rst, sto, snap, msgs, om, inode>>
    /\ i' = i + 1

RestartT ==
    /\ Guard
    /\ Trace[i].op = "restart"
    /\ cli' = NoSlots(Len(cli))
    /\ UNCHANGED <<ist, rst, sto, snap, msgs, om, inode>>
    /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == Begin \/ StartI \/ RecvI \/ KeyI \/ RetxI \/ ShedI \/ RecvR \/ KeyR \/ RetxR \/ ShedR \/ AcceptT \/ ExpireT
         \/ ExportT \/ RestoreT \/ RestartT \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

(* the whole recorded trace is a behaviour of the machines of HsOps.tla *)
TraceAccepted == <>(i = Len(Trace) + 1)
=============================================================================
