---------------------------- MODULE TraceHandshake ----------------------------
(***************************************************************************)
(* Trace validation of vinc-security Initiator and Responder.              *)
(*                                                                         *)
(* The Rust test tests/trace_handshake.rs drives real handshakes in        *)
(* memory (full, short Initial with hit and miss, resumption, replays,     *)
(* rejects, tampered and cut messages, key requests answered late or       *)
(* failing) and records one line per step of either machine: the input     *)
(* message, the outcome (ok, dropped, fatal), the messages sent, the key   *)
(* request raised, the events and the fingerprints of the keys. Every      *)
(* public value, transcript hash prefix and key is an id: one id per       *)
(* distinct byte string.                                                   *)
(*                                                                         *)
(* Each recorded world must be a behaviour of Handshake.tla's machines:    *)
(* every step is replayed through the SAME step functions (IBeginFull,     *)
(* IBeginResume, IHandle, IKey, RHandle, RKey of HsOps.tla), and           *)
(*  - the outcome, the events, the messages sent and the key request       *)
(*    must be the model's;                                                 *)
(*  - an input is the model message of an earlier output (a replay,        *)
(*    found by message id), or that message with the recorded field        *)
(*    replaced by a value the attacker made (a tampered message);          *)
(*  - the oracle om is a bijection between the symbolic terms the code     *)
(*    hashes or derives (ephemeral publics, prekey hash, ciphertexts,      *)
(*    transcript hashes, ticket ids, keys) and their recorded ids: equal   *)
(*    ids must be equal terms and equal terms equal ids, so the code       *)
(*    absorbs into each transcript exactly the fields the model does, and  *)
(*    both sides derive the same keys exactly when the model says so;      *)
(*  - the resolved tickets of a client are those a finished session        *)
(*    received.                                                            *)
(* A world starts from empty stores (the begin line); sessions are         *)
(* numbered by the test.                                                   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds handshake.ndjson.     *)
(***************************************************************************)
EXTENDS HsOps, Json, IOUtils

CONSTANTS INODE, R1, R2   \* the initiator's node and the two responder nodes of a world
MaxS == 12

VARIABLES ist, rst, sto, cli, msgs, om, i
vars == <<ist, rst, sto, cli, msgs, om, i>>

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/handshake.ndjson")

RNode(rn) == IF rn = 1 THEN R1 ELSE R2
EmptySto == [pkc |-> {}, clk |-> 0, tks |-> [k \in Slots |-> NoSlot]]

Init ==
    /\ i = 1
    /\ ist = [s \in 1..MaxS |-> INil]
    /\ rst = [x \in {1, 2} \X (1..MaxS) |-> RNil]
    /\ sto = [rn \in {1, 2} |-> EmptySto]
    /\ cli = {}
    /\ msgs = {}
    /\ om = {}

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

(* the ids the code recorded for a message it sent, paired with the model terms *)
HpkOf(m) == IF m.form = "full" THEN Hash(m.pk) ELSE m.pk
MPairs(m, rec) ==
    <<<<m.e, rec.e>>, <<m.ct, rec.ct>>, <<m.tid, rec.tid>>, <<m.echo, rec.echo>>>>
    \o (IF m.ty = "Init" THEN <<<<HpkOf(m), rec.hpk>>, <<m.pk, rec.pk>>>> ELSE <<>>)
    \o [j \in 1..Len(m.tids) |-> <<m.tids[j], rec.tids[j]>>]

(* ---- messages ---- *)
MsgOf(mid) == (CHOOSE p \in msgs : p[1] = mid)[2]
Forge(b, fld, mid) ==
    CASE fld = "prm" -> [b EXCEPT !.prm = "bad"]
      [] fld = "e" -> [b EXCEPT !.e = Pub(<<"x", A, mid>>)]
      [] fld = "pk" -> [b EXCEPT !.pk = IF b.form = "full" THEN EK(<<"x", A, mid>>) ELSE Hash(EK(<<"x", A, mid>>))]
      [] fld = "ct" -> [b EXCEPT !.ct = Ct(<<"m", A, mid>>, EK(A))]
      [] fld = "sealed" -> [b EXCEPT !.sealed = BadBlob]
      [] fld = "tid" -> [b EXCEPT !.tid = <<"tid", "x", mid>>]
      [] fld = "binder" -> [b EXCEPT !.binder = <<"bad">>]
      [] fld = "conf" -> [b EXCEPT !.conf = <<"bad">>]
      [] fld = "tids" -> [b EXCEPT !.tids = <<<<"tid", "x", mid>>>>]
      [] fld = "rprm" -> [b EXCEPT !.rprm = "alt"]
      [] fld = "echo" -> [b EXCEPT !.echo = <<"bad">>]
InputMsg(ev) ==
    IF ev.ibase = -1 THEN MsgOf(ev.imid) ELSE Forge(MsgOf(ev.ibase), ev.ifld, ev.imid)
InputKnown(ev) ==
    \/ ev.imal
    \/ (ev.ibase = -1 /\ \E p \in msgs : p[1] = ev.imid)
    \/ (ev.ibase # -1 /\ \E p \in msgs : p[1] = ev.ibase)

(* ---- the checks common to every step ---- *)
EvSet(ev) == {ev.evs[j] : j \in DOMAIN ev.evs}

ReqOf(who, old, new) ==
    IF who = "I"
    THEN (IF new.ph = "decap" /\ old.ph # "decap" THEN "decap"
          ELSE IF new.ph = "sign" /\ old.ph # "sign" THEN "sign" ELSE "none")
    ELSE (IF new.ph = "sign" /\ old.ph # "sign" THEN "sign" ELSE "none")

TidPairs(ev, who, new) ==
    IF ~("est" \in EvSet(ev)) THEN <<>>
    ELSE IF who = "I" THEN [j \in 1..Len(new.tids) |-> <<new.tids[j], ev.etids[j]>>]
    ELSE <<<<new.mytid, ev.etids[1]>>>>

StepPairs(ev, who, old, r) ==
    LET new == r.st
    IN (IF ev.outs = <<>> \/ r.out = {} THEN <<>> ELSE MPairs(CHOOSE m \in r.out : TRUE, ev.outs[1]))
       \o (IF ReqOf(who, old, new) = "sign"
           THEN <<<<IF who = "I" THEN new.th4 ELSE new.th2, ev.rth>>>> ELSE <<>>)
       \o (IF "est" \in r.ev THEN <<<<new.send, ev.send>>, <<new.recv, ev.recv>>, <<new.res, ev.rsm>>>> ELSE <<>>)
       \o (IF "early" \in r.ev THEN <<<<new.early, ev.early>>>> ELSE <<>>)
       \o TidPairs(ev, who, new)

(* the step is the model's: outcome, events, outputs, request, established session, oracle and message table *)
StepOK(ev, who, old, r) ==
    LET new == r.st
        fo == FoldOm(om, StepPairs(ev, who, old, r))
        peer == IF who = "I" THEN R1 ELSE INODE
    IN /\ ev.res = r.err
       /\ EvSet(ev) = r.ev
       /\ Len(ev.outs) = Cardinality(r.out)
       /\ ev.req = ReqOf(who, old, new)
       /\ ("est" \in r.ev) =>
            /\ new.est /\ new.peer = peer /\ new.resumed = ev.resumed
            /\ Len(ev.etids) = (IF who = "I" THEN Len(new.tids) ELSE 1)
       /\ ~("est" \in r.ev) => ev.peer = "none"
       /\ fo.ok
       /\ om' = fo.om
       /\ IF r.out = {} THEN msgs' = msgs
          ELSE LET m == CHOOSE x \in r.out : TRUE
                   mid == ev.outs[1].mid
               IN /\ ev.outs[1].ty = m.ty
                  /\ \A p \in msgs : (p[1] = mid) = (p[2] = m)
                  /\ msgs' = msgs \cup {<<mid, m>>}

(* ---- steps ---- *)
Begin ==
    /\ i <= Len(Trace)
    /\ Trace[i].op = "begin"
    /\ ist' = [s \in 1..MaxS |-> INil]
    /\ rst' = [x \in {1, 2} \X (1..MaxS) |-> RNil]
    /\ sto' = [rn \in {1, 2} |-> EmptySto]
    /\ cli' = {} /\ msgs' = {} /\ om' = {}
    /\ i' = i + 1

StartI ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
           x == <<"i", INODE, ev.s>>
       IN /\ ev.op = "start"
          /\ ist[ev.s].ph = "none"
          /\ \E tk \in IF ev.mode = "resume" THEN {t \in cli : <<t.tid, ev.tid>> \in om} ELSE {[tid |-> NIL]} :
               LET r == IF ev.mode = "resume" THEN IBeginResume(INODE, x, tk)
                        ELSE IBeginFull(INODE, x, R1, ev.mode = "short", NIL, NIL)
               IN /\ StepOK(ev, "I", INil, r)
                  /\ ist' = [ist EXCEPT ![ev.s] = r.st]
                  /\ cli' = IF ev.mode = "resume" THEN cli \ {tk} ELSE cli
          /\ UNCHANGED <<rst, sto>>
          /\ i' = i + 1

RecvI ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
           old == ist[ev.s]
           r == IF ev.imal THEN Drop(old) ELSE IHandle(old, INODE, InputMsg(ev))
       IN /\ ev.op = "recv" /\ ev.who = "I"
          /\ InputKnown(ev)
          /\ StepOK(ev, "I", old, r)
          /\ ist' = [ist EXCEPT ![ev.s] = r.st]
          /\ UNCHANGED <<rst, sto, cli>>
          /\ i' = i + 1

KeyI ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
           old == ist[ev.s]
           r == IKey(old, INODE, IF ev.kind = "ok" THEN "ok" ELSE "fail")
       IN /\ ev.op = "key" /\ ev.who = "I"
          /\ StepOK(ev, "I", old, r)
          /\ ist' = [ist EXCEPT ![ev.s] = r.st]
          /\ UNCHANGED <<rst, sto, cli>>
          /\ i' = i + 1

RecvR ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
           old == rst[<<ev.rn, ev.s>>]
           r == IF ev.imal THEN RDrop(old, sto[ev.rn])
                ELSE RHandle(old, <<RNode(ev.rn), ev.s>>, sto[ev.rn], InputMsg(ev))
       IN /\ ev.op = "recv" /\ ev.who = "R"
          /\ InputKnown(ev)
          /\ StepOK(ev, "R", old, r)
          /\ rst' = [rst EXCEPT ![<<ev.rn, ev.s>>] = r.st]
          /\ sto' = [sto EXCEPT ![ev.rn] = r.sto]
          /\ UNCHANGED <<ist, cli>>
          /\ i' = i + 1

KeyR ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
           old == rst[<<ev.rn, ev.s>>]
           r == RKey(old, <<RNode(ev.rn), ev.s>>, sto[ev.rn], IF ev.kind = "ok" THEN "ok" ELSE "fail")
       IN /\ ev.op = "key" /\ ev.who = "R"
          /\ StepOK(ev, "R", old, r)
          /\ rst' = [rst EXCEPT ![<<ev.rn, ev.s>>] = r.st]
          /\ sto' = [sto EXCEPT ![ev.rn] = r.sto]
          /\ UNCHANGED <<ist, cli>>
          /\ i' = i + 1

(* the client takes the tickets of a finished session: a resumed session's own, or the batch of the responder
   session of a full handshake, whose final transcript the client must share *)
AcceptT ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
           st == ist[ev.s]
           rr == rst[<<ev.rn, ev.rs>>]
           tid == IF st.resumed THEN st.tids[1] ELSE rr.mytid
           fo == FoldOm(om, <<<<tid, ev.tid>>>>)
       IN /\ ev.op = "accept"
          /\ st.ph = "done" /\ (st.resumed \/ (rr.ph = "done" /\ rr.thf = st.thf))
          /\ fo.ok /\ om' = fo.om
          /\ cli' = cli \cup {[tid |-> tid, psk |-> Psk(st.res, tid), peer |-> st.peer]}
          /\ UNCHANGED <<ist, rst, sto, msgs>>
          /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == Begin \/ StartI \/ RecvI \/ KeyI \/ RecvR \/ KeyR \/ AcceptT \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

(* the whole recorded trace is a behaviour of the machines of HsOps.tla *)
TraceAccepted == <>(i = Len(Trace) + 1)
=============================================================================
