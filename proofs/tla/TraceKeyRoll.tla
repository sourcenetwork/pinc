----------------------------- MODULE TraceKeyRoll -----------------------------
(***************************************************************************)
(* Trace validation of the key roll: vinc-security keyroll.rs (Roll,       *)
(* Rekey, due), record.rs (PacketKey seal, open, rolled) and schedule.rs   *)
(* (roll_secret, through the keys).                                        *)
(*                                                                         *)
(* The Rust test tests/trace_keyroll.rs runs the real code through seeded  *)
(* lossy, reordering and duplicating schedules: two Roll machines (a       *)
(* dialer and an acceptor) that start rolls, receive any message of the    *)
(* pool any number of times by either method, tampered and all-zero        *)
(* shares included; four packet keys that are rolled with the values the   *)
(* machines computed and seal and open packets, with refused numbers,      *)
(* tampered packets and keys of another chain; `due` verdicts at the       *)
(* limits; and the codec of the REKEY body. Every event must be the step   *)
(* the TLA+ operators of KeyRoll.tla (RStart, ROnRequest, ROnAnswer, Due),  *)
(* Record.tla (SealOp, OpenOp, RollOp) and RekeyCodec.tla (RkEncode,       *)
(* RkDecode) compute: the same outcome, the same state of the machine      *)
(* (idle, pending request, completed rolls) and the same counters.         *)
(*                                                                         *)
(* A share, a Diffie-Hellman value and a sealed packet are recorded as     *)
(* ids (one id per distinct byte string of a run). The checker keeps an    *)
(* oracle per kind, a bijection between ids and the symbolic terms of the  *)
(* model (a share is <<"pub", atom>>, the Diffie-Hellman value of two      *)
(* atoms is the unordered pair, a sealed packet is the pair of the key's   *)
(* secret and its number): an id seen for the first time as an input is a  *)
(* share the attacker made, and equal ids must be equal terms and equal    *)
(* terms equal ids. So the two sides of a roll hold the same value, and a  *)
(* packet opens, exactly when the terms say it does. A refused             *)
(* generator and a generation that cannot grow (GenerationExhausted)       *)
(* cannot be reached by the real code, and are covered by the models       *)
(* only.                                                                   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds keyroll.ndjson.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES i, rs
vars == <<i, rs>>

KR == INSTANCE KeyRoll WITH PTO <- 1, MaxTime <- 1, Cap0 <- 1, Cap1 <- 1, MaxPn <- 1, Sat <- 100000,
                            GateFirst <- FALSE, BindAnswers <- TRUE, ForgeOn <- FALSE,
                            nd <- 0, net <- 0, now <- 0, slog <- 0, ev <- 0, comp <- 0
RC == INSTANCE Record WITH MaxPn <- 1000000, AesLimit <- 0, ChachaLimit <- 0, MaxGen <- 1000000, Sat <- 1000000,
                           Aead <- "aes", DhIds <- {}, key <- 0, log <- 0
CD == INSTANCE RekeyCodec WITH ans <- 0, sh <- 0, spn <- 0
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/keyroll.ndjson")

NONEROLL == [none |-> TRUE]

(* ---- the oracles: bijections between recorded ids and model terms ---- *)
Bound(om, id) == \E p \in om : p[2] = id
TermOf(om, id) == (CHOOSE p \in om : p[2] = id)[1]
IdOf(om, t) == (CHOOSE p \in om : p[1] = t)[2]
Consistent(om, t, id) == (\E p \in om : p[1] = t \/ p[2] = id) => <<t, id>> \in om

(* an input share: a known id is its term; a new id is a share the attacker made (the all-zero value gives no key) *)
InShare(om, id, zero) ==
    IF Bound(om, id) THEN TermOf(om, id) ELSE IF zero THEN KR!JUNK ELSE KR!Pub(KR!Atom(99, id))

EmptyRun == [run |-> 0, rolls |-> <<>>, ctr |-> <<>>, keys |-> <<>>, sOm |-> {}, dOm |-> {}, cOm |-> {}]

Init == i = 1 /\ rs = EmptyRun

Ev == Trace[i]

PnOf(pn, big) == IF big = 0 THEN pn ELSE IF big = 1 THEN 1000001 + pn ELSE 2000000

BaseOf(slot) == IF slot = 0 \/ slot = 3 THEN 0 ELSE 1

(* ---- one event ---- *)
BeginEv ==
    /\ Ev.op = "begin"
    /\ rs' = [run |-> Ev.run,
              rolls |-> [n \in 0..1 |-> KR!RInit(n = 0)],
              ctr |-> [n \in 0..1 |-> 0],
              keys |-> [s \in 0..3 |-> RC!NewKey(IF Ev.aead = 1 THEN "aes" ELSE "chacha", BaseOf(s), Ev.al, Ev.cl)],
              sOm |-> {}, dOm |-> {}, cOm |-> {}]

PendId(r, om) == IF r.req = KR!NONE THEN -1 ELSE IdOf(om, r.req.sh)

StartEv ==
    LET n == Ev.n
        fr == KR!Atom(n, rs.ctr[n])
        r == KR!RStart(rs.rolls[n], fr)
        om2 == IF r.res = "ok" THEN rs.sOm \cup {<<KR!Pub(fr), Ev.share>>} ELSE rs.sOm
    IN /\ Ev.op = "start" /\ Ev.run = rs.run
       /\ Ev.res = r.res
       /\ IF r.res = "ok" THEN Consistent(rs.sOm, KR!Pub(fr), Ev.share) ELSE Ev.share = -1
       /\ Ev.pend = PendId(r.r, om2) /\ Ev.idle = (r.r.st = "idle") /\ Ev.rolls = r.r.rolls
       /\ rs' = [rs EXCEPT !.rolls[n] = r.r, !.ctr[n] = IF r.res = "ok" THEN @ + 1 ELSE @, !.sOm = om2]

OnReqEv ==
    LET n == Ev.n
        fr == KR!Atom(n, rs.ctr[n])
        sh == InShare(rs.sOm, Ev.share, Ev.zero)
        m == [ans |-> Ev.ans, sh |-> sh, spn |-> 0, to |-> KR!NONE, gdh |-> KR!NONE]
        r == KR!ROnRequest(rs.rolls[n], m, Ev.spn, fr)
        om1 == rs.sOm \cup {<<sh, Ev.share>>}
        om2 == IF r.res = "ok" THEN om1 \cup {<<r.ans.sh, Ev.oans>>} ELSE om1
        dm2 == IF r.res = "ok" /\ r.dh # KR!NONE THEN rs.dOm \cup {<<r.dh, Ev.dh>>} ELSE rs.dOm
    IN /\ Ev.op = "onreq" /\ Ev.run = rs.run
       /\ (Ev.zero => sh = KR!JUNK) /\ (~Ev.zero => sh # KR!JUNK)
       /\ Consistent(rs.sOm, sh, Ev.share)
       /\ Ev.res = r.res
       /\ IF r.res = "ok"
          THEN /\ Consistent(om1, r.ans.sh, Ev.oans) /\ Ev.ospn = r.ans.spn
               /\ IF r.dh = KR!NONE THEN Ev.dh = -1 ELSE Consistent(rs.dOm, r.dh, Ev.dh)
          ELSE Ev.oans = -1 /\ Ev.ospn = 0 /\ Ev.dh = -1
       /\ Ev.pend = PendId(r.r, om2) /\ Ev.idle = (r.r.st = "idle") /\ Ev.rolls = r.r.rolls
       /\ rs' = [rs EXCEPT !.rolls[n] = r.r, !.ctr[n] = IF r.drew THEN @ + 1 ELSE @, !.sOm = om2, !.dOm = dm2]

OnAnsEv ==
    LET n == Ev.n
        sh == InShare(rs.sOm, Ev.share, Ev.zero)
        m == [ans |-> Ev.ans, sh |-> sh, spn |-> Ev.spn, to |-> KR!NONE, gdh |-> KR!NONE]
        r == KR!ROnAnswer(rs.rolls[n], m)
        om1 == rs.sOm \cup {<<sh, Ev.share>>}
        dm2 == IF r.res = "ok" THEN rs.dOm \cup {<<r.dh, Ev.dh>>} ELSE rs.dOm
    IN /\ Ev.op = "onans" /\ Ev.run = rs.run
       /\ (Ev.zero => sh = KR!JUNK) /\ (~Ev.zero => sh # KR!JUNK)
       /\ Consistent(rs.sOm, sh, Ev.share)
       /\ Ev.res = r.res
       /\ IF r.res = "ok" THEN Consistent(rs.dOm, r.dh, Ev.dh) /\ Ev.pspn = r.pspn ELSE Ev.dh = -1 /\ Ev.pspn = 0
       /\ Ev.pend = PendId(r.r, om1) /\ Ev.idle = (r.r.st = "idle") /\ Ev.rolls = r.r.rolls
       /\ rs' = [rs EXCEPT !.rolls[n] = r.r, !.sOm = om1, !.dOm = dm2]

PkRollEv ==
    LET r == RC!RollOp(rs.keys[Ev.slot], Ev.dh)
    IN /\ Ev.op = "pkroll" /\ Ev.run = rs.run
       /\ Bound(rs.dOm, Ev.dh)               \* the value is one a machine computed
       /\ Ev.res = "ok" /\ r.err = "ok" /\ Ev.gen = r.k.gen
       /\ rs' = [rs EXCEPT !.keys[Ev.slot] = r.k]

SealName(e) == IF e = "ok" THEN "ok" ELSE IF e = "packet_number" THEN "pn" ELSE IF e = "not_increasing" THEN "inc" ELSE "roll"

SealEv ==
    LET k == rs.keys[Ev.slot]
        pn == PnOf(Ev.pn, Ev.big)
        r == RC!SealOp(k, pn)
        t == <<k.sec, pn>>
    IN /\ Ev.op = "seal" /\ Ev.run = rs.run
       /\ Ev.res = SealName(r.err)
       /\ IF r.err = "ok" THEN Consistent(rs.cOm, t, Ev.ct) ELSE Ev.ct = -1
       /\ Ev.sealed = r.k.sealed /\ Ev.gen = r.k.gen
       /\ rs' = [rs EXCEPT !.keys[Ev.slot] = r.k, !.cOm = IF r.err = "ok" THEN @ \cup {<<t, Ev.ct>>} ELSE @]

OpenName(e) == IF e = "ok" THEN "ok" ELSE IF e = "packet_number" THEN "pn" ELSE IF e = "roll_required" THEN "roll" ELSE "auth"

OpenEv ==
    LET k == rs.keys[Ev.slot]
        pn == PnOf(Ev.pn, Ev.big)
        valid == \E p \in rs.cOm : p[2] = Ev.ct /\ p[1] = <<k.sec, pn>>      \* a sealed packet of this secret and number
        r == RC!OpenOp(k, pn, valid)
    IN /\ Ev.op = "open" /\ Ev.run = rs.run
       /\ Ev.res = OpenName(r.err)
       /\ Ev.failed = r.k.failed /\ Ev.gen = r.k.gen
       /\ rs' = [rs EXCEPT !.keys[Ev.slot] = r.k]

LimitReached(k) == IF k.aead = "aes" THEN k.sealed >= k.aesLim ELSE k.failed >= k.chachaLim

(* the age is recorded in whole milliseconds and the remaining nanoseconds, since TLC integers are 32 bits: the
   key is old iff agem >= 600000 (10 minutes) *)
DueEv ==
    LET mk(a, s, f) == [RC!NewKey(IF a = 1 THEN "aes" ELSE "chacha", 0, Ev.al, Ev.cl) EXCEPT !.sealed = s, !.failed = f]
        sk == mk(Ev.sa, Ev.ss, Ev.sf)
        rk == mk(Ev.ra, Ev.rs, Ev.rf)
        d == KR!Due(LimitReached(sk), LimitReached(rk), sk.sealed, Ev.after, Ev.agem, 600000)
    IN /\ Ev.op = "due"
       /\ Ev.res = d /\ Ev.lrs = LimitReached(sk) /\ Ev.lrr = LimitReached(rk)
       /\ UNCHANGED rs

EncEv ==
    LET e == CD!RkEncode([ans |-> Ev.ans, sh |-> Ev.share, spn |-> U!FromLimbs(Ev.sl)])
    IN /\ Ev.op = "enc"
       /\ IF e.err = "ok" THEN Ev.res = "ok" /\ Ev.bytes = e.bytes ELSE Ev.res = "overflow" /\ Ev.bytes = <<>>
       /\ UNCHANGED rs

DecEv ==
    LET d == CD!RkDecode(Ev.bytes)
    IN /\ Ev.op = "dec"
       /\ IF d.err = "ok"
          THEN Ev.res = "ok" /\ Ev.ans = d.ans /\ Ev.share = d.sh /\ U!FromLimbs(Ev.sl) = d.spn
          ELSE Ev.res = (IF d.err \in {"kind", "trailing"} THEN d.err ELSE "other")
       /\ UNCHANGED rs

Step ==
    /\ i <= Len(Trace)
    /\ Ev.t = "kr"
    /\ \/ BeginEv \/ StartEv \/ OnReqEv \/ OnAnsEv \/ PkRollEv \/ SealEv \/ OpenEv \/ DueEv \/ EncEv \/ DecEv
    /\ i' = i + 1

\* the trace has ended: every event was a step of the model
Finished == i > Len(Trace) /\ UNCHANGED vars

TNext == Step \/ Finished

TraceSpec == Init /\ [][TNext]_vars

(* the safety facts of the model hold on every recorded state: the machines are in a legal shape, and the keys are
   the chains of the values the machines computed *)
Inv ==
    rs.run > 0 =>
        /\ \A n \in 0..1 : rs.rolls[n].st \in {"idle", "req"} /\ (rs.rolls[n].st = "req" => rs.rolls[n].req # KR!NONE)
        /\ \A s \in 0..3 : RC!Depth(rs.keys[s].sec) = rs.keys[s].gen
=============================================================================
