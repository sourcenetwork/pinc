------------------------------ MODULE KeyRoll ------------------------------
(***************************************************************************)
(* Model of the key roll: the state machine Roll of vinc-security          *)
(* keyroll.rs and the flip/hold layer of vinc-transport conn/keys.rs       *)
(* (staged keys, the switch of the sending key, the reactive switch of the *)
(* answerer, the previous key held for one probe timeout, the floors), for *)
(* two connections over a network that loses, reorders and duplicates      *)
(* every packet.                                                           *)
(*                                                                         *)
(* Roll (RStart, ROnRequest, ROnAnswer): Idle or Requested, the dialer     *)
(* flag, `last` (the last request answered and its answer) and the         *)
(* completed-rolls counter, exactly as in keyroll.rs, including the order  *)
(* of its checks and the state a failure leaves behind. A share is         *)
(* <<"pub", atom>>; the Diffie-Hellman value of two atoms is the unordered *)
(* pair, so both sides compute the same term from different secrets. A     *)
(* traffic secret is the free term Base(d), RollSec(secret, dh), so keys   *)
(* of different generations or different Diffie-Hellman values are         *)
(* different as a structural fact (perfect primitives).                    *)
(*                                                                         *)
(* The layer (RecvKeys, RekeyRx, Begin, SendPkt): the receive side keeps   *)
(* the current key, the previous one with its hold deadline, the staged    *)
(* next one with its floor, and the phase bit; a packet picks its key by   *)
(* its phase bit and number (Select) and is accepted iff it opens under    *)
(* that key; the first packet that opens under the staged key promotes it  *)
(* and, for the answerer, switches the sending key (behind_peer,           *)
(* update_send). The requester switches its sending key at the answer. A   *)
(* REKEY message rides in a packet (the polled message, sent again each    *)
(* PTO while a request is unanswered); a packet is processed once (the     *)
(* packet-number set), and its keys are used before that check, as in the  *)
(* code. Time advances by explicit Tick steps up to MaxTime; PTO is a      *)
(* parameter. The network is the set of every packet ever sent: any        *)
(* subset can be delivered in any order any number of times (loss is a     *)
(* packet that is never delivered), and an attacker can deliver a packet   *)
(* with its phase bit flipped (Forge), which cannot open.                  *)
(*                                                                         *)
(* An answer carries the identifier of the request it answers (the echo,  *)
(* RId: a short hash of the request share, injective in this model) and    *)
(* the Diffie-Hellman value of a roll has the identifier bound into it     *)
(* (Bound). The requester takes an answer only when its echo names the     *)
(* request that is out; any other answer is ignored. The ghost field gdh   *)
(* of a message records the value its sender used; no code reads it. The   *)
(* REKEY body travels in an authenticated packet, so the attacker of this  *)
(* model is passive for REKEY (it only delays, drops and repeats).         *)
(*                                                                         *)
(* The collision rule is one rule for both sides: the dialer keeps its     *)
(* request and ignores the acceptor's, the acceptor drops its own and      *)
(* answers. A duplicate of the request being answered is answered again    *)
(* with the same answer, also while the next key is staged. A request that *)
(* arrives in a packet opened under the previous generation's key is a     *)
(* late copy of a settled roll and is ignored. The loss events of the      *)
(* transport (a lost answer queued again, a lost request sent at the next  *)
(* opportunity) are steps of the model (RequeueAnswer, RequestLost).       *)
(*                                                                         *)
(* The probe timeout is an argument of the operators that use it (Promote, *)
(* RecvKeys, Poll); the system passes the constant PTO and the trace       *)
(* validation the timeout in force at each event.                          *)
(*                                                                         *)
(* Lean counterpart: Vinc/KeyRoll.lean. Trace validation: TraceKeyRoll.tla *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS PTO, MaxTime, Cap0, Cap1, MaxPn, Sat, ForgeOn

Nodes == {0, 1}
Peer(n) == 1 - n          \* node 0 is the dialer, node 1 the acceptor
CtrCap(n) == IF n = 0 THEN Cap0 ELSE Cap1     \* how many fresh atoms (rolls started or answered) a node may draw
NONE == [none |-> TRUE]          \* the absent value of a record-valued field
NOTIME == -1                    \* the absent value of a time

Inc(x) == IF x >= Sat THEN x ELSE x + 1      \* saturating add of one

(* ---- terms ---- *)
Atom(n, k) == [t |-> "atom", n |-> n, k |-> k]
Pub(a) == [t |-> "pub", a |-> a]
JUNK == [t |-> "junk"]
DhOf(own, sh) == IF sh = JUNK THEN NONE ELSE [t |-> "dh", s |-> {own, sh.a}]   \* unordered: both sides agree
RId(sh) == [t |-> "id", s |-> sh]                    \* the identifier of a request share (a short hash, injective here)
Bound(id, dh) == [t |-> "bound", id |-> id, dh |-> dh]       \* extract(dh, id): the identifier bound into the value
Base(d) == [t |-> "base", d |-> d]
RollSec(s, dh) == [t |-> "roll", s |-> s, dh |-> dh]
RECURSIVE Depth(_)
Depth(s) == IF s.t = "base" THEN 0 ELSE 1 + Depth(s.s)

(* ---- REKEY messages: to is the echo of an answer (NONE in a request) ---- *)
Req(sh) == [ans |-> FALSE, sh |-> sh, spn |-> 0, to |-> NONE, gdh |-> NONE]
Ans(sh, spn, to, gdh) == [ans |-> TRUE, sh |-> sh, spn |-> spn, to |-> to, gdh |-> gdh]

(* ---- keyroll.rs: Roll ---- *)
RInit(dialer) == [dialer |-> dialer, st |-> "idle", seed |-> NONE, req |-> NONE, last |-> NONE, rolls |-> 0]

(* Roll::start; fresh = NONE stands for a refused random generator *)
RStart(r, fresh) ==
    IF r.st # "idle" THEN [res |-> "unexpected", r |-> r, msg |-> NONE]
    ELSE IF fresh = NONE THEN [res |-> "randomness", r |-> r, msg |-> NONE]
    ELSE [res |-> "ok", r |-> [r EXCEPT !.st = "req", !.seed = fresh, !.req = Req(Pub(fresh))], msg |-> Req(Pub(fresh))]

IsDup(r, req) == r.last # NONE /\ r.last.sh = req.sh

(* Roll::on_request: the answer to a request. The order of the checks is the code's: an answer is refused, a
   duplicate request gets the same answer and no key, the dialer ignores a request while its own is out, the
   accepting side drops its own request, then the randomness and the share. drew: a fresh value was drawn. *)
ROnRequest(r, req, spn, fresh) ==
    IF req.ans THEN [res |-> "unexpected", r |-> r, ans |-> NONE, dh |-> NONE, drew |-> FALSE]
    ELSE IF IsDup(r, req) THEN [res |-> "ok", r |-> r, ans |-> r.last.ans, dh |-> NONE, drew |-> FALSE]
    ELSE IF r.st # "idle" /\ r.dialer THEN [res |-> "unexpected", r |-> r, ans |-> NONE, dh |-> NONE, drew |-> FALSE]
    ELSE LET r1 == IF r.st # "idle" THEN [r EXCEPT !.st = "idle", !.seed = NONE, !.req = NONE] ELSE r
         IN IF fresh = NONE THEN [res |-> "randomness", r |-> r1, ans |-> NONE, dh |-> NONE, drew |-> FALSE]
            ELSE LET dh == DhOf(fresh, req.sh)
                 IN IF dh = NONE THEN [res |-> "invalid", r |-> r1, ans |-> NONE, dh |-> NONE, drew |-> TRUE]
                    ELSE LET bd == Bound(RId(req.sh), dh)
                             a == Ans(Pub(fresh), spn, RId(req.sh), bd)
                         IN [res |-> "ok", r |-> [r1 EXCEPT !.last = [sh |-> req.sh, ans |-> a], !.rolls = Inc(@)],
                             ans |-> a, dh |-> bd, drew |-> TRUE]

(* Roll::on_answer: takes the answer to the request that is out; an answer that echoes another request is ignored *)
ROnAnswer(r, a) ==
    IF ~a.ans THEN [res |-> "unexpected", r |-> r, dh |-> NONE, pspn |-> 0]
    ELSE IF r.st # "req" THEN [res |-> "unexpected", r |-> r, dh |-> NONE, pspn |-> 0]
    ELSE IF a.to # RId(r.req.sh) THEN [res |-> "unexpected", r |-> r, dh |-> NONE, pspn |-> 0]
    ELSE LET dh == DhOf(r.seed, a.sh)
         IN IF dh = NONE THEN [res |-> "invalid", r |-> r, dh |-> NONE, pspn |-> 0]
            ELSE [res |-> "ok", r |-> [r EXCEPT !.st = "idle", !.seed = NONE, !.req = NONE, !.last = NONE, !.rolls = Inc(@)],
                  dh |-> Bound(RId(r.req.sh), dh), pspn |-> a.spn]

(* keyroll.rs due(): a limit reached, the sending key sealed `after` packets, or the keys are MaxAge old *)
Due(limitSend, limitRecv, sealed, after, age, maxAge) == limitSend \/ limitRecv \/ sealed >= after \/ age >= maxAge

(* ---- conn/keys.rs: the keys of one connection ---- *)
NewK(sec, g) == [sec |-> sec, g |-> g, fc |-> 0]

NodeInit(n) ==
    [roll |-> RInit(n = 0), ctr |-> 0,
     sk |-> NewK(Base(n), 0), sph |-> FALSE, stg |-> NONE, out |-> NONE, reqAt |-> NOTIME,
     cur |-> NewK(Base(Peer(n)), 0), rph |-> FALSE, first |-> 0, prev |-> NONE, nxt |-> NONE,
     npn |-> 0, seen |-> {}, chg |-> 0, promAt |-> NOTIME, lastAns |-> NONE]

(* RecvKeys::expire *)
Expire(s, t) == IF s.prev # NONE /\ s.prev.until <= t THEN [s EXCEPT !.prev = NONE] ELSE s

(* RecvKeys::select (after expire): the key slot a packet with phase bit ph and number pn is opened with *)
Select(s, ph, pn) ==
    IF ph = s.rph THEN "cur"
    ELSE IF s.nxt # NONE /\ pn >= s.nxt.floor THEN "next"
    ELSE IF pn < s.first /\ s.prev # NONE THEN "prev"
    ELSE "err"

SlotKey(s, sel) == CASE sel = "cur" -> s.cur [] sel = "next" -> s.nxt.k [] sel = "prev" -> s.prev.k

(* a failed open counts against the key it was tried with *)
BumpFC(s, sel) ==
    CASE sel = "cur" -> [s EXCEPT !.cur.fc = Inc(@)]
      [] sel = "prev" -> [s EXCEPT !.prev.k.fc = Inc(@)]
      [] sel = "next" -> [s EXCEPT !.nxt.k.fc = Inc(@)]
      [] OTHER -> s

(* RecvKeys::promote and Keys::update_send; pto is the probe timeout in force *)
Promote(s, pn, t, pto) ==
    [s EXCEPT !.prev = [k |-> s.cur, until |-> t + pto], !.cur = s.nxt.k, !.rph = ~s.rph, !.first = pn,
              !.nxt = NONE, !.promAt = t]
UpdateSend(s) == IF s.stg = NONE THEN s ELSE [s EXCEPT !.sk = s.stg, !.sph = ~s.sph, !.stg = NONE]

(* on_short, up to the opening: the new keys state and whether the packet opened. forged: the phase bit of the
   packet was flipped by the attacker, so the tag does not verify under any key. *)
RecvKeys(s, p, forged, t, pto) ==
    LET s1 == Expire(s, t)
        ph == IF forged THEN ~p.ph ELSE p.ph
        sel == Select(s1, ph, p.pn)
    IN IF sel = "err" THEN [s |-> s1, acc |-> FALSE, sel |-> sel]
       ELSE IF forged \/ p.sec # SlotKey(s1, sel).sec THEN [s |-> BumpFC(s1, sel), acc |-> FALSE, sel |-> sel]
       ELSE IF sel = "cur" THEN [s |-> [s1 EXCEPT !.first = IF p.pn < @ THEN p.pn ELSE @], acc |-> TRUE, sel |-> sel]
       ELSE IF sel = "next" THEN [s |-> UpdateSend(Promote(s1, p.pn, t, pto)), acc |-> TRUE, sel |-> sel]
       ELSE [s |-> s1, acc |-> TRUE, sel |-> sel]

IsDupMsg(s, m) == ~m.ans /\ IsDup(s.roll, m)

(* Keys::on_request is refused while a next key is staged, unless the request repeats the one answered *)
Gated(s, m) == s.nxt # NONE /\ ~IsDupMsg(s, m)

(* Connection::on_rekey: a request that arrived in a packet opened under the previous generation's key is a late
   copy of a settled roll, and is ignored; every answer is looked at *)
Acts(m, sel) == m.ans \/ sel # "prev"

(* a fresh atom is drawn for every request that is not a duplicate *)
CanRx(s, m, me) == m.ans \/ IsDupMsg(s, m) \/ Gated(s, m) \/ s.ctr < CtrCap(me) \/ (s.roll.dialer /\ s.roll.st # "idle")

(* the body of a REKEY frame: the answer switches the sending key, a request stages the keys *)
RekeyRx(s, m, me) ==
    IF m.ans THEN
        LET r == ROnAnswer(s.roll, m)
        IN IF r.res # "ok" THEN [s EXCEPT !.roll = r.r]
           ELSE [s EXCEPT !.roll = r.r, !.nxt = [k |-> NewK(RollSec(s.cur.sec, r.dh), s.cur.g + 1), floor |-> r.pspn],
                          !.sk = NewK(RollSec(s.sk.sec, r.dh), s.sk.g + 1), !.sph = ~@, !.reqAt = NOTIME,
                          !.chg = @ + 1]
    ELSE IF Gated(s, m) THEN s
    ELSE LET r == ROnRequest(s.roll, m, s.npn, Atom(me, s.ctr))
         IN IF r.res # "ok" THEN [s EXCEPT !.roll = r.r]
            ELSE IF r.dh = NONE THEN [s EXCEPT !.out = r.ans]
            ELSE [s EXCEPT !.roll = r.r, !.out = r.ans, !.ctr = @ + 1, !.chg = @ + 1,
                           !.stg = NewK(RollSec(s.sk.sec, r.dh), s.sk.g + 1),
                           !.nxt = [k |-> NewK(RollSec(s.cur.sec, r.dh), s.cur.g + 1), floor |-> 0]]

(* ---- the system ---- *)
VARIABLES nd, net, now, slog, ev, comp
vars == <<nd, net, now, slog, ev, comp>>
View == <<nd, net, now, slog, comp>>     \* the state identity: ev only labels the last step for the action properties

Init == /\ nd = [n \in Nodes |-> NodeInit(n)]
        /\ net = {} /\ now = 0 /\ slog = {} /\ ev = [t |-> "init"] /\ comp = {}

(* ---- the steps of one node, shared by the system below and by the trace validation ---- *)
(* poll_rekey: the message waiting, or the pending request again once a probe timeout passed *)
Poll(s, t, pto) ==
    IF s.out # NONE THEN [pl |-> s.out, s |-> [s EXCEPT !.out = NONE, !.reqAt = IF s.out.ans THEN @ ELSE t,
                                                          !.lastAns = IF s.out.ans THEN s.out ELSE @]]
    ELSE IF s.roll.req # NONE /\ (s.reqAt = NOTIME \/ t >= s.reqAt + pto)
         THEN [pl |-> s.roll.req, s |-> [s EXCEPT !.reqAt = t]]
    ELSE [pl |-> NONE, s |-> s]

(* Keys::requeue_answer: a lost answer goes out again; Keys::request_lost: a lost request goes out at the next
   opportunity *)
RequeueAns(s) == IF s.out = NONE THEN [s EXCEPT !.out = s.lastAns] ELSE s
RequestLostOp(s) == [s EXCEPT !.reqAt = NOTIME]

(* Connection::roll_tick: a due roll starts, when none is under way and nothing is staged *)
CanBegin(s, n) == s.stg = NONE /\ s.nxt = NONE /\ RStart(s.roll, Atom(n, s.ctr)).res = "ok"
BeginOp(s, n) ==
    LET r == RStart(s.roll, Atom(n, s.ctr))
    IN [s EXCEPT !.roll = r.r, !.out = r.msg, !.reqAt = NOTIME, !.ctr = @ + 1]

(* a packet sealed under the sending key, carrying the polled REKEY message if any (withPl); a packet built for a
   probe or a repair carries none, whatever is due; ok: a packet with a message has one to carry *)
SendOp(s0, t, pto, withPl, n) ==
    LET q == IF withPl THEN Poll(s0, t, pto) ELSE [pl |-> NONE, s |-> s0]
        s == q.s
    IN [p |-> [from |-> n, ph |-> s.sph, pn |-> s.npn, sec |-> s.sk.sec, pl |-> q.pl],
        s |-> [s EXCEPT !.npn = @ + 1],
        ok |-> (withPl => q.pl # NONE)]

(* a packet p arrives at node n (forged: with its phase bit flipped by the attacker): the keys layer, the packet
   number set (rx.contains(pn): a packet number is processed once), then the REKEY message *)
DeliverOp(s0, p, forged, t, pto, n) ==
    LET k == RecvKeys(s0, p, forged, t, pto)
        m == p.pl
        proc == k.acc /\ ~(p.pn \in s0.seen)
        s1 == IF proc THEN [k.s EXCEPT !.seen = @ \cup {p.pn}] ELSE k.s
        hasMsg == proc /\ m # NONE
        acts == hasMsg /\ Acts(m, k.sel)
    IN [s |-> IF acts THEN RekeyRx(s1, m, n) ELSE s1, s1 |-> s1, k |-> k, proc |-> proc, hasMsg |-> hasMsg, acts |-> acts]

(* ---- the system ---- *)

(* roll_tick *)
Begin(n) ==
    LET s == nd[n]
    IN /\ s.ctr < CtrCap(n) /\ CanBegin(s, n)
       /\ nd' = [nd EXCEPT ![n] = BeginOp(s, n)]
       /\ ev' = [t |-> "begin", n |-> n]
       /\ UNCHANGED <<net, now, slog, comp>>

(* a packet sealed under the sending key, carrying the polled REKEY message if any (withPl) *)
SendPkt(n, withPl) ==
    LET o == SendOp(nd[n], now, PTO, withPl, n)
        p == o.p
    IN /\ p.pn <= MaxPn
       /\ o.ok
       /\ nd' = [nd EXCEPT ![n] = o.s]
       /\ net' = net \cup {p}
       /\ slog' = slog \cup {[n |-> n, sec |-> p.sec, g |-> nd[n].sk.g, pn |-> p.pn]}
       /\ ev' = [t |-> "send", n |-> n, p |-> p]
       /\ UNCHANGED <<now, comp>>

(* the network delivers packet p to node n (forged: with its phase bit flipped by the attacker) *)
Deliver(n, p, forged) ==
    LET s0 == nd[n]
        o == DeliverOp(s0, p, forged, now, PTO, n)
        k == o.k
        m == p.pl
        done == o.hasMsg /\ m.ans /\ ROnAnswer(o.s1.roll, m).res = "ok"
    IN /\ p \in net /\ p.from = Peer(n) /\ (forged => ForgeOn)
       /\ (o.acts /\ ~m.ans) => CanRx(o.s1, m, n)
       /\ nd' = [nd EXCEPT ![n] = o.s]
       /\ comp' = IF done THEN comp \cup {[n |-> n, dh |-> ROnAnswer(o.s1.roll, m).dh, gdh |-> m.gdh, to |-> m.to,
                                              req |-> o.s1.roll.req.sh]}
                  ELSE comp
       /\ ev' = [t |-> "deliver", n |-> n, p |-> p, forged |-> forged, acc |-> k.acc, sel |-> k.sel, proc |-> o.proc]
       /\ UNCHANGED <<net, now, slog>>

(* loss detection queues a lost answer again, or marks a lost request *)
RequeueAnswer(n) ==
    /\ nd[n].out = NONE /\ nd[n].lastAns # NONE
    /\ nd' = [nd EXCEPT ![n] = RequeueAns(@)]
    /\ ev' = [t |-> "requeue", n |-> n]
    /\ UNCHANGED <<net, now, slog, comp>>

RequestLost(n) ==
    /\ nd[n].reqAt # NOTIME
    /\ nd' = [nd EXCEPT ![n] = RequestLostOp(@)]
    /\ ev' = [t |-> "reqlost", n |-> n]
    /\ UNCHANGED <<net, now, slog, comp>>

Tick == /\ now < MaxTime /\ now' = now + 1 /\ ev' = [t |-> "tick"] /\ UNCHANGED <<nd, net, slog, comp>>

Next == \/ \E n \in Nodes : Begin(n) \/ SendPkt(n, TRUE) \/ SendPkt(n, FALSE) \/ RequeueAnswer(n) \/ RequestLost(n)
        \/ \E n \in Nodes, p \in net, f \in BOOLEAN : Deliver(n, p, f)
        \/ Tick

Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------- invariants *)
Gens == {nd[n].sk.g : n \in Nodes} \cup {nd[n].cur.g : n \in Nodes}

TypeOK == /\ now \in 0..MaxTime
          /\ \A n \in Nodes : /\ nd[n].sk.g \in 0..Sat /\ nd[n].cur.g \in 0..Sat
                              /\ nd[n].roll.st \in {"idle", "req"} /\ nd[n].roll.rolls \in 0..Sat
                              /\ nd[n].npn \in 0..(MaxPn + 1)

GenIsDepth == \A n \in Nodes : \A x \in {nd[n].sk, nd[n].cur} : x.g = Depth(x.sec)

(* the phase bit is the parity of the generation, for every key held *)
PhaseParity == \A n \in Nodes :
    /\ nd[n].sph = (nd[n].sk.g % 2 = 1) /\ nd[n].rph = (nd[n].cur.g % 2 = 1)
    /\ nd[n].stg # NONE => nd[n].stg.g = nd[n].sk.g + 1
    /\ nd[n].nxt # NONE => nd[n].nxt.k.g = nd[n].cur.g + 1
    /\ nd[n].prev # NONE => nd[n].prev.k.g + 1 = nd[n].cur.g

(* both peers stay in step: every sending and receiving generation differs from another by at most one *)
InStep == \A x, y \in Gens : x - y <= 1 /\ y - x <= 1

(* the keys of one direction: what the sender holds and what the receiver holds *)
Held(n) == {nd[n].sk} \cup (IF nd[n].stg = NONE THEN {} ELSE {nd[n].stg})
           \cup {nd[Peer(n)].cur} \cup (IF nd[Peer(n)].prev = NONE THEN {} ELSE {nd[Peer(n)].prev.k})
           \cup (IF nd[Peer(n)].nxt = NONE THEN {} ELSE {nd[Peer(n)].nxt.k})

(* agreement on the keys: two keys of one direction of the same generation are the same secret *)
KeysAgree == \A n \in Nodes : \A x, y \in Held(n) : x.g = y.g => x.sec = y.sec

(* no (secret, packet number) is sealed twice, the numbers of a node increase, the sending generation of a node
   never goes back: the old sending key never seals after the switch *)
NoKeyReuse ==
    \A x, y \in slog : (x.n = y.n /\ x.pn < y.pn) => x.g <= y.g
(* a seal never repeats a (secret, packet number) pair and a node's numbers increase *)
FreshSeal == [][ev'.t = "send" => (\A x \in slog : ~(x.sec = ev'.p.sec /\ x.pn = ev'.p.pn)
                                  /\ (x.n = ev'.n => x.pn < ev'.p.pn))]_vars

(* every request share is used for one roll, every answer share for one answer *)
SharesOnce == /\ \A x, y \in comp : x.req = y.req => x = y
              /\ \A n \in Nodes : nd[n].roll.rolls = nd[n].chg

(* the old key is held exactly one PTO: its deadline is the promotion time plus PTO *)
HoldOnePTO == \A n \in Nodes : nd[n].prev # NONE => nd[n].prev.until = nd[n].promAt + PTO

(* when both complete a roll they computed the same Diffie-Hellman value *)
AgreeDh == \A x \in comp : x.dh = x.gdh

(* the floor in an answer is a true floor: every packet the peer sealed under the staged next key has a number at or
   above it *)
FloorHonoured == \A n \in Nodes : nd[n].nxt # NONE =>
    \A p \in net : (p.from = Peer(n) /\ p.sec = nd[n].nxt.k.sec) => p.pn >= nd[n].nxt.floor

(* Post-compromise, symbolically (KeyRoll.post_compromise in Lean): an attacker that stole the base secrets of both
   directions, owns no atom (both nodes are honest) and stays passive during the roll. A rolled secret is known iff the
   secret it rolls and the bound Diffie-Hellman value are; the identifier is a hash of a public share. With bx the
   attacker breaks X25519: it computes the Diffie-Hellman value from the two shares, which it reads from the REKEY
   messages (they travel under the current keys, which it holds). *)
RECURSIVE KnownSec(_, _)
KnownSec(t, bx) ==
    CASE t.t = "base" -> TRUE
      [] t.t = "roll" -> KnownSec(t.s, bx) /\ KnownSec(t.dh, bx)
      [] t.t = "bound" -> KnownSec(t.id, bx) /\ KnownSec(t.dh, bx)
      [] t.t = "id" -> TRUE
      [] t.t = "dh" -> bx
      [] OTHER -> FALSE
KeysHeld(n) == {nd[n].sk, nd[n].cur} \cup (IF nd[n].stg = NONE THEN {} ELSE {nd[n].stg})
               \cup (IF nd[n].prev = NONE THEN {} ELSE {nd[n].prev.k}) \cup (IF nd[n].nxt = NONE THEN {} ELSE {nd[n].nxt.k})
(* every key after a roll is secret again *)
PostCompromise == \A n \in Nodes : \A k \in KeysHeld(n) : k.g >= 1 => ~KnownSec(k.sec, FALSE)
(* the same with X25519 broken: false after the first roll (KeyRoll_xbroken), the roll is a fresh X25519 exchange only *)
PostCompromiseX == \A n \in Nodes : \A k \in KeysHeld(n) : k.g >= 1 => ~KnownSec(k.sec, TRUE)

Good == /\ \A n \in Nodes : nd[n].roll.st = "idle" /\ nd[n].stg = NONE /\ nd[n].nxt = NONE /\ nd[n].prev = NONE
        /\ nd[0].sk.g = nd[1].cur.g /\ nd[1].sk.g = nd[0].cur.g /\ nd[0].sk.g >= 1 /\ nd[1].sk.g >= 1

NotGood == ~Good

(* a node holds staged keys for a roll the peer never took and no longer can: the peer is idle with nothing
   staged and on the old generation *)
Orphan == \E n \in Nodes :
    /\ nd[n].stg # NONE /\ nd[Peer(n)].roll.st = "idle" /\ nd[Peer(n)].nxt = NONE
    /\ nd[Peer(n)].cur.g = nd[n].sk.g /\ nd[Peer(n)].sk.g = nd[n].sk.g
NoOrphan == ~Orphan

(* ---------------------------------------------------------- action properties *)
(* a packet is accepted iff the receiver holds the key it was sealed under: the current one, the previous one
   within its hold (the key is dropped at its deadline) and below the first number of the phase, or the staged
   next one at or above its floor *)
Holds(s, p, t) ==
    \/ p.sec = s.cur.sec
    \/ s.prev # NONE /\ t < s.prev.until /\ p.pn < s.first /\ p.sec = s.prev.k.sec
                     /\ ~(s.nxt # NONE /\ p.pn >= s.nxt.floor)
    \/ s.nxt # NONE /\ p.pn >= s.nxt.floor /\ p.sec = s.nxt.k.sec

AcceptIff == [][ev'.t = "deliver" /\ ~ev'.forged => (ev'.acc <=> Holds(nd[ev'.n], ev'.p, now))]_vars

(* a packet is never accepted under a key of another secret: the secret of an accepted packet is one the
   receiver holds (the previous one only before its deadline) *)
Held1(s, t) == {s.cur.sec} \cup (IF s.prev # NONE /\ t < s.prev.until THEN {s.prev.k.sec} ELSE {})
               \cup (IF s.nxt = NONE THEN {} ELSE {s.nxt.k.sec})
NeverOtherKey == [][ev'.t = "deliver" /\ ev'.acc => ev'.p.sec \in Held1(nd[ev'.n], now)]_vars

(* the previous key is accepted before its deadline and refused from it on *)
OldKeyOnePTO == [][ev'.t = "deliver" /\ ev'.sel = "prev" /\ ev'.acc => now < nd[ev'.n].prev.until]_vars

ZK(k) == [k EXCEPT !.fc = 0]
ZS(x) == [x EXCEPT !.k = ZK(x.k)]
Strip(s) == [s EXCEPT !.cur = ZK(@), !.sk = ZK(@), !.stg = IF @ = NONE THEN NONE ELSE ZK(@),
                      !.prev = IF @ = NONE THEN NONE ELSE ZS(@),
                      !.nxt = IF @ = NONE THEN NONE ELSE ZS(@)]
FCs(s) == s.cur.fc + s.sk.fc + (IF s.prev = NONE THEN 0 ELSE s.prev.k.fc) + (IF s.nxt = NONE THEN 0 ELSE s.nxt.k.fc)

(* a forged phase bit is never accepted, costs at most one failed open, and changes nothing else (the previous
   key may expire, as it would on any packet) *)
ForgedCostsOneOpen ==
    [][ev'.t = "deliver" /\ ev'.forged =>
        /\ ~ev'.acc
        /\ nd'[ev'.n].seen = nd[ev'.n].seen
        /\ Strip(nd'[ev'.n]) = Strip(Expire(nd[ev'.n], now))
        /\ FCs(nd'[ev'.n]) - FCs(Expire(nd[ev'.n], now))
             = (IF ev'.sel = "err" \/ SlotKey(Expire(nd[ev'.n], now), ev'.sel).fc >= Sat THEN 0 ELSE 1)
        /\ \A m \in Nodes : m # ev'.n => nd'[m] = nd[m]]_vars

(* the sending generation and the receiving generation only move forward, by one *)
GenMonotone == [][\A n \in Nodes : /\ nd'[n].sk.g \in {nd[n].sk.g, nd[n].sk.g + 1}
                                   /\ nd'[n].cur.g \in {nd[n].cur.g, nd[n].cur.g + 1}]_vars

(* the floor of a staged next key does not change while it is staged (a packet that promotes it may stage the
   next one in the same step) *)
FloorsRespected ==
    [][\A n \in Nodes : (nd[n].nxt # NONE /\ nd'[n].nxt # NONE /\ ~(ev'.t = "deliver" /\ ev'.n = n /\ ev'.sel = "next" /\ ev'.acc))
                        => nd'[n].nxt.floor = nd[n].nxt.floor]_vars

(* a duplicate request is answered with the same answer and creates no key *)
DupRequestAnswered ==
    [][ev'.t = "deliver" /\ ~ev'.forged /\ ev'.proc /\ ev'.p.pl # NONE /\ ~ev'.p.pl.ans
       /\ IsDup(nd[ev'.n].roll, ev'.p.pl)
       /\ ev'.sel # "prev"
       => (nd'[ev'.n].out = nd[ev'.n].roll.last.ans /\ nd'[ev'.n].chg = nd[ev'.n].chg)]_vars

(* the dialer wins a collision: the dialer ignores the acceptor's request while its own is out; the acceptor
   drops its own request and answers *)
DialerWins ==
    [][ev'.t = "deliver" /\ ~ev'.forged /\ ev'.proc /\ ev'.p.pl # NONE /\ ~ev'.p.pl.ans /\ ev'.sel # "prev"
       /\ nd[ev'.n].roll.st = "req" /\ ~IsDup(nd[ev'.n].roll, ev'.p.pl) /\ nd[ev'.n].nxt = NONE
       => IF nd[ev'.n].roll.dialer
          THEN nd'[ev'.n].roll = nd[ev'.n].roll /\ nd'[ev'.n].stg = NONE
          ELSE nd'[ev'.n].roll.st = "idle" /\ nd'[ev'.n].out # NONE]_vars

(* an answer while no request is out changes no key (a packet that promotes the staged key still does) *)
StaleAnswerNoKey ==
    [][ev'.t = "deliver" /\ ev'.proc /\ ev'.sel # "next" /\ ev'.p.pl # NONE /\ ev'.p.pl.ans /\ nd[ev'.n].roll.st = "idle"
       => (nd'[ev'.n].sk = nd[ev'.n].sk /\ nd'[ev'.n].chg = nd[ev'.n].chg)]_vars
=============================================================================
