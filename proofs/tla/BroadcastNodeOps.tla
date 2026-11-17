---------------------------- MODULE BroadcastNodeOps ----------------------------
(***************************************************************************)
(* The receive path of one vinc-broadcast node, as pure operators: the     *)
(* functions of msg.rs (on_msg, hub_store, offer, offer_held, deliver,     *)
(* acp_answer), floors.rs (is_old, hold_for_floor, floor_check), timers.rs *)
(* (sweep, poll_timeout) and table.rs (Seen) over one topic. A node state  *)
(* is a record; every operator returns a result record                     *)
(*   [n |-> the new state, outs |-> the trace records emitted, in order,   *)
(*    dl |-> the ids delivered to the application, in order,               *)
(*    ack |-> PACK frames sent, acc |-> ids accounted for]                 *)
(* so BroadcastNode (the model), BroadcastSystem (the scenarios) and       *)
(* TraceBroadcast (the recorded runs of the real code) call one            *)
(* definition of each step.                                                *)
(*                                                                         *)
(* Abstractions, each exact for what is checked: a message is the record   *)
(* [mid, origin, ts, kind, n] where kind says what the checks before the   *)
(* signature find (good, badhead: the head does not parse, big: the body   *)
(* is over the receiver's limit, badsig: the signature does not cover the  *)
(* topic, id and body; BroadcastAuth establishes when that is the case;    *)
(* graft: the id and signature of a stored message under another body,     *)
(* which never verifies as a new message),                                 *)
(* ts is the hybrid timestamp as one totally ordered number, n is the      *)
(* size of head and body in the log ring, and the signature's verdict is   *)
(* the oracle's. The slot arrays behind Seen are the association           *)
(* BroadcastMidMap proves them to be. The transmission of a stored         *)
(* message (push, mirror) and the replay floors the hub keeps are in       *)
(* BroadcastRepair and BroadcastFloors.                                    *)
(*                                                                         *)
(* HeldDedup, HeldFullKeepsUnseen, AckAfterStore and EvictGuard select the behaviour   *)
(* of the code after its fixes (TRUE) or before them (FALSE): a message    *)
(* that waits for an access-control answer is held once and a full held    *)
(* set leaves the id unseen; a hub acknowledges only a message it stored.  *)
(* The configs ending in _heldDup, _heldFull, _ackEarly, _evict are the    *)
(* witnesses that TLC finds the violations in the old behaviour.           *)
(* TopicFull: the topic table has no room for this topic.                  *)
(*                                                                         *)
(* A message also has a body (an opaque value: the body hash and the flag  *)
(* the signature covers). A hub keeps the print of each message it stored  *)
(* in `store`, set when the message is stored: here the content (origin,   *)
(* timestamp, body), which the signature binds, so two messages have the   *)
(* same print exactly when their content is equal and the signature of the *)
(* second verifies (kind "good"; the print is 64 bits in the code, an      *)
(* assumption). The print lives in the log while the message is logged and *)
(* in the dedupe map after the log let it go; an id that neither holds     *)
(* has no meaningful entry and Tidy drops it. A known id (a duplicate) due *)
(* an acknowledgement (a PUB or FANP at a hub) is compared with the print  *)
(* held for it: the same print is acknowledged, another is refused with    *)
(* IdTaken and no acknowledgement, after the log let the message go as     *)
(* well as while it holds it. A copy due none is a plain duplicate and     *)
(* compares nothing. A graft of the stored message carries the stored    *)
(* print, so it is acknowledged like the message itself when due; a graft  *)
(* for an id the hub holds no print for (a hub's own id the log refused,   *)
(* Own below) is answered IdTaken and not acknowledged; a graft is stored, *)
(* forwarded and delivered never (its signature fails as a new message).   *)
(* KeepPrint = FALSE (compare only while the id is logged), DueOnly =      *)
(* FALSE (compare every copy), GraftStored = FALSE (a graft is            *)
(* acknowledged whatever the hub holds) and AckById (acknowledge any known *)
(* id, the old rule) are the rules before the fix, kept as the witnesses   *)
(* of BroadcastNode.                                                       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS TTL, SeenCap, LogRing, LogCap, LogWin, FholdMax, HeldMax, ChecksMax, AcpCap, AcpMax, FloorWait, OldSlack,
          Mids, Origins, Me, IsHub, Revoked, HeldDedup, HeldFullKeepsUnseen, TopicFull, AckAfterStore, Gather, EvictGuard, LogTrack, AckById, KeepPrint, DueOnly, GraftStored

LG == INSTANCE BroadcastLogOps WITH Ring <- LogRing, Cap <- LogCap, Window <- LogWin, Track <- LogTrack

NoT == -1
NoAcp == [none |-> TRUE]
NoOf == [none |-> TRUE]
NoM == [none |-> TRUE]
Sub(a, b) == IF a >= b THEN a - b ELSE 0

(* ---- table.rs Seen: the association of ids to the time they were recorded, in insertion order ---- *)
SeenEmpty == [map |-> [x \in Mids |-> NoT], order |-> <<>>, last |-> 0]
SContains(S, mid, now) == S.map[mid] # NoT /\ Sub(now, S.map[mid]) <= TTL
SLen(S) == Len(S.order)
SNewest(S) == IF S.order = <<>> THEN NoT ELSE S.last
SNextExpiry(S) == IF S.order = <<>> THEN NoT ELSE Head(S.order)[2] + TTL + 1
SPopFront(S) ==
    LET e == Head(S.order)
    IN [S EXCEPT !.order = Tail(@), !.map = IF S.map[e[1]] = e[2] THEN [@ EXCEPT ![e[1]] = NoT] ELSE @]
RECURSIVE SExpire(_, _)
SExpire(S, now) == IF S.order # <<>> /\ Sub(now, Head(S.order)[2]) > TTL THEN SExpire(SPopFront(S), now) ELSE S
SMapLen(S) == Cardinality({x \in Mids : S.map[x] # NoT})
SPush(S, mid, now) ==
    IF S.map[mid] # NoT \/ SMapLen(S) < SeenCap
    THEN [s |-> [S EXCEPT !.map[mid] = now, !.order = Append(@, <<mid, now>>), !.last = now], ok |-> TRUE]
    ELSE [s |-> S, ok |-> Assert(FALSE, "the map refused an id the set had room for")]
\* Seen::insert: a full set refuses unless forced, which drops the oldest id first
SInsert(S, mid, now, force) ==
    IF Len(S.order) >= SeenCap
    THEN IF ~force THEN [s |-> S, ok |-> FALSE] ELSE SPush(SPopFront(S), mid, now)
    ELSE SPush(S, mid, now)
RECURSIVE SInsertAll(_, _, _)
\* an evicted id is recorded unless the set still holds it: a second record at the same instant would leave the id
\* forgotten when the first record is popped (EvictGuard is the code after the fix)
SInsertAll(S, ids, now) ==
    IF ids = <<>> THEN S
    ELSE SInsertAll(IF EvictGuard /\ SContains(S, Head(ids), now) THEN S ELSE SInsert(S, Head(ids), now, TRUE).s, Tail(ids), now)

(* ---- the node state ---- *)
NodeInit(born) ==
    [seen |-> SeenEmpty, lg |-> LG!EmptyLog, sub |-> TRUE, req |-> {},
     phase |-> IF IsHub THEN "never" ELSE IF Gather THEN "gathering" ELSE "done", rfloor |-> NoT, ofloor |-> NoOf, nohist |-> FALSE,
     fhold |-> <<>>, acp |-> [o \in Origins |-> NoAcp], checks |-> <<>>, nextCheck |-> 1, held |-> <<>>, born |-> born, store |-> [x \in Mids |-> NoM]]

Res(n, outs, dl, ack, acc) == [n |-> n, outs |-> outs, dl |-> dl, ack |-> ack, acc |-> acc]
Plain(n, outs) == Res(n, outs, <<>>, 0, {})
Bind(r, F(_)) ==
    LET r2 == F(r.n)
    IN Res(r2.n, r.outs \o r2.outs, r.dl \o r2.dl, r.ack + r2.ack, r.acc \union r2.acc)
Rejected(mid, why) == [k |-> "Rejected", mid |-> mid, why |-> why]

(* ---- floors.rs is_old ---- *)
IsOld(N, origin, ts) ==
    IF N.ofloor # NoOf THEN N.ofloor[origin] # NoT /\ ts <= N.ofloor[origin]
    ELSE IF N.rfloor # NoT /\ ts <= N.rfloor THEN TRUE
    ELSE N.rfloor = NoT /\ ~N.nohist /\ ts + OldSlack < N.born

(* ---- floors.rs hold_for_floor ---- *)
HoldFloor(N, m) ==
    IF Len(N.fhold) >= FholdMax \/ \E i \in 1..Len(N.fhold) : N.fhold[i].mid = m.mid THEN Plain(N, <<>>)
    ELSE Plain([N EXCEPT !.fhold = Append(@, [mid |-> m.mid, origin |-> m.origin, ts |-> m.ts])],
               <<[k |-> "Held", mid |-> m.mid, why |-> "Floor"]>>)

(* ---- msg.rs offer ---- *)
AskedFor(N, o) == \E i \in 1..Len(N.checks) : N.checks[i].origin = o
HeldHas(N, mid) == \E i \in 1..Len(N.held) : N.held[i].mid = mid

\* the part of offer after the verdict cache missed: hold the message and ask
HoldAndAsk(N, m) ==
    LET dupHeld == HeldDedup /\ HeldHas(N, m.mid)
        heldOK == Len(N.held) < HeldMax /\ ~dupHeld
        N2 == IF heldOK THEN [N EXCEPT !.held = Append(@, [mid |-> m.mid, origin |-> m.origin, ts |-> m.ts])] ELSE N
        ask == ~AskedFor(N2, m.origin) /\ Len(N2.checks) < ChecksMax
        N3 == IF ask THEN [N2 EXCEPT !.checks = Append(@, [id |-> N2.nextCheck, origin |-> m.origin]), !.nextCheck = @ + 1] ELSE N2
    IN Res(N3, (IF heldOK THEN <<[k |-> "Held", mid |-> m.mid, why |-> "Acp"]>> ELSE <<>>)
               \o (IF ask THEN <<[k |-> "AcpAsked", id |-> N2.nextCheck, origin |-> m.origin]>> ELSE <<>>),
           <<>>, 0, IF heldOK \/ dupHeld \/ HeldFullKeepsUnseen THEN {m.mid} ELSE {})

Offer(N, now, m) ==
    IF TopicFull THEN Res(N, <<Rejected(m.mid, "TopicsFull")>>, <<>>, 0, {m.mid})
    ELSE IF Len(N.seen.order) >= SeenCap THEN Res(N, <<Rejected(m.mid, "SeenFull")>>, <<>>, 0, {m.mid})
    ELSE LET old == IsOld(N, m.origin, m.ts)
             a == N.acp[m.origin]
             cached == a # NoAcp /\ a.exp >= now
             needsHold == N.sub /\ ~old /\ m.origin # Me /\ ~cached
             full == needsHold /\ HeldFullKeepsUnseen /\ Len(N.held) >= HeldMax /\ ~(HeldDedup /\ HeldHas(N, m.mid))
         IN IF N.phase = "gathering" /\ ~IsHub THEN HoldFloor(N, m)
            ELSE IF full
                 THEN \* the held set is full: ask the check, leave the id unseen so the gap repair brings it again
                      LET r == HoldAndAsk(N, m)
                      IN Res(r.n, r.outs \o <<Rejected(m.mid, "HeldFull")>>, <<>>, 0, {m.mid})
            ELSE LET N1 == [N EXCEPT !.seen = SInsert(N.seen, m.mid, now, FALSE).s]
                 IN IF ~N.sub \/ old \/ m.origin = Me
                    THEN Res(N1, IF old THEN <<Rejected(m.mid, "Old")>> ELSE <<>>, <<>>, 0, {m.mid})
                    ELSE IF cached
                         THEN IF a.allow
                              THEN Res(N1, <<[k |-> "Delivered", mid |-> m.mid, origin |-> m.origin, ts |-> m.ts, via |-> "cache"]>>, <<m.mid>>, 0, {m.mid})
                              ELSE Res(N1, <<>>, <<>>, 0, {m.mid})
                         ELSE HoldAndAsk(N1, m)

(* ---- msg.rs offer_held: a message held for the floors is offered again unless it arrived another way meanwhile ---- *)
IsDup(N, mid, now) == SContains(N.seen, mid, now) \/ LG!Contains(N.lg, mid)
OfferHeld(N, now, e) == IF IsDup(N, e.mid, now) THEN Plain(N, <<>>) ELSE Offer(N, now, e)

RECURSIVE OfferAll(_, _, _)
OfferAll(r, now, es) == IF es = <<>> THEN r ELSE OfferAll(Bind(r, LAMBDA x: OfferHeld(x, now, Head(es))), now, Tail(es))

(* ---- floors.rs floor_check: the floors are settled (or the wait ran out): offer what was held ---- *)
FloorsSettled(N, now, used, rf, of, nh) ==
    LET N1 == [N EXCEPT !.phase = "done", !.rfloor = rf, !.ofloor = of, !.nohist = nh, !.fhold = <<>>]
    IN OfferAll(Plain(N1, <<[k |-> "FloorDone", used |-> used]>>), now, N.fhold)

(* ---- msg.rs hub_store ---- *)
HubStore(N, now, wall, fanned, m) ==
  IF TopicFull THEN Plain(N, <<Rejected(m.mid, "TopicsFull")>>)
  ELSE
    LET r == LG!Push(N.lg, m.mid, now, wall, m.n)
        N1 == [N EXCEPT !.seen = SInsertAll(N.seen, r.ev, now), !.lg = r.log]
    IN IF ~r.ok THEN Plain(N1, <<Rejected(m.mid, "LogFull")>>)
       ELSE LET st == <<[k |-> "Stored", mid |-> m.mid, fanned |-> fanned]>>
            IN IF N1.sub /\ m.origin # Me
               THEN Bind(Plain(N1, st), LAMBDA x: Offer(x, now, m))
               ELSE Res([N1 EXCEPT !.seen = SInsert(N1.seen, m.mid, now, TRUE).s], st, <<>>, 0, {m.mid})

\* the print held for each id the log or the dedupe map holds; the entry of an id neither holds means nothing
Tidy(N) == [N EXCEPT !.store = [x \in Mids |-> IF LG!Contains(N.lg, x) \/ N.seen.map[x] # NoT THEN N.store[x] ELSE NoM]]
Content(m) == [origin |-> m.origin, ts |-> m.ts, body |-> m.body]
\* the print a frame carries: a good frame's is its content; a graft (the id and signature of a stored message under
\* another body) carries the print stored under its id; the other kinds carry none that is compared
PrintOf(N, m) == IF m.kind = "graft" THEN N.store[m.mid] ELSE Content(m)
\* the frame carries the print held for its id, and the signature it carries verifies against it
\* (a graft for an id with no print held is another message's: GraftStored = FALSE is the rule before the fix)
Same(N, m) == (m.kind = "good" /\ N.store[m.mid] = Content(m)) \/ (m.kind = "graft" /\ (~GraftStored \/ N.store[m.mid] # NoM))

(* ---- publish.rs: the hub records its own message's id, then hub_store stores it or refuses it (a message over the
   ring is LogFull), which leaves the id known with no print held ---- *)
Own(N, now, wall, m) ==
    LET r == HubStore([N EXCEPT !.seen = SInsert(N.seen, m.mid, now, TRUE).s], now, wall, FALSE, m)
    IN IF \E i \in 1..Len(r.outs) : r.outs[i].k = "Stored"
       THEN [r EXCEPT !.n.store = [@ EXCEPT ![m.mid] = Content(m)]]
       ELSE r

(* ---- msg.rs on_msg: a known id ---- *)
\* a copy due an acknowledgement (ack = 1) is compared with the print held for the id, while the log holds the id and,
\* with KeepPrint, after it let it go; DueOnly = FALSE compares every copy. The same print is a duplicate that is
\* acknowledged, another is IdTaken with none; an id that is not compared is a plain duplicate with none.
Dup(N, m, ack) ==
    LET look == (KeepPrint \/ LG!Contains(N.lg, m.mid)) /\ (ack = 1 \/ ~DueOnly)
        same == Same(N, m)
    IN IF AckById THEN Res(N, <<Rejected(m.mid, "Duplicate")>>, <<>>, ack, {})
       ELSE IF look /\ ~same THEN Res(N, <<Rejected(m.mid, "IdTaken")>>, <<>>, 0, {})
       ELSE Res(N, <<Rejected(m.mid, "Duplicate")>>, <<>>, IF look THEN ack ELSE 0, {})

(* ---- msg.rs on_msg ---- *)
Allowed(t, fromBoot) == IF t \in {"PUB", "FAN", "FANP"} THEN IsHub ELSE IF t = "MSG" THEN fromBoot ELSE TRUE

OnMsg(N, now, wall, t, fromBoot, m) ==
    IF ~Allowed(t, fromBoot) THEN Plain(N, <<>>)
    ELSE IF m.kind = "badhead" THEN Plain(N, <<Rejected(0, "BadHead")>>)
    ELSE IF m.kind = "big" THEN Plain(N, <<Rejected(m.mid, "BadHead")>>)
    ELSE LET ack == IF IsHub /\ t \in {"PUB", "FANP"} THEN 1 ELSE 0
         IN IF IsDup(N, m.mid, now)
            THEN Dup(N, m, ack)
            ELSE IF m.origin \in Revoked THEN Plain(N, <<Rejected(m.mid, "Revoked")>>)
            ELSE IF m.kind \in {"badsig", "graft"} THEN Plain(N, <<Rejected(m.mid, "BadSignature")>>)
            ELSE LET rep == m.mid \in N.req
                     N1 == [N EXCEPT !.req = @ \ {m.mid}]
                     o1 == IF rep THEN <<[k |-> "Repaired", mid |-> m.mid]>> ELSE <<>>
                     early == IF AckAfterStore THEN 0 ELSE ack
                     r0 == Res(N1, o1, <<>>, early, {})
                     stored(r) == \E i \in 1..Len(r.outs) : r.outs[i].k = "Stored"
                     late(r) == IF AckAfterStore /\ stored(r) THEN ack ELSE 0
                     rh == Bind(r0, LAMBDA x: HubStore(x, now, wall, t \in {"FAN", "FANP"}, m))
                     fin == [rh EXCEPT !.ack = @ + late(rh)]
                 IN IF IsHub
                    THEN IF stored(rh) THEN [fin EXCEPT !.n.store = [@ EXCEPT ![m.mid] = Content(m)]] ELSE fin
                    ELSE Bind(r0, LAMBDA x: Offer(x, now, m))

(* ---- gap.rs on_have: the ids this node lacks are asked for and remembered as requested ---- *)
OnHave(N, now, fromBoot, ids) ==
    IF ~fromBoot THEN Plain(N, <<>>)
    ELSE Plain([N EXCEPT !.req = @ \union {ids[i] : i \in {j \in 1..Len(ids) : ~SContains(N.seen, ids[j], now) /\ ~LG!Contains(N.lg, ids[j])}}], <<>>)

(* ---- msg.rs acp_answer ---- *)
FindCheck(N, id) == IF \E i \in 1..Len(N.checks) : N.checks[i].id = id
                    THEN CHOOSE i \in 1..Len(N.checks) : N.checks[i].id = id ELSE 0
AcpAnswer(N, now, id, allow) ==
    LET pos == FindCheck(N, id)
    IN IF pos = 0 THEN Plain(N, <<>>)
       ELSE LET origin == N.checks[pos].origin
                cached == AcpMax > Cardinality({o \in Origins : N.acp[o] # NoAcp})
                acp1 == IF N.acp[origin] # NoAcp \/ cached THEN [N.acp EXCEPT ![origin] = [allow |-> allow, exp |-> now + AcpCap]] ELSE N.acp
                mine == SelectSeq(N.held, LAMBDA e: e.origin = origin)
                N1 == [N EXCEPT !.checks = SubSeq(@, 1, pos - 1) \o SubSeq(@, pos + 1, Len(@)), !.acp = acp1,
                                !.held = SelectSeq(@, LAMBDA e: e.origin # origin)]
                dels == IF allow THEN [i \in 1..Len(mine) |-> mine[i].mid] ELSE <<>>
            IN Res(N1, <<[k |-> "AcpAnswered", id |-> id, allow |-> allow, origin |-> origin]>>
                       \o [i \in 1..Len(dels) |-> [k |-> "Delivered", mid |-> dels[i], origin |-> origin, ts |-> mine[i].ts, via |-> "answer"]],
                   dels, 0, {})

(* ---- timers.rs on_timer (sweep and the end of the floor wait) and poll_timeout ---- *)
RECURSIVE SweepIds(_, _, _)
SweepIds(S, ids, now) ==
    IF ids = <<>> THEN S
    ELSE SweepIds(IF SContains(S, Head(ids), now) THEN S ELSE SInsert(S, Head(ids), now, TRUE).s, Tail(ids), now)

Sweep(N, now) ==
    LET S1 == SExpire(N.seen, now)
        e == LG!Expire(N.lg, now)
    IN [N EXCEPT !.seen = SweepIds(S1, e.ev, now), !.lg = e.log]

OnTimer(N, now) ==
    LET N1 == Sweep(N, now)
    IN IF N1.phase = "gathering" /\ Sub(now, N1.born) > FloorWait
       THEN FloorsSettled(N1, now, FALSE, NoT, NoOf, FALSE)
       ELSE Plain(N1, <<>>)

MinOf(S) == IF S = {} THEN NoT ELSE CHOOSE x \in S : \A y \in S : x <= y
PollTimeout(N) ==
    MinOf({t \in {SNextExpiry(N.seen), IF N.lg.entries = <<>> THEN NoT ELSE N.lg.entries[1].at + LogWin + 1,
                  IF N.phase = "gathering" THEN N.born + FloorWait + 1 ELSE NoT} : t # NoT})
=============================================================================
