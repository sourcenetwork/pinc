------------------------------- MODULE HalfOpen ------------------------------
(***************************************************************************)
(* The endpoint's cap on half-open sessions and their lifetime (pinc-core  *)
(* rx.rs, events.rs, endpoint.rs, timers.rs), over every interleaving of   *)
(* first flights of any type and length, for an id no session holds or     *)
(* one that sessions hold, resumptions, establishment, the end of a        *)
(* connection, inputs that move a session's own deadline, dials, a stalled *)
(* event queue and timer calls, at any times (a clock that steps back      *)
(* included), at small sizes (HalfOpenOps.tla has the operators). ids[j]   *)
(* is the id the session in slot j was made under (0 for a free slot and a *)
(* dial); the sessions that hold an id are its holders.                    *)
(*                                                                         *)
(* With QCAP > 0 the host's accept queue is in the model too (pinc         *)
(* engine.rs session_up, sync_backlog; ops.rs accept_route): QCAP is       *)
(* accept_sessions, q the sessions waiting in it, and the room the host    *)
(* gives the endpoint (set_backlog_room) is QCAP - q, set again at every   *)
(* change of q before anything else runs. ow are the sessions the endpoint *)
(* owes the host (Meta::owed, Endpoint::owed): a first flight that makes a *)
(* session adds it, the host reading its Incoming (session_taken) or its   *)
(* end removes it. pend are the sessions whose Incoming the host has yet   *)
(* to read; gone counts the Incomings of ended sessions the host will      *)
(* still queue (only the RED BUG_GONE has any). A sub-session's Incoming   *)
(* (SubUp) comes with no first flight. QCAP = 0 leaves all of this out.    *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the count never passes MAX (Capped) and is the number of counted     *)
(*    sessions (Exact); a counted session is unauthenticated and in use, a *)
(*    free slot holds nothing (Shape);                                     *)
(*  - an unauthenticated session holds a deadline at most its own life     *)
(*    after its creation, and that life is never above HOLD: LIFE, or HOLD *)
(*    once it answered as a responder (DeadlineBound), so poll_timeout is  *)
(*    never later than the end of any unauthenticated session, and none    *)
(*    while the event queue is stalled (PollBound);                        *)
(*  - a first flight that makes no session (a stalled queue, no room left  *)
(*    to accept, a type that starts nothing, the floor or the cap, a first *)
(*    packet the responder would only reject, no protocol, no free slot, a *)
(*    failed construction) changes nothing (RefusedRight);                 *)
(*  - a first packet the responder would only reject (a Hello whose ticket *)
(*    does not open, a short Initial of a prekey this node does not hold)  *)
(*    or not answer at all is answered by the endpoint without a session   *)
(*    and takes no slot (RejectedRight), so the cap is never reached by    *)
(*    such packets and a genuine first flight is never refused for the     *)
(*    sessions they made (GenuineServed);                                  *)
(*  - a session enters the count only when an admitted first flight that   *)
(*    does not resume makes it, and leaves it only when it is established, *)
(*    when its connection ends, or at a timer call at or after its end,    *)
(*    the first instant past its life (LeftRight);                         *)
(*  - a timer call that the event queue did not stop leaves no             *)
(*    unauthenticated session at or past its end (TimerRight);             *)
(*  - a session made by a resumption is not counted and one made by        *)
(*    anything else is; only a resumption is admitted at the cap, and only *)
(*    a Hello resumes (ResumeRight);                                       *)
(*  - no arrival frees or replaces a session: a session, the first holder  *)
(*    of its id included, leaves its slot only by a close or at a timer    *)
(*    call at or after its end or when its connection ended (HolderKept);  *)
(*  - an id never has more than MAXH holders, and a free slot holds no id  *)
(*    (HeldBound);                                                         *)
(*  - no first flight makes a session while the owed sessions fill the     *)
(*    room, a new holder of a held id included (HeldRight);                *)
(*  - the sessions waiting and those owed never pass QCAP (Placed), the    *)
(*    owed are exactly those whose Incoming the host has not read, all in  *)
(*    use (OwedExact), and no session that finished its handshake finds    *)
(*    the queue full and is closed as busy (NoBusy).                       *)
(* BUG_LE admits while count <= MAX and while the id has at most MAXH      *)
(* holders: the witnesses HalfOpen_le and HalfOpen_le_held break Capped    *)
(* and HeldBound. A session lives LIFE and is gone one tick past it, as    *)
(* the transport's own deadline is; BUG_GE frees it at LIFE itself, the    *)
(* endpoint's rule before: the witness HalfOpen_strict breaks LeftRight.   *)
(* BUG_LATE frees it one tick past its end: the witness HalfOpen_late      *)
(* breaks TimerRight.                                                      *)
(* BUG_REJ admits a first packet the responder would only reject, as the   *)
(* endpoint did: the witness HalfOpen_rej breaks RejectedRight, and        *)
(* HalfOpen_rejfill breaks GenuineServed (the cap reached by rejected      *)
(* packets alone, a genuine first flight refused). The life is a           *)
(* parameter, in units of 30 s: HalfOpen.cfg is a thin node (LIFE = HOLD = *)
(* 2: 60 s, answered or not) and HalfOpen_answer a node that is not thin   *)
(* (LIFE = 1, HOLD = 2: 30 s, 60 s once it answered). BUG_HOLD lets an     *)
(* answer hold the session past HOLD: the witness HalfOpen_hold breaks     *)
(* DeadlineBound. SUPERSEDE is                                             *)
(* the rule before #365: a first flight that the one holder of its id      *)
(* refused as a first flight other than its own freed that holder and      *)
(* went to the admission; the                                              *)
(* witness HalfOpen_supersede breaks HolderKept. HalfOpen_reach and        *)
(* HalfOpen_holders are reachability witnesses: a resumption is admitted   *)
(* while the count is at the cap; an id gets MAXH holders.                 *)
(* The accept room (pinc#436): HalfOpen_room checks it all, HalfOpen_room2 *)
(* at three slots and a queue of two. Each guard has a RED that breaks     *)
(* NoBusy: BUG_ROOM admits with no room (HalfOpen_noroom); BUG_EST stops   *)
(* owing a session at its establishment, before the host read its          *)
(* Incoming (HalfOpen_owedest); BUG_GONE has the host queue the Incoming   *)
(* of a session that ended before it was read, whose place went back when  *)
(* it ended (HalfOpen_gone); BUG_SUB lets a sub-session take a place held  *)
(* for an owed session (HalfOpen_sub). HalfOpen_roomreach is a witness: a  *)
(* first flight is refused for want of room.                               *)
(* Of the room the counted sessions (unauthenticated, not resumed) hold at *)
(* most half, rounded up (HalfCap): a first flight that does not resume    *)
(* makes a session only below it (HalfRight), so the counted sessions      *)
(* never pass half of QCAP (HalfRoom) and, with an empty queue of two      *)
(* places or more and only counted sessions owed, a resumption that could  *)
(* be made is made (ResumeOpen): first flights that never finish cannot    *)
(* keep out a peer that resumes. HalfOpen_half checks it at three slots,   *)
(* a cap of two and a queue of two; BUG_HALF is the rule before, the whole *)
(* room, and HalfOpen_flood breaks ResumeOpen with it.                     *)
(* Lean counterpart: proofs/lean/Pinc/CoreHalfOpen*.lean, and              *)
(* proofs/lean/Pinc/CoreBacklog*.lean for the room.                        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS K, MAX, LIFE, HOLD, FULL, SHORT, HELLO, TMAX, LENS, IDS, MAXH, BUG_LE, BUG_GE, SUPERSEDE,
          QCAP, BUG_ROOM, BUG_EST, BUG_GONE, BUG_SUB, BUG_HALF, BUG_HOLD, BUG_REJ, BUG_LATE
VARIABLES e, ids, stalled, refused, left, timed, resumed, atcap, kept, ow, pend, q, gone, busy, heldok, roomref,
          halfok, resok, rejok, genok, rs
\* the history flags of the half rule and of the rejected first packets, and the slots whose session a rejected packet
\* made: only Arrive changes them
hk == <<halfok, resok, rejok, genok, rs>>
bk == <<ow, pend, q, gone, busy, heldok, roomref, halfok, resok, rejok, genok, rs>>
vars == <<e, ids, stalled, refused, left, timed, resumed, atcap, kept, ow, pend, q, gone, busy, heldok, roomref,
          halfok, resok, rejok, genok, rs>>

INSTANCE HalfOpenOps

\* The ids up to a swap, for the invariants only (never a liveness property or a printed trace). Every slot starts with
\* id 0, outside IDS, so a swap fixes it; ids are read only by membership, equality and ranging over IDS (no
\* arithmetic, order or CHOOSE touches them) and no invariant names one, so a swap of the ids maps steps to steps.
IdPerms == Permutations(IDS)

Slots == 0..(K - 1)
\* the host set a room: the accept queue is modelled
Limited == QCAP > 0
Init == /\ e = [slots |-> Table0(K), count |-> 0] /\ ids = [j \in Slots |-> 0] /\ stalled = FALSE
        /\ refused = TRUE /\ left = TRUE /\ timed = TRUE /\ resumed = TRUE /\ atcap = FALSE /\ kept = TRUE
        /\ ow = {} /\ pend = {} /\ q = 0 /\ gone = 0 /\ busy = FALSE /\ heldok = TRUE /\ roomref = FALSE
        /\ halfok = TRUE /\ resok = TRUE /\ rejok = TRUE /\ genok = TRUE /\ rs = {}

\* rx.rs unrouted: the counted sessions may hold at most half of the room, rounded up, and never more than MAX (under
\* BUG_HALF, the rule before, the whole room: MAX alone bounds them)
HalfCap == IF Limited /\ ~BUG_HALF /\ Half(QCAP - q) < MAX THEN Half(QCAP - q) ELSE MAX
AdmitM(count, kind, len, resume) ==
    IF BUG_LE THEN len >= Floor(kind, FULL, SHORT, HELLO) /\ (resume \/ count <= MAX)
    ELSE Admit(count, kind, len, resume, HalfCap, FULL, SHORT, HELLO)
RoomM(held) == IF BUG_LE THEN held <= MAXH ELSE Room(held, MAXH)
\* rx.rs unrouted: a first flight may start a session only while the owed sessions leave room (owed < room)
Open == ~Limited \/ BUG_ROOM \/ Cardinality(ow) < QCAP - q

\* the sessions that hold id x
Holders(x) == {j \in Slots : e.slots[j].use /\ ids[j] = x}
\* the counted slots that stopped being counted, and those that started
Lost(x, y) == {j \in Slots : x.slots[j].counted /\ ~y.slots[j].counted}
Won(x, y) == {j \in Slots : ~x.slots[j].counted /\ y.slots[j].counted}
\* the sessions of x (ids xi) that are not in their slot in y (ids yi) any more: freed, or replaced by another
Ended(x, y, xi, yi) ==
    {j \in Slots : x.slots[j].use /\ ~(y.slots[j].use /\ y.slots[j].created = x.slots[j].created /\ yi[j] = xi[j])}
\* the slots of x freed in y
Freed(x, y) == {j \in Slots : x.slots[j].use /\ ~y.slots[j].use}
\* sessions R of x end (endpoint.rs free_slot): they are owed no more and the host never reads their Incoming; under
\* BUG_GONE the host still queues the Incoming of those that had raised one (established, not yet read)
EndOwed(x, R) == /\ ow' = ow \ R /\ pend' = pend \ R
                 /\ gone' = gone + (IF BUG_GONE THEN Cardinality({j \in R \cap pend : ~x.slots[j].unauth}) ELSE 0)

\* a first flight for id x, a datagram every session that holds x refused as a first flight other than its own, or
\* one for an id no session holds (a holder that takes the datagram is Est or Touch); alpn: a protocol is registered;
\* fail: the construction or the id table fails; d: the new session's own deadline after the first flight. Under
\* SUPERSEDE (the rule before #365) the one holder of x is freed first and the flight goes to the admission as for an id
\* no session holds; an id held by more than one session took no first flight. With no room left to accept (Open) the
\* flight is refused before the admission, after its type and floor are read. rej: the responder would only reject the
\* flight or not answer it (a short Initial or a Hello, not a resumption): the endpoint answers it without a session
\* and it never reaches the admission; under BUG_REJ it does, as the endpoint's admission did before
Arrive == \E t \in 0..TMAX, kind \in {1, 2, 6, 4}, len \in LENS, resume \in BOOLEAN, alpn \in BOOLEAN,
             fail \in BOOLEAN, rej \in BOOLEAN, x \in IDS : \E d \in {t + 1, t + LIFE + 1} :
    /\ resume => (kind = 6 /\ alpn)
    /\ rej => (Forged(kind) /\ ~resume)
    /\ LET gone0 == IF SUPERSEDE /\ ~stalled /\ First(kind) /\ Cardinality(Holders(x)) = 1 THEN Holders(x) ELSE {}
           e0 == IF gone0 = {} THEN e ELSE Release(e, MinOf(gone0))
           ids0 == [k \in Slots |-> IF k \in gone0 THEN 0 ELSE ids[k]]
           held == Cardinality(Holders(x) \ gone0)
           room == ~stalled /\ First(kind) /\ Open
           adm == /\ room
                  /\ BUG_REJ \/ ~rej
                  /\ IF SUPERSEDE THEN held = 0 ELSE RoomM(held)
                  /\ AdmitM(e0.count, kind, len, resume)
           free == {k \in Slots : ~e0.slots[k].use}
           made == adm /\ alpn /\ ~fail /\ free # {}
           j == MinOf(free)
       IN /\ e' = IF made THEN Settle(Make(e0, j, t, resume, LIFE), j, d) ELSE e0
          /\ ids' = IF made THEN [ids0 EXCEPT ![j] = x] ELSE ids0
          /\ refused' = (refused /\ (made \/ e' = e))
          /\ resumed' = (resumed /\ (made => e'.slots[j].counted = ~resume)
                                 /\ (adm /\ e0.count >= MAX => resume))
          /\ atcap' = (atcap \/ (adm /\ resume /\ e0.count = MAX))
          /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') \subseteq (IF made /\ ~resume THEN {j} ELSE {}))
          /\ kept' = (kept /\ Ended(e, e', ids, ids') = {})
          /\ ow' = IF Limited /\ made THEN ow \cup {j} ELSE ow
          /\ pend' = IF Limited /\ made THEN pend \cup {j} ELSE pend
          /\ heldok' = (heldok /\ (Limited /\ Cardinality(ow) >= QCAP - q => ~made))
          /\ roomref' = (roomref \/ (Limited /\ ~stalled /\ First(kind) /\ ~Open))
          /\ halfok' = (halfok /\ (Limited /\ made /\ ~resume => e0.count < Half(QCAP - q)))
          /\ resok' = (resok /\ ((Limited /\ QCAP >= 2 /\ q = 0 /\ ~stalled /\ resume /\ ~fail /\ free # {}
                                    /\ (IF SUPERSEDE THEN held = 0 ELSE RoomM(held))
                                    /\ len >= Floor(kind, FULL, SHORT, HELLO)
                                    /\ ow \subseteq {k \in Slots : e0.slots[k].counted})
                                   => made))
          /\ rejok' = (rejok /\ (rej => ~made))
          /\ rs' = IF made THEN (IF rej THEN rs \cup {j} ELSE rs \ {j}) ELSE rs
          /\ genok' = (genok /\ ~(/\ ~rej /\ room /\ RoomM(held) /\ ~resume /\ e0.count > 0 /\ e0.count >= HalfCap
                                  /\ len >= Floor(kind, FULL, SHORT, HELLO)
                                  /\ \A k \in Slots : e0.slots[k].counted => k \in rs))
    /\ UNCHANGED <<stalled, timed, q, gone, busy>>

\* the handshake of an unauthenticated session completes; under BUG_EST it is owed no more (the host has not read its
\* Incoming yet)
Est == \E j \in Slots, d \in 1..(TMAX + 1) :
    /\ e.slots[j].use /\ e.slots[j].unauth
    /\ e' = Settle(Establish(e, j), j, d)
    /\ left' = (left /\ Lost(e, e') \subseteq {j} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids) = {})
    /\ ow' = IF BUG_EST THEN ow \ {j} ELSE ow
    /\ UNCHANGED <<ids, stalled, refused, timed, resumed, atcap, pend, q, gone, busy, heldok, roomref>> /\ UNCHANGED hk

\* a connection ends: a close finished, the peer gave up
Close == \E j \in Slots :
    /\ e.slots[j].use
    /\ e' = Release(e, j)
    /\ ids' = [ids EXCEPT ![j] = 0]
    /\ left' = (left /\ Lost(e, e') \subseteq {j} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids') \subseteq {j})
    /\ EndOwed(e, {j})
    /\ UNCHANGED <<stalled, refused, timed, resumed, atcap, q, busy, heldok, roomref>> /\ UNCHANGED hk

\* any other input to a session moves its own deadline
Touch == \E j \in Slots, d \in 1..(TMAX + 1) :
    /\ e.slots[j].use
    /\ e' = Settle(e, j, d)
    /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids) = {})
    /\ UNCHANGED <<ids, stalled, refused, timed, resumed, atcap>> /\ UNCHANGED bk

\* an unauthenticated session answers as a responder (its flight went out): it lives HOLD from now on, and its
\* connection's own deadline moves past every time checked (handshake.rs: the connect limit becomes the hold); BUG_HOLD
\* lets it hold past HOLD
AnswerA == \E j \in Slots : LET d == TMAX + 1 IN
    /\ HOLD > LIFE
    /\ e.slots[j].use /\ e.slots[j].unauth /\ e.slots[j].life = LIFE
    /\ e' = Settle(Answer(e, j, IF BUG_HOLD THEN HOLD + 1 ELSE HOLD), j, d)
    /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids) = {})
    /\ UNCHANGED <<ids, stalled, refused, timed, resumed, atcap>> /\ UNCHANGED bk

DialA == \E t \in 0..TMAX, j \in Slots, d \in 1..(TMAX + 1) :
    /\ ~e.slots[j].use
    /\ e' = Settle(Dial(e, j, t, LIFE), j, d)
    /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids) = {})
    /\ UNCHANGED <<ids, stalled, refused, timed, resumed, atcap>> /\ UNCHANGED bk

\* the host leaves events unread, or reads them
Stall == stalled' = ~stalled /\ UNCHANGED <<e, ids, refused, left, timed, resumed, atcap, kept>> /\ UNCHANGED bk

\* a timer call at t: each due connection's next deadline (or its end), and after how many pops the queue stalls
Timer == \E t \in 0..TMAX : \E ds \in [Slots -> {t, t + 2, Gone}], cut \in 0..(K + 1) :
    IF stalled THEN UNCHANGED vars
    ELSE /\ e' = Loop(e, t, ds, IF BUG_GE THEN -1 ELSE IF BUG_LATE THEN 1 ELSE 0, K, IF cut > K THEN K ELSE cut)
         /\ ids' = [j \in Slots |-> IF e'.slots[j].use THEN ids[j] ELSE 0]
         /\ stalled' = (cut <= K)
         /\ timed' = (timed /\ (~stalled' => \A j \in Slots : ~Expired(e'.slots[j], t)))
         /\ left' = (left /\ Won(e, e') = {}
                          /\ \A j \in Lost(e, e') : Expired(e.slots[j], t) \/ ds[j] = Gone)
         /\ kept' = (kept /\ \A j \in Ended(e, e', ids, ids') : Expired(e.slots[j], t) \/ ds[j] = Gone)
         /\ EndOwed(e, Freed(e, e'))
         /\ UNCHANGED <<refused, resumed, atcap, q, busy, heldok, roomref>> /\ UNCHANGED hk

\* engine.rs on_event: the host reads the Incoming of an established session j and takes it (session_taken says
\* Reserved): it waits in the queue, or, with the queue full, is closed as busy after its handshake
Take == \E j \in pend :
    /\ Limited /\ e.slots[j].use /\ ~e.slots[j].unauth
    /\ pend' = pend \ {j} /\ ow' = ow \ {j}
    /\ q' = IF q < QCAP THEN q + 1 ELSE q
    /\ busy' = (busy \/ q >= QCAP)
    /\ UNCHANGED <<e, ids, stalled, refused, left, timed, resumed, atcap, kept, gone, heldok, roomref>> /\ UNCHANGED hk

\* BUG_GONE: the host queues the Incoming of a session that ended before it read it
TakeGone ==
    /\ gone > 0
    /\ gone' = gone - 1
    /\ q' = IF q < QCAP THEN q + 1 ELSE q
    /\ busy' = (busy \/ q >= QCAP)
    /\ UNCHANGED <<e, ids, stalled, refused, left, timed, resumed, atcap, kept, ow, pend, heldok, roomref>> /\ UNCHANGED hk

\* the Incoming of a sub-session its peer opened inside a session it has (session_taken says Unreserved): it waits only
\* in a place no owed session holds (BUG_SUB: in any free place), else it is closed as busy; it had no handshake
SubUp ==
    /\ Limited
    /\ q' = IF (IF BUG_SUB THEN q < QCAP ELSE q + Cardinality(ow) < QCAP) THEN q + 1 ELSE q
    /\ UNCHANGED <<e, ids, stalled, refused, left, timed, resumed, atcap, kept, ow, pend, gone, busy, heldok, roomref>> /\ UNCHANGED hk

\* ops.rs accept_route: the application takes the oldest waiting session (a session that ended while it waited
\* included: it keeps its place until then)
Accept ==
    /\ Limited /\ q > 0
    /\ q' = q - 1
    /\ UNCHANGED <<e, ids, stalled, refused, left, timed, resumed, atcap, kept, ow, pend, gone, busy, heldok, roomref>> /\ UNCHANGED hk

Next == Arrive \/ Est \/ Close \/ Touch \/ DialA \/ Stall \/ Timer \/ Take \/ TakeGone \/ SubUp \/ Accept \/ AnswerA
Spec == Init /\ [][Next]_vars

Capped == e.count <= MAX
Exact == e.count = CountOf(e.slots)
Shape == \A j \in Slots : /\ e.slots[j].counted => e.slots[j].unauth /\ e.slots[j].use
                          /\ ~e.slots[j].use => e.slots[j] = Free
DeadlineBound == \A j \in Slots :
    e.slots[j].use /\ e.slots[j].unauth => /\ e.slots[j].dl # NoDl /\ e.slots[j].dl <= End(e.slots[j])
                                          /\ e.slots[j].life \in {LIFE, HOLD}
PollBound == /\ stalled => Poll(e.slots, stalled) = NoDl
             /\ \A j \in Slots : e.slots[j].use /\ e.slots[j].unauth /\ ~stalled =>
                    Poll(e.slots, stalled) # NoDl /\ Poll(e.slots, stalled) <= End(e.slots[j])
RefusedRight == refused
LeftRight == left
TimerRight == timed
ResumeRight == resumed
HolderKept == kept
HeldBound == /\ \A j \in Slots : ~e.slots[j].use => ids[j] = 0
             /\ \A x \in IDS : Cardinality(Holders(x)) <= MAXH
HeldRight == heldok
Placed == q + Cardinality(pend) + gone <= QCAP \/ ~Limited
OwedExact == ow = pend /\ \A j \in ow : e.slots[j].use
NoBusy == ~busy
HalfRight == halfok
HalfRoom == ~Limited \/ BUG_LE \/ e.count <= Half(QCAP)
ResumeOpen == resok
RejectedRight == rejok
GenuineServed == genok
Inv == Capped /\ Exact /\ Shape /\ DeadlineBound /\ PollBound /\ RefusedRight /\ LeftRight /\ TimerRight /\ ResumeRight
       /\ HolderKept /\ HeldBound /\ HeldRight /\ Placed /\ OwedExact /\ NoBusy /\ HalfRight /\ HalfRoom /\ ResumeOpen
       /\ RejectedRight /\ GenuineServed

\* reachability witnesses: a resumption is admitted while the count is at the cap; an id gets MAXH holders; a first
\* flight is refused for want of room
NoResumeAtCap == ~atcap
NoFullId == \A x \in IDS : Cardinality(Holders(x)) < MAXH
NoRoomRefusal == ~roomref
=============================================================================
