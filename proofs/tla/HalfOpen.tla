------------------------------- MODULE HalfOpen ------------------------------
(***************************************************************************)
(* The endpoint's cap on half-open sessions and their lifetime (vinc-core  *)
(* rx.rs, events.rs, endpoint.rs, timers.rs), over every interleaving of   *)
(* first flights of any type and length, for an id no session holds or     *)
(* one that sessions hold, resumptions, establishment, the end of a        *)
(* connection, inputs that move a session's own deadline, dials, a stalled *)
(* event queue and timer calls, at any times (a clock that steps back      *)
(* included), at small sizes (HalfOpenOps.tla has the operators). ids[j]   *)
(* is the id the session in slot j was made under (0 for a free slot and a *)
(* dial); the sessions that hold an id are its holders.                    *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the count never passes MAX (Capped) and is the number of counted     *)
(*    sessions (Exact); a counted session is unauthenticated and in use, a *)
(*    free slot holds nothing (Shape);                                     *)
(*  - an unauthenticated session holds a deadline at most LIFE after its   *)
(*    creation (DeadlineBound), so poll_timeout is never later than the    *)
(*    end of any unauthenticated session, and none while the event queue   *)
(*    is stalled (PollBound);                                              *)
(*  - a first flight that makes no session (a stalled queue, a type that   *)
(*    starts nothing, the floor or the cap, no protocol, no free slot, a   *)
(*    failed construction) changes nothing (RefusedRight);                 *)
(*  - a session enters the count only when an admitted first flight that   *)
(*    does not resume makes it, and leaves it only when it is established, *)
(*    when its connection ends, or at a timer call at or after its end     *)
(*    (LeftRight);                                                         *)
(*  - a timer call that the event queue did not stop leaves no             *)
(*    unauthenticated session at or past its end (TimerRight);             *)
(*  - a session made by a resumption is not counted and one made by        *)
(*    anything else is; only a resumption is admitted at the cap, and only *)
(*    a Hello resumes (ResumeRight);                                       *)
(*  - no arrival frees or replaces a session: a session, the first holder  *)
(*    of its id included, leaves its slot only by a close or at a timer    *)
(*    call at or after its end or when its connection ended (HolderKept);  *)
(*  - an id never has more than MAXH holders, and a free slot holds no id  *)
(*    (HeldBound).                                                         *)
(* BUG_LE admits while count <= MAX and while the id has at most MAXH      *)
(* holders: the witnesses HalfOpen_le and HalfOpen_le_held break Capped    *)
(* and HeldBound. STRICT expires only past the end: the witness            *)
(* HalfOpen_strict breaks TimerRight. SUPERSEDE is the rule before #365: a *)
(* first flight that the one holder of its id refused as a first flight    *)
(* other than its own freed that holder and went to the admission; the     *)
(* witness HalfOpen_supersede breaks HolderKept. HalfOpen_reach and        *)
(* HalfOpen_holders are reachability witnesses: a resumption is admitted   *)
(* while the count is at the cap; an id gets MAXH holders.                 *)
(* Lean counterpart: proofs/lean/Vinc/CoreHalfOpen*.lean.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS K, MAX, LIFE, FULL, SHORT, TMAX, LENS, IDS, MAXH, BUG_LE, STRICT, SUPERSEDE
VARIABLES e, ids, stalled, refused, left, timed, resumed, atcap, kept
vars == <<e, ids, stalled, refused, left, timed, resumed, atcap, kept>>

INSTANCE HalfOpenOps

Slots == 0..(K - 1)
Init == /\ e = [slots |-> Table0(K), count |-> 0] /\ ids = [j \in Slots |-> 0] /\ stalled = FALSE
        /\ refused = TRUE /\ left = TRUE /\ timed = TRUE /\ resumed = TRUE /\ atcap = FALSE /\ kept = TRUE

AdmitM(count, kind, len, resume) ==
    IF BUG_LE THEN len >= Floor(kind, FULL, SHORT) /\ (resume \/ count <= MAX)
    ELSE Admit(count, kind, len, resume, MAX, FULL, SHORT)
RoomM(held) == IF BUG_LE THEN held <= MAXH ELSE Room(held, MAXH)

\* the sessions that hold id x
Holders(x) == {j \in Slots : e.slots[j].use /\ ids[j] = x}
\* the counted slots that stopped being counted, and those that started
Lost(x, y) == {j \in Slots : x.slots[j].counted /\ ~y.slots[j].counted}
Won(x, y) == {j \in Slots : ~x.slots[j].counted /\ y.slots[j].counted}
\* the sessions of x (ids xi) that are not in their slot in y (ids yi) any more: freed, or replaced by another
Ended(x, y, xi, yi) ==
    {j \in Slots : x.slots[j].use /\ ~(y.slots[j].use /\ y.slots[j].created = x.slots[j].created /\ yi[j] = xi[j])}

\* a first flight for id x, a datagram every session that holds x refused as a first flight other than its own, or
\* one for an id no session holds (a holder that takes the datagram is Est or Touch); alpn: a protocol is registered;
\* fail: the construction or the id table fails; d: the new session's own deadline after the first flight. Under
\* SUPERSEDE (the rule before #365) the one holder of x is freed first and the flight goes to the admission as for an id
\* no session holds; an id held by more than one session took no first flight
Arrive == \E t \in 0..TMAX, kind \in {1, 2, 6, 4}, len \in LENS, resume \in BOOLEAN, alpn \in BOOLEAN,
             fail \in BOOLEAN, x \in IDS : \E d \in {t + 1, t + LIFE + 1} :
    /\ resume => (kind = 6 /\ alpn)
    /\ LET gone == IF SUPERSEDE /\ ~stalled /\ First(kind) /\ Cardinality(Holders(x)) = 1 THEN Holders(x) ELSE {}
           e0 == IF gone = {} THEN e ELSE Release(e, MinOf(gone))
           ids0 == [k \in Slots |-> IF k \in gone THEN 0 ELSE ids[k]]
           held == Cardinality(Holders(x) \ gone)
           adm == /\ ~stalled /\ First(kind)
                  /\ IF SUPERSEDE THEN held = 0 ELSE RoomM(held)
                  /\ AdmitM(e0.count, kind, len, resume)
           free == {k \in Slots : ~e0.slots[k].use}
           made == adm /\ alpn /\ ~fail /\ free # {}
           j == MinOf(free)
       IN /\ e' = IF made THEN Settle(Make(e0, j, t, resume), j, d, LIFE) ELSE e0
          /\ ids' = IF made THEN [ids0 EXCEPT ![j] = x] ELSE ids0
          /\ refused' = (refused /\ (made \/ e' = e))
          /\ resumed' = (resumed /\ (made => e'.slots[j].counted = ~resume)
                                 /\ (adm /\ e0.count >= MAX => resume))
          /\ atcap' = (atcap \/ (adm /\ resume /\ e0.count = MAX))
          /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') \subseteq (IF made /\ ~resume THEN {j} ELSE {}))
          /\ kept' = (kept /\ Ended(e, e', ids, ids') = {})
    /\ UNCHANGED <<stalled, timed>>

\* the handshake of an unauthenticated session completes
Est == \E j \in Slots, d \in 1..(TMAX + 1) :
    /\ e.slots[j].use /\ e.slots[j].unauth
    /\ e' = Settle(Establish(e, j), j, d, LIFE)
    /\ left' = (left /\ Lost(e, e') \subseteq {j} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids) = {})
    /\ UNCHANGED <<ids, stalled, refused, timed, resumed, atcap>>

\* a connection ends: a close finished, the peer gave up
Close == \E j \in Slots :
    /\ e.slots[j].use
    /\ e' = Release(e, j)
    /\ ids' = [ids EXCEPT ![j] = 0]
    /\ left' = (left /\ Lost(e, e') \subseteq {j} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids') \subseteq {j})
    /\ UNCHANGED <<stalled, refused, timed, resumed, atcap>>

\* any other input to a session moves its own deadline
Touch == \E j \in Slots, d \in 1..(TMAX + 1) :
    /\ e.slots[j].use
    /\ e' = Settle(e, j, d, LIFE)
    /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids) = {})
    /\ UNCHANGED <<ids, stalled, refused, timed, resumed, atcap>>

DialA == \E t \in 0..TMAX, j \in Slots, d \in 1..(TMAX + 1) :
    /\ ~e.slots[j].use
    /\ e' = Settle(Dial(e, j, t), j, d, LIFE)
    /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids) = {})
    /\ UNCHANGED <<ids, stalled, refused, timed, resumed, atcap>>

\* the host leaves events unread, or reads them
Stall == stalled' = ~stalled /\ UNCHANGED <<e, ids, refused, left, timed, resumed, atcap, kept>>

\* a timer call at t: each due connection's next deadline (or its end), and after how many pops the queue stalls
Timer == \E t \in 0..TMAX : \E ds \in [Slots -> {t, t + 2, Gone}], cut \in 0..(K + 1) :
    IF stalled THEN UNCHANGED vars
    ELSE /\ e' = Loop(e, t, ds, LIFE, STRICT, K, IF cut > K THEN K ELSE cut)
         /\ ids' = [j \in Slots |-> IF e'.slots[j].use THEN ids[j] ELSE 0]
         /\ stalled' = (cut <= K)
         /\ timed' = (timed /\ (~stalled' => \A j \in Slots : ~Expired(e'.slots[j], t, LIFE)))
         /\ left' = (left /\ Won(e, e') = {}
                          /\ \A j \in Lost(e, e') : Expired(e.slots[j], t, LIFE) \/ ds[j] = Gone)
         /\ kept' = (kept /\ \A j \in Ended(e, e', ids, ids') : Expired(e.slots[j], t, LIFE) \/ ds[j] = Gone)
         /\ UNCHANGED <<refused, resumed, atcap>>

Next == Arrive \/ Est \/ Close \/ Touch \/ DialA \/ Stall \/ Timer
Spec == Init /\ [][Next]_vars

Capped == e.count <= MAX
Exact == e.count = CountOf(e.slots)
Shape == \A j \in Slots : /\ e.slots[j].counted => e.slots[j].unauth /\ e.slots[j].use
                          /\ ~e.slots[j].use => e.slots[j] = Free
DeadlineBound == \A j \in Slots :
    e.slots[j].use /\ e.slots[j].unauth => e.slots[j].dl # NoDl /\ e.slots[j].dl <= End(e.slots[j], LIFE)
PollBound == /\ stalled => Poll(e.slots, stalled) = NoDl
             /\ \A j \in Slots : e.slots[j].use /\ e.slots[j].unauth /\ ~stalled =>
                    Poll(e.slots, stalled) # NoDl /\ Poll(e.slots, stalled) <= End(e.slots[j], LIFE)
RefusedRight == refused
LeftRight == left
TimerRight == timed
ResumeRight == resumed
HolderKept == kept
HeldBound == /\ \A j \in Slots : ~e.slots[j].use => ids[j] = 0
             /\ \A x \in IDS : Cardinality(Holders(x)) <= MAXH
Inv == Capped /\ Exact /\ Shape /\ DeadlineBound /\ PollBound /\ RefusedRight /\ LeftRight /\ TimerRight /\ ResumeRight
       /\ HolderKept /\ HeldBound

\* reachability witnesses: a resumption is admitted while the count is at the cap; an id gets MAXH holders
NoResumeAtCap == ~atcap
NoFullId == \A x \in IDS : Cardinality(Holders(x)) < MAXH
=============================================================================
