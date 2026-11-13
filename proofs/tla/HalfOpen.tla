------------------------------- MODULE HalfOpen ------------------------------
(***************************************************************************)
(* The endpoint's cap on half-open sessions and their lifetime (vinc-core  *)
(* rx.rs, events.rs, endpoint.rs, timers.rs), over every interleaving of   *)
(* first flights of any type and length, resumptions, establishment, the   *)
(* end of a connection, inputs that move a session's own deadline, dials,  *)
(* a stalled event queue and timer calls, at any times (a clock that steps *)
(* back included), at small sizes (HalfOpenOps.tla has the operators).     *)
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
(*    a Hello resumes (ResumeRight).                                       *)
(* BUG_LE admits while count <= MAX: the witness HalfOpen_le breaks        *)
(* Capped. STRICT expires only past the end: the witness HalfOpen_strict   *)
(* breaks TimerRight. HalfOpen_reach is a reachability witness: a          *)
(* resumption is admitted while the count is at the cap.                   *)
(* Lean counterpart: proofs/lean/Vinc/CoreHalfOpen*.lean.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS K, MAX, LIFE, FULL, SHORT, TMAX, LENS, BUG_LE, STRICT
VARIABLES e, stalled, refused, left, timed, resumed, atcap
vars == <<e, stalled, refused, left, timed, resumed, atcap>>

INSTANCE HalfOpenOps

Slots == 0..(K - 1)
Init == /\ e = [slots |-> Table0(K), count |-> 0] /\ stalled = FALSE
        /\ refused = TRUE /\ left = TRUE /\ timed = TRUE /\ resumed = TRUE /\ atcap = FALSE

AdmitM(count, kind, len, resume) ==
    IF BUG_LE THEN len >= Floor(kind, FULL, SHORT) /\ (resume \/ count <= MAX)
    ELSE Admit(count, kind, len, resume, MAX, FULL, SHORT)

\* the counted slots that stopped being counted, and those that started
Lost(x, y) == {j \in Slots : x.slots[j].counted /\ ~y.slots[j].counted}
Won(x, y) == {j \in Slots : ~x.slots[j].counted /\ y.slots[j].counted}

\* a first flight for an id no session holds; alpn: a protocol is registered; fail: the construction or the id table
\* fails; d: the new session's own deadline after the first flight
Arrive == \E t \in 0..TMAX, kind \in {1, 2, 6, 4}, len \in LENS, resume \in BOOLEAN, alpn \in BOOLEAN,
             fail \in BOOLEAN : \E d \in {t + 1, t + LIFE + 1} :
    /\ resume => (kind = 6 /\ alpn)
    /\ LET adm == ~stalled /\ First(kind) /\ AdmitM(e.count, kind, len, resume)
           free == {j \in Slots : ~e.slots[j].use}
           made == adm /\ alpn /\ ~fail /\ free # {}
           j == MinOf(free)
       IN /\ e' = IF made THEN Settle(Make(e, j, t, resume), j, d, LIFE) ELSE e
          /\ refused' = (refused /\ (made \/ e' = e))
          /\ resumed' = (resumed /\ (made => e'.slots[j].counted = ~resume)
                                 /\ (adm /\ e.count >= MAX => resume))
          /\ atcap' = (atcap \/ (adm /\ resume /\ e.count = MAX))
          /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') \subseteq (IF made /\ ~resume THEN {j} ELSE {}))
    /\ UNCHANGED <<stalled, timed>>

\* the handshake of an unauthenticated session completes
Est == \E j \in Slots, d \in 1..(TMAX + 1) :
    /\ e.slots[j].use /\ e.slots[j].unauth
    /\ e' = Settle(Establish(e, j), j, d, LIFE)
    /\ left' = (left /\ Lost(e, e') \subseteq {j} /\ Won(e, e') = {})
    /\ UNCHANGED <<stalled, refused, timed, resumed, atcap>>

\* a connection ends: a close finished, the peer gave up, a damaged first message superseded
Close == \E j \in Slots :
    /\ e.slots[j].use
    /\ e' = Release(e, j)
    /\ left' = (left /\ Lost(e, e') \subseteq {j} /\ Won(e, e') = {})
    /\ UNCHANGED <<stalled, refused, timed, resumed, atcap>>

\* any other input to a session moves its own deadline
Touch == \E j \in Slots, d \in 1..(TMAX + 1) :
    /\ e.slots[j].use
    /\ e' = Settle(e, j, d, LIFE)
    /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') = {})
    /\ UNCHANGED <<stalled, refused, timed, resumed, atcap>>

DialA == \E t \in 0..TMAX, j \in Slots, d \in 1..(TMAX + 1) :
    /\ ~e.slots[j].use
    /\ e' = Settle(Dial(e, j, t), j, d, LIFE)
    /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') = {})
    /\ UNCHANGED <<stalled, refused, timed, resumed, atcap>>

\* the host leaves events unread, or reads them
Stall == stalled' = ~stalled /\ UNCHANGED <<e, refused, left, timed, resumed, atcap>>

\* a timer call at t: each due connection's next deadline (or its end), and after how many pops the queue stalls
Timer == \E t \in 0..TMAX : \E ds \in [Slots -> {t, t + 2, Gone}], cut \in 0..(K + 1) :
    IF stalled THEN UNCHANGED vars
    ELSE /\ e' = Loop(e, t, ds, LIFE, STRICT, K, IF cut > K THEN K ELSE cut)
         /\ stalled' = (cut <= K)
         /\ timed' = (timed /\ (~stalled' => \A j \in Slots : ~Expired(e'.slots[j], t, LIFE)))
         /\ left' = (left /\ Won(e, e') = {}
                          /\ \A j \in Lost(e, e') : Expired(e.slots[j], t, LIFE) \/ ds[j] = Gone)
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
Inv == Capped /\ Exact /\ Shape /\ DeadlineBound /\ PollBound /\ RefusedRight /\ LeftRight /\ TimerRight /\ ResumeRight

\* a reachability witness: a resumption is admitted while the count is at the cap
NoResumeAtCap == ~atcap
=============================================================================
