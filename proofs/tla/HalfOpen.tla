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
(*    (HeldBound);                                                         *)
(*  - a session made by a resumption or behind a retry token is not        *)
(*    counted; only a Hello whose ticket opens or a flight behind a token  *)
(*    that opens passes a full cap, a forged token does not (TokenRight);  *)
(*  - a flight the cap refused although it met its floor, and whose id     *)
(*    had room for another holder, is answered with a retry only while the *)
(*    ring has room, so at most RQ wait to be sent, and the retry changes  *)
(*    no session (RingBound, RefusedRight);                                *)
(*  - while the handshakes under way fill the room the application has     *)
(*    left to accept (aroom, rx.rs set_backlog_room) no first flight makes *)
(*    a session or a retry, a new holder of a held id included (HeldRight).*)
(* TOKS: the tokens a flight may carry; the configs of #365 take none,     *)
(* HalfOpen_retry (a ring of one) takes all, HalfOpen_room lets the room   *)
(* to accept change.                                                       *)
(* HalfOpen.cfg checks Inv with no retry ring (RQ = 0) and HalfOpen_retry  *)
(* with a ring of one, one id and a shorter clock (TMAX = 2).              *)
(* BUG_TOKEN_COUNTED counts a session behind a token: admitted past the    *)
(* full cap it raises the count over it (HalfOpen_tokencount breaks        *)
(* Capped). BUG_ANY_TOKEN lets a forged token pass the cap                 *)
(* (HalfOpen_anytoken breaks TokenRight). BUG_RING queues a retry with the *)
(* ring full (HalfOpen_ring breaks RingBound). HalfOpen_tokreach is a      *)
(* reachability witness: a flight behind a token makes a session at the    *)
(* cap. BUG_HOLD admits with no room left (HalfOpen_hold breaks            *)
(* HeldRight); HOLD lets the room change (HalfOpen_retry, HalfOpen_hold).  *)
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
CONSTANTS K, MAX, LIFE, FULL, SHORT, TMAX, LENS, IDS, MAXH, BUG_LE, STRICT, SUPERSEDE, RQ, BUG_TOKEN_COUNTED,
          BUG_ANY_TOKEN, BUG_RING, HOLD, BUG_HOLD, TOKS
VARIABLES e, ids, stalled, refused, left, timed, resumed, atcap, kept, ring, tokened, tokatcap, aroom, heldok
vars == <<e, ids, stalled, refused, left, timed, resumed, atcap, kept, ring, tokened, tokatcap, aroom, heldok>>

INSTANCE HalfOpenOps

Slots == 0..(K - 1)
\* the sessions this node accepted whose handshake is under way (endpoint.rs handshaking)
Unauth(sl) == Cardinality({j \in Slots : sl[j].use /\ sl[j].unauth})
Init == /\ e = [slots |-> Table0(K), count |-> 0] /\ ids = [j \in Slots |-> 0] /\ stalled = FALSE
        /\ refused = TRUE /\ left = TRUE /\ timed = TRUE /\ resumed = TRUE /\ atcap = FALSE /\ kept = TRUE
        /\ ring = 0 /\ tokened = TRUE /\ tokatcap = FALSE /\ aroom = K + 1 /\ heldok = TRUE

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
\* one for an id no session holds (a holder that takes the datagram is Est or Touch); tok: no retry token in front of
\* it, one that opens for its address and id, or a forged, stale or misplaced one; alpn: a protocol is registered;
\* fail: the construction or the id table fails; d: the new session's own deadline after the first flight. Under
\* SUPERSEDE (the rule before #365) the one holder of x is freed first and the flight goes to the admission as for an id
\* no session holds; an id held by more than one session took no first flight
Arrive == \E t \in 0..TMAX, kind \in {1, 2, 6, 4}, len \in LENS, resume \in BOOLEAN, alpn \in BOOLEAN,
             fail \in BOOLEAN, x \in IDS, tok \in TOKS : \E d \in {t + 1, t + LIFE + 1} :
    /\ resume => (kind = 6 /\ alpn)
    \* a token is read only in front of a first message a ticket does not exempt; elsewhere it changes nothing
    /\ (resume \/ ~First(kind)) => tok = "none"
    /\ LET gone == IF SUPERSEDE /\ ~stalled /\ First(kind) /\ Cardinality(Holders(x)) = 1 THEN Holders(x) ELSE {}
           e0 == IF gone = {} THEN e ELSE Release(e, MinOf(gone))
           ids0 == [k \in Slots |-> IF k \in gone THEN 0 ELSE ids[k]]
           held == Cardinality(Holders(x) \ gone)
           \* rx.rs: a token is looked at only for a flight that met its floor and no ticket exempts
           token == ~resume /\ len >= Floor(kind, FULL, SHORT)
                    /\ (IF BUG_ANY_TOKEN THEN tok # "none" ELSE tok = "valid")
           exempt == resume \/ token
           \* rx.rs unrouted: no room left to accept stops every first flight before anything is read
           \* (without HOLD the room never changes from K + 1, which no table fills: the count is skipped)
           open == BUG_HOLD \/ ~HOLD \/ Unauth(e0.slots) < aroom
           room == /\ ~stalled /\ open /\ First(kind) /\ IF SUPERSEDE THEN held = 0 ELSE RoomM(held)
           adm == room /\ AdmitM(e0.count, kind, len, exempt)
           \* refused by the cap alone, the floor met: a retry is offered
           capped == room /\ len >= Floor(kind, FULL, SHORT) /\ ~adm
           free == {k \in Slots : ~e0.slots[k].use}
           made == adm /\ alpn /\ ~fail /\ free # {}
           j == MinOf(free)
       IN /\ e' = IF made THEN Settle(Make(e0, j, t, IF BUG_TOKEN_COUNTED THEN resume ELSE exempt), j, d, LIFE)
                   ELSE e0
          /\ ids' = IF made THEN [ids0 EXCEPT ![j] = x] ELSE ids0
          /\ refused' = (refused /\ (made \/ e' = e))
          /\ resumed' = (resumed /\ (made => e'.slots[j].counted = ~exempt)
                                 /\ (adm /\ e0.count >= MAX => exempt))
          /\ tokened' = (tokened /\ (adm /\ e0.count >= MAX => resume \/ tok = "valid"))
          /\ tokatcap' = (tokatcap \/ (made /\ token /\ e0.count = MAX))
          /\ ring' = IF capped THEN (IF BUG_RING THEN ring + 1 ELSE Offer(ring, RQ)) ELSE ring
          /\ atcap' = (atcap \/ (adm /\ resume /\ e0.count = MAX))
          /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') \subseteq (IF made /\ ~exempt THEN {j} ELSE {}))
          /\ kept' = (kept /\ Ended(e, e', ids, ids') = {})
          /\ heldok' = (heldok /\ (HOLD /\ Unauth(e0.slots) >= aroom => ~made /\ ring' = ring))
    /\ UNCHANGED <<stalled, timed, aroom>>

\* the handshake of an unauthenticated session completes
Est == \E j \in Slots, d \in 1..(TMAX + 1) :
    /\ e.slots[j].use /\ e.slots[j].unauth
    /\ e' = Settle(Establish(e, j), j, d, LIFE)
    /\ left' = (left /\ Lost(e, e') \subseteq {j} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids) = {})
    /\ UNCHANGED <<ids, stalled, refused, timed, resumed, atcap, ring, tokened, tokatcap, aroom, heldok>>

\* a connection ends: a close finished, the peer gave up
Close == \E j \in Slots :
    /\ e.slots[j].use
    /\ e' = Release(e, j)
    /\ ids' = [ids EXCEPT ![j] = 0]
    /\ left' = (left /\ Lost(e, e') \subseteq {j} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids') \subseteq {j})
    /\ UNCHANGED <<stalled, refused, timed, resumed, atcap, ring, tokened, tokatcap, aroom, heldok>>

\* any other input to a session moves its own deadline
Touch == \E j \in Slots, d \in 1..(TMAX + 1) :
    /\ e.slots[j].use
    /\ e' = Settle(e, j, d, LIFE)
    /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids) = {})
    /\ UNCHANGED <<ids, stalled, refused, timed, resumed, atcap, ring, tokened, tokatcap, aroom, heldok>>

DialA == \E t \in 0..TMAX, j \in Slots, d \in 1..(TMAX + 1) :
    /\ ~e.slots[j].use
    /\ e' = Settle(Dial(e, j, t), j, d, LIFE)
    /\ left' = (left /\ Lost(e, e') = {} /\ Won(e, e') = {})
    /\ kept' = (kept /\ Ended(e, e', ids, ids) = {})
    /\ UNCHANGED <<ids, stalled, refused, timed, resumed, atcap, ring, tokened, tokatcap, aroom, heldok>>

\* the host leaves events unread, or reads them
Stall == stalled' = ~stalled
         /\ UNCHANGED <<e, ids, refused, left, timed, resumed, atcap, kept, ring, tokened, tokatcap, aroom, heldok>>

\* poll_transmit sends the oldest waiting retry (through the ledger, which may hold it back: it leaves the ring
\* either way); nothing about a session changes
Send == ring > 0 /\ ring' = ring - 1
        /\ UNCHANGED <<e, ids, stalled, refused, left, timed, resumed, atcap, kept, tokened, tokatcap, aroom, heldok>>

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
         /\ UNCHANGED <<refused, resumed, atcap, ring, tokened, tokatcap, aroom, heldok>>

\* the room the application has left to accept sessions changes (engine.rs sync_backlog); K + 1 is no limit
Hold == HOLD /\ \E r \in 0..(K + 1) : aroom' = r
        /\ UNCHANGED <<e, ids, stalled, refused, left, timed, resumed, atcap, kept, ring, tokened, tokatcap, heldok>>

Next == Arrive \/ Est \/ Close \/ Touch \/ DialA \/ Stall \/ Timer \/ Send \/ Hold
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
TokenRight == tokened
RingBound == ring <= RQ
HeldRight == heldok
HeldBound == /\ \A j \in Slots : ~e.slots[j].use => ids[j] = 0
             /\ \A x \in IDS : Cardinality(Holders(x)) <= MAXH
Inv == Capped /\ Exact /\ Shape /\ DeadlineBound /\ PollBound /\ RefusedRight /\ LeftRight /\ TimerRight /\ ResumeRight
       /\ HolderKept /\ HeldBound /\ TokenRight /\ RingBound /\ HeldRight

\* reachability witnesses: a resumption is admitted while the count is at the cap; an id gets MAXH holders
NoResumeAtCap == ~atcap
NoFullId == \A x \in IDS : Cardinality(Holders(x)) < MAXH
\* a reachability witness: a flight behind a token makes a session while the count is at the cap
NoTokenAtCap == ~tokatcap
=============================================================================
