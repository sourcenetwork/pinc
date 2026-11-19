-------------------------------- MODULE Timers --------------------------------
(***************************************************************************)
(* The timers and the closing state of the PINCER connection               *)
(* (pinc-transport conn/timer.rs, conn/life.rs; TimersOps.tla has the      *)
(* operators) over every interleaving of the calls that move them, on a    *)
(* small clock: handle_timeout (with every close a component may decide    *)
(* in it), a datagram heard or refused (with SLEEP and CLOSE), frames that *)
(* do not decode or break a rule, close, poll_transmit (with or without a  *)
(* datagram, with SLEEP frames leaving), sleep, wake, the link going down  *)
(* and coming back, keepalive, pulse and the handshake establishing the    *)
(* session. In every state reached, poll_timeout and every call are        *)
(* checked for every input: every vector of CSet for the other components' *)
(* deadlines (both gates on and off; none, any one, or all of them at a    *)
(* value of CD), every time up to TMAX, every close a component may        *)
(* decide. The Lean theorems take every vector.                            *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - poll_timeout is exactly the minimum of the deadlines the code        *)
(*    combines, each under its gate (PollMin, against the independent set  *)
(*    Enabled), None exactly once closed and 0 while closing (PollPhase),  *)
(*    never later than the idle deadline, the end of a link outage or the  *)
(*    wake wait (PollLeLife);                                              *)
(*  - handle_timeout does nothing before the first of its own deadlines    *)
(*    (EarlyNothing; with PollLeLife: nothing before poll_timeout), closes *)
(*    silently and does nothing else at or after the idle deadline         *)
(*    (IdleExact), reports an unanswered WAKE exactly when its wait ran    *)
(*    out and ends a link outage exactly when it lasted LDM (DueWork), and *)
(*    leaves none of its own deadlines in the past (NoStale);              *)
(*  - at most one CLOSE ever leaves, only from the closing state, and the  *)
(*    connection is closed after it (OneClose); a peer's CLOSE, the idle   *)
(*    timeout, a dead path, a handshake timeout and a session its peer     *)
(*    never confirmed send nothing (SilentEnd); a closed connection stays  *)
(*    closed, has no timer, sends nothing and takes nothing (ClosedInert); *)
(*  - before the idle deadline the handshake timer ends a handshaking      *)
(*    connection whose handshake ran out of time ("hs") and a connected    *)
(*    one whose peer never confirmed the session ("unconf", a dialing side *)
(*    past its connect limit counted from when it established, #390),      *)
(*    each silently and only in its own phase (HsEnds);                    *)
(*  - a heard packet restarts the idle timer and clears the wake wait,     *)
(*    anything else refused leaves the state as it was (IdleRestart); a    *)
(*    sleeping peer is held HOLD after its SLEEP (SleepHold);              *)
(*  - a close with a CLOSE begins at a probe timeout only on a relay path  *)
(*    whose carrier was heard within CF, after 4 probe timeouts in a row   *)
(*    and 4 round trips of silence, and always begins there unless the     *)
(*    path is dead or the call ended the connection first (CarrierClose,   *)
(*    over the shapes of inputs ShapeSet; CarrierPure, the rule itself over *)
(*    every input, an ASSUME); the carrier close leaves its one CLOSE      *)
(*    (CarrierEnd, OneClose).                                              *)
(* BUG = "none" is the code; Timers_nowake (a poll_timeout that forgets    *)
(* the wake wait while suspended) and Timers_noheard (a receive path that  *)
(* does not restart the idle timer) are wrong rules TLC must catch, so are *)
(* Timers_norelay (a carrier close on a direct path) and Timers_nofresh (a *)
(* carrier close that ignores the carrier's freshness), and so is          *)
(* Timers_nounconf (the rule before #390: the handshake timer ends only a  *)
(* handshaking connection, so a dialing side whose peer never confirmed    *)
(* the session stays connected); Timers_close is the reachability witness  *)
(* of a CLOSE leaving and Timers_carrier that of a carrier close.          *)
(* Lean counterpart: proofs/lean/Pinc/TransportTimers*.lean.               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS IDLE, HOLD, WAKE, LDM, CF, IR, TMAX, KMAX, KAS, ERR, CD, BUG
VARIABLES s, now, n, closes, why
vars == <<s, now, n, closes, why>>

INSTANCE TimersOps

K == [idle |-> IDLE, hold |-> HOLD, wake |-> WAKE, ldm |-> LDM, cf |-> CF, ir |-> IR]
\* the component vectors: both gates on and off, with no deadline, with one deadline at a value of CD (so a deadline
\* read without its gate, or not read under it, is the minimum in some vector), or with all of them at one value
Comps == {"hs", "rec", "ack", "path", "rekey", "paced", "mtu"}
Pats == {[x \in Comps |-> None]} \cup {[x \in Comps |-> IF x = y THEN v ELSE None] : y \in Comps, v \in CD}
        \cup {[x \in Comps |-> v] : v \in CD}
CSet == {[conf |-> cf, amp |-> am, hs |-> f["hs"], rec |-> f["rec"], ack |-> f["ack"], path |-> f["path"],
          rekey |-> f["rekey"], paced |-> f["paced"], mtu |-> f["mtu"]] : cf \in BOOLEAN, am \in BOOLEAN, f \in Pats}
CC == {"none", "dead", "hs", "unconf"}
CloseWhy == {"local", "peer", "viol", "idle", "dead", "hs", "unconf"}

\* the inputs of the carrier rule. PR0 has no probe timeout; Shape(t, p, rl, pt, c) is a call at t with a carrier
\* heard at c, the peer last heard at 0 and a smoothed round trip of 1 (4 round trips of silence from t = 4)
PR0 == [ping |-> FALSE, relay |-> FALSE, ch |-> None, pto |-> 0, lh |-> 0, smp |-> TRUE, sr |-> 1, nd |-> 0]
Shape(t, p, rl, pt, c) == [ping |-> p, relay |-> rl, ch |-> c, pto |-> pt, lh |-> 0, smp |-> TRUE, sr |-> 1, nd |-> 0]
\* the shapes the transitions take (the rule over every input is CarrierPure) and the properties check
Move(t) == {PR0, Shape(t, TRUE, TRUE, 4, t)}
ShapeSet(t) == {Shape(t, p, rl, pt, c) : p \in BOOLEAN, rl \in BOOLEAN, pt \in {3, 4}, c \in {None, 0, t}}
\* every input of the rule
FullSet == {[ping |-> TRUE, relay |-> rl, ch |-> c, pto |-> pt, lh |-> l, smp |-> sm, sr |-> sr, nd |-> nd] :
              rl \in BOOLEAN, c \in {None} \cup 0..TMAX, pt \in 3..5, l \in 0..TMAX, sm \in BOOLEAN, sr \in 0..2, nd \in 0..1}

S0(ph) == [ph |-> ph, close |-> None, keys |-> ph = "conn", act |-> 0, sent |-> 0, ka |-> None, pa |-> None,
           la |-> FALSE, stx |-> 0, wd |-> None, ld |-> None]

Init == s \in {S0("hs"), S0("conn")} /\ now = 0 /\ n = 0 /\ closes = 0 /\ why = "none"

\* a step to the state r.s with the events r.ev; the reason of the end is kept
Reason(ev) == CHOOSE x \in {ev[i] : i \in DOMAIN ev} : x \in CloseWhy
\* a close that began with a CLOSE to send at a timeout is a carrier close (no other timeout call sets s.close)
DoW(r, w) == /\ s' = r.s /\ n' = n + 1 /\ UNCHANGED now /\ why' = w
Do(r) == DoW(r, IF Open(s) /\ ~Open(r.s) THEN Reason(r.ev) ELSE why)
Plain(x) == Do([s |-> x, ev |-> <<>>]) /\ UNCHANGED closes

Tick == now < TMAX /\ now' = now + 1 /\ UNCHANGED <<s, n, closes, why>>
\* the handshake decides "hs" only while handshaking (pump: Phase::Handshaking) and "unconf" only while connected
\* (pump: Phase::Connected)
TimeoutA == \E cc \in CC, pr \in Move(now) :
              /\ (cc = "hs" => s.ph = "hs")
              /\ (cc = "unconf" => s.ph = "conn")
              /\ LET r == TimeoutB(s, now, cc, pr, K, BUG)
                 IN DoW(r, IF Open(s) /\ ~Open(r.s) THEN (IF r.s.close # None THEN "carrier" ELSE Reason(r.ev)) ELSE why)
              /\ UNCHANGED closes
RecvA == \E heard, sleep, close \in BOOLEAN :
           ((sleep \/ close) => heard) /\ Do(RecvB(s, now, heard, sleep, close, BUG)) /\ UNCHANGED closes
BadA == Do(Bad(s, ERR)) /\ UNCHANGED closes
ViolA == Do(Viol(s, now, ERR)) /\ UNCHANGED closes
CloseA == \E e \in {0, ERR} : Do(Close(s, e)) /\ UNCHANGED closes
TxA == \E sent \in BOOLEAN, stx \in 0..s.stx :
         /\ sent => CanSend(s)
         /\ stx < s.stx => sent
         /\ Do([s |-> Tx(s, now, sent, stx), ev |-> <<>>]) /\ closes' = closes + (IF TxClose(s, sent) THEN 1 ELSE 0)
SleepA == Plain(Sleep(s))
WakeA == Plain(Wake(s, now, K))
LinkA == \E down \in BOOLEAN : Plain(Link(s, now, down, K))
KeepA == \E ka \in KAS \cup {None} : Plain(Keepalive(s, ka))
PulseA == \E sent \in BOOLEAN : Plain(Pulse(s, now, sent))
EstA == Plain(Est(s, now))

Next == Tick \/ TimeoutA \/ RecvA \/ BadA \/ ViolA \/ CloseA \/ TxA \/ SleepA \/ WakeA \/ LinkA \/ KeepA \/ PulseA \/ EstA
Spec == Init /\ [][Next]_vars
Bound == n <= KMAX

\* ---- poll_timeout ----
\* the deadlines poll_timeout reads in the state s with the components c, as a set: the idle deadline always, the
\* end of the outage, the wake wait and (with the link down) recovery while nothing can leave; all of them otherwise,
\* each under its gate
Some(x) == IF x = None THEN {} ELSE {x}
Enabled(c) ==
    {Idle(s, K)} \cup Some(LinkEnd(s, K)) \cup Some(s.wd)
    \cup (IF Suspended(s) THEN (IF s.ld # None THEN Some(c.rec) ELSE {})
          ELSE Some(c.rekey) \cup Some(c.rec) \cup Some(c.paced) \cup Some(c.path)
               \cup (IF ~c.conf THEN Some(c.hs) ELSE {}) \cup (IF c.amp THEN Some(c.ack) ELSE {})
               \cup (IF s.ph = "conn" THEN Some(KeepDue(s)) \cup Some(c.mtu) ELSE {}))
MinOf(X) == CHOOSE x \in X : \A y \in X : x <= y
PollMin == Open(s) => \A c \in CSet : LET p == PollB(s, c, K, BUG)
                                          E == Enabled(c)
                                      IN p \in E /\ \A y \in E : p <= y
PollPhase == \A c \in CSet : (Poll(s, c, K) = None <=> s.ph = "closed") /\ (s.ph = "closing" => Poll(s, c, K) = 0)
\* the first of the lifecycle's own deadlines
LifeDue == MinOf({Idle(s, K)} \cup Some(LinkEnd(s, K)) \cup Some(s.wd))
PollLeLife == Open(s) => LET L == LifeDue IN \A c \in CSet : PollB(s, c, K, BUG) <= L

\* ---- handle_timeout, at every time from now on ----
Times == now..TMAX
EarlyNothing == Open(s) => LET L == LifeDue IN
                  \A t \in Times : t < L => Timeout(s, t, "none", PR0, K) = [s |-> s, ev |-> <<>>]
Has(ev, x) == \E i \in DOMAIN ev : ev[i] = x
IdleExact == Open(s) => \A t \in Times : \A cc \in CC, pr \in Move(t) :
               LET r == Timeout(s, t, cc, pr, K) IN
               /\ t >= Idle(s, K) => r = [s |-> Silent(s), ev |-> <<"idle">>]
               /\ t < Idle(s, K) => ~Has(r.ev, "idle")
DueWork == Open(s) => \A t \in Times : \A cc \in CC, pr \in Move(t) :
             LET r == Timeout(s, t, cc, pr, K) IN
             t < Idle(s, K) =>
               /\ Has(r.ev, "unanswered") = (s.wd # None /\ s.wd <= t)
               /\ (r.s.wd = None) = (s.wd = None \/ s.wd <= t)
               /\ (r.s.ld = None) = (s.ld = None \/ s.ld + LDM <= t)
               /\ (Has(r.ev, "dead") \/ Has(r.ev, "hs") \/ Has(r.ev, "unconf")) = ~Open(r.s)
NoStale == Open(s) => \A t \in Times : \A cc \in CC, pr \in Move(t) :
             LET r == Timeout(s, t, cc, pr, K) IN
             Open(r.s) => /\ Idle(r.s, K) > t
                          /\ LinkEnd(r.s, K) = None \/ LinkEnd(r.s, K) > t
                          /\ r.s.wd = None \/ r.s.wd > t

\* ---- closing ----
OneClose == /\ closes <= 1
            /\ s.ph = "closing" => closes = 0 /\ s.close # None
            /\ closes = 1 => s.ph = "closed" /\ s.close = None
SilentEnd == why \in {"peer", "idle", "dead", "hs", "unconf"} => closes = 0 /\ s.ph = "closed" /\ s.close = None
\* the handshake's own ends, at a timer call before the idle deadline: a handshaking connection whose handshake ran out
\* of time and a connected one whose peer never confirmed the session end silently, each reported as its own reason
\* and only in its own phase
HsEnds == Open(s) => \A t \in Times : \A cc \in CC, pr \in Move(t) :
            LET r == TimeoutB(s, t, cc, pr, K, BUG) IN
            t < Idle(s, K) =>
              /\ Has(r.ev, "hs") = (cc = "hs" /\ s.ph = "hs")
              /\ Has(r.ev, "unconf") = (cc = "unconf" /\ s.ph = "conn")
              /\ (Has(r.ev, "hs") \/ Has(r.ev, "unconf")) => r.s.ph = "closed" /\ r.s.close = None
\* closed: no timer, nothing leaves, nothing is taken, and no call but keepalive and pulse changes anything
ClosedInert == s.ph = "closed" =>
                 /\ ~CanSend(s) /\ ~AppOpen(s) /\ \A c \in CSet : Poll(s, c, K) = None
                 /\ \A t \in Times : \A cc \in CC, pr \in Move(t) : Timeout(s, t, cc, pr, K) = [s |-> s, ev |-> <<>>]
                 /\ \A h, sl, cl \in BOOLEAN : Recv(s, now, h, sl, cl) = [s |-> s, ev |-> <<>>]
                 /\ Close(s, ERR) = [s |-> s, ev |-> <<>>]
                 /\ Bad(s, ERR) = [s |-> s, ev |-> <<>>] /\ Viol(s, now, ERR) = [s |-> s, ev |-> <<>>]
                 /\ \A sent \in BOOLEAN : Tx(s, now, sent, 0) = s
                 /\ Sleep(s) = s /\ Wake(s, now, K) = s /\ \A d \in BOOLEAN : Link(s, now, d, K) = s
KeysWhenConnected == s.ph \in {"conn", "closing"} => s.keys

\* ---- the idle timer and the sleep hold ----
IdleRestart == Open(s) => \A sl, cl \in BOOLEAN :
                 /\ Recv(s, now, FALSE, FALSE, FALSE) = [s |-> s, ev |-> <<>>]
                 /\ LET r == RecvB(s, now, TRUE, sl, cl, BUG) IN
                    r.s.act = now /\ r.s.wd = None /\ Idle(r.s, K) >= now + IDLE
SleepHold == s.pa # None => Idle(s, K) >= s.pa + HOLD
TimesPast == /\ s.act <= now /\ s.sent <= now /\ s.pa <= now /\ s.ld <= now /\ s.wd <= now + WAKE

\* ---- the close behind a live carrier ----
\* the rule as the comment of the code states it, written apart from CarrierB: a relay path, a carrier heard less than
\* CF ago, 4 probe timeouts in a row, nothing heard for 4 round trips (a peer "heard" after now has been silent for
\* no time, which is below 4 round trips unless the round trip is 0)
CarrierSpec(t, pr) == /\ pr.relay /\ pr.ch # None /\ (pr.ch > t \/ t - pr.ch < CF)
                      /\ pr.pto >= 4
                      /\ (4 * Rtt(pr, K) + pr.lh <= t \/ Rtt(pr, K) = 0)
\* the rule over every input (and every shape of a round trip: with a sample or the fallback of the node)
ASSUME \A t \in 0..TMAX, pr \in FullSet : Carrier(t, pr, K) = CarrierSpec(t, pr)
\* at a timer call before the idle deadline: a CLOSE is to leave only if the rule holds at a probe timeout and the path
\* is not dead; and when the rule holds at a probe timeout, the path is not dead and the call did not end the
\* connection first (a handshake timeout, or a session its peer never confirmed), the close begins with error 0 and is
\* reported as PathDead
CarrierClose == Open(s) => \A t \in Times : \A cc \in CC, pr \in ShapeSet(t) :
                  LET r == TimeoutB(s, t, cc, pr, K, BUG) IN
                  t < Idle(s, K) =>
                    /\ r.s.close # None => pr.ping /\ cc # "dead" /\ CarrierSpec(t, pr)
                    /\ (pr.ping /\ cc # "dead" /\ ~(cc = "hs" /\ s.ph = "hs") /\ ~(cc = "unconf" /\ s.ph = "conn")
                        /\ CarrierSpec(t, pr))
                         => r.s.close = 0 /\ Has(r.ev, "dead")
\* a carrier close ended the connection or owes its CLOSE with error 0
CarrierEnd == why = "carrier" => ~Open(s) /\ (s.ph = "closing" => s.close = 0)

Inv == /\ PollMin /\ PollPhase /\ PollLeLife /\ EarlyNothing /\ IdleExact /\ DueWork /\ NoStale
       /\ OneClose /\ SilentEnd /\ HsEnds /\ ClosedInert /\ KeysWhenConnected /\ IdleRestart /\ SleepHold /\ TimesPast
       /\ CarrierClose /\ CarrierEnd

\* ---- witnesses ----
NoCloseSent == closes = 0
NoCarrierClose == why # "carrier"
=============================================================================
