------------------------------ MODULE BroadcastPush ------------------------------
(***************************************************************************)
(* A hub pushing a topic to its live subscribers over streams that fill    *)
(* up: vinc-broadcast msg.rs (Topics::hub_store), behind.rs                 *)
(* (Topics::fall_behind, Topics::room_to_store, Topics::peer_writable) and *)
(* log.rs (HubLog::evicts). One publisher hands the hub messages 1..N in   *)
(* any order, again and again until one is stored; the hub stores it in a  *)
(* log of LogCap entries, acknowledges it (PACK follows the store) and     *)
(* pushes it into each subscriber's stream, which holds StreamCap frames   *)
(* and drains one at a time at the subscriber's pace.                      *)
(*                                                                         *)
(* When a stream is full the push is refused. The hub then marks the      *)
(* subscriber behind at that message's log position, pushes it nothing     *)
(* new directly, and when the stream has room (writable) sends it the log  *)
(* from that position on. A store that would evict a message still owed to *)
(* a behind subscriber is refused, so the publisher is not acknowledged    *)
(* and tries again later. A subscriber whose stream stalls (PUSH_STALL) or *)
(* that falls too far behind (PUSH_OWED_MAX) is let go (LetGo): it is      *)
(* held, stops pacing the topic, and keeps catching up from the log; the   *)
(* positions the log evicted before it got to them are `missed`, and when  *)
(* it has caught up the hub tells it (RESTORED), which moves them to       *)
(* `told`.                                                                 *)
(*                                                                         *)
(* What must never happen: a message the publisher heard acknowledged     *)
(* that a subscriber neither got, nor has in its stream, nor is owed from  *)
(* the log, nor was told it missed (AckedReachesLive). Checked as well:    *)
(* only a subscriber that was let go misses anything (MissedOnlyHeld); a   *)
(* position a pacing subscriber is owed is still in the log (OwedInLog);   *)
(* the streams and the log stay within their room (Bounds); and, with fair *)
(* streams and a publisher that keeps trying, every message is in the end  *)
(* acknowledged (AllAcked).                                                *)
(*                                                                         *)
(* Cursor = Guard = Tell = TRUE is the code.                               *)
(* BroadcastPush_nocursor.cfg sets Cursor = FALSE: the code before         *)
(* 05bf029, where a refused push was dropped after the publish was        *)
(* acknowledged; TLC finds AckedReachesLive violated.                      *)
(* BroadcastPush_noguard.cfg sets Guard = FALSE: the place in the log      *)
(* without the store refusal (05bf029 alone, option 2 of vinc#74), where a *)
(* burst longer than the log evicts what a subscriber is owed after it was *)
(* acknowledged; TLC finds OwedInLog violated.                             *)
(* BroadcastPush_notell.cfg sets Tell = FALSE: a let-go subscriber catches *)
(* up past a gap and is never told; TLC finds AckedReachesLive violated.   *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/BroadcastLogModel.lean (pushOwed,    *)
(* pushOwed_inv, pushOwed_keeps_owed, pushOwed_refused).                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* Subs: the subscribers; N: how many messages the publisher has; LogCap: LOG_CAP (the log's room, in entries);
\* StreamCap: how many frames a stream holds before it refuses (out_cap); Cursor, Guard, Tell: the parts of the fix
CONSTANTS Subs, N, LogCap, StreamCap, Cursor, Guard, Tell

\* msgAt: the message stored at each log position, positions 1..Len(msgAt), oldest first; base: the oldest position
\* still in the log; acked: the messages the publisher heard acknowledged; stream: each subscriber's frames in flight,
\* oldest first; got: what each subscriber received; behind: the first position each subscriber is owed, 0 when it
\* is not behind; held: the subscribers let go; missed: the positions each skipped because the log evicted them;
\* told: the positions each was told it missed
VARIABLES msgAt, base, acked, stream, got, behind, held, missed, told
vars == <<msgAt, base, acked, stream, got, behind, held, missed, told>>

\* the newest position in the log (0 while nothing is stored)
Top == Len(msgAt)
\* the position each message was stored at, for the messages that were stored
PosOf(m) == CHOOSE i \in 1..Top : msgAt[i] = m

Init == /\ msgAt = <<>> /\ base = 1 /\ acked = {}
        /\ stream = [s \in Subs |-> <<>>] /\ got = [s \in Subs |-> {}]
        /\ behind = [s \in Subs |-> 0] /\ held = {}
        /\ missed = [s \in Subs |-> {}] /\ told = [s \in Subs |-> {}]

\* Topics::hub_store with message m. The new entry goes to position Top + 1. With LogCap entries already in the log,
\* the oldest (base) is evicted to make room (HubLog::evicts says so before anything moves). With the guard
\* (Topics::room_to_store), a store
\* that would evict a position a pacing (not held) subscriber is still owed is refused: nothing changes and m is not
\* acknowledged. Otherwise m is stored and acknowledged, and pushed into every stream that is not behind: a full stream
\* refuses it, and with the cursor the subscriber is marked behind at m's position; without it the push is just lost.
Store(m) ==
    /\ m \notin acked
    /\ LET evict == Top - base + 1 >= LogCap
           owedLost == evict /\ \E s \in Subs \ held : behind[s] = base
           pos == Top + 1
       IN /\ ~(Guard /\ owedLost)
          /\ msgAt' = Append(msgAt, m)
          /\ base' = IF evict THEN base + 1 ELSE base
          /\ acked' = acked \union {m}
          /\ stream' = [s \in Subs |->
                IF behind[s] = 0 /\ Len(stream[s]) < StreamCap THEN Append(stream[s], m) ELSE stream[s]]
          /\ behind' = [s \in Subs |->
                IF Cursor /\ behind[s] = 0 /\ Len(stream[s]) >= StreamCap THEN pos ELSE behind[s]]
    /\ UNCHANGED <<got, held, missed, told>>

\* the subscriber reads the oldest frame of its stream
Drain(s) ==
    /\ stream[s] /= <<>>
    /\ got' = [got EXCEPT ![s] = @ \union {Head(stream[s])}]
    /\ stream' = [stream EXCEPT ![s] = Tail(@)]
    /\ UNCHANGED <<msgAt, base, acked, behind, held, missed, told>>

\* Topics::peer_writable: the stream has room, so the hub sends the next owed position, or the oldest still logged if the
\* log evicted the owed ones (`max(next, base)`; the skipped positions are missed). Once the newest position is sent
\* the subscriber is caught up: it is no longer behind or held, and with Tell it is sent RESTORED, so what it missed
\* is told. The Rust loop is this step repeated until the stream refuses or the subscriber is caught up.
Writable(s) ==
    /\ behind[s] /= 0
    /\ Len(stream[s]) < StreamCap
    /\ LET k == IF behind[s] < base THEN base ELSE behind[s]
           \* the positions skipped now (empty when nothing was evicted), added to those skipped before
           gap == missed[s] \union (behind[s]..(k - 1))
           done == k + 1 > Top
       IN /\ stream' = [stream EXCEPT ![s] = Append(@, msgAt[k])]
          /\ behind' = [behind EXCEPT ![s] = IF done THEN 0 ELSE k + 1]
          /\ held' = IF done THEN held \ {s} ELSE held
          /\ missed' = [missed EXCEPT ![s] = IF done THEN {} ELSE gap]
          /\ told' = [told EXCEPT ![s] = IF done /\ Tell THEN @ \union gap ELSE @]
    /\ UNCHANGED <<msgAt, base, acked, got>>

\* the store's PUSH_STALL and PUSH_OWED_MAX rules: a behind subscriber is let go (the timing is not modelled, so TLC
\* may let any behind subscriber go at any time)
LetGo(s) ==
    /\ behind[s] /= 0 /\ s \notin held
    /\ held' = held \union {s}
    /\ UNCHANGED <<msgAt, base, acked, stream, got, behind, missed, told>>

Next == \/ \E m \in 1..N : Store(m)
        \/ \E s \in Subs : Drain(s) \/ Writable(s) \/ LetGo(s)

\* streams drain, the hub answers writable, and the publisher keeps retrying; letting a subscriber go is never forced
Spec == /\ Init /\ [][Next]_vars
        /\ \A s \in Subs : WF_vars(Drain(s)) /\ WF_vars(Writable(s))
        /\ \A m \in 1..N : WF_vars(Store(m))

(* ---------------------------- the checked properties ---------------------------- *)
\* every acknowledged message reaches every subscriber: received, in its stream, owed from the position it is behind
\* at, or a position it missed and is told about once caught up (or was told about)
AckedReachesLive ==
    \A s \in Subs : \A m \in acked :
        \/ m \in got[s]
        \/ \E i \in 1..Len(stream[s]) : stream[s][i] = m
        \/ behind[s] /= 0 /\ PosOf(m) >= behind[s]
        \/ PosOf(m) \in missed[s] \union told[s]
\* only a subscriber that was let go misses anything
MissedOnlyHeld == \A s \in Subs : missed[s] /= {} => s \in held
\* a position a pacing subscriber is owed is still in the log
OwedInLog == \A s \in Subs : behind[s] /= 0 /\ s \notin held => base <= behind[s] /\ behind[s] <= Top
\* the streams and the log stay within their room
Bounds == /\ \A s \in Subs : Len(stream[s]) <= StreamCap
          /\ Top - base + 1 <= LogCap
\* with fair streams and a publisher that keeps trying, every message ends acknowledged
AllAcked == <>(acked = 1..N)
=============================================================================
