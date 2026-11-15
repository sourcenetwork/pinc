------------------------------ MODULE BroadcastPush ------------------------------
(***************************************************************************)
(* A hub pushing a topic to its live subscribers over streams that fill    *)
(* up: vinc-broadcast msg.rs (Topics::hub_store), behind.rs                 *)
(* (Topics::fall_behind, Topics::room_to_store, Topics::peer_writable),    *)
(* gap.rs (Topics::on_sub) and log.rs (HubLog::evicts). One publisher      *)
(* hands the hub messages 1..N in any order, again and again until one is  *)
(* stored; the hub stores it in a log of LogCap entries, acknowledges it   *)
(* (PACK follows the store) and pushes it into each subscriber's stream,   *)
(* which holds StreamCap frames and drains one at a time at the            *)
(* subscriber's pace.                                                      *)
(*                                                                         *)
(* When a stream is full the push is refused. The hub then marks the      *)
(* subscriber behind at that message's log position, pushes it nothing     *)
(* new directly, and when it is woken sends it the log from that position  *)
(* on. The host wakes it (StreamWritable, vinc-node events.rs) only when a *)
(* stream that was full takes more bytes. A store that would evict a       *)
(* message still owed to a behind subscriber is refused, so the publisher  *)
(* is not acknowledged and tries again later. A subscriber whose stream    *)
(* stalls (PUSH_STALL) or that falls too far behind (PUSH_OWED_MAX) is let *)
(* go (LetGo): it is held, stops pacing the topic, and keeps catching up   *)
(* from the log; the positions the log evicted before it got to them are   *)
(* `missed`, and when it has caught up the hub tells it (RESTORED), which  *)
(* moves them to `told`.                                                   *)
(*                                                                         *)
(* A subscriber's session can be replaced (Swap): the old stream is gone   *)
(* and the new one is empty, so it never was full and no host wakes the    *)
(* hub for it. The subscriber subscribes again on the new session (Sub,    *)
(* membership's resubscribe). With Resume, a SUB from a subscriber the hub *)
(* keeps behind wakes its catch-up (on_sub calls peer_writable).           *)
(*                                                                         *)
(* What must never happen: a message the publisher heard acknowledged     *)
(* that a subscriber neither got, nor has in its stream, nor is owed from  *)
(* the log, nor was told it missed (AckedReachesLive). Checked as well:    *)
(* only a subscriber that was let go misses anything (MissedOnlyHeld); a   *)
(* position a pacing subscriber is owed is still in the log (OwedInLog);   *)
(* the streams and the log stay within their room (Bounds); a subscriber   *)
(* that is behind is woken, or has a full stream that will wake it, or     *)
(* has a SUB on its way (WakeOrPending); with fair streams and a publisher *)
(* that keeps trying, every message is in the end acknowledged (AllAcked)  *)
(* and every subscriber that is behind in the end catches up (LiveAgain).  *)
(*                                                                         *)
(* Cursor = Guard = Tell = Resume = TRUE is the code.                      *)
(* BroadcastPush_nocursor.cfg sets Cursor = FALSE: the code before         *)
(* 05bf029, where a refused push was dropped after the publish was        *)
(* acknowledged; TLC finds AckedReachesLive violated.                      *)
(* BroadcastPush_noguard.cfg sets Guard = FALSE: the place in the log      *)
(* without the store refusal (05bf029 alone, option 2 of vinc#74), where a *)
(* burst longer than the log evicts what a subscriber is owed after it was *)
(* acknowledged; TLC finds OwedInLog violated.                             *)
(* BroadcastPush_notell.cfg sets Tell = FALSE: a let-go subscriber catches *)
(* up past a gap and is never told; TLC finds AckedReachesLive violated.   *)
(* BroadcastPush_noresume.cfg sets Resume = FALSE: the code before this    *)
(* change, where a subscriber that fell behind and got a new session is    *)
(* never woken again, so it is pushed nothing live and only a periodic gap *)
(* repair reaches it; TLC finds WakeOrPending violated.                    *)
(* BroadcastPush_noresume_live.cfg is the same plant checked for liveness: *)
(* TLC finds LiveAgain violated (the subscriber stays behind for ever).    *)
(*                                                                         *)
(* A subscriber's session can also end at the hub (End): membership then   *)
(* releases the subscriber, so the hub forgets its place, and what was in  *)
(* its stream is gone. The subscriber comes back and subscribes (Sub): the *)
(* hub offers its log (HAVE) and the subscriber asks for the positions it  *)
(* lacks (GET, `ask`). The hub answers into the new stream (Get, gap.rs    *)
(* Topics::on_get; the replay of a SUB is the same step): what the stream  *)
(* has room for is sent, in order. With Owe, the subscriber is behind from *)
(* the first position that found the stream full, let go from the start    *)
(* (a repair never paces the topic), and is caught up from the log like    *)
(* any subscriber that is behind. BroadcastPush_getdrop.cfg sets Owe =     *)
(* FALSE, the code before vinc#504, where the rest of the GET was dropped: *)
(* TLC finds AckedReachesLive violated. BroadcastPush_repair.cfg checks    *)
(* the step with Ends = 1.                                                 *)
(*                                                                         *)
(* A session may end at any time, and the log evicts freely while the      *)
(* subscriber is away or its GET is on its way (vinc#505). The hub then    *)
(* cannot give the subscriber everything, and says so (RESTORED), by       *)
(* three rules, each an element of Notice. "sub": the SUB that makes the   *)
(* subscriber live again asks from a position (`p`, the time `since` of    *)
(* the frame) at or before one the log dropped (HubLog::dropped_since).    *)
(* "forgot": the subscriber was behind when its session ended, the hub     *)
(* forgot its place (Topic::forget_place) and the SUB asks from after the  *)
(* first position it was owed there, so the answer does not reach back to  *)
(* it (Topic::forgot_since; `left` is that position, -1 when the place had *)
(* already lost something). "get": the GET names a position the log        *)
(* dropped since it was offered. The code keeps one span for the topic     *)
(* where the model keeps `left` for each subscriber: the span covers every *)
(* such subscriber and may tell others too, which no property forbids.     *)
(* The code sends the notice of a GET to a subscriber that is behind once  *)
(* it has caught up; the model counts it as told at once. The replay a     *)
(* restarted member asks for from its floor is judged by the rule "sub",   *)
(* as the SUB of a released subscriber is: End and Sub are that too.       *)
(* What a SUB asks from: every position the subscriber lacks is at or      *)
(* after it, except those the hub owed it at the place it forgot (its last *)
(* receipt can be later than those were logged), which is why "forgot" is  *)
(* a rule of its own. BroadcastPush_nosubtell.cfg, _noforgot.cfg and       *)
(* _nogettell.cfg each leave one rule out: TLC finds AckedReachesLive      *)
(* violated. BroadcastPush_away.cfg checks the three with Ends = 1.        *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/BroadcastLogModel.lean (pushOwed,    *)
(* pushOwed_inv, pushOwed_keeps_owed, pushOwed_refused) and                *)
(* proofs/lean/Vinc/BroadcastWake.lean (wake_inv, wake_stuck_without).     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

\* Subs: the subscribers; N: how many messages the publisher has; LogCap: LOG_CAP (the log's room, in entries);
\* StreamCap: how many frames a stream holds before it refuses (out_cap); Swaps: how many times each subscriber's
\* session may be replaced (a bound for TLC); Cursor, Guard, Tell, Resume: the parts of the fix
\* Ends: how many times each subscriber's session may end at the hub (a bound for TLC); Owe: a GET answered into a
\* stream that fills keeps the subscriber's place (vinc#504); Notice: the rules by which the hub tells a subscriber it
\* cannot give it everything it asks for, a subset of {"sub", "forgot", "get"} (vinc#505; all three is the code)
CONSTANTS Subs, N, LogCap, StreamCap, Swaps, Cursor, Guard, Tell, Resume, Ends, Owe, Notice

\* msgAt: the message stored at each log position, positions 1..Len(msgAt), oldest first; base: the oldest position
\* still in the log; acked: the messages the publisher heard acknowledged; stream: each subscriber's frames in flight,
\* oldest first; got: what each subscriber received; behind: the first position each subscriber is owed, 0 when it
\* is not behind; held: the subscribers let go; missed: the positions each skipped because the log evicted them;
\* told: the positions each was told it missed; wake: the host told the hub that the subscriber's stream has room
\* (the hub's `lagging` entry is being served); subq: a SUB from the subscriber's new session is on its way; swaps:
\* how many times each subscriber's session was replaced
\* ask: the positions each subscriber asked for in a GET the hub has yet to answer; ends: how many times each
\* subscriber's session ended at the hub; gone: the subscribers the hub released and has not heard a SUB from since;
\* left: the first position the hub owed each subscriber at the place it forgot when the session ended (0: it was
\* not behind; -1: the place had already lost a position)
VARIABLES msgAt, base, acked, stream, got, behind, held, missed, told, wake, subq, swaps, ask, ends, gone, left
vars == <<msgAt, base, acked, stream, got, behind, held, missed, told, wake, subq, swaps, ask, ends, gone, left>>
\* the variables of the repair step
rp == <<ask, ends, gone, left>>

\* the newest position in the log (0 while nothing is stored)
Top == Len(msgAt)
\* the position each message was stored at, for the messages that were stored
PosOf(m) == CHOOSE i \in 1..Top : msgAt[i] = m
\* the set of the frames in a stream
Frames(q) == {q[i] : i \in 1..Len(q)}
\* the lowest of a set of positions
Lowest(S) == CHOOSE x \in S : \A y \in S : x <= y
\* the k lowest positions of S
Firsts(S, k) == {i \in S : Cardinality({j \in S : j < i}) < k}
\* stream q with the messages at the positions S appended, oldest first
RECURSIVE Fill(_, _)
Fill(q, S) == IF S = {} THEN q ELSE Fill(Append(q, msgAt[Lowest(S)]), S \ {Lowest(S)})
\* the logged positions subscriber s lacks and is not owed from its place
Lacks(s) == {i \in base..Top : /\ msgAt[i] \notin got[s] \union Frames(stream[s])
                               /\ (behind[s] = 0 \/ i < behind[s])}
\* the positions a SUB of released subscriber s may ask from: every position s lacks is at or after it, except those
\* the hub owed it at the place it forgot
Since(s) == {p \in 1..(Top + 1) :
                \A i \in 1..Top : (msgAt[i] \notin got[s] /\ (left[s] = 0 \/ i < left[s])) => i >= p}

\* nothing stored, every stream empty, nobody behind, woken, resubscribing or swapped
Init == /\ msgAt = <<>> /\ base = 1 /\ acked = {}
        /\ stream = [s \in Subs |-> <<>>] /\ got = [s \in Subs |-> {}]
        /\ behind = [s \in Subs |-> 0] /\ held = {}
        /\ missed = [s \in Subs |-> {}] /\ told = [s \in Subs |-> {}]
        /\ wake = [s \in Subs |-> FALSE] /\ subq = [s \in Subs |-> FALSE] /\ swaps = [s \in Subs |-> 0]
        /\ ask = [s \in Subs |-> {}] /\ ends = [s \in Subs |-> 0]
        /\ gone = {} /\ left = [s \in Subs |-> 0]

\* Topics::hub_store with message m. The new entry goes to position Top + 1. With LogCap entries already in the log,
\* the oldest (base) is evicted to make room (HubLog::evicts says so before anything moves). With the guard
\* (Topics::room_to_store), a store
\* that would evict a position a pacing (not held) subscriber is still owed is refused: nothing changes and m is not
\* acknowledged. Otherwise m is stored and acknowledged, and pushed into every stream that is not behind: a full stream
\* refuses it, and with the cursor the subscriber is marked behind at m's position; without it the push is just lost.
\* A subscriber the hub released is pushed nothing and has no place.
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
                IF s \notin gone /\ behind[s] = 0 /\ Len(stream[s]) < StreamCap
                THEN Append(stream[s], m) ELSE stream[s]]
          /\ behind' = [s \in Subs |->
                IF Cursor /\ s \notin gone /\ behind[s] = 0 /\ Len(stream[s]) >= StreamCap
                THEN pos ELSE behind[s]]
    /\ UNCHANGED <<got, held, missed, told, wake, subq, swaps>> /\ UNCHANGED rp

\* the subscriber reads the oldest frame of its stream; a stream that was full now has room, and the host wakes the
\* hub for it (StreamWritable), which serves a subscriber that is behind (peer_writable does nothing for any other)
Drain(s) ==
    /\ stream[s] /= <<>>
    /\ got' = [got EXCEPT ![s] = @ \union {Head(stream[s])}]
    /\ stream' = [stream EXCEPT ![s] = Tail(@)]
    /\ wake' = [wake EXCEPT ![s] = @ \/ (Len(stream[s]) >= StreamCap /\ behind[s] /= 0)]
    /\ UNCHANGED <<msgAt, base, acked, behind, held, missed, told, subq, swaps>> /\ UNCHANGED rp

\* Topics::peer_writable, once woken: the stream has room, so the hub sends the next owed position, or the oldest still
\* logged if the log evicted the owed ones (`max(next, base)`; the skipped positions are missed). Once the newest
\* position is sent the subscriber is caught up: it is no longer behind, held or woken, and with Tell it is sent
\* RESTORED, so what it missed is told. The Rust loop is this step repeated until the stream refuses or the subscriber
\* is caught up.
Writable(s) ==
    /\ wake[s]
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
          /\ wake' = [wake EXCEPT ![s] = ~done]
    /\ UNCHANGED <<msgAt, base, acked, got, subq, swaps>> /\ UNCHANGED rp

\* the store's PUSH_STALL and PUSH_OWED_MAX rules: a behind subscriber is let go (the timing is not modelled, so TLC
\* may let any behind subscriber go at any time)
LetGo(s) ==
    /\ behind[s] /= 0 /\ s \notin held
    /\ held' = held \union {s}
    /\ UNCHANGED <<msgAt, base, acked, stream, got, behind, missed, told, wake, subq, swaps>> /\ UNCHANGED rp

\* the subscriber's session is replaced: the new stream is empty and was never full, so no host wakes the hub for it,
\* and the subscriber sends a SUB on it. The frames of the old stream are asked for again by that SUB, from the
\* subscriber's last receipt, and repaired from the log (BroadcastRepair.tla): they count as received here.
Swap(s) ==
    /\ swaps[s] < Swaps
    /\ got' = [got EXCEPT ![s] = @ \union Frames(stream[s])]
    /\ stream' = [stream EXCEPT ![s] = <<>>]
    /\ wake' = [wake EXCEPT ![s] = FALSE]
    /\ subq' = [subq EXCEPT ![s] = TRUE]
    /\ swaps' = [swaps EXCEPT ![s] = @ + 1]
    /\ UNCHANGED <<msgAt, base, acked, behind, held, missed, told>> /\ UNCHANGED rp

\* Topics::on_sub at the hub: with Resume, a subscriber it keeps behind is woken, so its catch-up goes on from its place
\* in the log; without it nothing wakes the subscriber. The hub offers its log (HAVE) and the subscriber asks for the
\* positions it lacks (GET), which is on its way to the hub from here. A released subscriber becomes live again: its
\* SUB asks from a position p, the hub offers what it holds from p on, and it tells the subscriber if the log dropped
\* a position from p on ("sub") or if p lies after the first position the hub owed it at the place it forgot
\* ("forgot"); what is told is everything the subscriber lacks and the answer does not fetch
Sub(s) ==
    /\ subq[s]
    /\ subq' = [subq EXCEPT ![s] = FALSE]
    /\ wake' = [wake EXCEPT ![s] = @ \/ (Resume /\ behind[s] /= 0)]
    /\ \E p \in (IF s \in gone THEN Since(s) ELSE {1}) :
          LET asked == {i \in Lacks(s) : i >= p}
              unmet == {i \in 1..Top : msgAt[i] \notin got[s]} \ asked
              short == /\ s \in gone
                       /\ \/ "sub" \in Notice /\ p < base
                          \/ "forgot" \in Notice /\ left[s] /= 0 /\ left[s] < p
          IN /\ ask' = [ask EXCEPT ![s] = asked]
             /\ told' = [told EXCEPT ![s] = IF short THEN @ \union unmet ELSE @]
    /\ gone' = gone \ {s}
    /\ left' = [left EXCEPT ![s] = 0]
    /\ UNCHANGED <<msgAt, base, acked, stream, got, behind, held, missed, swaps, ends>>

\* the subscriber's session ends at the hub and membership releases the subscriber (drop_peer, Topics::release): its
\* place is forgotten, with what the hub knew it had skipped, what was in its stream is gone, and it comes back and
\* subscribes on a new session. The hub keeps where the place it forgot began (Topic::forget_place)
End(s) ==
    /\ ends[s] < Ends
    /\ stream' = [stream EXCEPT ![s] = <<>>]
    /\ behind' = [behind EXCEPT ![s] = 0]
    /\ held' = held \ {s}
    /\ missed' = [missed EXCEPT ![s] = {}]
    /\ wake' = [wake EXCEPT ![s] = FALSE]
    /\ subq' = [subq EXCEPT ![s] = TRUE]
    /\ ask' = [ask EXCEPT ![s] = {}]
    /\ ends' = [ends EXCEPT ![s] = @ + 1]
    /\ gone' = gone \union {s}
    /\ left' = [left EXCEPT ![s] =
          IF behind[s] = 0 THEN 0 ELSE IF behind[s] < base \/ missed[s] /= {} THEN -1 ELSE behind[s]]
    /\ UNCHANGED <<msgAt, base, acked, got, told, swaps>>

\* Topics::on_get at the hub: the positions asked for go into the subscriber's stream, oldest first, while it has room.
\* With Owe the subscriber is behind from the first one that found the stream full (or from its earlier place), let
\* go; without it the rest is dropped. The positions asked for that the log dropped meanwhile are told ("get")
Get(s) ==
    /\ ask[s] /= {}
    /\ LET want == {i \in ask[s] : i >= base}
           sent == Firsts(want, StreamCap - Len(stream[s]))
           rest == want \ sent
       IN /\ stream' = [stream EXCEPT ![s] = Fill(@, sent)]
          /\ behind' = [behind EXCEPT ![s] =
                IF Owe /\ rest /= {} THEN (IF @ = 0 \/ Lowest(rest) < @ THEN Lowest(rest) ELSE @) ELSE @]
          /\ held' = IF Owe /\ rest /= {} THEN held \union {s} ELSE held
          /\ told' = [told EXCEPT ![s] = IF "get" \in Notice THEN @ \union (ask[s] \ want) ELSE @]
    /\ ask' = [ask EXCEPT ![s] = {}]
    /\ UNCHANGED <<msgAt, base, acked, got, missed, wake, subq, swaps, ends, gone, left>>

\* any store, or any subscriber's drain, catch-up step, let-go, session swap or end, SUB or answered GET
Next == \/ \E m \in 1..N : Store(m)
        \/ \E s \in Subs : Drain(s) \/ Writable(s) \/ LetGo(s) \/ Swap(s) \/ Sub(s) \/ End(s) \/ Get(s)

\* streams drain, the hub answers a wake, a SUB arrives, and the publisher keeps retrying; letting a subscriber go and
\* replacing a session are never forced
Spec == /\ Init /\ [][Next]_vars
        /\ \A s \in Subs : WF_vars(Drain(s)) /\ WF_vars(Writable(s)) /\ WF_vars(Sub(s)) /\ WF_vars(Get(s))
        /\ \A m \in 1..N : WF_vars(Store(m))

(* ---------------------------- the checked properties ---------------------------- *)
\* every acknowledged message reaches every subscriber: received, in its stream, owed from the position it is behind
\* at, a position it missed and is told about once caught up (or was told about), or one its repair is fetching or
\* will tell it about (its SUB is on its way and the position is still logged or the hub released it, or the position
\* is in its GET)
AckedReachesLive ==
    \A s \in Subs : \A m \in acked :
        \/ m \in got[s]
        \/ \E i \in 1..Len(stream[s]) : stream[s][i] = m
        \/ behind[s] /= 0 /\ PosOf(m) >= behind[s]
        \/ PosOf(m) \in missed[s] \union told[s]
        \/ subq[s] /\ (PosOf(m) >= base \/ s \in gone)
        \/ PosOf(m) \in ask[s]
\* only a subscriber that was let go misses anything
MissedOnlyHeld == \A s \in Subs : missed[s] /= {} => s \in held
\* a position a pacing subscriber is owed is still in the log
OwedInLog == \A s \in Subs : behind[s] /= 0 /\ s \notin held => base <= behind[s] /\ behind[s] <= Top
\* the streams and the log stay within their room
Bounds == /\ \A s \in Subs : Len(stream[s]) <= StreamCap
          /\ Top - base + 1 <= LogCap
\* a subscriber that is behind is woken, or its stream is full (its drain will wake it), or its SUB is on its way
WakeOrPending == \A s \in Subs : behind[s] /= 0 => wake[s] \/ Len(stream[s]) >= StreamCap \/ subq[s]
\* with fair streams and a publisher that keeps trying, every message ends acknowledged
AllAcked == <>(acked = 1..N)
\* a subscriber that is behind ends caught up, so it is pushed live again
LiveAgain == \A s \in Subs : behind[s] /= 0 ~> behind[s] = 0
=============================================================================
