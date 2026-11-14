---------------------------- MODULE FinishResend ----------------------------
(***************************************************************************)
(* The story. A dialing side has finished its half of the handshake and    *)
(* sent its last message, the Finish. Until it hears its first 1-RTT       *)
(* packet from the peer it cannot know the Finish arrived, so a timer      *)
(* sends the Finish again. Who acts: the dialing side's resend timer, and  *)
(* the network, which may lose every copy. What can happen: the timer      *)
(* fires again and again while the peer stays silent, on a fast path or a  *)
(* slow one, on an ordinary node or a thin one. What must never happen:    *)
(*  - a long probe timeout (42 s was seen on a slow path) holding back the *)
(*    first resend past 999 ms (the promise of #272, FirstBounded);        *)
(*  - a Finish lost in a burst on a fast path waiting a whole 999 ms when  *)
(*    its probe timeout is shorter (#427, FirstAtPto);                     *)
(*  - a wait on an ordinary node growing past 2 s (WaitsCapped);           *)
(*  - a wait shrinking from one resend to the next (WaitsGrow), or a       *)
(*    thin node resending before its answer could have come back           *)
(*    (ThinWaits), or a wait of no time at all (WaitsPositive).            *)
(*                                                                         *)
(* The code: crates/vinc-transport/src/conn/handshake.rs,                  *)
(* Handshake::finish_sent (the first wait, min(FINISH_FIRST, pto)) and the *)
(* Stage::Finish arm of Handshake::on_timer (each later wait); the probe   *)
(* timeout comes from Recovery::pto_duration in conn/drive.rs. Times are   *)
(* in milliseconds here and nanoseconds in the code; every constant of the *)
(* code is a whole number of milliseconds, so nothing is rounded.          *)
(*                                                                         *)
(* BUG = "none" is the code. Each other value removes one guard and TLC    *)
(* must find the invariant it protects broken:                             *)
(*  - "pto": the first wait is the probe timeout alone, the rule before    *)
(*    #272; a 42 s probe timeout delays the first resend 42 s, so          *)
(*    FirstBounded fails (FinishResend_pto.cfg);                           *)
(*  - "fixed": the first wait is 999 ms whatever the probe timeout, the    *)
(*    rule before #427; a Finish lost on an 85 ms path waits 999 ms, so    *)
(*    FirstAtPto fails (FinishResend_fixed.cfg);                           *)
(*  - "nocap": the doubling has no 2 s ceiling; the third wait of a        *)
(*    999 ms schedule is 3,996 ms, so WaitsCapped fails                    *)
(*    (FinishResend_nocap.cfg).                                            *)
(* Lean counterpart: proofs/lean/Vinc/TransportFinish.lean.                *)
(***************************************************************************)
EXTENDS Integers, Sequences \* whole numbers and the list of waits

CONSTANTS
    FIRST,   \* FINISH_FIRST: the longest first wait, 999 ms
    CAP,     \* FINISH_CAP: the longest later wait on an ordinary node, 2 s
    SHIFT,   \* FINISH_SHIFT: the doubling stops after this many steps, 3
    THINMAX, \* THIN_FINISH_MAX: the longest extra wait of a thin node, 20 s
    PTOS,    \* the probe timeouts the dialing side may have when it establishes
    RTTS,    \* the largest round trip a thin node knows (its srtt or the node's)
    SENDS,   \* how many flights went out before the Finish (the first flight and its resends)
    FIRES,   \* how many times the timer fires in a run: the peer stays silent throughout
    BUG      \* "none" is the code; the other values each remove one guard

VARIABLES
    pto,    \* the probe timeout when the session was established
    rtt,    \* the round trip a thin node waits twice for
    thin,   \* whether the node is thin (a constrained uplink)
    sends,  \* the flights sent so far, the Finish's resends included
    first,  \* the first wait, fixed when the Finish is sent
    waits   \* every wait so far, in order: waits[1] is the first

vars == <<pto, rtt, thin, sends, first, waits>> \* everything that changes

Min(a, b) == IF a <= b THEN a ELSE b \* the smaller of two numbers
Max(a, b) == IF a >= b THEN a ELSE b \* the larger of two numbers
Pow2(k) == 2^k                         \* 1 << k in the code

(* The first wait, as finish_sent sets it: the probe timeout, but never more than FIRST. *)
FirstWait(p) ==
    CASE BUG = "pto"   -> p            \* the rule before #272: the probe timeout alone
      [] BUG = "fixed" -> FIRST        \* the rule before #427: always 999 ms
      [] OTHER         -> Min(FIRST, p) \* the code

(* A later wait, as on_timer computes it from the sends before this one (`sent`). *)
Backoff(f, sent) ==
    IF BUG = "nocap"
    THEN f * Pow2(Min(sent, SHIFT))          \* the doubling without its ceiling
    ELSE Min(f * Pow2(Min(sent, SHIFT)), CAP) \* the code: doubled, at most CAP

(* A thin node waits at least twice its round trip, but never more than THINMAX for that reason. *)
LaterWait(f, sent) ==
    IF thin
    THEN Max(Backoff(f, sent), Min(THINMAX, 2 * rtt)) \* the thin node's floor
    ELSE Backoff(f, sent)                              \* an ordinary node

(* The session is established: the Finish has gone out, and the first wait is set. *)
Init ==
    /\ pto \in PTOS                     \* any probe timeout of the set
    /\ rtt \in RTTS                     \* any known round trip
    /\ thin \in BOOLEAN                 \* a thin node or an ordinary one
    /\ sends \in SENDS                  \* any count of flights before the Finish
    /\ first = FirstWait(pto)           \* finish_sent fixes the first wait
    /\ waits = <<FirstWait(pto)>>       \* and the timer is armed with it

(* The timer fires, the peer still silent: the Finish goes out again and the next wait is armed. *)
Fire ==
    /\ Len(waits) < FIRES                                  \* a run has a bounded number of fires
    /\ waits' = Append(waits, LaterWait(first, sends))     \* the next wait, from the sends before this one
    /\ sends' = sends + 1                                  \* this resend counts
    /\ UNCHANGED <<pto, rtt, thin, first>>                 \* nothing else moves

Next == Fire \/ (Len(waits) = FIRES /\ UNCHANGED vars) \* fire, or stop once the run is long enough
Spec == Init /\ [][Next]_vars                          \* every run of fires

TypeOK ==
    /\ pto \in PTOS /\ rtt \in RTTS /\ thin \in BOOLEAN \* the inputs stay what they were
    /\ sends \in Nat /\ first \in Nat                     \* counts and times are whole numbers
    /\ waits \in Seq(Nat)                                 \* the waits are a list of times

(* #272's promise: however long the probe timeout, the first resend waits at most 999 ms. *)
FirstBounded == waits[1] <= FIRST

(* #427's promise: a Finish lost on a path whose probe timeout is shorter waits only that probe timeout. *)
FirstAtPto == waits[1] <= pto

(* On an ordinary node no wait is longer than 2 s. *)
WaitsCapped == ~thin => \A i \in 1..Len(waits) : waits[i] <= CAP

(* No wait is shorter than the one before it. *)
WaitsGrow == \A i \in 2..Len(waits) : waits[i - 1] <= waits[i]

(* A thin node waits at least twice its round trip (at most THINMAX) before every resend after the first. *)
ThinWaits == thin => \A i \in 2..Len(waits) : waits[i] >= Min(THINMAX, 2 * rtt)

(* No wait is zero: the timer never spins. *)
WaitsPositive == \A i \in 1..Len(waits) : waits[i] >= 1

(* The probe timeout is never zero in the code (it is at least the 25 ms of ack delay); the model assumes the same. *)
ASSUME \A p \in PTOS : p >= 1
=============================================================================
