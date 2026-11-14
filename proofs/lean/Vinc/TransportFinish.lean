import Vinc.Axioms

/-!
# The Finish resend schedule

The story: a dialing side has sent its Finish, the last message of the handshake, and cannot know it arrived until it
hears a 1-RTT packet from the peer. A timer sends the Finish again while the peer stays silent. This file is the
schedule of that timer, as `crates/vinc-transport/src/conn/handshake.rs` computes it: `Handshake::finish_sent` sets
the first wait to the probe timeout, at most `FINISH_FIRST` (999 ms), and the `Stage::Finish` arm of
`Handshake::on_timer` sets each later wait to that first wait doubled once per send so far (at most `FINISH_SHIFT`
doublings), at most `FINISH_CAP` (2 s), and on a thin node at least twice its round trip (at most
`THIN_FINISH_MAX`). Times are milliseconds here and nanoseconds in the code; every constant is whole milliseconds.

What must never happen, and the theorem that rules it out:
- a long probe timeout holding back the first resend past 999 ms (`first_le_max`, the promise of #272);
- a Finish lost on a fast path waiting longer than its probe timeout (`first_le_pto`, #427);
- a wait of no time, so the timer spins (`first_pos`, `later_pos`);
- a wait on an ordinary node longer than 2 s (`later_le_cap`);
- a later wait shorter than the first, or than the wait before it (`later_ge_first`, `later_mono`);
- a thin node resending before its answer could have come back (`thin_floor`).
FinishResend.tla checks the same promises over every run of fires on small inputs, with a RED configuration per guard.
-/

namespace Vinc.TransportFinish

/-- `FINISH_FIRST`: the longest first wait, 999 ms. -/
def finishFirstMax : Nat := 999
/-- `FINISH_CAP`: the longest later wait on an ordinary node, 2 s. -/
def finishCap : Nat := 2000
/-- `FINISH_SHIFT`: the doubling stops after this many steps. -/
def finishShift : Nat := 3
/-- `THIN_FINISH_MAX`: the longest extra wait of a thin node, 20 s. -/
def thinMax : Nat := 20000

/-- `finish_sent`: the first wait is the probe timeout `pto`, never more than `FINISH_FIRST`. -/
def firstWait (pto : Nat) : Nat := min finishFirstMax pto

/-- The doubling of `on_timer`: the first wait `f` doubled once per send before this one (`sent`), at most
`FINISH_CAP`. -/
def backoff (f sent : Nat) : Nat := min (f * 2 ^ (min sent finishShift)) finishCap

/-- A later wait: the doubling, and on a thin node at least twice the round trip `rtt` (at most `THIN_FINISH_MAX`). -/
def laterWait (thin : Bool) (rtt f sent : Nat) : Nat :=
  -- a thin node takes the larger of the doubling and its floor
  if thin then max (backoff f sent) (min thinMax (2 * rtt))
  -- an ordinary node takes the doubling alone
  else backoff f sent

/-- However long the probe timeout, the first resend waits at most 999 ms (#272). -/
theorem first_le_max (pto : Nat) : firstWait pto ≤ finishFirstMax := by
  -- the minimum is at most each of its arguments
  unfold firstWait; omega

/-- A Finish lost on a path whose probe timeout is shorter than 999 ms waits only that probe timeout (#427). -/
theorem first_le_pto (pto : Nat) : firstWait pto ≤ pto := by
  -- the minimum is at most its second argument
  unfold firstWait; omega

/-- The probe timeout is never zero in the code (it includes the 25 ms ack delay), so neither is the first wait. -/
theorem first_pos (pto : Nat) (h : 1 ≤ pto) : 1 ≤ firstWait pto := by
  -- both arguments of the minimum are at least 1
  unfold firstWait finishFirstMax; omega

/-- The doubling of a first wait of at most 999 ms is at least that first wait: the factor `2 ^ k` is at least 1. -/
theorem backoff_ge_first (f sent : Nat) (hf : f ≤ finishFirstMax) : f ≤ backoff f sent := by
  -- `2 ^ k ≥ 1`, so `f * 2 ^ k ≥ f`
  have hp : 1 ≤ 2 ^ (min sent finishShift) := Nat.one_le_two_pow
  -- multiplying by at least 1 does not shrink
  have hm : f ≤ f * 2 ^ (min sent finishShift) := Nat.le_mul_of_pos_right f hp
  -- and the cap of 2 s is above 999 ms
  unfold backoff finishCap; unfold finishFirstMax at hf; omega

/-- On an ordinary node no later wait is longer than 2 s. -/
theorem later_le_cap (rtt f sent : Nat) : laterWait false rtt f sent ≤ finishCap := by
  -- an ordinary node's wait is the capped doubling
  unfold laterWait backoff; simp; omega

/-- Every later wait is at least the first one, so the schedule never speeds up after the first resend. -/
theorem later_ge_first (thin : Bool) (rtt f sent : Nat) (hf : f ≤ finishFirstMax) :
    f ≤ laterWait thin rtt f sent := by
  -- the doubling alone is at least the first wait
  have h := backoff_ge_first f sent hf
  -- and a thin node's wait is at least the doubling
  unfold laterWait; cases thin <;> simp <;> omega

/-- More sends never give a shorter wait: the doubling grows with the count, and the floor does not depend on it. -/
theorem later_mono (thin : Bool) (rtt f s t : Nat) (h : s ≤ t) :
    laterWait thin rtt f s ≤ laterWait thin rtt f t := by
  -- the exponent grows with the count
  have hk : 2 ^ (min s finishShift) ≤ 2 ^ (min t finishShift) := Nat.pow_le_pow_right (by decide) (by omega)
  -- so does the product with the first wait
  have hp : f * 2 ^ (min s finishShift) ≤ f * 2 ^ (min t finishShift) := Nat.mul_le_mul_left f hk
  -- capping and the thin floor keep the order
  unfold laterWait backoff; cases thin <;> simp <;> omega

/-- A later wait is never zero when the first is not. -/
theorem later_pos (thin : Bool) (rtt f sent : Nat) (hf1 : 1 ≤ f) (hf : f ≤ finishFirstMax) :
    1 ≤ laterWait thin rtt f sent := by
  -- every later wait is at least the first, which is at least 1
  have := later_ge_first thin rtt f sent hf; omega

/-- A thin node waits at least twice its round trip, at most `THIN_FINISH_MAX`, before every resend after the first. -/
theorem thin_floor (rtt f sent : Nat) : min thinMax (2 * rtt) ≤ laterWait true rtt f sent := by
  -- the maximum is at least its second argument
  unfold laterWait; simp; omega

end Vinc.TransportFinish
