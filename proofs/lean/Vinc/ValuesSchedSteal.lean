import Vinc.Axioms
import Vinc.ValuesSchedList

/-!
# Targets, rates and the steal arithmetic

`Fetch::prate`, `Fetch::target` (ARRIVAL_CURVE), the TAIL_SHRINK cap of a top-up, and the choice and the cut of a steal
(STEAL, with the two idle corrections), as the code computes them on `u64` with `saturating_*`, `checked_div` and
`div_ceil`. Times are nanoseconds, rates bytes per millisecond.

- `target_bounds`: the target is always between four groups and `TGT_MAX`, so `tgt - outstanding` never underflows when a
  top-up runs (`topup_want_pos`).
- `tail_shrink_inactive`: TAIL_SHRINK changes nothing while a queue of `4 * STRIPE_CHUNK * k` bytes is left, and a
  shrunk top-up is at least a group (`tail_want_pos`).
- `steal_idle_robbed`, `steal_idle_below_min`: a provider idle for `STEAL_IDLE` that holds any bytes is a candidate with
  the stalled eta whatever it holds, even less than `STEAL_MIN`. `fresh_work_not_idle`: a provider whose clock was set
  when it was handed work is not idle for `STEAL_IDLE` after that.
- `keep_group`, `keep_stalled_zero`, `steal_tail_total`: the cut is on a group boundary, a stalled victim loses
  everything, and the bytes moved are the list's total beyond `keep`.
- `steal_empty_tail_witness`: the rounding up of `keep` can make the tail empty (a concrete case); the code then resets
  the victim's streams although nothing moved (a finding, see the report).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Vinc.ValuesSched

/-! ## The constants of `knobs.rs` -/

def MS : Nat := 1000000
def NS : Nat := 1000000000
def TGT0 : Nat := 786432
def TGT_MAX : Nat := 1572864
def RATE_HORIZON : Nat := 1000
def RATE_WARMUP : Nat := 500 * MS
def STRIPE_CHUNK : Nat := 1048576
def MIN_TARGET_GROUPS : Nat := 4
def STEAL_MIN : Nat := 262144
def STEAL_IDLE : Nat := 2 * NS
def STEAL_ETA_MS : Nat := 800
def STEAL_ETA_STALLED_MS : Nat := 2 ^ 40

/-- `a.saturating_mul(b)`. -/
def satMul (a b : Nat) : Nat := min (a * b) M

/-- `Fetch::prate`: verified bytes per millisecond; 0 before 500 ms of samples. `pt` is the time of the first verified
group, `pb` the verified bytes. -/
def prate (pt : Option Nat) (pb now : Nat) : Nat :=
  match pt with
  | none => 0
  | some t => if now - t < RATE_WARMUP then 0 else pb / max ((now - t) / MS) 1

/-- `Fetch::target`: the outstanding target of a provider (ARRIVAL_CURVE). The rate replaces the starting target after
the warm-up, or as soon as the provider has verified twice `TGT0`. -/
def target (pt : Option Nat) (pb now : Nat) : Nat :=
  match pt with
  | some t =>
    if now - t ≥ RATE_WARMUP ∨ 2 * TGT0 ≤ pb then
      max (MIN_TARGET_GROUPS * G) (min TGT_MAX (satMul pb RATE_HORIZON / max ((now - t) / MS) 1))
    else TGT0
  | none => TGT0

theorem target_bounds (pt : Option Nat) (pb now : Nat) :
    MIN_TARGET_GROUPS * G ≤ target pt pb now ∧ target pt pb now ≤ TGT_MAX := by
  unfold target
  cases pt with
  | none => simp only [TGT0, MIN_TARGET_GROUPS, TGT_MAX, G]; omega
  | some t =>
    simp only
    split
    · simp only [MIN_TARGET_GROUPS, TGT_MAX, G]; omega
    · simp only [TGT0, MIN_TARGET_GROUPS, TGT_MAX, G]; omega

/-- A top-up runs only below half the target, so its `tgt - outstanding` is positive and no `u64` underflows. -/
theorem topup_want_pos (pt : Option Nat) (pb now outstanding : Nat)
    (h : outstanding < target pt pb now / 2) : 0 < target pt pb now - outstanding := by
  omega

/-- A provider with no sample yet, or inside the warm-up, has rate 0 and the first-round target. -/
theorem prate_warmup (t pb now : Nat) (h : now - t < RATE_WARMUP) : prate (some t) pb now = 0 := by
  simp [prate, h]

theorem target_warmup (t pb now : Nat) (h : now - t < RATE_WARMUP) (hb : pb < 2 * TGT0) :
    target (some t) pb now = TGT0 := by
  simp [target]; omega

/-- Inside the warm-up, a provider that has verified twice `TGT0` has left the first-round target for its rate. -/
theorem target_early (t pb now : Nat) (h : now - t < RATE_WARMUP) (hb : 2 * TGT0 ≤ pb) :
    target (some t) pb now
      = max (MIN_TARGET_GROUPS * G) (min TGT_MAX (satMul pb RATE_HORIZON / max ((now - t) / MS) 1)) := by
  simp [target]; omega

/-! ## TAIL_SHRINK -/

/-- The prefix sum of the queue's span lengths that the TAIL_SHRINK loop stops at: it adds spans until the sum reaches
`4 * STRIPE_CHUNK * k`. `left += s.len` is a saturating add. -/
def leftSum (lim : Nat) : Nat → List Nat → Nat
  | left, [] => left
  | left, len :: rest => if lim ≤ left then left else leftSum lim (min (left + len) M) rest

/-- The cap TAIL_SHRINK puts on `want`. -/
def tailWant (want k left : Nat) : Nat := min want (max (MIN_TARGET_GROUPS * G) (left / (2 * k)))

/-- While at least `4 * STRIPE_CHUNK * k` bytes are queued, TAIL_SHRINK is the identity on the wanted size. -/
theorem tail_shrink_inactive (want k left : Nat) (hk : 0 < k) (hw : want ≤ TGT_MAX)
    (hl : 4 * STRIPE_CHUNK * k ≤ left) : tailWant want k left = want := by
  unfold tailWant
  simp only [STRIPE_CHUNK, MIN_TARGET_GROUPS, G, TGT_MAX] at *
  have : 2097152 ≤ left / (2 * k) := by
    apply Nat.le_div_iff_mul_le (by omega) |>.2
    omega
  omega

/-- A shrunk top-up still asks for at least a group when anything was wanted. -/
theorem tail_want_pos (want k left : Nat) (hw : 0 < want) : 0 < tailWant want k left := by
  unfold tailWant
  simp only [MIN_TARGET_GROUPS, G]; omega

/-- `leftSum` never exceeds `u64::MAX` once saturating: the unchecked `left += s.len` of the first version overflowed
when one span was within `4 * STRIPE_CHUNK * k` of `u64::MAX`. -/
theorem leftSum_le (lim : Nat) (hlim : lim ≤ M) (lens : List Nat) :
    ∀ left, left ≤ M → leftSum lim left lens ≤ M := by
  induction lens with
  | nil => intro left h; simpa [leftSum] using h
  | cons len rest ih =>
    intro left h
    unfold leftSum
    split
    · exact h
    · exact ih _ (by simp only [M]; omega)

/-! ## STEAL -/

/-- Whether a provider is idle: no verified group (or no work handed over) for `STEAL_IDLE`. `lp` is the clock, `t0`
the start of the fetch used when it never started. -/
def idle (lp : Option Nat) (t0 now : Nat) : Bool := decide (STEAL_IDLE ≤ now - lp.getD t0)

/-- The eta of a candidate holding `m` bytes with rate `rq`, if it is one: `None` if it is skipped. -/
def etaOf (idl : Bool) (m rq : Nat) : Option Nat :=
  if m = 0 ∨ (m < STEAL_MIN ∧ idl = false) then none
  else if idl then some STEAL_ETA_STALLED_MS
  else if rq = 0 then none
  else some (m / rq)

/-- A provider idle for `STEAL_IDLE` that holds any bytes is a candidate with the stalled eta, whatever it holds and
whatever its rate: the reference `STEAL_MIN` floor would leave the last 256 KiB of a dead provider unfetched. -/
theorem steal_idle_robbed (m rq : Nat) (hm : 0 < m) : etaOf true m rq = some STEAL_ETA_STALLED_MS := by
  unfold etaOf; simp; omega

theorem steal_idle_below_min (m rq : Nat) (hm : 0 < m) (hmin : m < STEAL_MIN) :
    etaOf true m rq = some STEAL_ETA_STALLED_MS ∧ etaOf false m rq = none := by
  refine ⟨steal_idle_robbed m rq hm, ?_⟩
  unfold etaOf; simp; omega

/-- The stalled eta is above every real eta a provider can have, and above `STEAL_ETA_MS`, so a stalled provider is
always eligible and always preferred: a real eta is `m / rq` with `m` at most a target plus a group. -/
theorem stalled_eta_max (m rq : Nat) (hm : m ≤ TGT_MAX + G) : m / rq < STEAL_ETA_STALLED_MS := by
  have : m / rq ≤ m := Nat.div_le_self m rq
  simp only [STEAL_ETA_STALLED_MS, TGT_MAX, G] at *; omega

/-- A provider given work at `now` has its idle clock at `now`: it is not idle until `STEAL_IDLE` later. -/
theorem fresh_work_not_idle (t0 now later : Nat) (h : later < now + STEAL_IDLE) :
    idle (some now) t0 later = false := by
  unfold idle
  apply decide_eq_false
  simp only [Option.getD_some, STEAL_IDLE, NS] at *
  omega

/-- ... and idle exactly `STEAL_IDLE` later (and from then on, without a verified group). -/
theorem idle_after (t0 now later : Nat) (h : now + STEAL_IDLE ≤ later) : idle (some now) t0 later = true := by
  unfold idle
  apply decide_eq_true
  simp only [Option.getD_some, STEAL_IDLE, NS] at *
  omega

/-- A provider never given work or verified uses the start of the fetch. -/
theorem idle_none (t0 now : Nat) : idle none t0 now = decide (STEAL_IDLE ≤ now - t0) := rfl

/-- `keep` before the rounding: `bm.saturating_mul(rq).checked_div(rq + rp)`, 0 on a zero divisor. `rp0` is the thief's
rate, replaced by `rq` when it has none. -/
def keep0 (bm rq rp0 : Nat) : Nat :=
  let rp := if rp0 = 0 then rq else rp0
  if rq + rp = 0 then 0 else satMul bm rq / (rq + rp)

/-- `keep`: the bytes the victim keeps, rounded up to a group (`div_ceil`). -/
def keepOf (bm rq rp0 : Nat) : Nat := (keep0 bm rq rp0 + G - 1) / G * G

theorem keep_group (bm rq rp : Nat) : keepOf bm rq rp % G = 0 := by
  unfold keepOf; simp only [G]; omega

/-- A stalled victim (rate 0) loses everything: `keep = 0`. -/
theorem keep_stalled_zero (bm rp : Nat) : keepOf bm 0 rp = 0 := by
  unfold keepOf keep0; simp [satMul, G]

theorem keep0_le (bm rq rp : Nat) : keep0 bm rq rp ≤ bm := by
  unfold keep0 satMul
  generalize hd : (if rp = 0 then rq else rp) = d
  have hle : rq ≤ rq + d := by omega
  simp only []
  by_cases h : rq + d = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]
    apply Nat.div_le_of_le_mul
    have h1 : min (bm * rq) M ≤ bm * rq := Nat.min_le_left _ _
    have h2 : bm * rq ≤ (rq + d) * bm := by
      rw [Nat.mul_comm (rq + d) bm]
      exact Nat.mul_le_mul_left bm hle
    exact Nat.le_trans h1 h2

/-- The victim never keeps more than its list plus the rounding to the next group. -/
theorem keep_lt (bm rq rp : Nat) : keepOf bm rq rp < bm + G := by
  have := keep0_le bm rq rp
  unfold keepOf; simp only [G] at *; omega

/-- A concrete steal whose tail is empty: a victim of 327 B/ms holding 16 groups (eta 801 ms, so a candidate) and a
thief of 1 B/ms. `keep` rounds up to the whole list, so nothing moves, yet the code resets the victim's streams. -/
theorem steal_empty_tail_witness :
    etaOf false 262144 327 = some 801 ∧ 800 ≤ 801 ∧ keepOf 262144 327 1 = 262144 := by
  refine ⟨by decide, by decide, by decide⟩

/-- With the fix (do nothing when the tail would be empty) the steal is a no-op exactly when `keep` covers the list. -/
theorem steal_noop_iff (bm rq rp : Nat) : bm ≤ keepOf bm rq rp ↔ bm - keepOf bm rq rp = 0 := by omega

end Vinc.ValuesSched

#audit_axioms Vinc.ValuesSched.target_bounds
#audit_axioms Vinc.ValuesSched.topup_want_pos
#audit_axioms Vinc.ValuesSched.prate_warmup
#audit_axioms Vinc.ValuesSched.target_warmup
#audit_axioms Vinc.ValuesSched.target_early
#audit_axioms Vinc.ValuesSched.tail_shrink_inactive
#audit_axioms Vinc.ValuesSched.tail_want_pos
#audit_axioms Vinc.ValuesSched.leftSum_le
#audit_axioms Vinc.ValuesSched.steal_idle_robbed
#audit_axioms Vinc.ValuesSched.steal_idle_below_min
#audit_axioms Vinc.ValuesSched.stalled_eta_max
#audit_axioms Vinc.ValuesSched.fresh_work_not_idle
#audit_axioms Vinc.ValuesSched.idle_after
#audit_axioms Vinc.ValuesSched.keep_group
#audit_axioms Vinc.ValuesSched.keep_stalled_zero
#audit_axioms Vinc.ValuesSched.keep0_le
#audit_axioms Vinc.ValuesSched.keep_lt
#audit_axioms Vinc.ValuesSched.steal_empty_tail_witness
#audit_axioms Vinc.ValuesSched.steal_noop_iff
