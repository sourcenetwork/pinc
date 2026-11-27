import Pinc.Axioms

/-!
# The anti-amplification budget

A model of `pinc-security/src/amp.rs`, constant by constant: `OVERHEAD = 48`, `FACTOR = 3`; `AmpBudget` holds `rx` and
`tx` (`u64`) and a `validated` flag; `on_receive` and `on_send` are `saturating_add` on `u64`; `can_send(n)` is
`validated || tx != u64::MAX && tx + n + OVERHEAD <= rx * FACTOR`, the comparison evaluated in 128 bits, which cannot overflow for `u64` operands
(`u128_no_overflow`), so it equals the comparison on `Nat`, which is what the model uses (`canSend_iff`); `validate`
sets the flag and nothing clears it (`validated_sticky`).

The bound `amplification_bound` (`tx <= 3 * rx` before validation) and its margin `reach_margin`
(`tx = 0 or tx + OVERHEAD <= 3 * rx`) are statements about the reachable set `Reach`: the budgets that result from
any sequence of receives, validations and sends in which every send obeyed `can_send` at the moment of the send. That
is the definition of the reachable set, not an assumption about a caller: a send that `can_send` refuses is simply
not an operation of the discipline. The model proves nothing about a caller that sends without asking.

Counters saturate at `u64::MAX`, so after `2^64` bytes `tx` stops counting (`satAdd_exact` is the exactness below
saturation). `true_bound` is the bound over the true totals, which `TReach` carries as ghosts: before validation the
bytes sent, counted without saturation, are at most three times the bytes received. The bound over the recorded
counters alone let the saturation bug through: at `tx = u64::MAX` the old `can_send` still allowed sends that no
counter recorded; the fixed one refuses every unvalidated send once `tx` is saturated. `can_send` counts the datagram's overhead although
`on_send` records only its payload, which is why the margin `tx + OVERHEAD <= 3 * rx` holds after every send.
Amp.tla checks the same facts exhaustively on small counters, and TraceAmp.tla and `lake exe replay` check the
recorded events of the real `AmpBudget`.
-/

namespace Pinc.Amp

/-- `u64::MAX`. -/
def u64max : Nat := 2 ^ 64 - 1
/-- `OVERHEAD`. -/
def overhead : Nat := 48
/-- `FACTOR`. -/
def factor : Nat := 3

/-- `AmpBudget`. -/
structure Budget where
  rx : Nat
  tx : Nat
  validated : Bool

/-- `AmpBudget::new`. -/
def Budget.new : Budget := ⟨0, 0, false⟩

/-- `u64::saturating_add` on values below `2^64`. -/
def satAdd (a n : Nat) : Nat := min (a + n) u64max

/-- `on_receive`. -/
def onReceive (b : Budget) (n : Nat) : Budget := { b with rx := satAdd b.rx n }

/-- `on_send`. -/
def onSend (b : Budget) (n : Nat) : Budget := { b with tx := satAdd b.tx n }

/-- `validate`. -/
def validate (b : Budget) : Budget := { b with validated := true }

/-- `can_send`: the comparison done in 128 bits, shown equal to the one on `Nat` below. -/
def canSend (b : Budget) (n : Nat) : Bool :=
  b.validated || (decide (b.tx ≠ u64max) && decide (b.tx + n + overhead ≤ b.rx * factor))

/-- Both sides of the `u128` comparison fit in 128 bits when the counters and `n` are `u64`: the code's
128-bit arithmetic never wraps, so the `Nat` model is exact. -/
theorem u128_no_overflow (b : Budget) (n : Nat) (hrx : b.rx ≤ u64max) (htx : b.tx ≤ u64max) (hn : n ≤ u64max) :
    b.tx + n + overhead < 2 ^ 128 ∧ b.rx * factor < 2 ^ 128 := by
  unfold u64max at *
  unfold overhead factor
  constructor <;> omega

/-- The counters and the argument are `u64`s. -/
def Valid (b : Budget) : Prop := b.rx ≤ u64max ∧ b.tx ≤ u64max

/-- The discipline: receive anything, send only what `can_send` allows, validate. -/
inductive Reach : Budget → Prop where
  | init : Reach Budget.new
  | recv {b} (n : Nat) : Reach b → n ≤ u64max → Reach (onReceive b n)
  | send {b} (n : Nat) : Reach b → n ≤ u64max → canSend b n = true → Reach (onSend b n)
  | validate {b} : Reach b → Reach (validate b)

theorem satAdd_le (a n : Nat) : satAdd a n ≤ a + n := by unfold satAdd; omega

theorem satAdd_le_max (a n : Nat) : satAdd a n ≤ u64max := by unfold satAdd; omega

theorem satAdd_ge (a n : Nat) (ha : a ≤ u64max) : a ≤ satAdd a n := by unfold satAdd; omega

/-- The saturating add is the exact sum until it reaches `u64::MAX`. -/
theorem satAdd_exact (a n : Nat) (h : a + n ≤ u64max) : satAdd a n = a + n := by unfold satAdd; omega

theorem reach_valid {b : Budget} (h : Reach b) : Valid b := by
  induction h with
  | init => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | recv n _ _ ih => exact ⟨satAdd_le_max _ _, ih.2⟩
  | send n _ _ _ ih => exact ⟨ih.1, satAdd_le_max _ _⟩
  | validate _ ih => exact ih

/-- The state before validation, with the margin the discipline guarantees. -/
def Margin (b : Budget) : Prop := b.validated = false → b.tx = 0 ∨ b.tx + overhead ≤ b.rx * factor

/-- `can_send` is exact: before validation it holds iff `tx` is not saturated and the sent total plus `n` and the
overhead stays within three times the received bytes. -/
theorem canSend_iff (b : Budget) (n : Nat) (hv : b.validated = false) :
    canSend b n = true ↔ b.tx ≠ u64max ∧ b.tx + n + overhead ≤ b.rx * factor := by
  simp [canSend, hv]

/-- After validation there is no limit. -/
theorem canSend_validated (b : Budget) (n : Nat) (hv : b.validated = true) : canSend b n = true := by
  simp [canSend, hv]

/-- The saturating send never records more than the exact sum. -/
theorem onSend_tx_le (b : Budget) (n : Nat) : (onSend b n).tx ≤ b.tx + n := satAdd_le _ _

/-- A permitted send keeps the margin: the new `tx` plus the overhead is within three times `rx`. -/
theorem onSend_margin (b : Budget) (n : Nat) (hv : b.validated = false) (h : canSend b n = true) :
    (onSend b n).tx + overhead ≤ b.rx * factor := by
  have := ((canSend_iff b n hv).1 h).2
  have := onSend_tx_le b n
  omega

/-- Counters never decrease. -/
theorem onReceive_mono (b : Budget) (n : Nat) (h : b.rx ≤ u64max) : b.rx ≤ (onReceive b n).rx :=
  satAdd_ge _ _ h

theorem onSend_mono (b : Budget) (n : Nat) (h : b.tx ≤ u64max) : b.tx ≤ (onSend b n).tx :=
  satAdd_ge _ _ h

/-- Validation is sticky: no operation clears it. -/
theorem validated_sticky {b : Budget} (_h : Reach b) (hv : b.validated = true) :
    ∀ n, (onReceive b n).validated = true ∧ (onSend b n).validated = true ∧ (validate b).validated = true :=
  fun _ => ⟨hv, hv, rfl⟩

theorem reach_margin {b : Budget} (h : Reach b) : Margin b := by
  induction h with
  | init => intro _; exact Or.inl rfl
  | @recv b n hb _ ih =>
    intro hv
    rcases ih hv with h1 | h1
    · exact Or.inl h1
    · right
      have h2 := onReceive_mono _ n (reach_valid hb).1
      have h3 : b.rx * factor ≤ (onReceive b n).rx * factor := Nat.mul_le_mul_right _ h2
      have h4 : (onReceive b n).tx = b.tx := rfl
      show (onReceive b n).tx + overhead ≤ (onReceive b n).rx * factor
      omega
  | send n _ _ hc ih =>
    intro hv
    exact Or.inr (onSend_margin _ n hv hc)
  | validate _ _ => intro hv; simp [validate] at hv

/-- Before validation, a sender that follows `can_send` has sent at most three times what it received. -/
theorem amplification_bound {b : Budget} (h : Reach b) (hv : b.validated = false) : b.tx ≤ 3 * b.rx := by
  rcases reach_margin h hv with h1 | h1
  · omega
  · unfold factor overhead at h1; omega

/-- The discipline with the true totals as ghosts: `got` the bytes received and `sent` the bytes sent, neither
saturated. -/
inductive TReach : Budget → Nat → Nat → Prop where
  | init : TReach Budget.new 0 0
  | recv {b g s} (n : Nat) : TReach b g s → n ≤ u64max → TReach (onReceive b n) (g + n) s
  | send {b g s} (n : Nat) : TReach b g s → n ≤ u64max → canSend b n = true → TReach (onSend b n) g (s + n)
  | validate {b g s} : TReach b g s → TReach (validate b) g s

/-- The counters are the saturated true totals, and before validation the true totals keep the margin. -/
theorem treach_inv {b : Budget} {g s : Nat} (h : TReach b g s) :
    b.rx = min g u64max ∧ b.tx = min s u64max ∧ (b.validated = false → s = 0 ∨ s + overhead ≤ g * factor) := by
  induction h with
  | init => simp [Budget.new]
  | @recv b g s n _ _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, h2, ?_⟩
    · show satAdd b.rx n = min (g + n) u64max
      unfold satAdd; omega
    · intro hv
      rcases h3 hv with h4 | h4
      · exact Or.inl h4
      · right; unfold overhead factor at *; omega
  | @send b g s n _ _ hc ih =>
    obtain ⟨h1, h2, _⟩ := ih
    refine ⟨h1, ?_, ?_⟩
    · show satAdd b.tx n = min (s + n) u64max
      unfold satAdd; omega
    · intro hv
      have hv' : b.validated = false := hv
      have hc' := (canSend_iff b n hv').1 hc
      right; unfold overhead factor at *; omega
  | validate _ ih =>
    obtain ⟨h1, h2, _⟩ := ih
    exact ⟨h1, h2, fun hv => by simp [validate] at hv⟩

/-- Before validation, a sender that follows `can_send` has sent, in truth and not only as counted, at most three
times what it received. -/
theorem true_bound {b : Budget} {g s : Nat} (h : TReach b g s) (hv : b.validated = false) : s ≤ 3 * g := by
  rcases (treach_inv h).2.2 hv with h1 | h1
  · omega
  · unfold factor overhead at h1; omega

end Pinc.Amp

#audit_axioms Pinc.Amp.u128_no_overflow
#audit_axioms Pinc.Amp.canSend_iff
#audit_axioms Pinc.Amp.canSend_validated
#audit_axioms Pinc.Amp.onSend_margin
#audit_axioms Pinc.Amp.onSend_tx_le
#audit_axioms Pinc.Amp.satAdd_exact
#audit_axioms Pinc.Amp.reach_margin
#audit_axioms Pinc.Amp.amplification_bound
#audit_axioms Pinc.Amp.validated_sticky
#audit_axioms Pinc.Amp.onReceive_mono
#audit_axioms Pinc.Amp.onSend_mono
#audit_axioms Pinc.Amp.treach_inv
#audit_axioms Pinc.Amp.true_bound
