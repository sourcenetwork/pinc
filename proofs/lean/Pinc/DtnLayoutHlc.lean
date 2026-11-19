import Pinc.DtnLayout
import Pinc.Labels

/-!
# The hybrid logical clock, the bundle lifetime and the labels (`hlc.rs`, `head.rs`, `labels.rs`)

`Hlc.tick` and `Hlc.observe` on natural numbers with the saturating `u32` counter: both return the physical component
`max` of their inputs, the result is never below the receiver, and strictly above it (and above the remote stamp for
`observe`) unless the 32-bit counter is saturated. `expiresAt` is the saturating `u64` sum, `isExpired now` is
`expires <= now`, so a bundle is alive strictly before its expiry and expired from it on, and expiry is monotone in
the time. The six delay-tolerant labels are pairwise distinct, start with the protocol prefix and are disjoint from
the labels of the security layer and of `pinc-crypto`.
-/

namespace Pinc.DtnLayoutHlc
open Pinc.DtnLayout

/-- `u32::MAX`. -/
def cmax : Nat := 4294967295

/-- `u32::saturating_add(_, 1)`. -/
def sat1 (c : Nat) : Nat := min (c + 1) cmax

structure H where
  wall : Nat
  counter : Nat
  deriving DecidableEq

/-- The order of `Hlc`: `(wall, counter)` lexicographically. -/
def H.lt (a b : H) : Prop := a.wall < b.wall ∨ (a.wall = b.wall ∧ a.counter < b.counter)
def H.le (a b : H) : Prop := a.wall < b.wall ∨ (a.wall = b.wall ∧ a.counter ≤ b.counter)

def H.tick (h : H) (now : Nat) : H :=
  if now > h.wall then ⟨now, 0⟩ else ⟨h.wall, sat1 h.counter⟩

def H.observe (h r : H) (now : Nat) : H :=
  let wall := max (max h.wall r.wall) now
  let counter :=
    if wall = h.wall ∧ wall = r.wall then sat1 (max h.counter r.counter)
    else if wall = h.wall then sat1 h.counter
    else if wall = r.wall then sat1 r.counter
    else 0
  ⟨wall, counter⟩

theorem tick_wall (h : H) (now : Nat) : (h.tick now).wall = max h.wall now := by
  unfold H.tick; split <;> simp <;> omega

theorem tick_le (h : H) (now : Nat) (hc : h.counter ≤ cmax) : h.le (h.tick now) := by
  by_cases hn : now > h.wall <;> simp [H.le, H.tick, hn, sat1, cmax] at * <;> omega

/-- The tick is strictly above the receiver unless the counter is saturated and the clock did not move. -/
theorem tick_lt (h : H) (now : Nat) (hc : h.counter < cmax ∨ now > h.wall) : h.lt (h.tick now) := by
  by_cases hn : now > h.wall <;> simp [H.lt, H.tick, hn, sat1, cmax] at * <;> omega

theorem tick_now (h : H) (now : Nat) : now ≤ (h.tick now).wall := by rw [tick_wall]; omega

theorem observe_wall (h r : H) (now : Nat) : (h.observe r now).wall = max (max h.wall r.wall) now := rfl

theorem observe_now (h r : H) (now : Nat) : now ≤ (h.observe r now).wall := by
  unfold H.observe; simp; omega

theorem observe_gt_self (h r : H) (now : Nat) (hc : h.counter < cmax) : h.lt (h.observe r now) := by
  simp only [H.lt, H.observe, sat1, cmax] at *
  by_cases c1 : max (max h.wall r.wall) now = h.wall ∧ max (max h.wall r.wall) now = r.wall
  · rw [if_pos c1]; omega
  · by_cases c2 : max (max h.wall r.wall) now = h.wall
    · rw [if_neg c1, if_pos c2]; omega
    · by_cases c3 : max (max h.wall r.wall) now = r.wall
      · rw [if_neg c1, if_neg c2, if_pos c3]; omega
      · rw [if_neg c1, if_neg c2, if_neg c3]; omega

theorem observe_gt_remote (h r : H) (now : Nat) (hc : r.counter < cmax) : r.lt (h.observe r now) := by
  simp only [H.lt, H.observe, sat1, cmax] at *
  by_cases c1 : max (max h.wall r.wall) now = h.wall ∧ max (max h.wall r.wall) now = r.wall
  · rw [if_pos c1]; omega
  · by_cases c2 : max (max h.wall r.wall) now = h.wall
    · rw [if_neg c1, if_pos c2]; omega
    · by_cases c3 : max (max h.wall r.wall) now = r.wall
      · rw [if_neg c1, if_neg c2, if_pos c3]; omega
      · rw [if_neg c1, if_neg c2, if_neg c3]; omega

/-! ## Lifetime -/

/-- `Hlc::expires_at`: `wall.saturating_add(lifetime)`. -/
def expiresAt (wall life : Nat) : Nat := if wall + life < M then wall + life else M - 1

/-- `Head::is_expired`. -/
def isExpired (wall life now : Nat) : Bool := decide (expiresAt wall life ≤ now)

theorem expiresAt_exact (wall life : Nat) (h : wall + life < M) : expiresAt wall life = wall + life := by
  simp [expiresAt, h]

theorem expiresAt_sat (wall life : Nat) (h : ¬ wall + life < M) : expiresAt wall life = M - 1 := by
  simp [expiresAt, h]

theorem expiresAt_lt_M (wall life : Nat) (hw : wall < M) : expiresAt wall life < M := by
  unfold expiresAt; have := M_def; split <;> omega

/-- Alive strictly before the expiry, expired from it on. -/
theorem expired_iff (wall life now : Nat) : isExpired wall life now = true ↔ expiresAt wall life ≤ now := by
  simp [isExpired]

theorem expired_mono (wall life a b : Nat) (hab : a ≤ b) (h : isExpired wall life a = true) :
    isExpired wall life b = true := by
  simp [isExpired] at *; omega

theorem expiresAt_mono_life (wall l1 l2 : Nat) (h : l1 ≤ l2) : expiresAt wall l1 ≤ expiresAt wall l2 := by
  unfold expiresAt; have := M_def; split <;> split <;> omega

theorem expiresAt_ge_wall (wall life : Nat) (hw : wall < M) : wall ≤ expiresAt wall life := by
  unfold expiresAt; have := M_def; split <;> omega

/-! ## Labels -/

def chain : String := "PINC 2026 v1 dtn chain"
def transcript : String := "PINC 2026 v1 dtn transcript"
def sliceKey : String := "PINC 2026 v1 dtn slice key"
def bundleId : String := "PINC 2026 v1 dtn bundle id"
def head : String := "PINC 2026 v1 dtn head"
def custodyAck : String := "PINC 2026 v1 dtn custody ack"

/-- `labels::ALL` of `pinc-dtn`. -/
def all : List String := [chain, transcript, sliceKey, bundleId, head, custodyAck]

theorem all_nodup : all.Nodup := by decide
theorem all_prefix : ∀ l ∈ all, Labels.prefix_.toList <+: l.toList := by decide
theorem disjoint_security : ∀ l ∈ all, l ∉ Labels.all := by decide
theorem disjoint_crypto : ∀ l ∈ all, l ∉ Labels.cryptoLabels := by decide

#print axioms tick_lt
#print axioms observe_gt_self
#print axioms expired_iff
#print axioms all_nodup

end Pinc.DtnLayoutHlc
