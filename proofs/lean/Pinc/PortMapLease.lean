import Pinc.Axioms

/-!
# The lease arithmetic of port mapping

A model of `crates/pinc-portmap/src/lease.rs`: `clamp`, `renew_at`, `expiry` and `restarted`.

The story. A client holds a port mapping its gateway granted for a lifetime in seconds. The lease started when the
client's request first left (`sent`, nanoseconds on the client's clock). The client renews half way and gives the
mapping up at the end. Every answer of the gateway carries its epoch, the seconds since it last lost its mappings,
and the client compares it with the last one it heard. What must never happen: a renewal scheduled at or after the
end of the lease; a lifetime taken past the cap; a gateway that went back in time not counted as restarted; a gateway
whose clock keeps pace with the client's counted as restarted.

The model. Numbers are `Nat`s; the code's `saturating_add` on a `u64` is `sat`, its `saturating_sub` is `Nat`
subtraction (which stops at 0, as the code's does), and its integer divisions are `/`. `U64` is `2^64`.

Stated assumption for `renew_before_expiry`: the start plus the longest lease fits a `u64` (`sent` is the client's
clock, nanoseconds since its endpoint started, about 584 years short of that).

Theorems: `clamp_le` (the cap), `renew_le_expiry` and `renew_before_expiry` (the renewal comes before the end),
`back_is_restart` (an epoch that went back by more than a second is a restart), `same_pace_no_restart` (an epoch
that moved exactly as the client's clock did is no restart).

TLA+ counterpart: proofs/tla/PortMapLease.tla (renewal half way, the end on the client's clock, the epoch rule).
-/

namespace Pinc.PortMapLease

/-- Nanoseconds in a second (`SEC`). -/
def SEC : Nat := 1000000000

/-- The longest lease taken (`MAX_LIFETIME`). -/
def MAX_LIFETIME : Nat := 86400

/-- The first number past a `u64`. -/
def U64 : Nat := 2 ^ 64

/-- `saturating_add` on a `u64`: the sum, or the largest `u64` when it does not fit. -/
def sat (x : Nat) : Nat := min x (U64 - 1)

/-- `clamp`: the lifetime a lease is scheduled with, at most the cap. -/
def clamp (l : Nat) : Nat := if l > MAX_LIFETIME then MAX_LIFETIME else l

/-- `renew_at`: half way through the lease, `clamp l` times half a second after the start. -/
def renewAt (sent l : Nat) : Nat := sat (sent + clamp l * (SEC / 2))

/-- `expiry`: the end of the lease on the client's clock. -/
def expiry (sent l : Nat) : Nat := sat (sent + clamp l * SEC)

/-- `restarted`: the epoch went back by more than a second, or the two clocks moved at paces more than a sixteenth
and two seconds apart. `prevAt` and `now` are the client's nanoseconds, `prevSrv` and `srv` the gateway's seconds. -/
def restarted (prevAt prevSrv now srv : Nat) : Bool :=
  -- the epoch went back by more than a second
  if srv + 1 < prevSrv then true
  else
    -- the whole seconds the client's clock moved, and the seconds the gateway's epoch moved
    let c := (now - prevAt) / SEC
    let g := srv - prevSrv
    -- either moved further than the other by more than its sixteenth and two seconds
    decide (c + 2 < g - g / 16) || decide (g + 2 < c - c / 16)

/-- The cap: no lease is scheduled longer than `MAX_LIFETIME`. -/
theorem clamp_le (l : Nat) : clamp l ≤ MAX_LIFETIME := by
  -- either the cap itself, or a lifetime no longer than it
  unfold clamp; split <;> omega

/-- The renewal is never after the end. -/
theorem renew_le_expiry (sent l : Nat) : renewAt sent l ≤ expiry sent l := by
  -- half a second per second of lifetime is no more than a second per second, and `sat` keeps the order
  unfold renewAt expiry sat SEC
  have : clamp l * (1000000000 / 2) ≤ clamp l * 1000000000 := Nat.mul_le_mul_left _ (by decide)
  omega

/-- The renewal comes strictly before the end of a lease of at least a second, when the longest lease from the start
fits a `u64`. -/
theorem renew_before_expiry (sent l : Nat) (h1 : 1 ≤ l) (hs : sent + MAX_LIFETIME * SEC < U64) :
    renewAt sent l < expiry sent l := by
  -- the clamped lifetime is between 1 and the cap, so the end fits and the half is strictly earlier
  have hc1 : 1 ≤ clamp l := by unfold clamp; split <;> simp [MAX_LIFETIME] at * <;> omega
  have hc2 := clamp_le l
  unfold renewAt expiry sat
  unfold SEC at *
  unfold MAX_LIFETIME U64 at *
  have hm : clamp l * 1000000000 ≤ 86400 * 1000000000 := Nat.mul_le_mul_right _ hc2
  have hh : clamp l * (1000000000 / 2) < clamp l * 1000000000 :=
    Nat.mul_lt_mul_of_pos_left (by decide) (by omega)
  omega

/-- An epoch that went back by more than one second is a restart. -/
theorem back_is_restart (prevAt prevSrv now srv : Nat) (h : srv + 1 < prevSrv) :
    restarted prevAt prevSrv now srv = true := by
  -- the first test of the rule
  simp [restarted, h]

/-- An epoch that moved exactly as many seconds as the client's clock is no restart. -/
theorem same_pace_no_restart (prevAt prevSrv now srv : Nat) (hge : prevSrv ≤ srv)
    (hpace : now - prevAt = (srv - prevSrv) * SEC) : restarted prevAt prevSrv now srv = false := by
  -- the epoch did not go back, and both clocks moved the same whole seconds
  have hnot : ¬ (srv + 1 < prevSrv) := by omega
  have hc : (now - prevAt) / SEC = srv - prevSrv := by
    rw [hpace]; exact Nat.mul_div_cancel _ (by decide)
  simp only [restarted, hnot, ↓reduceIte, hc]
  -- a number is never two more than itself less its sixteenth
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

end Pinc.PortMapLease
