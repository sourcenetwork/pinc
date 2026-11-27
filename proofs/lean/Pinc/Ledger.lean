import Pinc.Axioms

/-!
# The per-address send ledger

A model of one entry of `pinc-core/src/ledger.rs`, at a counter top `u` (`u64::MAX`) and a header charge `ovh`
(`DATAGRAM_OVERHEAD`, 28): `allow_send` charges `n + ovh` (saturating); an address that is validated is charged with
a saturating add and always passes; one that is not passes when the charge keeps `tx` within three times `rx` and,
under the rule of the code (`fit`), when it does not pass the counter's top (`checked_add`), so a charge is never
recorded short (`allow_exact`). The three-times bound holds under either rule (`allow_bound`, `recv_bound`); without
the fit rule a charge near the top is recorded short and every later one passes uncounted (`unfit_undercounts`), which
is the case the rule refuses (`fit_refuses_at_top`). The table around the entries (look-up, insertion, the first send
that validates an address) is checked by Ledger.tla, and TraceLedger.tla replays the real ledger.
-/

namespace Pinc.Ledger

/-- `LedgerEntry`. -/
structure E where
  rx : Nat
  tx : Nat
  v : Bool
  deriving DecidableEq, Repr

/-- `saturating_add` at the top `u`. -/
def satAdd (u a n : Nat) : Nat := min (a + n) u

/-- `on_receive`. -/
def recv (u : Nat) (e : E) (n : Nat) : E := { e with rx := satAdd u e.rx n }

/-- `allow_send` on an entry the ledger holds: the answer and the entry after it. `fit` is the code's rule; without it
the gate is the saturating one of the earlier ledger. -/
def allow (u ovh : Nat) (fit : Bool) (e : E) (n : Nat) : Bool × E :=
  if e.v then (true, { e with tx := satAdd u e.tx (satAdd u n ovh) })
  else if e.tx + satAdd u n ovh ≤ 3 * e.rx ∧ (fit = false ∨ e.tx + satAdd u n ovh ≤ u) then
    (true, { e with tx := satAdd u e.tx (satAdd u n ovh) })
  else (false, e)

/-- Under the fit rule a charge to an address that is not validated is recorded in full. -/
theorem allow_exact {u ovh n : Nat} {e : E} (hv : e.v = false) (h : (allow u ovh true e n).1 = true) :
    (allow u ovh true e n).2.tx = e.tx + satAdd u n ovh := by
  unfold allow at h ⊢
  rw [hv] at h ⊢
  rw [ite_eq_right Bool.false_ne_true] at h ⊢
  by_cases hc : e.tx + satAdd u n ovh ≤ 3 * e.rx ∧ (true = false ∨ e.tx + satAdd u n ovh ≤ u)
  · rw [ite_eq_left hc]
    have ht : e.tx + satAdd u n ovh ≤ u := by
      rcases hc.2 with h2 | h2
      · cases h2
      · exact h2
    show min (e.tx + satAdd u n ovh) u = _
    omega
  · rw [ite_eq_right hc] at h
    cases h

/-- The fit rule refuses a charge that would pass the counter's top. -/
theorem fit_refuses_at_top {u ovh n : Nat} {e : E} (hv : e.v = false) (h : u < e.tx + satAdd u n ovh) :
    allow u ovh true e n = (false, e) := by
  unfold allow
  rw [hv, ite_eq_right Bool.false_ne_true]
  have hc : ¬ (e.tx + satAdd u n ovh ≤ 3 * e.rx ∧ (true = false ∨ e.tx + satAdd u n ovh ≤ u)) := by
    intro hc
    rcases hc.2 with h2 | h2
    · cases h2
    · omega
  rw [ite_eq_right hc]

/-- An address that is not validated is charged at most three times what it received, under either rule. -/
theorem allow_bound {u ovh n : Nat} {fit : Bool} {e : E} (hv : e.v = false) (hb : e.tx ≤ 3 * e.rx) :
    (allow u ovh fit e n).2.tx ≤ 3 * (allow u ovh fit e n).2.rx := by
  unfold allow
  rw [hv, ite_eq_right Bool.false_ne_true]
  by_cases hc : e.tx + satAdd u n ovh ≤ 3 * e.rx ∧ (fit = false ∨ e.tx + satAdd u n ovh ≤ u)
  · rw [ite_eq_left hc]
    show min (e.tx + satAdd u n ovh) u ≤ 3 * e.rx
    have := hc.1
    omega
  · rw [ite_eq_right hc]
    exact hb

/-- Receiving keeps the bound: `rx` only grows while it is below the top. -/
theorem recv_bound {u n : Nat} {e : E} (hr : e.rx ≤ u) (hb : e.tx ≤ 3 * e.rx) :
    (recv u e n).tx ≤ 3 * (recv u e n).rx ∧ (recv u e n).rx ≤ u := by
  show e.tx ≤ 3 * min (e.rx + n) u ∧ min (e.rx + n) u ≤ u
  omega

/-- Without the fit rule a charge near the top passes and is recorded short (a counter of 30, 9 bytes charged at 28,
30 recorded); the fit rule refuses it. -/
theorem unfit_undercounts :
    allow 30 2 false ⟨30, 28, false⟩ 7 = (true, ⟨30, 30, false⟩) ∧
      30 < 28 + satAdd 30 7 2 ∧ allow 30 2 true ⟨30, 28, false⟩ 7 = (false, ⟨30, 28, false⟩) := by
  decide

end Pinc.Ledger

#audit_axioms Pinc.Ledger.allow_exact
#audit_axioms Pinc.Ledger.fit_refuses_at_top
#audit_axioms Pinc.Ledger.allow_bound
#audit_axioms Pinc.Ledger.recv_bound
#audit_axioms Pinc.Ledger.unfit_undercounts
