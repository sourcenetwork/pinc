import Pinc.ReconcileApsSafe

/-!
# Reconcile APS, part 5: the session

`aps_session_exact`: for sorted `A` and `B`, a fingerprint that does not collide on the sums of lists (`EncInj`), for every id function and every choice of the
nondeterminism of the code (leaf or split, narrowing fan, what fits a message, the order parts are processed):

* a first pass that has run to the end (`pend = []`) reports a difference that passes the final check exactly when it is
  the exact symmetric difference (the final check detects every wrong result), and a first pass that exchanged no
  ids leaf (`leafed = false`: only fingerprints, responder leaves and cold chunks) is already exact;
* an exact pass that has run to the end is exact and passes the final check, so an honest responder never answers it
  with a second disagreement (`Mismatch` needs a faulty peer or a changed index).

The cold stream is `ColdInit`; its final states are covered by the same statement (`exact = false`, `leafed = false`).
-/

namespace Pinc.Reconcile

/-- The final check of the initiator: the fingerprint it sends equals the responder's whole-set fingerprint. -/
def CheckPasses (c : Cfg) (s : St) : Prop :=
  checkFp c.o c.A c.A.length s.here s.there = c.o.enc (sumH c.B) c.B.length

theorem aps_pass1_final {c : Cfg} (hE : EncInj c.o) {s : St} (h : PReach c s) (hp : s.pend = []) :
    (CheckPasses c s ↔ ExactReport c.A c.B s.here s.there) := by
  obtain ⟨hsafe, _⟩ := reach_inv h
  exact ⟨fun hc => check_detects_wrong hE c.hA.nodup c.hB.nodup hsafe hc,
    fun hx => exact_passes_check c.o c.hA.nodup c.hB.nodup hx⟩

theorem aps_session_exact {c : Cfg} (hE : EncInj c.o) :
    (∀ s, PReach c s → s.exact = false → s.pend = [] →
      (CheckPasses c s ↔ ExactReport c.A c.B s.here s.there) ∧
      (s.leafed = false → ExactReport c.A c.B s.here s.there)) ∧
    (∀ s, PReach c s → s.exact = true → s.pend = [] →
      ExactReport c.A c.B s.here s.there ∧ CheckPasses c s) := by
  refine ⟨fun s h _ hp => ⟨aps_pass1_final hE h hp, fun hl => final_exact_of_lossless hE h (Or.inr hl) hp⟩,
    fun s h he hp => ?_⟩
  have hx := final_exact_of_lossless hE h (Or.inl he) hp
  exact ⟨hx, (aps_pass1_final hE h hp).mpr hx⟩

end Pinc.Reconcile
