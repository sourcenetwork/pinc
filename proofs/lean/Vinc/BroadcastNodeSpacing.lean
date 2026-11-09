import Vinc.BroadcastNodeLemmas7

/-!
# What the dedupe window bounds

The unbounded counterpart of `EpochSpacing` of `proofs/tla/BroadcastNode.tla`. With `epochBound` (an id is delivered at
most once per epoch, an epoch being a record the dedupe set made while it held none for the id), `epochSpacing` says
exactly when a new epoch can start: only when the previous record of the id is older than the window (`ttl`, 600 s) or
the full set dropped it early to make room (`capd`), or the id had no epoch yet. So the window bounds the span between
two deliveries of an id measured between arrivals, and of the last `SEEN_CAP` recorded ids when the set is full.

`GInv` is the invariant that makes it true: a record the set holds is the latest recorded time of the id (`recd`) and
an epoch exists for it; an id the set holds nothing for either never had an epoch, was dropped early, or its last
record is older than the window.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Vinc.BroadcastNode

/-- The ghost invariant of the epochs. -/
structure GInv (p : Params) (s : Sys) : Prop where
  recorded : ∀ m t, s.node.seen.map m = some t → 1 ≤ s.ep m ∧ s.recd m = t
  gone' : ∀ m, s.node.seen.map m = none → s.ep m = 0 ∨ s.capd m = true ∨ p.ttl < s.now - s.recd m

theorem ginv_init (p : Params) : GInv p (SInit p) :=
  ⟨fun m t h => by simp [SInit, NodeInit, SeenEmpty] at h, fun m _ => Or.inl (by simp [SInit])⟩

theorem apply_ginv {p : Params} {s : Sys} {r : Res} {what : Last} {mid : Nat} (hs : GInv p s)
    (M : MapStep s.now s.node.seen r.n.seen) : GInv p (Apply p s r what mid) := by
  refine ⟨fun m t h => ?_, fun m h => ?_⟩
  · change r.n.seen.map m = some t at h
    show 1 ≤ EpG p s.now s.node r.n s.ep m ∧ RecG s.node r.n s.recd m = t
    unfold EpG RecG NewRec
    rcases ha : s.node.seen.map m with _ | t0
    · simp [ha, h]
    · have := hs.recorded m t0 ha
      by_cases hb : r.n.seen.map m = some t0
      · rw [hb] at h; cases h
        simp [ha, hb, this]
      · rcases M m with h1 | h1 | h1
        · exact absurd (h1.trans ha) hb
        · rw [h1] at h; cases h
          simp [ha, h1]; split <;> omega
        · rw [h1] at h; cases h
  · change r.n.seen.map m = none at h
    show EpG p s.now s.node r.n s.ep m = 0 ∨ CapG p s.now s.node r.n s.capd m = true ∨ p.ttl < s.now - RecG s.node r.n s.recd m
    unfold EpG RecG CapG NewRec
    rcases ha : s.node.seen.map m with _ | t0
    · have := hs.gone' m ha
      simp [ha, h]; exact this
    · have hr := hs.recorded m t0 ha
      by_cases hc : s.now - t0 ≤ p.ttl
      · right; left; simp [ha, h, hc]
      · right; right; simp [ha, h]; omega

theorem spacing_core {p : Params} {s : Sys} (hs : GInv p s) (N' : Node) (m : Nat)
    (h : NewRec p s.now s.node N' m = true) : s.ep m = 0 ∨ s.capd m = true ∨ p.ttl < s.now - s.recd m := by
  unfold NewRec at h
  rcases ha : s.node.seen.map m with _ | t0
  · exact hs.gone' m ha
  · right; right
    have := (hs.recorded m t0 ha).2
    rw [this]
    simp [ha] at h
    omega

theorem step_ginv {p : Params} {s s' : Sys} (hs : GInv p s) (st : Step p s s') : GInv p s' := by
  cases st with
  | msg t b m => exact apply_ginv hs (OnMsg_mapStep p s.node s.now s.now t b m)
  | timer => exact apply_ginv hs (OnTimer_mapStep p s.node s.now)
  | answer c hc allow => exact apply_ginv hs (AcpAnswer_mapStep p s.node s.now c.id allow)
  | floors rf of_ nh h => exact apply_ginv hs (FloorsSettled_mapStep p s.node s.now true rf of_ nh)
  | tick h =>
    refine ⟨hs.recorded, fun m hm => ?_⟩
    rcases hs.gone' m hm with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (by show p.ttl < s.now + 1 - s.recd m; omega))
  | restart =>
    exact ⟨fun m t h => by simp [Restarted, NodeInit, SeenEmpty] at h,
      fun m _ => Or.inl (by simp [Restarted])⟩

theorem reach_ginv {p : Params} {s : Sys} (r : Reach p s) : GInv p s := by
  induction r with
  | init => exact ginv_init p
  | step _ st ih => exact step_ginv ih st

/-- A new epoch of an id starts only when the id had no epoch yet, the full set dropped its record early, or its last
record is older than the window. -/
theorem epochSpacing {p : Params} {s s' : Sys} (r : Reach p s) (st : Step p s s') (m : Nat)
    (h : NewRec p s.now s.node s'.node m = true) : s.ep m = 0 ∨ s.capd m = true ∨ p.ttl < s.now - s.recd m :=
  spacing_core (reach_ginv r) _ m h

#audit_axioms Vinc.BroadcastNode.reach_ginv
#audit_axioms Vinc.BroadcastNode.epochSpacing

end Vinc.BroadcastNode
