import Vinc.MembershipOkBase

/-!
# The view never lists the node itself or a revoked node: `recompute_one`

* `removeFromView_mem_sub`: `remove_from_view` never adds a member.
* `recomputeOne_new_listed`: `recompute_one` adds a member only when some hub copy lists it.
* `vk_recomputeOne`: so it keeps `VOK`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

theorem AMap.has_of_has_erase {α : Type} (m : AMap α) (k j : Nat) (h : (m.erase k).has j = true) : m.has j = true := by
  unfold AMap.erase AMap.has at *
  simp only [List.any_eq_true, List.mem_filter] at h ⊢
  obtain ⟨p, ⟨hp, -⟩, hq⟩ := h
  exact ⟨p, hp, hq⟩

theorem AMap.mem_insert' {α : Type} (m : AMap α) (k : Nat) (v : α) (p : Nat × α) (h : p ∈ m.insert k v) : p = (k, v) ∨ p ∈ m := by
  induction m with
  | nil => simp [AMap.insert] at h; exact Or.inl h
  | cons q r ih =>
    obtain ⟨a, b⟩ := q
    simp only [AMap.insert] at h
    split at h
    · simp at h; rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
    · split at h
      · simp at h; rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])
      · simp at h; rcases h with h | h
        · exact Or.inr (by simp [h])
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (by simp [h])

theorem AMap.mem_erase' {α : Type} (m : AMap α) (k : Nat) (p : Nat × α) (h : p ∈ m.erase k) : p ∈ m := by
  unfold AMap.erase at h
  exact (List.mem_filter.mp h).1

theorem removeFromView_mem_sub (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (x : Bool) (k : Nat)
    (h : (N.removeFromView e n now m cur src x).1.members.has k = true) : n.members.has k = true := by
  unfold N.removeFromView at h
  split at h
  · exact h
  · split at h
    · exact h
    · split at h
      · simpa using h
      · by_cases hh : n.isHub = true <;> by_cases hg : (n.goneVer.len < MAX_TABLE ∨ n.goneVer.has m = true) <;>
          by_cases hl : n.left.has m = true <;> by_cases hx : x = true <;> simp [hh, hg, hl, hx] at h <;>
          exact AMap.has_of_has_erase _ _ _ h

theorem recomputeOne_new_listed (e : Env) (n : N) (now m : Nat) (hnew : n.members.has m = false)
    (h : (N.recomputeOne e n now m).1.members.has m = true) : (n.candidates now (n.source now) m).1 ≠ none := by
  intro hc
  rw [recomputeOne_none e n now m hc] at h
  have := removeFromView_mem_sub e n now m _ _ _ m h
  rw [hnew] at this
  cases this

theorem vk_recomputeOne {e : Env} {n : N} (hx : VOK n) (now m : Nat) : VOK (N.recomputeOne e n now m).1 := by
  obtain ⟨⟨k_hv, k_ep, k_rev, k_me, -⟩, k_mem⟩ := recomputeOne_keeps2 e n now m
  refine ⟨fun p hp m' hm => ?_, fun k hk => ?_⟩
  · rw [k_hv] at hp
    have := hx.hv p hp m' hm
    unfold Clean at *; rw [k_rev, k_me]; exact this
  · have cl : ∀ j, Clean n j → Clean (N.recomputeOne e n now m).1 j := fun j hj => by
      unfold Clean at *; rw [k_rev, k_me]; exact hj
    by_cases hkm : k = m
    · subst hkm
      by_cases hb : n.members.has k = true
      · exact cl _ (hx.mem k hb)
      · have hb' : n.members.has k = false := by simpa using hb
        have hc := recomputeOne_new_listed e n now k hb' hk
        obtain ⟨b, ba, hbb⟩ : ∃ b ba, (n.candidates now (n.source now) k).1 = some (b, ba) := by
          cases hh : (n.candidates now (n.source now) k).1 with
          | none => exact absurd hh hc
          | some q => exact ⟨q.1, q.2, rfl⟩
        obtain ⟨p, hp, ce, ⟨-, hce, -⟩, -⟩ := candidates_listed n now (n.source now) k b ba hbb
        exact cl _ (hx.hv p hp k (AMap.get?_has _ _ _ hce))
    · rw [AMap.has_iff_get] at hk
      rw [k_mem k hkm] at hk
      exact cl _ (hx.mem k (by rw [AMap.has_iff_get]; exact hk))

theorem vk_recomputeOne1 {e : Env} {n : N} (hx : VOK n) (now m : Nat) : VOK (N.recomputeOne e n now m).1 := vk_recomputeOne hx now m

macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_recomputeOne)

end Vinc.Membership
