import Pinc.MembershipOkView

/-!
# The view never lists the node itself or a revoked node: deltas

The hub copies are written by `apply_delta` / `push_delta` (an alive delta inserts the member, a down delta erases it) and
by `apply_snap` (next file). An insert goes through the tests of the code: the member is not this node (`apply_delta`,
`push_delta` and `apply_snap` test it before) and not revoked (`N.applyDeltaCore`, the model's cut of `apply_delta`, and `apply_snap` test it). So every
copy keeps listing only clean nodes (`vk_applyDeltaCore`, `vk_pushDelta`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Pinc.Membership
open Pinc.MemInc

theorem AMap.mem_of_get?' {α : Type} (m : AMap α) (k : Nat) (v : α) (h : m.get? k = some v) : (k, v) ∈ m := by
  unfold AMap.get? at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨p, hp, hv⟩ := h
  have h2 : (p.fst == k) = true := @List.find?_some (Nat × α) (fun p : Nat × α => p.fst == k) p m hp
  have hk : p.1 = k := by simpa using h2
  have : p = (k, v) := by obtain ⟨a, b⟩ := p; simp at hk hv; subst hk; subst hv; rfl
  rw [← this]; exact List.mem_of_find?_eq_some hp

theorem AMap.has_insert_cases {α : Type} (m : AMap α) (k j : Nat) (v : α) (h : (m.insert k v).has j = true) : j = k ∨ m.has j = true := by
  unfold AMap.has at h ⊢
  simp only [List.any_eq_true] at h ⊢
  obtain ⟨p, hp, hq⟩ := h
  rcases AMap.mem_insert' m k v p hp with h | h
  · left; subst h; exact (by simpa using hq : k = j).symm
  · right; exact ⟨p, h, hq⟩

theorem hvok_insert {n n' : N} (h : HvOK n) (hub : Nat) (c : HubCopy) (e1 : n'.hv = n.hv.insert hub c) (e3 : n'.revoked = n.revoked)
    (e4 : n'.me = n.me) (hc : ∀ m, c.entries.has m = true → Clean n m) : HvOK n' := by
  intro p hp m hm
  rw [e1] at hp
  have := fun hq => (show Clean n m from hq)
  unfold Clean at *
  rcases AMap.mem_insert' _ _ _ _ hp with h1 | h1
  · subst h1; have := hc m hm; rw [e3, e4]; exact this
  · have := h p h1 m hm; rw [e3, e4]; exact this

theorem vk_adEnsure {n : N} (hx : VOK n) (hub : Nat) : VOK (n.adEnsure hub).1 := by
  unfold N.adEnsure
  split
  · split
    · exact hx
    · exact ⟨hvok_insert hx.hv hub _ rfl rfl rfl (fun m hm => by simp [AMap.has] at hm), hx.mem⟩
  · exact hx

theorem vk_adEntries {n : N} (hx : VOK n) (hub m : Nat) (rc : Rec) (a : Alive) (hme : m ≠ n.me) (hrev : n.revoked.has m = false) :
    VOK (n.adEntries hub m rc a) := by
  unfold N.adEntries
  cases hg : n.hv.get? hub with
  | none => exact hx
  | some c =>
    have hcmem : (hub, c) ∈ n.hv := AMap.mem_of_get?' _ _ _ hg
    have hcl : ∀ k, c.entries.has k = true → Clean n k := fun k hk => hx.hv _ hcmem k hk
    cases a with
    | alive =>
      simp only []
      split
      · refine ⟨hvok_insert hx.hv hub _ rfl rfl rfl (fun k hk => ?_), hx.mem⟩
        rcases AMap.has_insert_cases _ _ _ _ hk with h | h
        · subst h; exact ⟨hme, hrev⟩
        · exact hcl k h
      · exact hx
    | down =>
      simp only [N.adDown]
      split
      · split
        · have h1 : VOK ({ n with hv := n.hv.insert hub { c with entries := c.entries.erase m } } : N) :=
            ⟨hvok_insert hx.hv hub { c with entries := c.entries.erase m } rfl rfl rfl
              (fun k hk => hcl k (AMap.has_of_has_erase _ _ _ hk)), hx.mem⟩
          split <;> exact vk_of h1 rfl rfl rfl rfl
        · exact hx
      · exact hx
    | left =>
      simp only [N.adDown]
      split
      · split
        · have h1 : VOK ({ n with hv := n.hv.insert hub { c with entries := c.entries.erase m } } : N) :=
            ⟨hvok_insert hx.hv hub { c with entries := c.entries.erase m } rfl rfl rfl
              (fun k hk => hcl k (AMap.has_of_has_erase _ _ _ hk)), hx.mem⟩
          split <;> exact vk_of h1 rfl rfl rfl rfl
        · exact hx
      · exact hx

theorem vk_applyDeltaCore {e : Env} {n : N} (hx : VOK n) (now hub m : Nat) (rc : Rec) (a : Alive) (hme : m ≠ n.me) :
    VOK (N.applyDeltaCore e n now hub m rc a) := by
  rw [applyDeltaCore_eq]
  unfold N.applyDeltaCoreS
  split
  · exact hx
  · rename_i hrev
    have hrev' : n.revoked.has m = false := by simpa using hrev
    have h1 := vk_adEnsure hx hub
    have e1 : (n.adEnsure hub).1.me = n.me := by unfold N.adEnsure; split <;> (try split) <;> rfl
    have e2 : (n.adEnsure hub).1.revoked = n.revoked := by unfold N.adEnsure; split <;> (try split) <;> rfl
    generalize n.adEnsure hub = R at h1 e1 e2 ⊢
    obtain ⟨n1, ok⟩ := R
    simp only [] at h1 e1 e2 ⊢
    split
    · exact h1
    · have h2 := vk_adEntries h1 hub m rc a (by rw [e1]; exact hme) (by rw [e2]; exact hrev')
      have h3 := vk_recomputeOne (e := e) h2 now m
      generalize N.recomputeOne e (n1.adEntries hub m rc a) now m = R2 at h3 ⊢
      obtain ⟨n2, ch⟩ := R2
      simp only [] at h3 ⊢
      split
      · exact vk_bump h3
      · exact h3

theorem vk_pushDelta {e : Env} {n : N} (hx : VOK n) (now m : Nat) (rc : Rec) (a : Alive) : VOK (N.pushDelta e n now m rc a) := by
  unfold N.pushDelta
  dsimp only
  have h1 : VOK (forKeys n.attached.keys
      (fun p n => if p != m && (n.isBoot p || (m == n.me && n.homed.has p)) then N.deltaTo e n p m rc a else n) n) :=
    vk_forKeys (fun k b hb => by split; exact vk_deltaTo hb _ _ _ _; exact hb) hx
  have hme : (forKeys n.attached.keys
      (fun p n => if p != m && (n.isBoot p || (m == n.me && n.homed.has p)) then N.deltaTo e n p m rc a else n) n).me = n.me :=
    (forKeys_ht _ _ (fun k b => by split; exact deltaTo_ht ..; exact N.HT_refl b) n).2.2.2.2.2.2.2.2.1
  split
  · exact h1
  · rename_i hm
    exact vk_applyDeltaCore h1 now _ m rc a (by simpa using hm)

macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_pushDelta)

end Pinc.Membership
