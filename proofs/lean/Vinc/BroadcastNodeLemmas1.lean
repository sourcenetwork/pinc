import Vinc.BroadcastNode

/-!
# Broadcast node: lemmas on the dedupe set and the hub log

Facts used by the node theorems of `BroadcastNodeThm`: the invariant of the dedupe set `Seen` (within capacity,
every map entry is an order entry), what the insert, expire and sweep functions keep, and what a push to and an
expiry of the hub log guarantee (ids kept, ids evicted, bounds).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Vinc.BroadcastNode

section SeenLemmas
variable {p : Params}

/-- The invariant of a dedupe set: within capacity, every map entry is an order entry. -/
structure SeenInv (p : Params) (S : Seen) : Prop where
  len : S.order.length ≤ p.seenCap
  map : ∀ m t, S.map m = some t → (m, t) ∈ S.order

theorem SeenEmpty_inv (p : Params) : SeenInv p SeenEmpty := ⟨by simp [SeenEmpty], by simp [SeenEmpty]⟩

theorem SPopFront_len (S : Seen) : (SPopFront S).order.length = S.order.length - 1 := by
  unfold SPopFront; split <;> simp_all

theorem SPopFront_map {S : Seen} {m t : Nat} (h : (SPopFront S).map m = some t) : S.map m = some t := by
  unfold SPopFront at h
  rcases hS : S.order with _ | ⟨e, rest⟩
  · simp only [hS] at h; exact h
  · simp only [hS] at h
    by_cases hc : S.map e.1 = some e.2
    · simp only [hc, ite_true] at h
      by_cases hm : m = e.1
      · simp [mapSet, hm] at h
      · simpa [mapSet, hm] using h
    · simpa [hc] using h

theorem SPopFront_inv (h : SeenInv p S) : SeenInv p (SPopFront S) := by
  refine ⟨by rw [SPopFront_len]; have := h.len; omega, ?_⟩
  intro m t hm
  have h1 := SPopFront_map hm
  have h2 := h.map m t h1
  unfold SPopFront at hm ⊢
  rcases hS : S.order with _ | ⟨e, rest⟩
  · simp only [hS] at h2 ⊢; exact h2
  · simp only [hS] at h2 hm ⊢
    rcases List.mem_cons.1 h2 with h3 | h3
    · exfalso
      have h4 : m = e.1 := by rw [Prod.ext_iff] at h3; exact h3.1
      have h5 : t = e.2 := by rw [Prod.ext_iff] at h3; exact h3.2
      subst h4; subst h5
      simp [h1, mapSet] at hm
    · exact h3

theorem SPush_inv (h : SeenInv p S) (hl : S.order.length < p.seenCap) : SeenInv p (SPush S mid now) := by
  refine ⟨by simp [SPush]; omega, ?_⟩
  intro m t hm
  by_cases hmk : m = mid
  · subst hmk; simp [SPush, mapSet] at hm ⊢; exact Or.inr hm.symm
  · simp [SPush, mapSet, hmk] at hm ⊢; exact h.map m t hm

theorem SInsert_inv (hc : 0 < p.seenCap) (h : SeenInv p S) : SeenInv p (SInsert p S mid now force) := by
  unfold SInsert
  split
  · rename_i hl
    split
    · apply SPush_inv (SPopFront_inv h)
      rw [SPopFront_len]; have := h.len; omega
    · exact h
  · exact SPush_inv h (by omega)

theorem SInsertAll_inv (hc : 0 < p.seenCap) (ids : List Nat) : ∀ {S : Seen}, SeenInv p S → SeenInv p (SInsertAll p S now ids) := by
  induction ids with
  | nil => intro S h; simpa [SInsertAll] using h
  | cons i ids ih =>
    intro S h; simp only [SInsertAll]
    apply ih
    split
    · exact h
    · exact SInsert_inv hc h

theorem SweepIds_inv (hc : 0 < p.seenCap) (ids : List Nat) : ∀ {S : Seen}, SeenInv p S → SeenInv p (SweepIds p S now ids) := by
  induction ids with
  | nil => intro S h; simpa [SweepIds] using h
  | cons i ids ih =>
    intro S h; simp only [SweepIds]
    apply ih
    split
    · exact h
    · exact SInsert_inv hc h

theorem SExpireAux_inv (now : Nat) (f : Nat) : ∀ {S : Seen}, SeenInv p S → SeenInv p (SExpireAux p now f S) := by
  induction f with
  | zero => intro S h; simpa [SExpireAux] using h
  | succ f ih =>
    intro S h; simp only [SExpireAux]
    split
    · exact h
    · split
      · exact ih (SPopFront_inv h)
      · exact h

theorem SExpire_inv (h : SeenInv p S) : SeenInv p (SExpire p S now) := SExpireAux_inv _ _ h

end SeenLemmas

/-! ## The hub log -/

/-- The ids in a log, oldest first. -/
def LIds (L : Log) : List Nat := L.entries.map (·.mid)

theorem LContains_iff (L : Log) (x : Nat) : LContains L x = true ↔ x ∈ LIds L := by
  simp [LContains, LIds, List.any_eq_true]

theorem LPop_entries (L : Log) : (LPop L).entries = L.entries.tail := by
  unfold LPop; split <;> simp_all

/-- What a push (with the evicted ids collected so far in `ev`) guarantees. -/
structure PushSpec (p : Params) (mid : Nat) (L : Log) (ev : List Nat) (r : PushRes) : Prop where
  len : L.entries.length ≤ p.logCap → r.log.entries.length ≤ p.logCap
  new : ∀ x ∈ LIds r.log, x ∈ LIds L ∨ x = mid
  evSub : ∀ x ∈ r.ev, x ∈ ev ∨ x ∈ LIds L
  ok : r.ok = true → mid ∈ LIds r.log
  keep : ∀ x ∈ LIds L, x ∈ LIds r.log ∨ x ∈ r.ev
  evMono : ∀ x ∈ ev, x ∈ r.ev
  evLen : r.ev.length ≤ ev.length + L.entries.length
  noOk : r.ok = false → ∀ x ∈ LIds r.log, x ∈ LIds L

theorem PushSpec_refl (p : Params) (mid : Nat) (L : Log) (ev : List Nat) : PushSpec p mid L ev ⟨L, false, ev⟩ :=
  ⟨fun h => h, fun _ hx => Or.inl hx, fun _ hx => Or.inl hx, fun h => by simp at h,
   fun _ hx => Or.inl hx, fun _ hx => hx, Nat.le_add_right _ _, fun _ _ hx => hx⟩

theorem LLoop_spec (p : Params) (mid at_ wall n : Nat) (f : Nat) :
    ∀ (L : Log) (ev : List Nat), PushSpec p mid L ev (LLoop p mid at_ wall n f L ev) := by
  induction f with
  | zero => intro L ev; exact PushSpec_refl p mid L ev
  | succ f ih =>
    intro L ev
    unfold LLoop
    split
    · rename_i hc
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; simp [LWrite]; omega
      · intro x hx; simpa [LIds, LWrite] using hx
      · intro x hx; exact Or.inl hx
      · intro _; simp [LIds, LWrite]
      · intro x hx; left; simp only [LIds, LWrite, List.map_append, List.mem_append]; exact Or.inl hx
      · intro x hx; exact hx
      · exact Nat.le_add_right _ _
      · intro h; simp at h
    · rcases hL : L.entries with _ | ⟨e, rest⟩
      · exact PushSpec_refl p mid L ev
      ·
        have h := ih (LPop L) (ev ++ [e.mid])
        have hp : (LPop L).entries = rest := by rw [LPop_entries, hL]; rfl
        have hI : LIds L = e.mid :: LIds (LPop L) := by simp [LIds, hp, hL]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro hl; apply h.len; rw [hp]; rw [hL] at hl; simp at hl; omega
        · intro x hx; rcases h.new x hx with h1 | h1
          · rw [hI]; exact Or.inl (List.mem_cons_of_mem _ h1)
          · exact Or.inr h1
        · intro x hx; rcases h.evSub x hx with h1 | h1
          · simp at h1; rcases h1 with h1 | h1
            · exact Or.inl h1
            · rw [hI]; exact Or.inr (by simp [h1])
          · rw [hI]; exact Or.inr (List.mem_cons_of_mem _ h1)
        · intro hok; have := h.ok hok; exact this
        · intro x hx
          rw [hI] at hx
          rcases List.mem_cons.1 hx with h1 | h1
          · exact Or.inr (h.evMono x (by simp [h1]))
          · exact h.keep x h1
        · intro x hx; exact h.evMono x (by simp [hx])
        · have := h.evLen; simp [hp, hL] at this ⊢; omega
        · intro hk x hx
          have := h.noOk hk x hx
          rw [hI]; exact List.mem_cons_of_mem _ this

theorem LPush_spec (p : Params) (L : Log) (mid at_ wall n : Nat) :
    PushSpec p mid L [] (LPush p L mid at_ wall n) := by
  unfold LPush
  split
  · exact PushSpec_refl p mid L []
  · exact LLoop_spec p mid at_ wall n _ L []

/-- What an expiry guarantees. -/
structure ExpSpec (L : Log) (ev : List Nat) (r : ExpRes) : Prop where
  len : r.log.entries.length ≤ L.entries.length
  new : ∀ x ∈ LIds r.log, x ∈ LIds L
  evSub : ∀ x ∈ r.ev, x ∈ ev ∨ x ∈ LIds L
  keep : ∀ x ∈ LIds L, x ∈ LIds r.log ∨ x ∈ r.ev
  evMono : ∀ x ∈ ev, x ∈ r.ev

theorem ExpSpec_refl (L : Log) (ev : List Nat) : ExpSpec L ev ⟨L, ev⟩ :=
  ⟨Nat.le_refl _, fun _ hx => hx, fun _ hx => Or.inl hx, fun _ hx => Or.inl hx, fun _ hx => hx⟩

theorem LExpireAux_spec (p : Params) (now f : Nat) :
    ∀ (L : Log) (ev : List Nat), ExpSpec L ev (LExpireAux p now f L ev) := by
  induction f with
  | zero => intro L ev; exact ExpSpec_refl L ev
  | succ f ih =>
    intro L ev
    unfold LExpireAux
    rcases hL : L.entries with _ | ⟨e, rest⟩
    · exact ExpSpec_refl L ev
    · by_cases hc : p.logWin < now - e.at_
      · simp only [hc, ite_true]
        have h := ih (LPop L) (ev ++ [e.mid])
        have hp : (LPop L).entries = rest := by rw [LPop_entries, hL]; rfl
        have hI : LIds L = e.mid :: LIds (LPop L) := by simp [LIds, hp, hL]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · have := h.len; rw [hp] at this; simp [hL]; omega
        · intro x hx; rw [hI]; exact List.mem_cons_of_mem _ (h.new x hx)
        · intro x hx; rcases h.evSub x hx with h1 | h1
          · simp at h1; rcases h1 with h1 | h1
            · exact Or.inl h1
            · rw [hI]; exact Or.inr (by simp [h1])
          · rw [hI]; exact Or.inr (List.mem_cons_of_mem _ h1)
        · intro x hx
          rw [hI] at hx
          rcases List.mem_cons.1 hx with h1 | h1
          · exact Or.inr (h.evMono x (by simp [h1]))
          · exact h.keep x h1
        · intro x hx; exact h.evMono x (by simp [hx])
      · simp only [hc, ite_false]; exact ExpSpec_refl L ev

theorem LExpire_spec (p : Params) (L : Log) (now : Nat) : ExpSpec L [] (LExpire p L now) :=
  LExpireAux_spec p now _ L []


/-! ## More on the dedupe set -/

theorem SContains_iff (p : Params) (S : Seen) (x now : Nat) :
    SContains p S x now = true ↔ ∃ t, S.map x = some t ∧ now - t ≤ p.ttl := by
  unfold SContains; cases h : S.map x <;> simp

theorem SPush_map (S : Seen) (mid now x : Nat) : (SPush S mid now).map x = if x = mid then some now else S.map x := by
  simp [SPush, mapSet]

theorem SPush_contains_self (p : Params) (S : Seen) (mid now : Nat) : SContains p (SPush S mid now) mid now = true := by
  simp [SContains, SPush_map]

theorem SPush_contains_mono (p : Params) (S : Seen) (mid now x : Nat) (h : SContains p S x now = true) :
    SContains p (SPush S mid now) x now = true := by
  by_cases hx : x = mid
  · subst hx; exact SPush_contains_self p S _ _
  · simpa [SContains, SPush_map, hx] using h

theorem SPush_contains_ne (p : Params) (S : Seen) (mid now x : Nat) (hx : x ≠ mid)
    (h : SContains p (SPush S mid now) x now = true) : SContains p S x now = true := by
  simpa [SContains, SPush_map, hx] using h

theorem SInsert_map_sub (p : Params) (S : Seen) (i now x : Nat) (f : Bool) (h : (SInsert p S i now f).map x ≠ none) :
    x = i ∨ S.map x ≠ none := by
  unfold SInsert at h
  split at h
  · split at h
    · rw [SPush_map] at h
      by_cases hx : x = i
      · exact Or.inl hx
      · simp [hx] at h
        cases h2 : (SPopFront S).map x with
        | none => exact absurd h2 h
        | some t => exact Or.inr (by rw [SPopFront_map h2]; simp)
    · exact Or.inr h
  · rw [SPush_map] at h
    by_cases hx : x = i
    · exact Or.inl hx
    · exact Or.inr (by simpa [hx] using h)

theorem SInsertAll_map_sub (p : Params) (now : Nat) (ids : List Nat) :
    ∀ (S : Seen) (x : Nat), (SInsertAll p S now ids).map x ≠ none → x ∈ ids ∨ S.map x ≠ none := by
  induction ids with
  | nil => intro S x h; exact Or.inr h
  | cons i ids ih =>
    intro S x h
    simp only [SInsertAll] at h
    rcases ih _ x h with h1 | h1
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · split at h1
      · exact Or.inr h1
      · rcases SInsert_map_sub p S i now x true h1 with h2 | h2
        · exact Or.inl (by simp [h2])
        · exact Or.inr h2

theorem SweepIds_map_sub (p : Params) (now : Nat) (ids : List Nat) :
    ∀ (S : Seen) (x : Nat), (SweepIds p S now ids).map x ≠ none → x ∈ ids ∨ S.map x ≠ none := by
  induction ids with
  | nil => intro S x h; exact Or.inr h
  | cons i ids ih =>
    intro S x h
    simp only [SweepIds] at h
    rcases ih _ x h with h1 | h1
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · split at h1
      · exact Or.inr h1
      · rcases SInsert_map_sub p S i now x true h1 with h2 | h2
        · exact Or.inl (by simp [h2])
        · exact Or.inr h2

theorem SPopFront_map2 (S : Seen) (x : Nat) :
    (SPopFront S).map x = S.map x ∨ ((SPopFront S).map x = none ∧ ∃ e, S.order.head? = some e ∧ S.map x = some e.2) := by
  unfold SPopFront
  rcases hS : S.order with _ | ⟨e, rest⟩
  · left; rfl
  · simp only []
    by_cases hc : S.map e.1 = some e.2
    · simp only [hc, ite_true]
      by_cases hx : x = e.1
      · subst hx; right; refine ⟨by simp [mapSet], e, by simp, hc⟩
      · left; simp [mapSet, hx]
    · simp [hc]

theorem SExpireAux_map (p : Params) (now x : Nat) (f : Nat) :
    ∀ (S : Seen), (SExpireAux p now f S).map x = S.map x ∨
      ((SExpireAux p now f S).map x = none ∧ ∃ t, S.map x = some t ∧ p.ttl < now - t) := by
  induction f with
  | zero => intro S; left; rfl
  | succ f ih =>
    intro S
    unfold SExpireAux
    rcases hS : S.order with _ | ⟨e, rest⟩
    · left; rfl
    · by_cases hc : p.ttl < now - e.2
      · simp only [hc, ite_true]
        have hpop := SPopFront_map2 S x
        have hS' : S.order.head? = some e := by simp [hS]
        rcases ih (SPopFront S) with h1 | ⟨h1, t, ht, hexp⟩
        · rcases hpop with h2 | ⟨h2, e', he', h3⟩
          · exact Or.inl (h1.trans h2)
          · rw [hS'] at he'; cases he'
            exact Or.inr ⟨by rw [h1]; exact h2, _, h3, hc⟩
        · rcases hpop with h2 | ⟨h2, e', he', h3⟩
          · exact Or.inr ⟨h1, t, by rw [← h2]; exact ht, hexp⟩
          · exact Or.inr ⟨h1, t, (by rw [h2] at ht; cases ht), hexp⟩
      · simp [hc]

theorem SExpire_keep (p : Params) (S : Seen) (x now : Nat) (h : SContains p S x now = true) :
    SContains p (SExpire p S now) x now = true := by
  rw [SContains_iff] at h ⊢
  obtain ⟨t, ht, hle⟩ := h
  rcases SExpireAux_map p now x S.order.length S with h1 | ⟨_, t', ht', hexp⟩
  · exact ⟨t, by unfold SExpire; rw [h1]; exact ht, hle⟩
  · rw [ht] at ht'; cases ht'; omega

theorem SExpireAux_map_sub (p : Params) (now x f : Nat) :
    ∀ (S : Seen) (t : Nat), (SExpireAux p now f S).map x = some t → S.map x = some t := by
  intro S t h
  rcases SExpireAux_map p now x f S with h1 | ⟨h1, _⟩
  · rwa [h1] at h
  · rw [h1] at h; cases h



end Vinc.BroadcastNode
