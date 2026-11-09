import Vinc.Axioms
import Vinc.TransportCid

/-!
# Connection ids: the theorems

What the model proves about the connection id table (`conn/cid.rs`), over unbounded indices and any run of calls:

- the table holds each derived index at most once, at most `slots` ids, none below 1 (`Core`);
- once the secret is installed the `look` indices after the highest one seen are always held, so a packet on a
  fresh path is routable (`Inv.ahead`, `install_inv`, `auth_inv`);
- an entry makes room only if it is stale or used, so it is at or below the highest index seen, and an index
  forgotten is never held again (`Reach.retired`): a retired id is never accepted again;
- the sender takes each index once, in order (`claim_next`).
-/

namespace Vinc.TransportCid

/-- The shape every table keeps. -/
structure Core (c : C) : Prop where
  bound : ∀ s, slots ≤ s → c.ent s = none
  nodup : ∀ s t e f, c.ent s = some e → c.ent t = some f → e.idx = f.idx → s = t
  pos : ∀ s e, c.ent s = some e → 1 ≤ e.idx
  window : ∀ s e, c.ent s = some e → e.idx ≤ c.hi + look
  seenLe : ∀ s e, c.ent s = some e → e.seen = true → e.idx ≤ c.hi

/-- The lookahead ids are held once the secret is installed. -/
def Ahead (c : C) : Prop := c.sec = true → ∀ j, c.hi < j → j ≤ c.hi + look → has c j = true

theorem has_iff (c : C) (hb : ∀ s, slots ≤ s → c.ent s = none) (k : Nat) :
    has c k = true ↔ ∃ s e, c.ent s = some e ∧ e.idx = k := by
  unfold has
  rw [List.any_eq_true]
  constructor
  · rintro ⟨s, _, h⟩
    cases hs : c.ent s with
    | none => simp [hs] at h
    | some e => simp [hs] at h; exact ⟨s, e, hs, h⟩
  · rintro ⟨s, e, hs, he⟩
    have : s < slots := by
      apply Classical.byContradiction; intro hlt
      have := hb s (by omega)
      rw [hs] at this
      simp at this
    exact ⟨s, List.mem_range.2 this, by simp [hs, he]⟩

theorem foldl_pick_mem : ∀ (l : List (Nat × Nat)) (acc : Option (Nat × Nat)) (p : Nat × Nat),
    l.foldl pick acc = some p → acc = some p ∨ p ∈ l
  | [], acc, p, h => by simp at h; exact Or.inl h
  | x :: t, acc, p, h => by
    simp only [List.foldl_cons] at h
    rcases foldl_pick_mem t (pick acc x) p h with h1 | h1
    · unfold pick at h1
      cases acc with
      | none => simp at h1; subst h1; exact Or.inr (by simp)
      | some q =>
        simp only at h1
        split at h1
        · simp at h1; subst h1; exact Or.inr (by simp)
        · exact Or.inl h1
    · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem foldl_pick_isSome : ∀ (l : List (Nat × Nat)) (acc : Option (Nat × Nat)),
    (acc.isSome = true ∨ l ≠ []) → (l.foldl pick acc).isSome = true
  | [], acc, h => by simpa using h
  | x :: t, acc, _ => by
    simp only [List.foldl_cons]
    refine foldl_pick_isSome t (pick acc x) (Or.inl ?_)
    unfold pick
    cases acc with
    | none => simp
    | some q => simp only; split <;> simp

theorem victim_spec (c : C) (s : Nat) (h : victim c = some s) :
    s < slots ∧ ∃ e, c.ent s = some e ∧ evictable c e = true := by
  unfold victim at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  rcases foldl_pick_mem (cands c) none p hp with h1 | h1
  · simp at h1
  · unfold cands at h1
    rw [List.mem_filterMap] at h1
    obtain ⟨s', hs', hb⟩ := h1
    cases he : c.ent s' with
    | none => simp [he] at hb
    | some e =>
      simp only [he, Option.bind_some] at hb
      split at hb
      · rename_i hev
        simp at hb
        subst hb
        exact ⟨List.mem_range.1 hs', e, he, hev⟩
      · simp at hb

theorem victim_isSome (c : C) (s : Nat) (hs : s < slots) (e : E) (he : c.ent s = some e)
    (hev : evictable c e = true) : (victim c).isSome = true := by
  unfold victim
  simp only [Option.isSome_map]
  refine foldl_pick_isSome _ _ (Or.inr ?_)
  intro hnil
  have : (e.used, s) ∈ cands c := by
    unfold cands
    rw [List.mem_filterMap]
    exact ⟨s, List.mem_range.2 hs, by simp [he, hev]⟩
  rw [hnil] at this
  simp at this

theorem freeSlot_spec (c : C) (s : Nat) (h : freeSlot c = some s) : s < slots ∧ c.ent s = none := by
  unfold freeSlot at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  exact ⟨List.mem_range.1 h2, by simpa using h1⟩

theorem freeSlot_none (c : C) (h : freeSlot c = none) : ∀ s, s < slots → c.ent s ≠ none := by
  unfold freeSlot at h
  rw [List.find?_eq_none] at h
  intro s hs hn
  exact h s (List.mem_range.2 hs) (by simp [hn])

theorem put_ent (c : C) (s : Nat) (e : E) (t : Nat) : (put c s e).ent t = if t = s then some e else c.ent t := rfl

theorem put_bound (c : C) (s : Nat) (e : E) (hs : s < slots) (hb : ∀ t, slots ≤ t → c.ent t = none) :
    ∀ t, slots ≤ t → (put c s e).ent t = none := by
  intro t ht
  rw [put_ent]
  have : t ≠ s := by omega
  simp [this, hb t ht]

/-- Pigeonhole: a full table with the window shape has an entry at or below the highest index. -/
theorem full_has_low (c : C) (hc : Core c) (hfull : ∀ s, s < slots → c.ent s ≠ none) :
    ∃ s, s < slots ∧ ∃ e, c.ent s = some e ∧ e.idx ≤ c.hi := by
  apply Classical.byContradiction; intro hno
  have key : ∀ s, s < slots → ∃ e, c.ent s = some e ∧ c.hi < e.idx := by
    intro s hs
    cases he : c.ent s with
    | none => exact absurd he (hfull s hs)
    | some e =>
      refine ⟨e, rfl, ?_⟩
      apply Classical.byContradiction; intro hle
      exact hno ⟨s, hs, e, he, by omega⟩
  obtain ⟨e0, h0, l0⟩ := key 0 (by decide)
  obtain ⟨e1, h1, l1⟩ := key 1 (by decide)
  obtain ⟨e2, h2, l2⟩ := key 2 (by decide)
  have w0 := hc.window 0 e0 h0
  have w1 := hc.window 1 e1 h1
  have w2 := hc.window 2 e2 h2
  have n01 : e0.idx ≠ e1.idx := fun h => by have := hc.nodup 0 1 e0 e1 h0 h1 h; omega
  have n02 : e0.idx ≠ e2.idx := fun h => by have := hc.nodup 0 2 e0 e2 h0 h2 h; omega
  have n12 : e1.idx ≠ e2.idx := fun h => by have := hc.nodup 1 2 e1 e2 h1 h2 h; omega
  simp only [look] at w0 w1 w2
  omega

end Vinc.TransportCid
