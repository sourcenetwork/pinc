import Pinc.ReconcileRefReply

/-!
# Reconcile refinement, part 2m: from the bitmap and the extras to the abstract reply

The reply the machine builds (a bitmap by `rposition`, the extras by id) and reads back (the clear bits) are the
`idsHere`/`idsThere` of the abstract part system; the exact replies are `exactHere`/`exactThere`.
-/

namespace Pinc.Reconcile

theorem lastIdx_none_iff {α : Type} (p : α → Bool) : ∀ (l : List α) (n : Nat),
    lastIdx p l n = none ↔ ∀ x ∈ l, p x = false
  | [], _ => by simp [lastIdx]
  | a :: l, n => by
    have ih := lastIdx_none_iff p l (n + 1)
    unfold lastIdx
    cases h : lastIdx p l (n + 1) with
    | some j =>
      have hn : ¬ ∀ x ∈ l, p x = false := fun hh => by have := ih.mpr hh; simp [h] at this
      simp only [Option.some_ne_none, false_iff]
      exact fun hh => hn (fun x hx => hh x (List.mem_cons_of_mem _ hx))
    | none =>
      have hl := ih.mp h
      by_cases hp : p a = true
      · simp only [hp, ite_true, Option.some_ne_none, false_iff]
        exact fun hh => by have := hh a (List.mem_cons_self ..); simp [hp] at this
      · have hp' : p a = false := by simpa using hp
        simp only [hp', Bool.false_eq_true, ite_false, true_iff]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hp'
        · exact hl x hx

theorem rposN_isNone (is : List Nat) (v : Nat) : (rposN is v).isNone = !is.contains v := by
  rw [rposN_eq]
  have key : (∀ x ∈ is, (x == v) = false) ↔ v ∉ is := by
    constructor
    · intro hh hv; have := hh v hv; simp at this
    · intro hv x hx
      have hne : x ≠ v := fun e => hv (e ▸ hx)
      simp [hne]
  by_cases hm : v ∈ is
  · have h1 : lastIdx (fun a => a == v) is 0 ≠ none := fun hh => by
      have := key.mp ((lastIdx_none_iff _ is 0).mp hh); exact this hm
    cases hl : lastIdx (fun a => a == v) is 0 with
    | none => exact absurd hl h1
    | some j => simp [hm]
  · have h1 : lastIdx (fun a => a == v) is 0 = none := (lastIdx_none_iff _ is 0).mpr (key.mpr hm)
    simp [h1, hm]

theorem lastIdx_lt {α : Type} (p : α → Bool) : ∀ (l : List α) (n k : Nat), lastIdx p l n = some k → n ≤ k ∧ k < n + l.length
  | [], _, _, h => by simp [lastIdx] at h
  | a :: l, n, k, h => by
    unfold lastIdx at h
    cases hl : lastIdx p l (n + 1) with
    | some j =>
      rw [hl] at h; simp at h; subst h
      have := lastIdx_lt p l (n + 1) j hl
      simp; omega
    | none =>
      rw [hl] at h
      by_cases hp : p a = true
      · simp [hp] at h; subst h; simp
      · simp [hp] at h

theorem rposN_lt (is : List Nat) (v k : Nat) (h : rposN is v = some k) : k < is.length := by
  rw [rposN_eq] at h
  have := lastIdx_lt _ is 0 k h
  omega

theorem bitAt_zero4 (j : Nat) : bitAt [0, 0, 0, 0] j = false := by
  unfold bitAt
  cases hq : ([0, 0, 0, 0] : List Nat)[j / 8]? with
  | none => rfl
  | some b =>
    have : b ∈ ([0, 0, 0, 0] : List Nat) := List.mem_of_getElem? hq
    have hb : b = 0 := by simpa using this
    subst hb; simp

theorem bitAt_take (seen : List Nat) (n j : Nat) (h : j / 8 < n) : bitAt (seen.take n) j = bitAt seen j := by
  unfold bitAt; rw [List.getElem?_take_of_lt h]

theorem bmFold_length (o : Oracle) (is : List Nat) : ∀ (xs : List Item) (seen : List Nat),
    (bmFold o is xs seen).length = seen.length
  | [], seen => rfl
  | x :: xs, seen => by
    unfold bmFold at *
    simp only [List.foldl_cons]
    cases hr : rposN is (o.idf x) with
    | none => exact bmFold_length o is xs seen
    | some k => rw [show (List.foldl _ _ xs) = bmFold o is xs (setBit seen k) from rfl, bmFold_length o is xs, setBit_length]

theorem bmFold_bit (o : Oracle) (is : List Nat) (hl : is.length ≤ 32) :
    ∀ (xs : List Item) (seen : List Nat) (j : Nat), seen.length = 4 →
      bitAt (bmFold o is xs seen) j = (bitAt seen j || xs.any (fun x => rposN is (o.idf x) == some j))
  | [], seen, j, _ => by simp [bmFold]
  | x :: xs, seen, j, h4 => by
    have hfold : ∀ s, bmFold o is (x :: xs) s = bmFold o is xs (match rposN is (o.idf x) with
        | some k => setBit s k | none => s) := fun s => rfl
    rw [hfold]
    cases hr : rposN is (o.idf x) with
    | none =>
      rw [bmFold_bit o is hl xs seen j h4]
      simp [hr]
    | some k =>
      have hk := rposN_lt is _ k hr
      have h4' : (setBit seen k).length = 4 := by rw [setBit_length]; exact h4
      rw [bmFold_bit o is hl xs (setBit seen k) j h4', bitAt_setBit seen k j (by omega)]
      have hd : decide (j = k) = (k == j) := by
        by_cases e : j = k
        · subst e; simp
        · have e' : k ≠ j := fun h => e h.symm
          simp [e, e']
      simp [hr, hd, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

theorem unseenList_eq (seen : List Nat) : ∀ (xs : List Item) (j : Nat),
    unseenList seen xs j = ((xs.zipIdx j).filter (fun p => !bitAt seen p.2)).map (·.1)
  | [], _ => by simp [unseenList]
  | x :: xs, j => by
    rw [List.zipIdx_cons, List.filter_cons, unseenList, unseenList_eq seen xs (j + 1)]
    by_cases hb : bitAt seen j = true <;> simp [hb]

/-- The reply to an ids part, read back by the initiator, is the abstract `idsThere` and `idsHere`. -/
theorem ids_reply_bridge (c : Cfg) (I : Iv) (hl : (I.items c.A).length ≤ 32) :
    unseenList ((bmFold c.o (c.ids I) (I.items c.B) [0, 0, 0, 0]).take (((c.ids I).length + 7) / 8))
      (I.items c.A) 0 = c.idsThere I ∧
    extrasOf c.o (c.ids I) (I.items c.B) = c.idsHere I := by
  have hlen : (c.ids I).length = (I.items c.A).length := by simp [Cfg.ids]
  constructor
  · rw [unseenList_eq]
    unfold Cfg.idsThere
    congr 1
    apply List.filter_congr
    intro p hp
    have hj : p.2 < (I.items c.A).length := by
      have := List.mem_zipIdx hp; simp at this; omega
    rw [bitAt_take _ _ _ (by omega), bmFold_bit c.o (c.ids I) (by omega) _ _ _ rfl]
    simp [bitAt_zero4]
  · unfold extrasOf Cfg.idsHere
    apply List.filter_congr
    intro x _
    rw [rposN_isNone]

/-! ## The exact reply -/

theorem bitAt_foldl_setBit : ∀ (L : List Nat) (seen : List Nat) (j : Nat), seen.length = 4 → (∀ k ∈ L, k < 32) →
    bitAt (L.foldl setBit seen) j = (bitAt seen j || L.contains j)
  | [], seen, j, _, _ => by simp
  | k :: L, seen, j, h4, hL => by
    have hk : k < 32 := hL k (List.mem_cons_self ..)
    have h4' : (setBit seen k).length = 4 := by rw [setBit_length]; exact h4
    simp only [List.foldl_cons]
    rw [bitAt_foldl_setBit L (setBit seen k) j h4' (fun x hx => hL x (List.mem_cons_of_mem _ hx)),
      bitAt_setBit seen k j (by omega)]
    have hd : decide (j = k) = (k == j) := by
      by_cases e : j = k
      · subst e; simp
      · have e' : k ≠ j := fun h => e h.symm
        simp [e, e']
    simp [hd, List.contains_cons, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

theorem idxOf_lt (ms : List Item) : ∀ (xs : List Item) (k j : Nat), j ∈ idxOf ms xs k → k ≤ j ∧ j < k + xs.length
  | [], _, _, h => by simp [idxOf] at h
  | x :: xs, k, j, h => by
    unfold idxOf at h
    by_cases hm : ms.contains x = true
    · simp only [hm, ite_true, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have := idxOf_lt ms xs (k + 1) j h; simp; omega
    · simp only [hm, ite_false] at h
      have := idxOf_lt ms xs (k + 1) j h; simp; omega

theorem idxOf_mem (ms : List Item) (hnd : True) : ∀ (xs : List Item) (hx : xs.Nodup) (k i : Nat) (hi : i < xs.length),
    (k + i ∈ idxOf ms xs k ↔ ms.contains xs[i] = true)
  | [], _, _, i, hi => by simp at hi
  | x :: xs, hx, k, 0, hi => by
    unfold idxOf
    simp only [Nat.add_zero, List.getElem_cons_zero]
    by_cases hm : ms.contains x = true
    · rw [if_pos hm]; simp; simpa using hm
    · rw [if_neg hm]
      constructor
      · intro h
        have := idxOf_lt ms xs (k + 1) k h
        omega
      · intro h; exact absurd h hm
  | x :: xs, hx, k, i + 1, hi => by
    unfold idxOf
    have ih := idxOf_mem ms hnd xs (List.nodup_cons.mp hx).2 (k + 1) i (by simpa using hi)
    have e : k + (i + 1) = (k + 1) + i := by omega
    by_cases hm : ms.contains x = true
    · simp only [hm, ite_true, List.mem_cons, e]
      have hne : k + 1 + i ≠ k := by omega
      simp [hne, ih]
    · simp only [hm, ite_false, e]
      simpa using ih

theorem exact_unseen (ms : List Item) (seen : List Nat) : ∀ (xs : List Item) (k : Nat),
    (∀ i (hi : i < xs.length), bitAt seen (k + i) = ms.contains xs[i]) →
    unseenList seen xs k = xs.filter (fun x => !ms.contains x)
  | [], _, _ => by simp [unseenList]
  | x :: xs, k, h => by
    have h0 := h 0 (by simp)
    have ih := exact_unseen ms seen xs (k + 1) (fun i hi => by
      have := h (i + 1) (by simpa using hi)
      simpa [show k + (i + 1) = k + 1 + i by omega] using this)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    unfold unseenList
    rw [ih, List.filter_cons]
    by_cases hm : ms.contains x = true <;> simp [h0, hm]

theorem items_contains (T : List Item) (I : Iv) (x : Item) (hx : I.has x = true) :
    (I.items T).contains x = T.contains x := by
  unfold Iv.items
  by_cases h : x ∈ T
  · simp [List.mem_filter, h, hx]
  · simp [List.mem_filter, h]

/-- The exact reply to an items part: the bitmap says which of the initiator's items we hold. -/
theorem exact_reply_bridge (c : Cfg) (I : Iv) (hl : (I.items c.A).length ≤ 32) :
    unseenList (((bitsFull (I.items c.B) (I.items c.A)).take (((I.items c.A).length + 7) / 8)))
      (I.items c.A) 0 = c.exactThere I ∧
    (I.items c.B).filter (fun x => !(I.items c.A).contains x) = c.exactHere I := by
  have hnd : (I.items c.A).Nodup := (c.hA.filter' I.has).nodup
  constructor
  · have hb : ∀ i (hi : i < (I.items c.A).length),
        bitAt ((bitsFull (I.items c.B) (I.items c.A)).take (((I.items c.A).length + 7) / 8)) (0 + i) =
          (I.items c.B).contains (I.items c.A)[i] := by
      intro i hi
      rw [Nat.zero_add, bitAt_take _ _ _ (by omega)]
      unfold bitsFull
      rw [bitAt_foldl_setBit _ [0, 0, 0, 0] i rfl (fun k hk => by have := idxOf_lt _ _ _ _ hk; omega), bitAt_zero4]
      have := idxOf_mem (I.items c.B) trivial (I.items c.A) hnd 0 i hi
      rw [Nat.zero_add] at this
      cases hc : (I.items c.B).contains (I.items c.A)[i]
      · have hn : i ∉ idxOf (I.items c.B) (I.items c.A) 0 := fun hh => by
          have h1 := this.mp hh; rw [hc] at h1; exact absurd h1 (by decide)
        simpa using hn
      · have h2 := this.mpr hc
        simpa using h2
    rw [exact_unseen _ _ _ _ hb]
    unfold Cfg.exactThere
    apply List.filter_congr
    intro x hx
    have hxI : I.has x = true := (List.mem_filter.mp hx).2
    rw [items_contains c.B I x hxI]
  · unfold Cfg.exactHere
    apply List.filter_congr
    intro x hx
    have hxI : I.has x = true := (List.mem_filter.mp hx).2
    rw [items_contains c.A I x hxI]

end Pinc.Reconcile
