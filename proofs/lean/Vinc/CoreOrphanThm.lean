import Vinc.Axioms
import Vinc.CoreOrphan

/-!
# Held first-flight fragments: the table is bounded and gives a datagram out once, fresh, for its own message

What the model proves about `Orphans`, for any number of entries, any times (a clock that steps back included) and
any run of calls:

- the table never grows: every call leaves the number of entries as it was (`expire_length`, `hold_length`,
  `take_length`), and every datagram in it is at most `max` bytes, the places in the order of arrival are distinct
  and below the next one, and `held = replayed + expired + evicted + waiting` (`Inv`, `expire_inv`, `hold_inv`,
  `take_inv`);
- after every call that looks at the table no datagram in it is older than `life` at the time of that call
  (`expire_mem`, `hold_fresh`, `take_mem`);
- the table holds only what `hold` put there, unchanged (`expire_mem`, `hold_mem`, `take_mem`);
- a datagram is given out only if it was held for the message asked for and is not older than `life`; it is the
  oldest arrival of that message still fresh, and it is gone from the table (`take_some`); when none is given, none
  such was held (`take_none`);
- a datagram longer than `max` changes nothing (`hold_refused`); one of at most `max` bytes is always held
  (`hold_mem`); it costs no fresh datagram its entry while an entry is free or holds an old one (`hold_keeps`), and
  else only the oldest arrival (`hold_evicts`);
- over any run of calls no datagram is given out twice (`run_once`).
-/

namespace Vinc.CoreOrphan

/-- The table is well formed. -/
structure Inv (max : Nat) (o : O) : Prop where
  ord_lt : ∀ (i : Nat) (h : H), o.slots[i]? = some (some h) → h.ord < o.order
  len_le : ∀ (i : Nat) (h : H), o.slots[i]? = some (some h) → h.len ≤ max
  distinct : ∀ (i j : Nat) (h h' : H), o.slots[i]? = some (some h) → o.slots[j]? = some (some h') → h.ord = h'.ord → i = j
  balance : o.held = o.replayed + o.expired + o.evicted + waiting o.slots

theorem init_inv (max n : Nat) : Inv max (init n) := by
  have hw : ∀ n, waiting (List.replicate n none) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [waiting, List.replicate_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i h hi
    simp [init, List.getElem?_replicate] at hi
  · intro i h hi
    simp [init, List.getElem?_replicate] at hi
  · intro i j h h' hi
    simp [init, List.getElem?_replicate] at hi
  · simp [init, hw]

/-! ## The scans -/

theorem getD_eq (l : List (Option H)) (k : Nat) : l.getD k none = (l[k]?).getD none := by
  simp [List.getD]

theorem least_none (p : Option H → Bool) : ∀ l, least p l = none → ∀ x ∈ l, p x = false
  | [], _, x, hx => by simp at hx
  | s :: t, h, x, hx => by
    unfold least at h
    cases hl : least p t with
    | none =>
      rw [hl] at h
      dsimp only at h
      by_cases hp : p s = true
      · simp [hp] at h
      · rcases List.mem_cons.mp hx with rfl | hx
        · simpa using hp
        · exact least_none p t hl x hx
    | some k =>
      rw [hl] at h
      dsimp only at h
      split at h <;> simp at h

theorem least_some (p : Option H → Bool) : ∀ l k, least p l = some k →
    k < l.length ∧ p (l.getD k none) = true ∧ ∀ x ∈ l, p x = true → ordOf (l.getD k none) ≤ ordOf x
  | [], k, h => by simp [least] at h
  | s :: t, k, h => by
    unfold least at h
    cases hl : least p t with
    | none =>
      rw [hl] at h
      dsimp only at h
      by_cases hp : p s = true
      · simp [hp] at h
        subst h
        refine ⟨by simp, by simpa using hp, ?_⟩
        intro x hx hpx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rw [least_none p t hl x hx] at hpx
          cases hpx
      · simp [hp] at h
    | some k' =>
      rw [hl] at h
      dsimp only at h
      obtain ⟨hk, hpk, hmin⟩ := least_some p t k' hl
      split at h
      · rename_i hc
        simp at h
        subst h
        refine ⟨by simp, by simpa using hc.1, ?_⟩
        intro x hx hpx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · simp only [List.getD_cons_zero]
          exact Nat.le_trans hc.2 (hmin x hx hpx)
      · rename_i hc
        simp at h
        subst h
        refine ⟨by simpa using hk, by simpa using hpk, ?_⟩
        intro x hx hpx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only [List.getD_cons_succ]
          have : ¬ ordOf x ≤ ordOf (t.getD k' none) := fun hle => hc ⟨hpx, hle⟩
          omega
        · simpa using hmin x hx hpx

theorem firstFree_some : ∀ (l : List (Option H)) k, firstFree l = some k → l[k]? = some none
  | [], k, h => by simp [firstFree] at h
  | none :: t, k, h => by
    simp [firstFree] at h
    subst h
    rfl
  | some a :: t, k, h => by
    simp only [firstFree, Option.map_eq_some_iff] at h
    obtain ⟨k', hk', rfl⟩ := h
    simpa using firstFree_some t k' hk'

theorem firstFree_none : ∀ (l : List (Option H)), firstFree l = none → ∀ i : Nat, l[i]? ≠ some none
  | [], _, i => by simp
  | none :: t, h, i => by simp [firstFree] at h
  | some a :: t, h, i => by
    simp only [firstFree, Option.map_eq_none_iff] at h
    cases i with
    | zero => simp
    | succ i => simpa using firstFree_none t h i

theorem waiting_set : ∀ (l : List (Option H)) (k : Nat) (x y : Option H), l[k]? = some y →
    waiting (l.set k x) + (if y.isSome then 1 else 0) = waiting l + (if x.isSome then 1 else 0)
  | [], k, x, y, h => by simp at h
  | s :: t, 0, x, y, h => by
    simp at h
    subst h
    cases s <;> cases x <;> simp [waiting, List.filter_cons]
  | s :: t, k + 1, x, y, h => by
    simp at h
    have ih := waiting_set t k x y h
    cases s
    · simpa [waiting, List.filter_cons] using ih
    · simp only [waiting, List.set_cons_succ, List.filter_cons, Option.isSome_some, if_true,
        List.length_cons] at ih ⊢
      omega

theorem waiting_expire (life now : Nat) : ∀ (l : List (Option H)),
    waiting l = waiting (l.map fun s => s.filter (fresh life now)) + staleCount life now l
  | [] => rfl
  | none :: t => by
    have ih := waiting_expire life now t
    simpa [waiting, staleCount, List.filter_cons] using ih
  | some h :: t => by
    have ih := waiting_expire life now t
    by_cases hf : fresh life now h = true
    · simp [waiting, staleCount, List.filter_cons, hf] at ih ⊢
      omega
    · simp [waiting, staleCount, List.filter_cons, hf] at ih ⊢
      omega

/-! ## Expire -/

theorem expire_length (life now : Nat) (o : O) : (expire life now o).slots.length = o.slots.length := by
  simp [expire]

theorem expire_get (life now : Nat) (o : O) (i : Nat) (h : H) :
    (expire life now o).slots[i]? = some (some h) ↔ o.slots[i]? = some (some h) ∧ fresh life now h = true := by
  simp only [expire, List.getElem?_map]
  cases hi : o.slots[i]? with
  | none => simp
  | some s =>
    cases s with
    | none => simp
    | some a =>
      by_cases hf : fresh life now a = true
      · simp only [Option.map_some, Option.filter, hf, if_true, Option.some.injEq]
        constructor
        · intro e
          subst e
          exact ⟨rfl, hf⟩
        · exact fun e => e.1
      · simp only [Option.map_some, Option.filter, hf, Option.some.injEq]
        constructor
        · intro e
          simp at e
        · rintro ⟨e, hf'⟩
          subst e
          exact absurd hf' hf

/-- What is in the table after `expire` is what was in it and is not older than `life`. -/
theorem expire_mem (life now : Nat) (o : O) (h : H) :
    some h ∈ (expire life now o).slots ↔ some h ∈ o.slots ∧ now - h.t ≤ life := by
  simp only [List.mem_iff_getElem?, expire_get, fresh, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hf⟩
    exact ⟨⟨i, hi⟩, hf⟩
  · rintro ⟨⟨i, hi⟩, hf⟩
    exact ⟨i, hi, hf⟩

theorem expire_inv (max life now : Nat) (o : O) (hI : Inv max o) : Inv max (expire life now o) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i h hi
    exact hI.ord_lt i h ((expire_get life now o i h).mp hi).1
  · intro i h hi
    exact hI.len_le i h ((expire_get life now o i h).mp hi).1
  · intro i j h h' hi hj
    exact hI.distinct i j h h' ((expire_get life now o i h).mp hi).1 ((expire_get life now o j h').mp hj).1
  · have hw := waiting_expire life now o.slots
    have hb := hI.balance
    simp only [expire] at hw ⊢
    omega

/-! ## Hold -/

theorem get_set (l : List (Option H)) (k i : Nat) (x : Option H) (hk : k < l.length) :
    (l.set k x)[i]? = if i = k then some x else l[i]? := by
  rw [List.getElem?_set]
  by_cases h : k = i
  · subst h
    simp [hk]
  · have h' : ¬ i = k := fun e => h e.symm
    simp [h, h']

theorem get_lt (l : List (Option H)) (k : Nat) (s : Option H) (hk : l[k]? = some s) : k < l.length := by
  rcases Nat.lt_or_ge k l.length with h | h
  · exact h
  · rw [List.getElem?_eq_none h] at hk
    cases hk

theorem hold_refused (max life now : Nat) (key : Key) (loc len tag : Nat) (o : O) (h : max < len) :
    hold max life now key loc len tag o = (false, o) := by
  simp [hold, h]

/-- A datagram of at most `max` bytes takes one entry `k`: a free one after the old ones are let go (`e = 0`), or,
when every entry holds a fresh datagram, the entry of the oldest arrival (`e = 1`). -/
theorem hold_cases (max life now : Nat) (key : Key) (loc len tag : Nat) (o : O) (hlen : len ≤ max)
    (hn : 0 < o.slots.length) :
    ∃ k e, k < (expire life now o).slots.length ∧
      hold max life now key loc len tag o = (true, { expire life now o with
        slots := (expire life now o).slots.set k (some { t := now, ord := o.order, key, loc, len, tag })
        order := o.order + 1
        held := o.held + 1
        evicted := o.evicted + e }) ∧
      (((expire life now o).slots[k]? = some none ∧ e = 0) ∨
        ((∀ i : Nat, (expire life now o).slots[i]? ≠ some none) ∧ e = 1 ∧
          ∃ v, (expire life now o).slots[k]? = some (some v) ∧
            ∀ (i : Nat) (h : H), (expire life now o).slots[i]? = some (some h) → v.ord ≤ h.ord)) := by
  have hn1 : 0 < (expire life now o).slots.length := by rw [expire_length]; exact hn
  unfold hold
  rw [if_neg (Nat.not_lt.mpr hlen)]
  cases hf : firstFree (expire life now o).slots with
  | some k =>
    have hk := firstFree_some _ k hf
    have hlt := get_lt _ k _ hk
    refine ⟨k, 0, hlt, ?_, Or.inl ⟨hk, rfl⟩⟩
    simp [hf, hlt]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | none =>
    have hfull := firstFree_none _ hf
    cases hl : least (fun _ => true) (expire life now o).slots with
    | none =>
      have := least_none _ _ hl
      cases hs : (expire life now o).slots with
      | nil => rw [hs] at hn1; simp at hn1
      | cons a t =>
        rw [hs] at this
        have := this a (by simp)
        simp at this
    | some k =>
      obtain ⟨hlt, _, hmin⟩ := least_some _ _ k hl
      have hsome : ∃ v, (expire life now o).slots[k]? = some (some v) := by
        cases hk : (expire life now o).slots[k]? with
        | none =>
          rw [List.getElem?_eq_none_iff] at hk
          omega
        | some s =>
          cases s with
          | none => exact absurd hk (hfull k)
          | some v => exact ⟨v, rfl⟩
      obtain ⟨v, hv⟩ := hsome
      refine ⟨k, 1, hlt, ?_, Or.inr ⟨hfull, rfl, v, hv, ?_⟩⟩
      · simp [hf, hl, hlt]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · intro i h hi
        have hm : some h ∈ (expire life now o).slots := List.mem_iff_getElem?.mpr ⟨i, hi⟩
        have := hmin (some h) hm rfl
        rw [getD_eq, hv] at this
        exact this

theorem hold_length (max life now : Nat) (key : Key) (loc len tag : Nat) (o : O) (hn : 0 < o.slots.length) :
    (hold max life now key loc len tag o).2.slots.length = o.slots.length := by
  rcases Nat.lt_or_ge max len with h | h
  · rw [hold_refused _ _ _ _ _ _ _ _ h]
  · obtain ⟨k, e, _, he, _⟩ := hold_cases max life now key loc len tag o h hn
    rw [he]
    simp [expire]

theorem hold_inv (max life now : Nat) (key : Key) (loc len tag : Nat) (o : O) (hI : Inv max o)
    (hn : 0 < o.slots.length) : Inv max (hold max life now key loc len tag o).2 := by
  rcases Nat.lt_or_ge max len with h | h
  · rw [hold_refused _ _ _ _ _ _ _ _ h]
    exact hI
  · obtain ⟨k, e, hk, he, hc⟩ := hold_cases max life now key loc len tag o h hn
    have hI1 := expire_inv max life now o hI
    have ho : (expire life now o).order = o.order := rfl
    rw [he]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i x hi
      simp only [get_set _ k i _ hk] at hi
      split at hi
      · simp at hi
        subst hi
        simp
      · have := hI1.ord_lt i x hi
        simp only [ho] at this ⊢
        omega
    · intro i x hi
      simp only [get_set _ k i _ hk] at hi
      split at hi
      · simp at hi
        subst hi
        exact h
      · exact hI1.len_le i x hi
    · intro i j x y hi hj hxy
      simp only [get_set _ k _ _ hk] at hi hj
      split at hi <;> split at hj
      · omega
      · simp at hi
        subst hi
        have := hI1.ord_lt j y hj
        simp only [ho] at this hxy
        omega
      · simp at hj
        subst hj
        have := hI1.ord_lt i x hi
        simp only [ho] at this hxy
        omega
      · exact hI1.distinct i j x y hi hj hxy
    · have hb := hI1.balance
      have he1 : (expire life now o).held = o.held := rfl
      have he2 : (expire life now o).evicted = o.evicted := rfl
      have he3 : (expire life now o).replayed = o.replayed := rfl
      rcases hc with ⟨hfree, rfl⟩ | ⟨_, rfl, v, hv, _⟩
      · have hw := waiting_set (expire life now o).slots k
          (some { t := now, ord := o.order, key, loc, len, tag }) none hfree
        simp at hw
        simp only [he1, he2, he3] at hb ⊢
        omega
      · have hw := waiting_set (expire life now o).slots k
          (some { t := now, ord := o.order, key, loc, len, tag }) (some v) hv
        simp at hw
        simp only [he1, he2, he3] at hb ⊢
        omega

/-- A datagram of at most `max` bytes is always held, and what the table holds after is that datagram and
datagrams it held before that are not older than `life`. -/
theorem hold_mem (max life now : Nat) (key : Key) (loc len tag : Nat) (o : O) (hlen : len ≤ max)
    (hn : 0 < o.slots.length) :
    (hold max life now key loc len tag o).1 = true ∧
      some { t := now, ord := o.order, key, loc, len, tag } ∈ (hold max life now key loc len tag o).2.slots ∧
      ∀ h, some h ∈ (hold max life now key loc len tag o).2.slots →
        h = { t := now, ord := o.order, key, loc, len, tag } ∨ (some h ∈ o.slots ∧ now - h.t ≤ life) := by
  obtain ⟨k, e, hk, he, _⟩ := hold_cases max life now key loc len tag o hlen hn
  rw [he]
  refine ⟨rfl, ?_, ?_⟩
  · exact List.mem_iff_getElem?.mpr ⟨k, by simp [get_set _ k k _ hk]⟩
  · intro h hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    simp only [get_set _ k i _ hk] at hi
    split at hi
    · simp at hi
      exact Or.inl hi.symm
    · exact Or.inr ((expire_mem life now o h).mp (List.mem_iff_getElem?.mpr ⟨i, hi⟩))

/-- After a datagram is held nothing in the table is older than `life`. -/
theorem hold_fresh (max life now : Nat) (key : Key) (loc len tag : Nat) (o : O) (hlen : len ≤ max)
    (hn : 0 < o.slots.length) (h : H) (hm : some h ∈ (hold max life now key loc len tag o).2.slots) :
    now - h.t ≤ life := by
  rcases (hold_mem max life now key loc len tag o hlen hn).2.2 h hm with rfl | ⟨_, hf⟩
  · simp
  · exact hf

/-- While an entry is free or holds a datagram older than `life`, holding a datagram costs no fresh one its
entry and evicts nothing. -/
theorem hold_keeps (max life now : Nat) (key : Key) (loc len tag : Nat) (o : O) (hlen : len ≤ max)
    (hn : 0 < o.slots.length) (hfree : none ∈ (expire life now o).slots) :
    (hold max life now key loc len tag o).2.evicted = o.evicted ∧
      ∀ h, some h ∈ o.slots → now - h.t ≤ life → some h ∈ (hold max life now key loc len tag o).2.slots := by
  obtain ⟨k, e, hk, he, hc⟩ := hold_cases max life now key loc len tag o hlen hn
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hfree
  rcases hc with ⟨hkfree, rfl⟩ | ⟨hfull, _⟩
  · rw [he]
    refine ⟨rfl, ?_⟩
    intro h hm hf
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ((expire_mem life now o h).mpr ⟨hm, hf⟩)
    refine List.mem_iff_getElem?.mpr ⟨i, ?_⟩
    simp only [get_set _ k i _ hk]
    split
    · rename_i hik
      subst hik
      rw [hkfree] at hi
      simp at hi
    · exact hi
  · exact absurd hj (hfull j)

/-- When every entry holds a datagram not older than `life`, holding one more evicts one, the oldest arrival:
every datagram that arrived after another one held stays. -/
theorem hold_evicts (max life now : Nat) (key : Key) (loc len tag : Nat) (o : O)
    (hlen : len ≤ max) (hn : 0 < o.slots.length) (hfull : none ∉ (expire life now o).slots) :
    (hold max life now key loc len tag o).2.evicted = o.evicted + 1 ∧
      ∀ h h', some h ∈ o.slots → now - h.t ≤ life → some h' ∈ o.slots → now - h'.t ≤ life → h'.ord < h.ord →
        some h ∈ (hold max life now key loc len tag o).2.slots := by
  obtain ⟨k, e, hk, he, hc⟩ := hold_cases max life now key loc len tag o hlen hn
  rcases hc with ⟨hkfree, _⟩ | ⟨_, rfl, v, hv, hmin⟩
  · exact absurd (List.mem_iff_getElem?.mpr ⟨k, hkfree⟩) hfull
  · rw [he]
    refine ⟨rfl, ?_⟩
    intro h h' hm hf hm' hf' hlt
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ((expire_mem life now o h).mpr ⟨hm, hf⟩)
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ((expire_mem life now o h').mpr ⟨hm', hf'⟩)
    refine List.mem_iff_getElem?.mpr ⟨i, ?_⟩
    simp only [get_set _ k i _ hk]
    split
    · rename_i hik
      subst hik
      rw [hv] at hi
      simp at hi
      subst hi
      have := hmin j h' hj
      omega
    · exact hi

/-! ## Take -/

theorem take_cases (life now : Nat) (key : Key) (o : O) :
    (take life now key o = (none, expire life now o) ∧
        ∀ (i : Nat) (h : H), (expire life now o).slots[i]? = some (some h) → h.key ≠ key) ∨
      ∃ k h, (expire life now o).slots[k]? = some (some h) ∧ h.key = key ∧
        (∀ (i : Nat) (h' : H), (expire life now o).slots[i]? = some (some h') → h'.key = key → h.ord ≤ h'.ord) ∧
        take life now key o = (some h, { expire life now o with
          slots := (expire life now o).slots.set k none
          replayed := o.replayed + 1 }) := by
  unfold take
  cases hl : least (isMsg key) (expire life now o).slots with
  | none =>
    refine Or.inl ⟨by simp [hl], ?_⟩
    intro i h hi hkey
    have := least_none _ _ hl (some h) (List.mem_iff_getElem?.mpr ⟨i, hi⟩)
    simp [isMsg, hkey] at this
  | some k =>
    obtain ⟨hlt, hp, hmin⟩ := least_some _ _ k hl
    cases hg : (expire life now o).slots.getD k none with
    | none =>
      rw [hg] at hp
      simp [isMsg] at hp
    | some h =>
      rw [hg] at hp hmin
      have hkey : h.key = key := by simpa [isMsg] using hp
      have hk : (expire life now o).slots[k]? = some (some h) := by
        rw [getD_eq] at hg
        cases hk : (expire life now o).slots[k]? with
        | none =>
          rw [List.getElem?_eq_none_iff] at hk
          omega
        | some s =>
          rw [hk] at hg
          simp at hg
          rw [hg]
      refine Or.inr ⟨k, h, hk, hkey, ?_, ?_⟩
      · intro i h' hi hk'
        exact hmin (some h') (List.mem_iff_getElem?.mpr ⟨i, hi⟩) (by simp [isMsg, hk'])
      · simp [hl, hk]
        rfl

theorem take_length (life now : Nat) (key : Key) (o : O) : (take life now key o).2.slots.length = o.slots.length := by
  rcases take_cases life now key o with ⟨he, _⟩ | ⟨k, h, _, _, _, he⟩ <;> rw [he] <;> simp [expire]

/-- What the table holds after a `take` it held before, and none of it is older than `life`. -/
theorem take_mem (life now : Nat) (key : Key) (o : O) (h : H) (hm : some h ∈ (take life now key o).2.slots) :
    some h ∈ o.slots ∧ now - h.t ≤ life := by
  rcases take_cases life now key o with ⟨he, _⟩ | ⟨k, x, hk, _, _, he⟩ <;> rw [he] at hm
  · exact (expire_mem life now o h).mp hm
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    have hlt := get_lt _ k _ hk
    simp only [get_set _ k i _ hlt] at hi
    split at hi
    · simp at hi
    · exact (expire_mem life now o h).mp (List.mem_iff_getElem?.mpr ⟨i, hi⟩)

theorem take_inv (max life now : Nat) (key : Key) (o : O) (hI : Inv max o) : Inv max (take life now key o).2 := by
  have hI1 := expire_inv max life now o hI
  rcases take_cases life now key o with ⟨he, _⟩ | ⟨k, x, hk, _, _, he⟩ <;> rw [he]
  · exact hI1
  · have hlt := get_lt _ k _ hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i y hi
      simp only [get_set _ k i _ hlt] at hi
      split at hi
      · simp at hi
      · exact hI1.ord_lt i y hi
    · intro i y hi
      simp only [get_set _ k i _ hlt] at hi
      split at hi
      · simp at hi
      · exact hI1.len_le i y hi
    · intro i j y z hi hj
      simp only [get_set _ k _ _ hlt] at hi hj
      split at hi
      · simp at hi
      · split at hj
        · simp at hj
        · exact hI1.distinct i j y z hi hj
    · have hb := hI1.balance
      have hw := waiting_set (expire life now o).slots k none (some x) hk
      have he3 : (expire life now o).replayed = o.replayed := rfl
      simp at hw
      simp only [he3] at hb ⊢
      omega

/-- A datagram given out was held for the message asked for and is not older than `life`; it is the oldest
arrival of that message still fresh; and it is gone from the table. -/
theorem take_some (max life now : Nat) (key : Key) (o : O) (hI : Inv max o) (h : H) (o' : O)
    (ht : take life now key o = (some h, o')) :
    some h ∈ o.slots ∧ h.key = key ∧ now - h.t ≤ life ∧
      (∀ h', some h' ∈ o.slots → h'.key = key → now - h'.t ≤ life → h.ord ≤ h'.ord) ∧
      (∀ h', some h' ∈ o'.slots → h'.ord ≠ h.ord) ∧ o'.replayed = o.replayed + 1 := by
  have hI1 := expire_inv max life now o hI
  rcases take_cases life now key o with ⟨he, _⟩ | ⟨k, x, hk, hkey, hmin, he⟩ <;> rw [he] at ht
  · simp at ht
  · simp only [Prod.mk.injEq, Option.some.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    have hm := (expire_mem life now o x).mp (List.mem_iff_getElem?.mpr ⟨k, hk⟩)
    have hlt := get_lt _ k _ hk
    refine ⟨hm.1, hkey, hm.2, ?_, ?_, rfl⟩
    · intro h' hm' hk' hf'
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ((expire_mem life now o h').mpr ⟨hm', hf'⟩)
      exact hmin i h' hi hk'
    · intro h' hm' heq
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm'
      simp only [get_set _ k i _ hlt] at hi
      split at hi
      · simp at hi
      · rename_i hik
        exact hik (hI1.distinct i k h' x hi hk heq)

/-- When no datagram is given out, none that is not older than `life` was held for the message asked for. -/
theorem take_none (life now : Nat) (key : Key) (o o' : O) (ht : take life now key o = (none, o')) :
    o' = expire life now o ∧ ∀ h, some h ∈ o.slots → now - h.t ≤ life → h.key ≠ key := by
  rcases take_cases life now key o with ⟨he, hno⟩ | ⟨k, x, _, _, _, he⟩ <;> rw [he] at ht
  · simp only [Prod.mk.injEq, true_and] at ht
    refine ⟨ht.symm, ?_⟩
    intro h hm hf
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ((expire_mem life now o h).mpr ⟨hm, hf⟩)
    exact hno i h hi
  · simp at ht

/-! ## Any run of calls -/

inductive Op where
  | expire (now : Nat)
  | hold (now : Nat) (key : Key) (loc len tag : Nat)
  | take (now : Nat) (key : Key)

/-- One call: the datagram given out, if any, and the table after. -/
def step (max life : Nat) (o : O) : Op → Option H × O
  | .expire now => (none, expire life now o)
  | .hold now key loc len tag => (none, (hold max life now key loc len tag o).2)
  | .take now key => take life now key o

/-- The datagrams a run of calls gives out, in order. -/
def run (max life : Nat) : O → List Op → List H
  | _, [] => []
  | o, op :: ops => (step max life o op).1.toList ++ run max life (step max life o op).2 ops

theorem step_inv (max life : Nat) (o : O) (op : Op) (hI : Inv max o) (hn : 0 < o.slots.length) :
    Inv max (step max life o op).2 ∧ 0 < (step max life o op).2.slots.length := by
  cases op with
  | expire now => exact ⟨expire_inv max life now o hI, by simp [step, expire_length, hn]⟩
  | hold now key loc len tag =>
    exact ⟨hold_inv max life now key loc len tag o hI hn, by simp [step, hold_length _ _ _ _ _ _ _ _ hn, hn]⟩
  | take now key => exact ⟨take_inv max life now key o hI, by simp [step, take_length, hn]⟩

/-- What the table holds after a call it held before, or it arrived in that call. -/
theorem step_mem (max life : Nat) (o : O) (op : Op) (hn : 0 < o.slots.length) (h : H)
    (hm : some h ∈ (step max life o op).2.slots) : some h ∈ o.slots ∨ o.order ≤ h.ord := by
  cases op with
  | expire now => exact Or.inl ((expire_mem life now o h).mp hm).1
  | hold now key loc len tag =>
    simp only [step] at hm
    rcases Nat.lt_or_ge max len with hl | hl
    · rw [hold_refused _ _ _ _ _ _ _ _ hl] at hm
      exact Or.inl hm
    · rcases (hold_mem max life now key loc len tag o hl hn).2.2 h hm with rfl | ⟨hm', _⟩
      · exact Or.inr (Nat.le_refl _)
      · exact Or.inl hm'
  | take now key => exact Or.inl (take_mem life now key o h hm).1

theorem step_order (max life : Nat) (o : O) (op : Op) (hn : 0 < o.slots.length) :
    o.order ≤ (step max life o op).2.order := by
  cases op with
  | expire now => exact Nat.le_refl _
  | hold now key loc len tag =>
    simp only [step]
    rcases Nat.lt_or_ge max len with hl | hl
    · rw [hold_refused _ _ _ _ _ _ _ _ hl]
      exact Nat.le_refl _
    · obtain ⟨k, e, _, he, _⟩ := hold_cases max life now key loc len tag o hl hn
      rw [he]
      exact Nat.le_succ _
  | take now key =>
    simp only [step]
    rcases take_cases life now key o with ⟨he, _⟩ | ⟨k, x, _, _, _, he⟩ <;> rw [he] <;> exact Nat.le_refl _

/-- Every datagram a run gives out is one the table held at the start, or one that arrived during the run. -/
theorem run_mem (max life : Nat) : ∀ (ops : List Op) (o : O), Inv max o → 0 < o.slots.length →
    ∀ h ∈ run max life o ops, some h ∈ o.slots ∨ o.order ≤ h.ord
  | [], _, _, _, h, hm => by simp [run] at hm
  | op :: ops, o, hI, hn, h, hm => by
    simp only [run, List.mem_append] at hm
    rcases hm with hm | hm
    · cases op with
      | expire now => simp [step] at hm
      | hold now key loc len tag => simp [step] at hm
      | take now key =>
        simp only [step] at hm
        cases hr : take life now key o with
        | mk out o' =>
          rw [hr] at hm
          cases out with
          | none => simp at hm
          | some x =>
            simp at hm
            subst hm
            exact Or.inl (take_some max life now key o hI h o' hr).1
    · obtain ⟨hI', hn'⟩ := step_inv max life o op hI hn
      rcases run_mem max life ops _ hI' hn' h hm with h1 | h1
      · exact step_mem max life o op hn h h1
      · exact Or.inr (Nat.le_trans (step_order max life o op hn) h1)

/-- Over any run of calls no datagram is given out twice: the places in the order of arrival of the datagrams
given out are all different. -/
theorem run_once (max life : Nat) : ∀ (ops : List Op) (o : O), Inv max o → 0 < o.slots.length →
    ((run max life o ops).map (·.ord)).Nodup
  | [], _, _, _ => by simp [run]
  | op :: ops, o, hI, hn => by
    obtain ⟨hI', hn'⟩ := step_inv max life o op hI hn
    have ih := run_once max life ops _ hI' hn'
    have hrest := run_mem max life ops _ hI' hn'
    cases op with
    | expire now => simpa [run, step] using ih
    | hold now key loc len tag => simpa [run, step] using ih
    | take now key =>
      simp only [run, step] at ih hrest ⊢
      cases hr : take life now key o with
      | mk out o' =>
        rw [hr] at ih hrest
        cases out with
        | none => simpa using ih
        | some x =>
          obtain ⟨hx, _, _, _, hgone, _⟩ := take_some max life now key o hI x o' hr
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
          have hxo := hI.ord_lt i x hi
          have hoo : o.order ≤ o'.order := by
            have := step_order max life o (.take now key) hn
            simpa [step, hr] using this
          simp only [Option.toList_some, List.singleton_append, List.map_cons, List.nodup_cons]
          refine ⟨?_, ih⟩
          intro hin
          obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hin
          rcases hrest y hy with h1 | h1
          · exact hgone y h1 hyx
          · have hyx' : y.ord = x.ord := hyx
            have h1' : o'.order ≤ y.ord := h1
            omega

#audit_axioms Vinc.CoreOrphan.init_inv
#audit_axioms Vinc.CoreOrphan.expire_inv
#audit_axioms Vinc.CoreOrphan.expire_mem
#audit_axioms Vinc.CoreOrphan.hold_inv
#audit_axioms Vinc.CoreOrphan.hold_mem
#audit_axioms Vinc.CoreOrphan.hold_keeps
#audit_axioms Vinc.CoreOrphan.hold_evicts
#audit_axioms Vinc.CoreOrphan.take_inv
#audit_axioms Vinc.CoreOrphan.take_some
#audit_axioms Vinc.CoreOrphan.take_none
#audit_axioms Vinc.CoreOrphan.take_mem
#audit_axioms Vinc.CoreOrphan.run_once

end Vinc.CoreOrphan
