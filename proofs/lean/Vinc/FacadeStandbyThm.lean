import Vinc.Axioms
import Vinc.FacadeStandby

/-!
# The facade's standby slab: bounded, stale tickets dead

What the model proves about `Standby`, for any number of slots and any run of calls, stale and forged tickets
included:

- every entry of the queue names a slot of the slab; a queued slot is live and the entry of its ticket is in the
  queue; a slot keeps a waker only while it is live and queued; the free stack holds each slot at most once, exactly
  the slots that are not live; every generation is below `2^32` (`Inv`, `init_inv`, `alloc_inv`, `arm_inv`,
  `notify_inv`, `baton_inv`, `notifyAll_inv`, `release_inv`, `run_inv`, `exec_inv`; the release that brings a
  generation round drops only stale entries, `wrapQueue_filter`);
- the slab is as long as the most tickets held at once (`exec_hw`, over any run from the empty slab);
- an `arm`, `notify` or `release` with a ticket that names no live slot of its generation changes nothing and wakes
  nothing (`arm_stale`, `notify_stale`, `release_stale`); a release leaves its ticket dead (`release_dead`), and a
  released ticket names a live slot again only after its slot was released a multiple of `2^32` times in all
  (`dead_stays`);
- `alloc` hands out a ticket that was not live and is now (`alloc_fresh`, `alloc_valid`), the slot on top of the
  free stack, and a new slot only when every slot is live (`alloc_grow`);
- `notify` wakes the ticket's waker if it has one and nothing else (`notify_spec`); `notifyAll` wakes the waker of
  every live slot, in slot order, and leaves no live slot armed (`notifyAll_spec`).

The baton's order, the exact queue and the documented order are in `Vinc.FacadeStandbyOrder`.
-/

namespace Vinc.FacadeStandby

/-! ## Lists -/

theorem get_set {α : Type} (l : List α) (i j : Nat) (v : α) :
    (l.set i v)[j]? = if i = j ∧ i < l.length then some v else l[j]? := by
  rw [List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases h' : i < l.length
    · simp [h']
    · simp [h']
  · simp [h]

theorem get_push {α : Type} (l : List α) (a : α) (j : Nat) :
    (l ++ [a])[j]? = if j = l.length then some a else l[j]? := by
  by_cases h : j < l.length
  · rw [List.getElem?_append_left h]; simp [Nat.ne_of_lt h]
  · by_cases h' : j = l.length
    · subst h'; simp
    · have h2 : l.length < j := by omega
      rw [List.getElem?_append_right (by omega)]
      simp [h', show l[j]? = none from List.getElem?_eq_none (by omega)]
      omega

theorem lt_of_get {α : Type} {l : List α} {i : Nat} {v : α} (h : l[i]? = some v) : i < l.length := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp h
  exact hi

/-- A filter by a predicate that implies another keeps a sublist of the other's filter. -/
theorem filter_mono {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true → q x = true) → (l.filter p).Sublist (l.filter q)
  | [], _ => List.Sublist.slnil
  | a :: t, h => by
    have ih := filter_mono p q t (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases hp : p a = true
    · have hq := h a List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq]
      exact ih.cons_cons a
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q a = true
      · rw [List.filter_cons_of_pos hq]
        exact ih.cons a
      · rw [List.filter_cons_of_neg hq]
        exact ih

/-! ## Tickets -/

theorem ticket_eq {u t : Ticket} (h1 : u.idx = t.idx) (h2 : u.gen = t.gen) : u = t := by
  cases u
  cases t
  rw [Ticket.mk.injEq]
  exact ⟨h1, h2⟩

theorem slotAt_some {slots : List Slot} {t : Ticket} {sl : Slot} :
    slotAt slots t = some sl ↔ slots[t.idx]? = some sl ∧ sl.live = true ∧ sl.gen = t.gen := by
  unfold slotAt
  cases h : slots[t.idx]? with
  | none => simp
  | some x =>
    by_cases hc : x.live = true ∧ x.gen = t.gen
    · simp only [hc, and_self, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hc⟩
      · rintro ⟨rfl, _⟩; rfl
    · simp only [hc, ↓reduceIte, reduceCtorEq, Option.some.injEq, false_iff]
      rintro ⟨rfl, h1, h2⟩; exact hc ⟨h1, h2⟩

theorem slotOf_some {s : S} {t : Ticket} {sl : Slot} :
    slotOf s t = some sl ↔ s.slots[t.idx]? = some sl ∧ sl.live = true ∧ sl.gen = t.gen := slotAt_some

theorem valid_iff {slots : List Slot} {t : Ticket} : valid slots t = true ↔ ∃ sl, slotAt slots t = some sl := by
  unfold valid
  cases slotAt slots t <;> simp

/-- Two live tickets of one slot are the same ticket. -/
theorem valid_idx {slots : List Slot} {x y : Ticket} (hx : valid slots x = true) (hy : valid slots y = true)
    (h : x.idx = y.idx) : x = y := by
  obtain ⟨sx, hsx⟩ := valid_iff.mp hx
  obtain ⟨sy, hsy⟩ := valid_iff.mp hy
  obtain ⟨h1, _, h3⟩ := slotAt_some.mp hsx
  obtain ⟨h4, _, h6⟩ := slotAt_some.mp hsy
  rw [h, h4] at h1
  cases h1
  exact ticket_eq h (h3.symm.trans h6)

/-- A slot changed at another index: the ticket names what it named. -/
theorem slotAt_set_ne (slots : List Slot) (i : Nat) (v : Slot) (u : Ticket) (h : u.idx ≠ i) :
    slotAt (slots.set i v) u = slotAt slots u := by
  unfold slotAt
  rw [get_set]
  simp [Ne.symm h]

/-- The slot of index `i` changed to `v`: a ticket of that slot names `v` if `v` is live of its generation. -/
theorem slotAt_set_same (slots : List Slot) (i : Nat) (v : Slot) (u : Ticket) (hu : u.idx = i)
    (hlt : i < slots.length) :
    slotAt (slots.set i v) u = if v.live = true ∧ v.gen = u.gen then some v else none := by
  unfold slotAt
  rw [get_set, hu]
  simp [hlt]

theorem slotAt_get (slots : List Slot) (i : Nat) (sl : Slot) (u : Ticket) (hu : u.idx = i)
    (hsl : slots[i]? = some sl) :
    slotAt slots u = if sl.live = true ∧ sl.gen = u.gen then some sl else none := by
  simp only [slotAt, hu, hsl]

theorem slotAt_set_eq {slots : List Slot} {i : Nat} {v x : Slot} {u : Ticket} (hu : u.idx = i)
    (h : slotAt (slots.set i v) u = some x) : x = v := by
  have hlt : i < slots.length := by
    have := lt_of_get (slotAt_some.mp h).1
    rw [hu, List.length_set] at this
    exact this
  rw [slotAt_set_same slots i v u hu hlt] at h
  by_cases hc : v.live = true ∧ v.gen = u.gen
  · rw [ite_eq_left hc] at h
    cases h
    rfl
  · rw [ite_eq_right hc] at h
    cases h

/-- A slot changed keeping its liveness and generation: every ticket is live exactly when it was. -/
theorem valid_set (slots : List Slot) (i : Nat) (sl v : Slot) (hsl : slots[i]? = some sl)
    (hl : v.live = sl.live) (hg : v.gen = sl.gen) (u : Ticket) : valid (slots.set i v) u = valid slots u := by
  by_cases hu : u.idx = i
  · unfold valid
    rw [slotAt_set_same slots i v u hu (lt_of_get hsl), slotAt_get slots i sl u hu hsl, hl, hg]
    by_cases hc : sl.live = true ∧ sl.gen = u.gen
    · rw [ite_eq_left hc, ite_eq_left hc] <;> simp
    · rw [ite_eq_right hc, ite_eq_right hc]
  · unfold valid
    rw [slotAt_set_ne slots i v u hu]

/-- A slot changed keeping its liveness, generation and waker: every ticket keeps the waker it had. -/
theorem wakerAt_set (slots : List Slot) (i : Nat) (sl v : Slot) (hsl : slots[i]? = some sl)
    (hl : v.live = sl.live) (hg : v.gen = sl.gen) (hw : v.waker = sl.waker) (u : Ticket) :
    wakerAt (slots.set i v) u = wakerAt slots u := by
  by_cases hu : u.idx = i
  · unfold wakerAt
    rw [slotAt_set_same slots i v u hu (lt_of_get hsl), slotAt_get slots i sl u hu hsl, hl, hg]
    by_cases hc : sl.live = true ∧ sl.gen = u.gen
    · rw [ite_eq_left hc, ite_eq_left hc] <;> simp [hw]
    · rw [ite_eq_right hc, ite_eq_right hc]
  · unfold wakerAt
    rw [slotAt_set_ne slots i v u hu]

/-! ## The invariant -/

/-- The slab is well formed. -/
structure Inv (s : S) : Prop where
  q_idx : ∀ t ∈ s.queue, t.idx < s.slots.length
  q_live : ∀ (i : Nat) (sl : Slot), s.slots[i]? = some sl → sl.queued = true →
    sl.live = true ∧ (⟨i, sl.gen⟩ : Ticket) ∈ s.queue
  w_q : ∀ (i : Nat) (sl : Slot), s.slots[i]? = some sl → sl.waker.isSome = true → sl.live = true ∧ sl.queued = true
  f_nodup : s.free.Nodup
  f_iff : ∀ i : Nat, i ∈ s.free ↔ ∃ sl : Slot, s.slots[i]? = some sl ∧ sl.live = false
  gen_lt : ∀ (i : Nat) (sl : Slot), s.slots[i]? = some sl → sl.gen < GENS

theorem init_inv : Inv ({} : S) := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_⟩ <;> simp

/-! ## The calls keep it -/

theorem alloc_inv (s : S) (h : Inv s) : Inv (alloc s).2 := by
  unfold alloc
  cases hf : s.free with
  | nil =>
    simp only
    refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_⟩
    · intro u hu
      have := h.q_idx u hu
      show u.idx < (s.slots ++ [newSlot]).length
      simp only [List.length_append, List.length_singleton]
      omega
    · intro j sl hj hq
      rw [get_push] at hj
      by_cases hj' : j = s.slots.length
      · simp [hj'] at hj; subst hj; simp [newSlot] at hq
      · simp [hj'] at hj; exact h.q_live j sl hj hq
    · intro j sl hj hw
      rw [get_push] at hj
      by_cases hj' : j = s.slots.length
      · simp [hj'] at hj; subst hj; simp [newSlot] at hw
      · simp [hj'] at hj; exact h.w_q j sl hj hw
    · intro j
      rw [get_push]
      by_cases hj : j = s.slots.length
      · simp [hj, newSlot]
      · simp only [hj, ↓reduceIte, List.not_mem_nil, false_iff]
        intro ⟨sl, h1, h2⟩
        have := (h.f_iff j).mpr ⟨sl, h1, h2⟩
        rw [hf] at this; cases this
    · intro j sl hj
      rw [get_push] at hj
      by_cases hj' : j = s.slots.length
      · simp [hj'] at hj; subst hj; simp [newSlot, GENS]
      · simp [hj'] at hj; exact h.gen_lt j sl hj
  | cons i rest =>
    have hi : i ∈ s.free := by rw [hf]; exact List.mem_cons_self
    obtain ⟨sl0, hsl0, hdead⟩ := (h.f_iff i).mp hi
    have hnd : (i :: rest).Nodup := hf ▸ h.f_nodup
    simp only [hsl0]
    refine ⟨?_, ?_, ?_, (List.nodup_cons.mp hnd).2, ?_, ?_⟩
    · intro u hu
      show u.idx < (s.slots.set i { sl0 with live := true }).length
      rw [List.length_set]; exact h.q_idx u hu
    · intro j sl hj hq
      rw [get_set] at hj
      by_cases hij : i = j
      · subst hij
        simp [lt_of_get hsl0] at hj; subst hj
        have := (h.q_live i sl0 hsl0 hq).1
        rw [hdead] at this; cases this
      · simp [hij] at hj; exact h.q_live j sl hj hq
    · intro j sl hj hw
      rw [get_set] at hj
      by_cases hij : i = j
      · subst hij
        simp [lt_of_get hsl0] at hj; subst hj
        have := h.w_q i sl0 hsl0 hw
        rw [hdead] at this; cases this.1
      · simp [hij] at hj; exact h.w_q j sl hj hw
    · intro j
      rw [get_set]
      by_cases hij : i = j
      · subst hij
        simp [lt_of_get hsl0, (List.nodup_cons.mp hnd).1]
      · simp only [hij, false_and, ↓reduceIte]
        rw [← h.f_iff j, hf]
        simp [Ne.symm hij]
    · intro j sl hj
      rw [get_set] at hj
      by_cases hij : i = j
      · subst hij; simp [lt_of_get hsl0] at hj; subst hj; exact h.gen_lt i sl0 hsl0
      · simp [hij] at hj; exact h.gen_lt j sl hj

/-- Changing the slot `i` to `v`, with the same liveness, queued mark and generation and a waker only on a live
queued slot, keeps the invariant. -/
theorem set_inv (s : S) (h : Inv s) (i : Nat) (sl v : Slot) (hsl : s.slots[i]? = some sl)
    (hl : v.live = sl.live) (hq : v.queued = sl.queued) (hg : v.gen = sl.gen)
    (hw : v.waker.isSome = true → v.live = true ∧ v.queued = true) :
    Inv { s with slots := s.slots.set i v } := by
  have hlt := lt_of_get hsl
  refine ⟨?_, ?_, ?_, h.f_nodup, ?_, ?_⟩
  · intro u hu
    show u.idx < (s.slots.set i v).length
    rw [List.length_set]; exact h.q_idx u hu
  · intro j sl' hj hq'
    simp only [get_set] at hj
    by_cases hij : i = j
    · subst hij; simp [hlt] at hj; subst hj
      rw [hq] at hq'
      obtain ⟨h1, h2⟩ := h.q_live i sl hsl hq'
      refine ⟨by rw [hl]; exact h1, ?_⟩
      show (⟨i, v.gen⟩ : Ticket) ∈ s.queue
      rw [hg]; exact h2
    · simp [hij] at hj; exact h.q_live j sl' hj hq'
  · intro j sl' hj hw'
    simp only [get_set] at hj
    by_cases hij : i = j
    · subst hij; simp [hlt] at hj; subst hj; exact hw hw'
    · simp [hij] at hj; exact h.w_q j sl' hj hw'
  · intro j
    show j ∈ s.free ↔ _
    rw [h.f_iff j, get_set]
    by_cases hj : i = j
    · subst hj; rw [hsl]; simp [hlt, hl]
    · simp [hj]
  · intro j sl' hj
    simp only [get_set] at hj
    by_cases hij : i = j
    · subst hij; simp [hlt] at hj; subst hj; rw [hg]; exact h.gen_lt i sl hsl
    · simp [hij] at hj; exact h.gen_lt j sl' hj

/-! ### The compaction of `arm` -/

theorem compact_sub {s : S} {u : Ticket} (h : u ∈ compact s) : u ∈ s.queue := by
  unfold compact at h
  split at h
  · exact (List.mem_filter.mp h).1
  · exact h

theorem compact_keep {s : S} {u : Ticket} (hu : u ∈ s.queue) (hv : valid s.slots u = true) : u ∈ compact s := by
  unfold compact
  split
  · exact List.mem_filter.mpr ⟨hu, hv⟩
  · exact hu

/-- The compaction drops only stale entries. -/
theorem compact_filter (s : S) : (compact s).filter (valid s.slots) = s.queue.filter (valid s.slots) := by
  unfold compact
  split
  · rw [List.filter_filter]
    exact List.filter_congr (fun x _ => by simp)
  · rfl

/-! ### The queue a release leaves -/

theorem wrapQueue_sub {g : Nat} {slots : List Slot} {q : List Ticket} {u : Ticket} (h : u ∈ wrapQueue g slots q) :
    u ∈ q := by
  unfold wrapQueue at h
  split at h
  · exact (List.mem_filter.mp h).1
  · exact h

theorem wrapQueue_keep {g : Nat} {slots : List Slot} {q : List Ticket} {u : Ticket} (hu : u ∈ q)
    (hv : valid slots u = true) : u ∈ wrapQueue g slots q := by
  unfold wrapQueue
  split
  · exact List.mem_filter.mpr ⟨hu, hv⟩
  · exact hu

/-- The drop at the wrap drops only stale entries. -/
theorem wrapQueue_filter (g : Nat) (slots : List Slot) (q : List Ticket) :
    (wrapQueue g slots q).filter (valid slots) = q.filter (valid slots) := by
  unfold wrapQueue
  split
  · rw [List.filter_filter]
    exact List.filter_congr (fun x _ => by simp)
  · rfl

theorem wrapQueue_len (g : Nat) (slots : List Slot) (q : List Ticket) : (wrapQueue g slots q).length ≤ q.length := by
  unfold wrapQueue
  split
  · exact List.length_filter_le _ _
  · exact Nat.le_refl _

theorem arm_inv (t : Ticket) (w : Nat) (s : S) (h : Inv s) : Inv (arm t w s) := by
  unfold arm
  cases hs : slotOf s t with
  | none => exact h
  | some sl =>
    obtain ⟨hsl, hlive, hgen⟩ := slotOf_some.mp hs
    have hlt := lt_of_get hsl
    by_cases hq : sl.queued = true
    · simp only [hq, ↓reduceIte]
      exact set_inv s h t.idx sl _ hsl rfl (by simp [hq]) rfl (fun _ => ⟨hlive, rfl⟩)
    · simp only [hq, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_, ?_, h.f_nodup, ?_, ?_⟩
      · intro u hu
        show u.idx < (s.slots.set t.idx { sl with waker := some w, queued := true }).length
        rw [List.length_set]
        rcases List.mem_append.mp hu with hu | hu
        · exact h.q_idx u (compact_sub hu)
        · rw [List.mem_singleton] at hu; subst hu; exact hlt
      · intro j sl' hj hq'
        simp only [get_set] at hj
        by_cases hij : t.idx = j
        · subst hij; simp [hlt] at hj; subst hj
          refine ⟨hlive, List.mem_append.mpr (Or.inr (List.mem_singleton.mpr ?_))⟩
          exact ticket_eq rfl hgen
        · simp [hij] at hj
          obtain ⟨h1, h2⟩ := h.q_live j sl' hj hq'
          refine ⟨h1, List.mem_append.mpr (Or.inl (compact_keep h2 ?_))⟩
          exact valid_iff.mpr ⟨sl', slotAt_some.mpr ⟨hj, h1, rfl⟩⟩
      · intro j sl' hj hw'
        simp only [get_set] at hj
        by_cases hij : t.idx = j
        · subst hij; simp [hlt] at hj; subst hj; exact ⟨hlive, rfl⟩
        · simp [hij] at hj; exact h.w_q j sl' hj hw'
      · intro j
        show j ∈ s.free ↔ _
        rw [h.f_iff j, get_set]
        by_cases hj : t.idx = j
        · subst hj; rw [hsl]; simp [hlt]
        · simp [hj]
      · intro j sl' hj
        simp only [get_set] at hj
        by_cases hij : t.idx = j
        · subst hij; simp [hlt] at hj; subst hj; exact h.gen_lt _ sl hsl
        · simp [hij] at hj; exact h.gen_lt j sl' hj

theorem notify_inv (t : Ticket) (s : S) (h : Inv s) : Inv (notify t s).2 := by
  unfold notify
  cases hs : slotOf s t with
  | none => exact h
  | some sl =>
    obtain ⟨hsl, _, _⟩ := slotOf_some.mp hs
    cases hw : sl.waker with
    | none => simp only [hw]; exact h
    | some w => simp only [hw]; exact set_inv s h t.idx sl _ hsl rfl rfl rfl (by simp)

theorem release_inv (t : Ticket) (s : S) (h : Inv s) : Inv (release t s) := by
  unfold release
  cases hs : slotOf s t with
  | none => exact h
  | some sl =>
    obtain ⟨hsl, hlive, _⟩ := slotOf_some.mp hs
    have hlt := lt_of_get hsl
    have hnot : t.idx ∉ s.free := fun hm => by
      obtain ⟨sl', h1, h2⟩ := (h.f_iff _).mp hm
      rw [hsl] at h1; cases h1; rw [hlive] at h2; cases h2
    refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨hnot, h.f_nodup⟩, ?_, ?_⟩
    · intro u hu
      show u.idx < (s.slots.set t.idx _).length
      rw [List.length_set]; exact h.q_idx u (wrapQueue_sub hu)
    · intro j sl' hj hq'
      have hj0 := hj
      simp only [get_set] at hj
      by_cases hij : t.idx = j
      · subst hij; simp [hlt] at hj; subst hj; simp at hq'
      · simp [hij] at hj
        obtain ⟨h1, h2⟩ := h.q_live j sl' hj hq'
        exact ⟨h1, wrapQueue_keep h2 (valid_iff.mpr ⟨sl', slotAt_some.mpr ⟨hj0, h1, rfl⟩⟩)⟩
    · intro j sl' hj hw'
      simp only [get_set] at hj
      by_cases hij : t.idx = j
      · subst hij; simp [hlt] at hj; subst hj; simp at hw'
      · simp [hij] at hj; exact h.w_q j sl' hj hw'
    · intro j
      show j ∈ t.idx :: s.free ↔ _
      rw [List.mem_cons, h.f_iff j, get_set]
      by_cases hj : t.idx = j
      · subst hj; simp [hlt]
      · simp [hj, Ne.symm hj]
    · intro j sl' hj
      simp only [get_set] at hj
      by_cases hij : t.idx = j
      · subst hij; simp [hlt] at hj; subst hj; exact Nat.mod_lt _ (by simp [GENS])
      · simp [hij] at hj; exact h.gen_lt j sl' hj

theorem notifyAll_inv (s : S) (h : Inv s) : Inv (notifyAll s).2 := by
  unfold notifyAll
  refine ⟨?_, ?_, ?_, h.f_nodup, ?_, ?_⟩
  · intro u hu
    show u.idx < (s.slots.map _).length
    rw [List.length_map]; exact h.q_idx u hu
  · intro j sl' hj hq'
    simp only [List.getElem?_map] at hj
    cases hj0 : s.slots[j]? with
    | none => simp [hj0] at hj
    | some sl =>
      simp only [hj0, Option.map_some, Option.some.injEq] at hj
      by_cases hl : sl.live = true
      · simp [hl] at hj; subst hj; exact ⟨rfl, (h.q_live j sl hj0 hq').2⟩
      · simp [hl] at hj; subst hj; exact h.q_live j sl hj0 hq'
  · intro j sl' hj hw'
    simp only [List.getElem?_map] at hj
    cases hj0 : s.slots[j]? with
    | none => simp [hj0] at hj
    | some sl =>
      simp only [hj0, Option.map_some, Option.some.injEq] at hj
      by_cases hl : sl.live = true
      · simp [hl] at hj; subst hj; simp at hw'
      · simp [hl] at hj; subst hj; exact h.w_q j sl hj0 hw'
  · intro j
    show j ∈ s.free ↔ _
    rw [h.f_iff j, List.getElem?_map]
    cases hj : s.slots[j]? with
    | none => simp
    | some sl => by_cases hl : sl.live = true <;> simp [hl]
  · intro j sl' hj
    simp only [List.getElem?_map] at hj
    cases hj0 : s.slots[j]? with
    | none => simp [hj0] at hj
    | some sl =>
      simp only [hj0, Option.map_some, Option.some.injEq] at hj
      by_cases hl : sl.live = true
      · simp [hl] at hj; subst hj; exact h.gen_lt j sl hj0
      · simp [hl] at hj; subst hj; exact h.gen_lt j sl hj0

/-! ### The baton -/

/-- One turn of the baton's loop on a stale entry: it leaves the queue, and nothing else changes. -/
theorem skip_inv (slots : List Slot) (free : List Nat) (t : Ticket) (rest : List Ticket)
    (h : Inv ⟨slots, free, t :: rest⟩) (ht : slotAt slots t = none) : Inv ⟨slots, free, rest⟩ := by
  refine ⟨fun u hu => h.q_idx u (List.mem_cons_of_mem _ hu), ?_, h.w_q, h.f_nodup, h.f_iff, h.gen_lt⟩
  intro j sl hj hq
  obtain ⟨h1, h2⟩ := h.q_live j sl hj hq
  refine ⟨h1, ?_⟩
  rcases List.mem_cons.mp h2 with e | e
  · exfalso
    have : slotAt slots ⟨j, sl.gen⟩ = some sl := slotAt_some.mpr ⟨hj, h1, rfl⟩
    rw [e, ht] at this; cases this
  · exact e

/-- One turn of the baton's loop on a live entry: it leaves the queue, and its slot is unqueued with no waker. -/
theorem pop_inv (slots : List Slot) (free : List Nat) (t : Ticket) (rest : List Ticket) (sl v : Slot)
    (h : Inv ⟨slots, free, t :: rest⟩) (hsl : slotAt slots t = some sl)
    (hl : v.live = sl.live) (hq : v.queued = false) (hg : v.gen = sl.gen) (hw : v.waker = none) :
    Inv ⟨slots.set t.idx v, free, rest⟩ := by
  obtain ⟨hs, _, _⟩ := slotAt_some.mp hsl
  have hlt := lt_of_get hs
  refine ⟨?_, ?_, ?_, h.f_nodup, ?_, ?_⟩
  · intro u hu
    show u.idx < (slots.set t.idx v).length
    rw [List.length_set]; exact h.q_idx u (List.mem_cons_of_mem _ hu)
  · intro j sl' hj hq'
    simp only [get_set] at hj
    by_cases hij : t.idx = j
    · subst hij; simp [hlt] at hj; subst hj; rw [hq] at hq'; cases hq'
    · simp [hij] at hj
      obtain ⟨h1, h2⟩ := h.q_live j sl' hj hq'
      refine ⟨h1, ?_⟩
      rcases List.mem_cons.mp h2 with e | e
      · exact absurd (show t.idx = j by rw [← e]) hij
      · exact e
  · intro j sl' hj hw'
    simp only [get_set] at hj
    by_cases hij : t.idx = j
    · subst hij; simp [hlt] at hj; subst hj; rw [hw] at hw'; cases hw'
    · simp [hij] at hj; exact h.w_q j sl' hj hw'
  · intro j
    show j ∈ free ↔ _
    rw [h.f_iff j, get_set]
    by_cases hj : t.idx = j
    · subst hj; simp only [hs]; simp [hlt, hl]
    · simp [hj]
  · intro j sl' hj
    simp only [get_set] at hj
    by_cases hij : t.idx = j
    · subst hij; simp [hlt] at hj; subst hj; rw [hg]; exact h.gen_lt _ sl hs
    · simp [hij] at hj; exact h.gen_lt j sl' hj

theorem batonGo_inv (free : List Nat) : ∀ (q : List Ticket) (slots : List Slot), Inv ⟨slots, free, q⟩ →
    Inv ⟨(batonGo slots q).2.1, free, (batonGo slots q).2.2⟩
  | [], slots, h => by simp only [batonGo]; exact h
  | t :: rest, slots, h => by
    unfold batonGo
    cases hst : slotAt slots t with
    | none =>
      simp only
      exact batonGo_inv free rest slots (skip_inv slots free t rest h hst)
    | some sl =>
      simp only
      cases hw : sl.waker with
      | some w =>
        simp only
        exact pop_inv slots free t rest sl _ h hst rfl rfl rfl rfl
      | none =>
        simp only
        exact batonGo_inv free rest _ (pop_inv slots free t rest sl _ h hst rfl rfl rfl rfl)

theorem baton_inv (s : S) (h : Inv s) : Inv (baton s).2 := by
  have := batonGo_inv s.free s.queue s.slots h
  unfold baton
  cases hb : batonGo s.slots s.queue with
  | mk w r =>
    cases r with
    | mk sl q =>
      rw [hb] at this
      exact this

theorem run_inv (o : Op) (s : S) (h : Inv s) : Inv (o.run s) := by
  cases o with
  | alloc => exact alloc_inv s h
  | arm t w => exact arm_inv t w s h
  | notify t => exact notify_inv t s h
  | baton => exact baton_inv s h
  | notifyAll => exact notifyAll_inv s h
  | release t => exact release_inv t s h

theorem exec_inv : ∀ (os : List Op) (s : S), Inv s → Inv (exec os s)
  | [], _, h => h
  | o :: os, s, h => exec_inv os (o.run s) (run_inv o s h)

/-! ## Stale tickets -/

theorem arm_stale (t : Ticket) (w : Nat) (s : S) (h : slotOf s t = none) : arm t w s = s := by
  unfold arm; rw [h]

theorem notify_stale (t : Ticket) (s : S) (h : slotOf s t = none) : notify t s = ([], s) := by
  unfold notify; rw [h]

theorem release_stale (t : Ticket) (s : S) (h : slotOf s t = none) : release t s = s := by
  unfold release; rw [h]

/-- A ticket is dead once released. -/
theorem release_dead (t : Ticket) (s : S) : slotOf (release t s) t = none := by
  cases hs : slotOf s t with
  | none => rw [release_stale t s hs]; exact hs
  | some sl =>
    obtain ⟨hsl, _, _⟩ := slotOf_some.mp hs
    have hlt := lt_of_get hsl
    unfold release
    rw [hs]
    cases h2 : slotOf _ t with
    | none => rfl
    | some sl' =>
      obtain ⟨h3, h4, _⟩ := slotOf_some.mp h2
      simp only [get_set, hlt, and_self, ↓reduceIte, Option.some.injEq] at h3
      subst h3; simp at h4

/-! ## alloc -/

/-- `alloc` hands out a ticket that was not live, and is now. -/
theorem alloc_fresh (s : S) (h : Inv s) : slotOf s (alloc s).1 = none := by
  unfold alloc
  cases hf : s.free with
  | nil =>
    simp only
    cases hs : slotOf s ⟨s.slots.length, 0⟩ with
    | none => rfl
    | some sl => obtain ⟨h1, _, _⟩ := slotOf_some.mp hs; simp at h1
  | cons i rest =>
    obtain ⟨sl0, hsl0, hdead⟩ := (h.f_iff i).mp (by rw [hf]; exact List.mem_cons_self)
    simp only [hsl0]
    cases hs : slotOf s ⟨i, sl0.gen⟩ with
    | none => rfl
    | some sl =>
      obtain ⟨h1, h2, _⟩ := slotOf_some.mp hs
      simp only at h1; rw [hsl0] at h1; cases h1; rw [hdead] at h2; cases h2

/-- What `alloc` does, for an invariant slab. -/
theorem alloc_cases (s : S) (h : Inv s) :
    (∃ i rest sl0, s.free = i :: rest ∧ s.slots[i]? = some sl0 ∧ sl0.live = false ∧
      (alloc s).1 = ⟨i, sl0.gen⟩ ∧
      (alloc s).2 = { s with free := rest, slots := s.slots.set i { sl0 with live := true } }) ∨
    (s.free = [] ∧ (alloc s).1 = ⟨s.slots.length, 0⟩ ∧ (alloc s).2 = { s with slots := s.slots ++ [newSlot] }) := by
  unfold alloc
  cases hf : s.free with
  | nil => right; exact ⟨rfl, rfl, rfl⟩
  | cons i rest =>
    left
    obtain ⟨sl0, hsl0, hdead⟩ := (h.f_iff i).mp (by rw [hf]; exact List.mem_cons_self)
    refine ⟨i, rest, sl0, rfl, hsl0, hdead, ?_, ?_⟩ <;> simp only [hsl0]

theorem alloc_valid (s : S) (h : Inv s) : ((slotOf (alloc s).2 (alloc s).1).isSome) = true := by
  rcases alloc_cases s h with ⟨i, rest, sl0, _, hsl0, _, h1, h2⟩ | ⟨_, h1, h2⟩
  · rw [h1, h2]
    show (slotAt (s.slots.set i { sl0 with live := true }) ⟨i, sl0.gen⟩).isSome = true
    rw [slotAt_set_same s.slots i _ _ rfl (lt_of_get hsl0)]
    simp
  · rw [h1, h2]
    show (slotAt (s.slots ++ [newSlot]) ⟨s.slots.length, 0⟩).isSome = true
    simp [slotAt, newSlot]

/-- `alloc` takes the slot on top of the free stack and keeps the slab's length; it pushes a new slot only when no
slot is free, that is when every slot is live. -/
theorem alloc_grow (s : S) (h : Inv s) :
    (∃ i rest, s.free = i :: rest ∧ (alloc s).1.idx = i ∧ (alloc s).2.free = rest ∧
      (alloc s).2.slots.length = s.slots.length) ∨
    (s.free = [] ∧ (alloc s).1 = ⟨s.slots.length, 0⟩ ∧ (alloc s).2.slots.length = s.slots.length + 1 ∧
      ∀ (i : Nat) (sl : Slot), s.slots[i]? = some sl → sl.live = true) := by
  unfold alloc
  cases hf : s.free with
  | nil =>
    right
    refine ⟨rfl, rfl, by simp, ?_⟩
    intro i sl hi
    cases hl : sl.live with
    | true => rfl
    | false => have := (h.f_iff i).mpr ⟨sl, hi, hl⟩; rw [hf] at this; cases this
  | cons i rest =>
    left
    obtain ⟨sl0, hsl0, _⟩ := (h.f_iff i).mp (by rw [hf]; exact List.mem_cons_self)
    simp only [hsl0]
    exact ⟨i, rest, rfl, rfl, rfl, by simp⟩

/-! ## notify and notify_all -/

/-- `notify` wakes the ticket's waker if the ticket is live and armed, and nothing else; the waker is taken. -/
theorem notify_spec (t : Ticket) (s : S) :
    (notify t s).1 = (match slotOf s t with | some sl => sl.waker.toList | none => []) ∧
    ∀ sl : Slot, slotOf s t = some sl → ∀ sl' : Slot, (notify t s).2.slots[t.idx]? = some sl' → sl'.waker = none := by
  unfold notify
  cases hs : slotOf s t with
  | none => simp
  | some sl =>
    obtain ⟨hsl, _, _⟩ := slotOf_some.mp hs
    cases hw : sl.waker with
    | none =>
      refine ⟨by simp [hw], ?_⟩
      intro sl1 h1 sl' h2
      cases h1; simp only [hw] at h2; rw [hsl] at h2; cases h2; exact hw
    | some w =>
      refine ⟨by simp [hw], ?_⟩
      intro sl1 h1 sl' h2
      cases h1; simp only [hw, get_set, lt_of_get hsl, and_self, ↓reduceIte, Option.some.injEq] at h2
      subst h2; rfl

/-- `notifyAll` wakes the waker of every live slot, in slot order, and leaves no live slot armed. -/
theorem notifyAll_spec (s : S) :
    (notifyAll s).1 = s.slots.filterMap armedW ∧
    ∀ (i : Nat) (sl : Slot), (notifyAll s).2.slots[i]? = some sl → sl.live = true → sl.waker = none := by
  refine ⟨rfl, ?_⟩
  intro i sl h hl
  simp only [notifyAll, List.getElem?_map] at h
  cases h0 : s.slots[i]? with
  | none => simp [h0] at h
  | some sl0 =>
    simp only [h0, Option.map_some, Option.some.injEq] at h
    by_cases hl0 : sl0.live = true
    · simp [hl0] at h; subst h; rfl
    · simp [hl0] at h; subst h; exact absurd hl hl0

/-! ## What a waking call changes -/

/-- From the slots `a` to `b`, each slot keeps its liveness and generation, and keeps its waker or gives it up to
`ws`. -/
def Shape (a b : List Slot) (ws : List Nat) : Prop :=
  a.length = b.length ∧ ∀ (j : Nat) (sl : Slot), a[j]? = some sl → ∃ sl' : Slot, b[j]? = some sl' ∧
    sl'.live = sl.live ∧ sl'.gen = sl.gen ∧ (sl'.waker = sl.waker ∨ (sl'.waker = none ∧ ∀ w, sl.waker = some w → w ∈ ws))

theorem shape_set (a : List Slot) (j : Nat) (sl v : Slot) (ws : List Nat) (hsl : a[j]? = some sl)
    (hl : v.live = sl.live) (hg : v.gen = sl.gen)
    (hw : v.waker = sl.waker ∨ (v.waker = none ∧ ∀ w, sl.waker = some w → w ∈ ws)) :
    Shape a (a.set j v) ws := by
  have hlt := lt_of_get hsl
  refine ⟨by simp, ?_⟩
  intro k sk hk
  rw [get_set]
  by_cases hjk : j = k
  · subst hjk; rw [hsl] at hk; cases hk; exact ⟨v, by simp [hlt], hl, hg, hw⟩
  · simp only [hjk, false_and, ↓reduceIte]; exact ⟨sk, hk, rfl, rfl, Or.inl rfl⟩

theorem shape_trans (a b c : List Slot) (ws1 ws2 : List Nat) (h1 : Shape a b ws1) (h2 : Shape b c ws2) :
    Shape a c (ws1 ++ ws2) := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  intro j sl hj
  obtain ⟨sl1, hb, l1, g1, w1⟩ := h1.2 j sl hj
  obtain ⟨sl2, hc, l2, g2, w2⟩ := h2.2 j sl1 hb
  refine ⟨sl2, hc, l2.trans l1, g2.trans g1, ?_⟩
  rcases w1 with w1 | ⟨w1, w1'⟩ <;> rcases w2 with w2 | ⟨w2, w2'⟩
  · exact Or.inl (w2.trans w1)
  · right; refine ⟨w2, fun w hw => ?_⟩; rw [← w1] at hw; exact List.mem_append_right _ (w2' w hw)
  · right; exact ⟨w2.trans w1, fun w hw => List.mem_append_left _ (w1' w hw)⟩
  · right; exact ⟨w2, fun w hw => List.mem_append_left _ (w1' w hw)⟩

theorem shape_refl (a : List Slot) (ws : List Nat) : Shape a a ws :=
  ⟨rfl, fun _ sl h => ⟨sl, h, rfl, rfl, Or.inl rfl⟩⟩

theorem batonGo_shape : ∀ (q : List Ticket) (slots : List Slot),
    Shape slots (batonGo slots q).2.1 (batonGo slots q).1
  | [], slots => by simp only [batonGo]; exact shape_refl _ _
  | t :: rest, slots => by
    unfold batonGo
    cases hst : slotAt slots t with
    | none => simp only; exact batonGo_shape rest slots
    | some sl =>
      simp only
      have hsl := (slotAt_some.mp hst).1
      cases hw : sl.waker with
      | some w =>
        simp only
        exact shape_set slots t.idx sl _ [w] hsl rfl rfl
          (Or.inr ⟨rfl, fun w' h => by rw [hw] at h; cases h; exact List.mem_singleton_self _⟩)
      | none =>
        simp only
        have step := shape_trans _ _ _ [] _
          (shape_set slots t.idx sl { sl with waker := none, queued := false } [] hsl rfl rfl (Or.inl hw.symm))
          (batonGo_shape rest (slots.set t.idx { sl with waker := none, queued := false }))
        simp only [List.nil_append] at step
        exact step

theorem baton_shape (s : S) : Shape s.slots (baton s).2.slots (baton s).1 ∧ (baton s).2.free = s.free := by
  have := batonGo_shape s.queue s.slots
  unfold baton
  cases hb : batonGo s.slots s.queue with
  | mk w r =>
    cases r with
    | mk sl q =>
      rw [hb] at this
      exact ⟨this, rfl⟩

theorem notify_shape (t : Ticket) (s : S) :
    Shape s.slots (notify t s).2.slots (notify t s).1 ∧ (notify t s).2.free = s.free ∧
    (notify t s).2.queue = s.queue := by
  unfold notify
  cases hs : slotOf s t with
  | none => exact ⟨shape_refl _ _, by simp, by simp⟩
  | some sl =>
    obtain ⟨hsl, _, _⟩ := slotOf_some.mp hs
    cases hw : sl.waker with
    | none => simp only [hw]; exact ⟨shape_refl _ _, by simp, by simp⟩
    | some w =>
      simp only [hw]
      exact ⟨shape_set _ _ sl _ _ hsl rfl rfl
        (Or.inr ⟨rfl, fun w' h => by rw [hw] at h; cases h; exact List.mem_singleton_self _⟩), by simp, by simp⟩

theorem notifyAll_shape (s : S) :
    Shape s.slots (notifyAll s).2.slots (notifyAll s).1 ∧ (notifyAll s).2.free = s.free ∧
    (notifyAll s).2.queue = s.queue := by
  refine ⟨⟨by simp [notifyAll], ?_⟩, rfl, rfl⟩
  intro j sl hj
  simp only [notifyAll, List.getElem?_map, hj, Option.map_some, Option.some.injEq, exists_eq_left']
  by_cases hl : sl.live = true
  · simp only [hl, ↓reduceIte, true_and]
    right
    intro w hw
    rw [List.mem_filterMap]
    exact ⟨sl, List.mem_of_getElem? hj, by simp [armedW, hl, hw]⟩
  · simp [hl]

/-! ## The slab is as long as the most tickets held at once -/

theorem liveCount_le (s : S) : liveCount s ≤ s.slots.length := List.length_filter_le _ _

/-- Every call keeps the slab's length, except an `alloc` with no free slot, after which every slot is live. -/
theorem run_len (o : Op) (s : S) (h : Inv s) :
    (o.run s).slots.length = s.slots.length ∨
    ((o.run s).slots.length = s.slots.length + 1 ∧ liveCount (o.run s) = s.slots.length + 1) := by
  cases o with
  | alloc =>
    rcases alloc_grow s h with ⟨_, _, _, _, _, hl⟩ | ⟨hf, _, hl, hall⟩
    · left; exact hl
    · right
      refine ⟨hl, ?_⟩
      simp only [Op.run, alloc, hf, liveCount]
      rw [List.filter_eq_self.mpr]
      · simp
      · intro a ha
        rw [List.mem_append] at ha
        rcases ha with ha | ha
        · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
          exact hall i a hi
        · rw [List.mem_singleton] at ha; subst ha; rfl
  | arm t w =>
    left
    simp only [Op.run, arm]
    split
    · rfl
    · split <;> simp
  | notify t => left; exact (notify_shape t s).1.1.symm
  | baton => left; exact (baton_shape s).1.1.symm
  | notifyAll => left; exact (notifyAll_shape s).1.1.symm
  | release t =>
    left
    simp only [Op.run, release]
    split <;> simp

/-- A run that keeps, beside the slab, the most tickets held at once after any call. -/
def execH : List Op → S → Nat → S × Nat
  | [], s, hw => (s, hw)
  | o :: os, s, hw => execH os (o.run s) (max hw (liveCount (o.run s)))

theorem execH_hw : ∀ (os : List Op) (s : S) (hw : Nat), Inv s → s.slots.length = hw →
    (execH os s hw).1.slots.length = (execH os s hw).2
  | [], _, _, _, h => h
  | o :: os, s, hw, hi, h => by
    apply execH_hw os _ _ (run_inv o s hi)
    have hc := liveCount_le (o.run s)
    rcases run_len o s hi with hl | ⟨hl, hc'⟩
    · rw [hl] at hc ⊢; omega
    · rw [hl, hc']; omega

/-- From the empty slab, over any run, the slab is as long as the most tickets held at once. -/
theorem exec_hw (os : List Op) : (execH os {} 0).1.slots.length = (execH os {} 0).2 :=
  execH_hw os {} 0 init_inv rfl

/-! ## Generations -/

/-- Whether a call is a release that acts on the slot `i`. -/
def acts (i : Nat) : Op → S → Nat
  | .release t, s => if t.idx = i ∧ (slotOf s t).isSome = true then 1 else 0
  | _, _ => 0

/-- How many releases of a run act on the slot `i`. -/
def rels (i : Nat) : List Op → S → Nat
  | [], _ => 0
  | o :: os, s => acts i o s + rels i os (o.run s)

/-- A slot's generation moves on by one, modulo `2^32`, at each release that acts on it, and at no other call. -/
theorem gen_op (o : Op) (s : S) (h : Inv s) (i : Nat) (sl : Slot) (hsl : s.slots[i]? = some sl) :
    ∃ sl', (o.run s).slots[i]? = some sl' ∧ sl'.gen = (sl.gen + acts i o s) % GENS := by
  have hmod : sl.gen % GENS = sl.gen := Nat.mod_eq_of_lt (h.gen_lt i sl hsl)
  have hlt := lt_of_get hsl
  have viaShape : ∀ b ws, Shape s.slots b ws → ∃ sl', b[i]? = some sl' ∧ sl'.gen = sl.gen := by
    intro b ws hb
    obtain ⟨sl', h1, _, h2, _⟩ := hb.2 i sl hsl
    exact ⟨sl', h1, h2⟩
  cases o with
  | alloc =>
    simp only [acts, Nat.add_zero, hmod, Op.run]
    unfold alloc
    cases hf : s.free with
    | nil =>
      simp only
      exact ⟨sl, by rw [get_push]; simp [Nat.ne_of_lt hlt, hsl], rfl⟩
    | cons j rest =>
      obtain ⟨sl0, hsl0, _⟩ := (h.f_iff j).mp (by rw [hf]; exact List.mem_cons_self)
      simp only [hsl0]
      by_cases hji : j = i
      · subst hji; rw [hsl] at hsl0; cases hsl0; exact ⟨{ sl with live := true }, by simp [hlt], rfl⟩
      · exact ⟨sl, by simp [hji, hsl], rfl⟩
  | arm t w =>
    simp only [acts, Nat.add_zero, hmod, Op.run]
    unfold arm
    cases hs : slotOf s t with
    | none => exact ⟨sl, hsl, rfl⟩
    | some sl1 =>
      obtain ⟨hsl1, _, _⟩ := slotOf_some.mp hs
      simp only
      by_cases hti : t.idx = i
      · subst hti; rw [hsl] at hsl1; cases hsl1
        split
        · exact ⟨{ sl with waker := some w }, by simp [hlt], rfl⟩
        · exact ⟨{ sl with waker := some w, queued := true }, by simp [hlt], rfl⟩
      · split <;> exact ⟨sl, by simp [hti, hsl], rfl⟩
  | notify t =>
    simp only [acts, Nat.add_zero, hmod, Op.run]
    exact viaShape _ _ (notify_shape t s).1
  | baton =>
    simp only [acts, Nat.add_zero, hmod, Op.run]
    exact viaShape _ _ (baton_shape s).1
  | notifyAll =>
    simp only [acts, Nat.add_zero, hmod, Op.run]
    exact viaShape _ _ (notifyAll_shape s).1
  | release t =>
    simp only [Op.run, acts]
    unfold release
    cases hs : slotOf s t with
    | none => exact ⟨sl, hsl, by simp [hmod]⟩
    | some sl1 =>
      obtain ⟨hsl1, _, _⟩ := slotOf_some.mp hs
      simp only
      by_cases hti : t.idx = i
      · subst hti; rw [hsl] at hsl1; cases hsl1
        exact ⟨{ sl with live := false, gen := (sl.gen + 1) % GENS, waker := none, queued := false },
          by simp [hlt], by simp⟩
      · exact ⟨sl, by simp [hti, hsl], by simp [hti, hmod]⟩

theorem gen_exec : ∀ (os : List Op) (s : S), Inv s → ∀ (i : Nat) (sl : Slot), s.slots[i]? = some sl →
    ∃ sl', (exec os s).slots[i]? = some sl' ∧ sl'.gen = (sl.gen + rels i os s) % GENS
  | [], s, h, i, sl, hsl => ⟨sl, hsl, by simp [rels, Nat.mod_eq_of_lt (h.gen_lt i sl hsl)]⟩
  | o :: os, s, h, i, sl, hsl => by
    obtain ⟨sl1, h1, g1⟩ := gen_op o s h i sl hsl
    obtain ⟨sl2, h2, g2⟩ := gen_exec os (o.run s) (run_inv o s h) i sl1 h1
    refine ⟨sl2, h2, ?_⟩
    rw [g2, g1]
    simp only [rels, GENS]
    omega

/-- A released ticket names a live slot again only after its slot was released a multiple of `2^32` times in all,
counting its own release: until then every `arm`, `notify` and `release` with it does nothing. -/
theorem dead_stays (s0 : S) (h : Inv s0) (t : Ticket) (sl : Slot) (hs : slotOf s0 t = some sl) (os : List Op)
    (hv : (slotOf (exec os (release t s0)) t).isSome = true) :
    (rels t.idx os (release t s0) + 1) % GENS = 0 := by
  obtain ⟨hsl, _, hg⟩ := slotOf_some.mp hs
  have hlt := lt_of_get hsl
  have hrel : (release t s0).slots[t.idx]? =
      some { sl with live := false, gen := (sl.gen + 1) % GENS, waker := none, queued := false } := by
    unfold release; rw [hs]; simp [hlt]
  obtain ⟨sl2, h2, g2⟩ := gen_exec os _ (release_inv t s0 h) t.idx _ hrel
  have hglt := h.gen_lt _ sl hsl
  cases hv2 : slotOf (exec os (release t s0)) t with
  | none => rw [hv2] at hv; cases hv
  | some sl3 =>
    obtain ⟨h3, _, g3⟩ := slotOf_some.mp hv2
    rw [h2] at h3; cases h3
    rw [g3, ← hg] at g2
    simp only [GENS] at g2 hglt ⊢
    omega

#audit_axioms Vinc.FacadeStandby.init_inv
#audit_axioms Vinc.FacadeStandby.exec_inv
#audit_axioms Vinc.FacadeStandby.exec_hw
#audit_axioms Vinc.FacadeStandby.arm_stale
#audit_axioms Vinc.FacadeStandby.notify_stale
#audit_axioms Vinc.FacadeStandby.release_stale
#audit_axioms Vinc.FacadeStandby.release_dead
#audit_axioms Vinc.FacadeStandby.dead_stays
#audit_axioms Vinc.FacadeStandby.alloc_fresh
#audit_axioms Vinc.FacadeStandby.alloc_valid
#audit_axioms Vinc.FacadeStandby.alloc_grow
#audit_axioms Vinc.FacadeStandby.notify_spec
#audit_axioms Vinc.FacadeStandby.notifyAll_spec

end Vinc.FacadeStandby
