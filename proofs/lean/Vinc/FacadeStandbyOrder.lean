import Vinc.Axioms
import Vinc.FacadeStandbyThm

/-!
# The facade's standby slab: the exact queue and the baton's order

What the model proves about the queue of `Standby` and its baton, for any number of slots and any run of calls:

- the baton, as the code has it: the waker of the first entry of the queue whose ticket is live and armed is woken,
  and every entry up to it leaves the queue; with none, nothing is woken and the queue empties (`baton_first`);
  whenever a slot is armed, exactly one waker is woken (`baton_one`);
- while no `alloc` hands out a ticket that a stale entry of the queue still names (`NoRevive`: that entry's ticket
  was released, so by `dead_stays` its slot was released a multiple of `2^32` times since): the slot of every live
  entry is queued, no ticket has two live entries, and the queue holds at most twice as many entries as the slab has
  slots (`QInv`, `init_qinv`, `run_qinv`, `exec_qinv`), so its live entries are at most the slab (`live_le`); and the
  live entries of the queue are the documented order, the tickets waiting for the role in the order they were queued,
  so a ticket that reuses a released slot queues behind those already waiting (`run_order`, `exec_order`);
- what the baton wakes and the live entries it leaves are what the documented order says of the live entries it
  found (`baton_order`), so it wakes the oldest armed ticket of the documented order (`baton_oldest`; from the empty
  slab over any run that revives no stale entry, `exec_oldest`; on the run of issue #311, `oldest_ok`);
- the rule before the fix of #311 (release left the slot queued and its entry in the queue, and the baton took an
  entry by its slot), under which a ticket that reused a queued slot kept that place, fails the documented order
  (`oldest_bad`).
-/

namespace Vinc.FacadeStandby

/-! ## The baton's order -/

/-- The ticket is live and armed. -/
def Hit (slots : List Slot) (t : Ticket) : Prop := (wakerAt slots t).isSome = true

theorem batonGo_first : ∀ (q : List Ticket) (slots : List Slot),
    ((batonGo slots q).1 = [] ∧ (batonGo slots q).2.2 = [] ∧ ∀ t ∈ q, ¬Hit slots t) ∨
    (∃ pre t rest sl w, q = pre ++ t :: rest ∧ (∀ u ∈ pre, ¬Hit slots u) ∧ slotAt slots t = some sl ∧
      sl.waker = some w ∧ (batonGo slots q).1 = [w] ∧ (batonGo slots q).2.2 = rest)
  | [], slots => by left; simp [batonGo]
  | t :: rest, slots => by
    unfold batonGo
    cases hst : slotAt slots t with
    | none =>
      simp only
      have hi : ¬Hit slots t := by simp [Hit, wakerAt, hst]
      rcases batonGo_first rest slots with ⟨h1, h2, h3⟩ | ⟨pre, k, r, sl, w, h1, h2, h3, h4, h5, h6⟩
      · left
        refine ⟨h1, h2, ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hi
        · exact h3 u hu
      · right
        refine ⟨t :: pre, k, r, sl, w, by rw [h1]; rfl, ?_, h3, h4, h5, h6⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hi
        · exact h2 u hu
    | some sl =>
      simp only
      have hs := (slotAt_some.mp hst).1
      cases hw : sl.waker with
      | some w =>
        simp only
        right
        exact ⟨[], t, rest, sl, w, rfl, by simp, hst, hw, rfl, rfl⟩
      | none =>
        simp only
        have hi : ¬Hit slots t := by simp [Hit, wakerAt, hst, hw]
        have same : ∀ u, Hit (slots.set t.idx { sl with waker := none, queued := false }) u ↔ Hit slots u := by
          intro u
          unfold Hit
          rw [wakerAt_set slots t.idx sl { sl with waker := none, queued := false } hs rfl rfl hw.symm u]
        rcases batonGo_first rest (slots.set t.idx { sl with waker := none, queued := false }) with
          ⟨h1, h2, h3⟩ | ⟨pre, k, r, sl', w, h1, h2, h3, h4, h5, h6⟩
        · left
          refine ⟨h1, h2, ?_⟩
          intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hi
          · exact fun hh => h3 u hu ((same u).mpr hh)
        · right
          have hk : k.idx ≠ t.idx := by
            intro e
            have := slotAt_set_eq e h3
            subst this
            have h4' : (none : Option Nat) = some w := h4
            cases h4'
          rw [slotAt_set_ne _ _ _ _ hk] at h3
          refine ⟨t :: pre, k, r, sl', w, by rw [h1]; rfl, ?_, h3, h4, h5, h6⟩
          intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hi
          · exact fun hh => h2 u hu ((same u).mpr hh)

/-- The baton, as the code has it: the waker of the first entry of the queue whose ticket is live and armed is woken,
and every entry up to it leaves the queue; with none, nothing is woken and the queue empties. -/
theorem baton_first (s : S) :
    ((baton s).1 = [] ∧ (baton s).2.queue = [] ∧ ∀ t ∈ s.queue, ¬Hit s.slots t) ∨
    (∃ pre t rest sl w, s.queue = pre ++ t :: rest ∧ (∀ u ∈ pre, ¬Hit s.slots u) ∧ slotAt s.slots t = some sl ∧
      sl.waker = some w ∧ (baton s).1 = [w] ∧ (baton s).2.queue = rest) := by
  have := batonGo_first s.queue s.slots
  unfold baton
  cases hb : batonGo s.slots s.queue with
  | mk w r =>
    cases r with
    | mk sl q =>
      rw [hb] at this
      exact this

/-- Whenever a slot is armed, the baton wakes exactly one waker. -/
theorem baton_one (s : S) (h : Inv s) (i : Nat) (sl : Slot) (hsl : s.slots[i]? = some sl)
    (hw : sl.waker.isSome = true) : ∃ w, (baton s).1 = [w] := by
  rcases baton_first s with ⟨_, _, h3⟩ | ⟨_, _, _, _, w, _, _, _, _, h6, _⟩
  · exfalso
    obtain ⟨hl, hq⟩ := h.w_q i sl hsl hw
    obtain ⟨_, hm⟩ := h.q_live i sl hsl hq
    apply h3 _ hm
    have : slotAt s.slots ⟨i, sl.gen⟩ = some sl := slotAt_some.mpr ⟨hsl, hl, rfl⟩
    simp [Hit, wakerAt, this, hw]
  · exact ⟨w, h6⟩

/-! ## The queue is exact while no stale entry is revived -/

theorem len_filter_split {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter fun x => !p x).length = l.length
  | [] => rfl
  | a :: t => by
    have := len_filter_split p t
    cases hp : p a <;> simp [hp] <;> omega

theorem nodup_const_le {l : List Nat} {n : Nat} (hn : l.Nodup) (h : ∀ x ∈ l, x = n) : l.length ≤ 1 := by
  match l, hn, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: t, hn, h =>
    exfalso
    have ha := h a List.mem_cons_self
    have hb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
    exact (List.nodup_cons.mp hn).1 (by rw [ha, ← hb]; exact List.mem_cons_self)

theorem nodup_bound : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n
  | 0, l, _, h => by
    cases l with
    | nil => simp
    | cons a t => exact absurd (h a List.mem_cons_self) (Nat.not_lt_zero _)
  | n + 1, l, hn, h => by
    have hsplit := len_filter_split (fun x => x != n) l
    have h1 : (l.filter fun x => x != n).length ≤ n := by
      apply nodup_bound n
      · exact hn.sublist List.filter_sublist
      · intro x hx
        rw [List.mem_filter] at hx
        have := h x hx.1
        have : x ≠ n := by simpa using hx.2
        omega
    have h2 : (l.filter fun x => !(x != n)).length ≤ 1 := by
      apply nodup_const_le (n := n) (hn.sublist List.filter_sublist)
      intro x hx
      rw [List.mem_filter] at hx
      simpa using hx.2
    omega

theorem nodup_map_idx : ∀ (l : List Ticket), l.Nodup → (∀ x ∈ l, ∀ y ∈ l, x.idx = y.idx → x = y) →
    (l.map (·.idx)).Nodup
  | [], _, _ => List.nodup_nil
  | a :: t, hn, hi => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_idx t (List.nodup_cons.mp hn).2
      (fun x hx y hy => hi x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    intro hm
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp hm
    have e := hi a List.mem_cons_self b (List.mem_cons_of_mem _ hb) hab.symm
    exact (List.nodup_cons.mp hn).1 (by rw [e]; exact hb)

/-- The queue is exact: the slot of every live entry is queued, no ticket has two live entries, and the queue holds
at most twice as many entries as the slab has slots. -/
structure QInv (s : S) : Prop where
  lq_q : ∀ t ∈ s.queue, ∀ sl : Slot, slotOf s t = some sl → sl.queued = true
  lq_nodup : (s.queue.filter (valid s.slots)).Nodup
  q_len : s.queue.length ≤ 2 * s.slots.length

theorem init_qinv : QInv ({} : S) := ⟨by simp, List.nodup_nil, by simp⟩

/-- The live entries of an exact queue are at most the slab. -/
theorem live_le (s : S) (hq : QInv s) : (s.queue.filter (valid s.slots)).length ≤ s.slots.length := by
  have hn : ((s.queue.filter (valid s.slots)).map (·.idx)).Nodup := by
    apply nodup_map_idx _ hq.lq_nodup
    intro x hx y hy hxy
    exact valid_idx (List.mem_filter.mp hx).2 (List.mem_filter.mp hy).2 hxy
  have hb := nodup_bound s.slots.length _ hn (by
    intro i hi
    obtain ⟨x, hx, hxi⟩ := List.mem_map.mp hi
    obtain ⟨sx, hsx⟩ := valid_iff.mp (List.mem_filter.mp hx).2
    rw [← hxi]
    exact lt_of_get (slotAt_some.mp hsx).1)
  rw [List.length_map] at hb
  exact hb

/-- An entry of the queue that is not the ticket `alloc` hands out names after it what it named before. -/
theorem alloc_slotAt (s : S) (h : Inv s) (u : Ticket) (hu : u ∈ s.queue) (hne : u ≠ (alloc s).1) :
    slotAt (alloc s).2.slots u = slotAt s.slots u := by
  have hlt := h.q_idx u hu
  rcases alloc_cases s h with ⟨i, rest, sl0, _, hsl0, hdead, h1, h2⟩ | ⟨_, _, h2⟩
  · rw [h2]
    rw [h1] at hne
    show slotAt (s.slots.set i { sl0 with live := true }) u = slotAt s.slots u
    by_cases hui : u.idx = i
    · have hg : u.gen ≠ sl0.gen := fun e => hne (ticket_eq hui e)
      rw [slotAt_set_same s.slots i _ u hui (lt_of_get hsl0), slotAt_get s.slots i sl0 u hui hsl0]
      simp [hdead, Ne.symm hg]
    · exact slotAt_set_ne s.slots i _ u hui
  · rw [h2]
    show slotAt (s.slots ++ [newSlot]) u = slotAt s.slots u
    unfold slotAt
    rw [get_push]
    simp [Nat.ne_of_lt hlt]

/-- An `alloc` that revives no stale entry leaves the live entries of the queue as they were. -/
theorem alloc_live (s : S) (h : Inv s) (hn : (alloc s).1 ∉ s.queue) :
    (alloc s).2.queue.filter (valid (alloc s).2.slots) = s.queue.filter (valid s.slots) := by
  have hq' : (alloc s).2.queue = s.queue := by
    rcases alloc_cases s h with ⟨_, _, _, _, _, _, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2]
  rw [hq']
  apply List.filter_congr
  intro u hu
  unfold valid
  rw [alloc_slotAt s h u hu (fun e => hn (e ▸ hu))]

theorem alloc_qinv (s : S) (h : Inv s) (hq : QInv s) (hn : (alloc s).1 ∉ s.queue) : QInv (alloc s).2 := by
  have same : ∀ u ∈ s.queue, slotAt (alloc s).2.slots u = slotAt s.slots u :=
    fun u hu => alloc_slotAt s h u hu (fun e => hn (e ▸ hu))
  have hq' : (alloc s).2.queue = s.queue := by
    rcases alloc_cases s h with ⟨_, _, _, _, _, _, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2]
  have hlen : s.slots.length ≤ (alloc s).2.slots.length := by
    rcases alloc_cases s h with ⟨_, _, _, _, _, _, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] <;> simp
  refine ⟨?_, ?_, ?_⟩
  · intro u hu sl hs
    rw [hq'] at hu
    have hs' : slotAt (alloc s).2.slots u = some sl := hs
    rw [same u hu] at hs'
    exact hq.lq_q u hu sl hs'
  · rw [alloc_live s h hn]; exact hq.lq_nodup
  · rw [hq']; have := hq.q_len; omega

/-- The slots `b` keep, slot for slot, the liveness and generation of `a`. -/
def LG (a b : List Slot) : Prop :=
  a.length = b.length ∧ ∀ (j : Nat) (sl : Slot), a[j]? = some sl →
    ∃ sl' : Slot, b[j]? = some sl' ∧ sl'.live = sl.live ∧ sl'.gen = sl.gen

theorem lg_back {a b : List Slot} (hk : LG a b) {j : Nat} {sl' : Slot} (hb : b[j]? = some sl') :
    ∃ sl, a[j]? = some sl ∧ sl'.live = sl.live ∧ sl'.gen = sl.gen := by
  have hlt : j < a.length := by rw [hk.1]; exact lt_of_get hb
  obtain ⟨sl, ha⟩ : ∃ sl, a[j]? = some sl := ⟨a[j], by simp [hlt]⟩
  obtain ⟨sl'', h1, h2⟩ := hk.2 j sl ha
  rw [hb] at h1; cases h1
  exact ⟨sl, ha, h2⟩

theorem valid_lg {a b : List Slot} (hk : LG a b) (u : Ticket) : valid b u = valid a u := by
  cases hb : valid b u with
  | true =>
    obtain ⟨sl', hs'⟩ := valid_iff.mp hb
    obtain ⟨h1, h2, h3⟩ := slotAt_some.mp hs'
    obtain ⟨sl, ha, l1, g1⟩ := lg_back hk h1
    exact (valid_iff.mpr ⟨sl, slotAt_some.mpr ⟨ha, l1.symm.trans h2, g1.symm.trans h3⟩⟩).symm
  | false =>
    cases ha : valid a u with
    | false => rfl
    | true =>
      obtain ⟨sl, hs⟩ := valid_iff.mp ha
      obtain ⟨h1, h2, h3⟩ := slotAt_some.mp hs
      obtain ⟨sl', hb', l1, g1⟩ := hk.2 _ sl h1
      have : valid b u = true := valid_iff.mpr ⟨sl', slotAt_some.mpr ⟨hb', l1.trans h2, g1.trans h3⟩⟩
      rw [hb] at this; cases this

theorem shape_lg {a b : List Slot} {ws : List Nat} (h : Shape a b ws) : LG a b :=
  ⟨h.1, fun j sl hj => by obtain ⟨sl', h1, h2, h3, _⟩ := h.2 j sl hj; exact ⟨sl', h1, h2, h3⟩⟩

/-- The slots `b` keep, slot for slot, the liveness, generation and queued mark of `a`. -/
def Keeps (a b : List Slot) : Prop :=
  a.length = b.length ∧ ∀ (j : Nat) (sl : Slot), a[j]? = some sl →
    ∃ sl' : Slot, b[j]? = some sl' ∧ sl'.live = sl.live ∧ sl'.gen = sl.gen ∧ sl'.queued = sl.queued

theorem keeps_lg {a b : List Slot} (hk : Keeps a b) : LG a b :=
  ⟨hk.1, fun j sl h => by obtain ⟨sl', h1, h2, h3, _⟩ := hk.2 j sl h; exact ⟨sl', h1, h2, h3⟩⟩

theorem keeps_set (a : List Slot) (i : Nat) (sl v : Slot) (hsl : a[i]? = some sl)
    (hl : v.live = sl.live) (hg : v.gen = sl.gen) (hq : v.queued = sl.queued) : Keeps a (a.set i v) := by
  have hlt := lt_of_get hsl
  refine ⟨by simp, ?_⟩
  intro j sk hj
  rw [get_set]
  by_cases hij : i = j
  · subst hij; rw [hsl] at hj; cases hj; exact ⟨v, by simp [hlt], hl, hg, hq⟩
  · simp only [hij, false_and, ↓reduceIte]; exact ⟨sk, hj, rfl, rfl, rfl⟩

theorem keeps_qinv (s : S) (hq : QInv s) (b : List Slot) (hk : Keeps s.slots b) : QInv { s with slots := b } := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu sl' hs'
    have hs'' : slotAt b u = some sl' := hs'
    obtain ⟨h1, h2, h3⟩ := slotAt_some.mp hs''
    have hlt : u.idx < s.slots.length := by rw [hk.1]; exact lt_of_get h1
    obtain ⟨sl, ha⟩ : ∃ sl, s.slots[u.idx]? = some sl := ⟨s.slots[u.idx], by simp [hlt]⟩
    obtain ⟨sl'', hb, l1, g1, q1⟩ := hk.2 _ sl ha
    rw [h1] at hb; cases hb
    rw [q1]
    exact hq.lq_q u hu sl (slotOf_some.mpr ⟨ha, l1.symm.trans h2, g1.symm.trans h3⟩)
  · show (s.queue.filter (valid b)).Nodup
    rw [List.filter_congr (fun u _ => valid_lg (keeps_lg hk) u)]
    exact hq.lq_nodup
  · show s.queue.length ≤ 2 * b.length
    rw [← hk.1]; exact hq.q_len

theorem notify_qinv (t : Ticket) (s : S) (hq : QInv s) : QInv (notify t s).2 := by
  unfold notify
  cases hs : slotOf s t with
  | none => exact hq
  | some sl =>
    obtain ⟨hsl, _, _⟩ := slotOf_some.mp hs
    cases hw : sl.waker with
    | none => simp only [hw]; exact hq
    | some w => simp only [hw]; exact keeps_qinv s hq _ (keeps_set s.slots t.idx sl _ hsl rfl rfl rfl)

theorem notifyAll_keeps (s : S) :
    Keeps s.slots (s.slots.map fun sl => if sl.live then { sl with waker := none } else sl) := by
  refine ⟨by simp, ?_⟩
  intro j sl hj
  refine ⟨if sl.live then { sl with waker := none } else sl, by simp [List.getElem?_map, hj], ?_, ?_, ?_⟩
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl

theorem notifyAll_qinv (s : S) (hq : QInv s) : QInv (notifyAll s).2 := by
  unfold notifyAll
  exact keeps_qinv s hq _ (notifyAll_keeps s)

theorem skip_qinv (slots : List Slot) (free : List Nat) (t : Ticket) (rest : List Ticket)
    (h : QInv ⟨slots, free, t :: rest⟩) (ht : slotAt slots t = none) : QInv ⟨slots, free, rest⟩ := by
  have hv : ¬valid slots t = true := by simp [valid, ht]
  refine ⟨fun u hu => h.lq_q u (List.mem_cons_of_mem _ hu), ?_, ?_⟩
  · have hn : ((t :: rest).filter (valid slots)).Nodup := h.lq_nodup
    rw [List.filter_cons_of_neg hv] at hn
    exact hn
  · have hl : (t :: rest).length ≤ 2 * slots.length := h.q_len
    show rest.length ≤ 2 * slots.length
    simp only [List.length_cons] at hl
    omega

/-- One turn of the baton's loop on a live entry keeps the queue exact: no later entry is live of the same slot. -/
theorem pop_qinv (slots : List Slot) (free : List Nat) (t : Ticket) (rest : List Ticket) (sl v : Slot)
    (h : QInv ⟨slots, free, t :: rest⟩) (hsl : slotAt slots t = some sl)
    (hl : v.live = sl.live) (hg : v.gen = sl.gen) : QInv ⟨slots.set t.idx v, free, rest⟩ := by
  obtain ⟨hs, _, _⟩ := slotAt_some.mp hsl
  have vset := valid_set slots t.idx sl v hs hl hg
  have hvt : valid slots t = true := valid_iff.mpr ⟨sl, hsl⟩
  have hn : ((t :: rest).filter (valid slots)).Nodup := h.lq_nodup
  rw [List.filter_cons_of_pos hvt, List.nodup_cons] at hn
  refine ⟨?_, ?_, ?_⟩
  · intro u hu sl' hs'
    have hs'' : slotAt (slots.set t.idx v) u = some sl' := hs'
    by_cases hut : u.idx = t.idx
    · exfalso
      have hvu : valid slots u = true := by rw [← vset u]; exact valid_iff.mpr ⟨sl', hs''⟩
      have e : u = t := valid_idx hvu hvt hut
      rw [e] at hu
      exact hn.1 (List.mem_filter.mpr ⟨hu, hvt⟩)
    · rw [slotAt_set_ne _ _ _ _ hut] at hs''
      exact h.lq_q u (List.mem_cons_of_mem _ hu) sl' hs''
  · show (rest.filter (valid (slots.set t.idx v))).Nodup
    rw [List.filter_congr (fun u _ => vset u)]
    exact hn.2
  · have hq : (t :: rest).length ≤ 2 * slots.length := h.q_len
    show rest.length ≤ 2 * (slots.set t.idx v).length
    simp only [List.length_cons, List.length_set] at hq ⊢
    omega

theorem batonGo_qinv (free : List Nat) : ∀ (q : List Ticket) (slots : List Slot), QInv ⟨slots, free, q⟩ →
    QInv ⟨(batonGo slots q).2.1, free, (batonGo slots q).2.2⟩
  | [], slots, h => by simp only [batonGo]; exact h
  | t :: rest, slots, h => by
    unfold batonGo
    cases hst : slotAt slots t with
    | none =>
      simp only
      exact batonGo_qinv free rest slots (skip_qinv slots free t rest h hst)
    | some sl =>
      simp only
      cases hw : sl.waker with
      | some w =>
        simp only
        exact pop_qinv slots free t rest sl _ h hst rfl rfl
      | none =>
        simp only
        exact batonGo_qinv free rest _ (pop_qinv slots free t rest sl _ h hst rfl rfl)

theorem baton_qinv (s : S) (hq : QInv s) : QInv (baton s).2 := by
  have := batonGo_qinv s.free s.queue s.slots hq
  unfold baton
  cases hb : batonGo s.slots s.queue with
  | mk w r =>
    cases r with
    | mk sl q =>
      rw [hb] at this
      exact this

theorem arm_qinv (t : Ticket) (w : Nat) (s : S) (hq : QInv s) : QInv (arm t w s) := by
  unfold arm
  cases hs : slotOf s t with
  | none => exact hq
  | some sl =>
    obtain ⟨hsl, _, _⟩ := slotOf_some.mp hs
    have hlt := lt_of_get hsl
    by_cases hqd : sl.queued = true
    · simp only [hqd, ↓reduceIte]
      exact keeps_qinv s hq _ (keeps_set s.slots t.idx sl _ hsl rfl rfl (by simp [hqd]))
    · simp only [hqd, Bool.false_eq_true, ↓reduceIte]
      have vset := valid_set s.slots t.idx sl { sl with waker := some w, queued := true } hsl rfl rfl
      have hvt : valid s.slots t = true := valid_iff.mpr ⟨sl, hs⟩
      have tnot : t ∉ s.queue.filter (valid s.slots) := by
        intro hm
        exact hqd (hq.lq_q t (List.mem_filter.mp hm).1 sl hs)
      refine ⟨?_, ?_, ?_⟩
      · intro u hu sl' hs'
        have hs'' : slotAt (s.slots.set t.idx { sl with waker := some w, queued := true }) u = some sl' := hs'
        by_cases hut : u.idx = t.idx
        · have := slotAt_set_eq hut hs''
          subst this
          rfl
        · rw [slotAt_set_ne _ _ _ _ hut] at hs''
          rcases List.mem_append.mp hu with hu | hu
          · exact hq.lq_q u (compact_sub hu) sl' hs''
          · rw [List.mem_singleton] at hu; subst hu; exact absurd rfl hut
      · show ((compact s ++ [t]).filter (valid (s.slots.set t.idx { sl with waker := some w, queued := true }))).Nodup
        rw [List.filter_congr (fun u _ => vset u), List.filter_append, compact_filter,
          List.filter_cons_of_pos hvt, List.filter_nil]
        refine List.nodup_append.mpr ⟨hq.lq_nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb; subst hb
        exact fun e => tnot (e ▸ ha)
      · show (compact s ++ [t]).length ≤ 2 * (s.slots.set t.idx { sl with waker := some w, queued := true }).length
        simp only [List.length_append, List.length_singleton, List.length_set]
        unfold compact
        split
        · have := live_le s hq
          omega
        · omega

theorem release_qinv (t : Ticket) (s : S) (hq : QInv s) : QInv (release t s) := by
  unfold release
  cases hs : slotOf s t with
  | none => exact hq
  | some sl =>
    -- after the release, a ticket names a live slot only if it did before and is not of the released slot
    have back : ∀ u sl', slotAt (s.slots.set t.idx
        { sl with live := false, gen := (sl.gen + 1) % GENS, waker := none, queued := false }) u = some sl' →
        slotAt s.slots u = some sl' := by
      intro u sl' hu
      by_cases hut : u.idx = t.idx
      · exfalso
        have := (slotAt_some.mp hu).2.1
        rw [slotAt_set_eq hut hu] at this
        simp at this
      · rw [slotAt_set_ne _ _ _ _ hut] at hu; exact hu
    refine ⟨?_, ?_, ?_⟩
    · intro u hu sl' hs'
      exact hq.lq_q u hu sl' (back u sl' hs')
    · show (s.queue.filter (valid (s.slots.set t.idx _))).Nodup
      refine hq.lq_nodup.sublist (filter_mono _ _ s.queue ?_)
      intro u _ hv
      obtain ⟨sl', hs'⟩ := valid_iff.mp hv
      exact valid_iff.mpr ⟨sl', back u sl' hs'⟩
    · show s.queue.length ≤ 2 * (s.slots.set t.idx _).length
      rw [List.length_set]; exact hq.q_len

theorem run_qinv (o : Op) (s : S) (h : Inv s) (hq : QInv s) (hn : ¬o.revives s) : QInv (o.run s) := by
  cases o with
  | alloc => exact alloc_qinv s h hq hn
  | arm t w => exact arm_qinv t w s hq
  | notify t => exact notify_qinv t s hq
  | baton => exact baton_qinv s hq
  | notifyAll => exact notifyAll_qinv s hq
  | release t => exact release_qinv t s hq

/-- Over any run that revives no stale entry, an exact queue stays exact. -/
theorem exec_qinv : ∀ (os : List Op) (s : S), Inv s → QInv s → NoRevive os s → QInv (exec os s)
  | [], _, _, hq, _ => hq
  | o :: os, s, h, hq, hn => exec_qinv os (o.run s) (run_inv o s h) (run_qinv o s h hq hn.1) hn.2

/-! ## The live entries of the queue are the documented order -/

theorem orderAfter_congr {a b : List Slot} (h : ∀ u, wakerAt a u = wakerAt b u) :
    ∀ l, orderAfter a l = orderAfter b l
  | [] => rfl
  | t :: rest => by simp only [orderAfter, h t, orderAfter_congr h rest]

theorem orderWoken_congr {a b : List Slot} (h : ∀ u, wakerAt a u = wakerAt b u) :
    ∀ l, orderWoken a l = orderWoken b l
  | [] => rfl
  | t :: rest => by simp only [orderWoken, h t, orderWoken_congr h rest]

/-- The baton's loop wakes what the documented order of the live entries says, and leaves as live entries the order
after it. -/
theorem batonGo_order : ∀ (q : List Ticket) (slots : List Slot),
    (batonGo slots q).2.2.filter (valid (batonGo slots q).2.1) = orderAfter slots (q.filter (valid slots)) ∧
    (batonGo slots q).1 = orderWoken slots (q.filter (valid slots))
  | [], slots => by simp [batonGo, orderAfter, orderWoken]
  | t :: rest, slots => by
    unfold batonGo
    cases hst : slotAt slots t with
    | none =>
      simp only
      have hv : ¬valid slots t = true := by simp [valid, hst]
      rw [List.filter_cons_of_neg hv]
      exact batonGo_order rest slots
    | some sl =>
      simp only
      have hv : valid slots t = true := valid_iff.mpr ⟨sl, hst⟩
      have hs := (slotAt_some.mp hst).1
      rw [List.filter_cons_of_pos hv]
      cases hw : sl.waker with
      | some w =>
        simp only
        have hwa : wakerAt slots t = some w := by simp [wakerAt, hst, hw]
        refine ⟨?_, ?_⟩
        · rw [List.filter_congr (fun u _ => valid_set slots t.idx sl { sl with queued := false, waker := none }
            hs rfl rfl u)]
          simp [orderAfter, hwa]
        · simp [orderWoken, hwa]
      | none =>
        simp only
        have hwa : wakerAt slots t = none := by simp [wakerAt, hst, hw]
        have ih := batonGo_order rest (slots.set t.idx { sl with waker := none, queued := false })
        rw [List.filter_congr (fun u _ => valid_set slots t.idx sl { sl with waker := none, queued := false } hs rfl rfl
          u)] at ih
        have hw2 : ∀ u, wakerAt (slots.set t.idx { sl with waker := none, queued := false }) u = wakerAt slots u :=
          wakerAt_set slots t.idx sl _ hs rfl rfl hw.symm
        rw [orderAfter_congr hw2, orderWoken_congr hw2] at ih
        simp only [orderAfter, orderWoken, hwa, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        exact ih

theorem baton_order (s : S) :
    (baton s).2.queue.filter (valid (baton s).2.slots) = orderAfter s.slots (s.queue.filter (valid s.slots)) ∧
    (baton s).1 = orderWoken s.slots (s.queue.filter (valid s.slots)) := by
  have := batonGo_order s.queue s.slots
  unfold baton
  cases hb : batonGo s.slots s.queue with
  | mk w r =>
    cases r with
    | mk sl q =>
      rw [hb] at this
      exact this

/-- With the live entries of the queue in the documented order, the baton wakes what that order says: the waker of
its oldest armed ticket. -/
theorem baton_oldest (s : S) (o : List Ticket) (ho : s.queue.filter (valid s.slots) = o) :
    (baton s).1 = orderWoken s.slots o := by
  rw [← ho]; exact (baton_order s).2

theorem arm_order (t : Ticket) (w : Nat) (s : S) (o : List Ticket) (h : Inv s) (hq : QInv s)
    (ho : s.queue.filter (valid s.slots) = o) :
    (arm t w s).queue.filter (valid (arm t w s).slots) = if valid s.slots t = true ∧ t ∉ o then o ++ [t] else o := by
  unfold arm
  cases hs : slotOf s t with
  | none =>
    have hv : ¬valid s.slots t = true := by
      have hs' : slotAt s.slots t = none := hs
      simp [valid, hs']
    rw [ite_eq_right (fun hc => hv hc.1)]
    exact ho
  | some sl =>
    obtain ⟨hsl, _, hgen⟩ := slotOf_some.mp hs
    have hv : valid s.slots t = true := valid_iff.mpr ⟨sl, hs⟩
    by_cases hqd : sl.queued = true
    · have hin : t ∈ o := by
        rw [← ho]
        obtain ⟨_, h2⟩ := h.q_live t.idx sl hsl hqd
        have e : (⟨t.idx, sl.gen⟩ : Ticket) = t := ticket_eq rfl hgen
        rw [e] at h2
        exact List.mem_filter.mpr ⟨h2, hv⟩
      rw [ite_eq_right (fun hc => hc.2 hin)]
      simp only [hqd, ↓reduceIte]
      show s.queue.filter (valid (s.slots.set t.idx { sl with waker := some w, queued := true })) = o
      rw [List.filter_congr (fun u _ => valid_set s.slots t.idx sl { sl with waker := some w, queued := true } hsl rfl
        rfl u)]
      exact ho
    · have hnin : t ∉ o := by
        rw [← ho]; intro hm
        exact hqd (hq.lq_q t (List.mem_filter.mp hm).1 sl hs)
      rw [ite_eq_left ⟨hv, hnin⟩]
      simp only [hqd, Bool.false_eq_true, ↓reduceIte]
      show (compact s ++ [t]).filter (valid (s.slots.set t.idx { sl with waker := some w, queued := true })) =
        o ++ [t]
      rw [List.filter_congr (fun u _ => valid_set s.slots t.idx sl { sl with waker := some w, queued := true }
          hsl rfl rfl u), List.filter_append, compact_filter, ho, List.filter_cons_of_pos hv, List.filter_nil]

theorem release_order (t : Ticket) (s : S) (o : List Ticket) (ho : s.queue.filter (valid s.slots) = o) :
    (release t s).queue.filter (valid (release t s).slots) =
      if valid s.slots t = true then o.filter (fun u => decide (u ≠ t)) else o := by
  unfold release
  cases hs : slotOf s t with
  | none =>
    have hv : ¬valid s.slots t = true := by
      have hs' : slotAt s.slots t = none := hs
      simp [valid, hs']
    rw [ite_eq_right hv]
    exact ho
  | some sl =>
    obtain ⟨hsl, _, _⟩ := slotOf_some.mp hs
    have hv : valid s.slots t = true := valid_iff.mpr ⟨sl, hs⟩
    rw [ite_eq_left hv, ← ho, List.filter_filter]
    show s.queue.filter (valid (s.slots.set t.idx
      { sl with live := false, gen := (sl.gen + 1) % GENS, waker := none, queued := false })) = _
    apply List.filter_congr
    intro u _
    show valid (s.slots.set t.idx _) u = (decide (u ≠ t) && valid s.slots u)
    by_cases hut : u.idx = t.idx
    · have h1 : valid (s.slots.set t.idx
          { sl with live := false, gen := (sl.gen + 1) % GENS, waker := none, queued := false }) u = false := by
        unfold valid
        rw [slotAt_set_same s.slots t.idx _ u hut (lt_of_get hsl)]
        simp
      have h2 : (decide (u ≠ t) && valid s.slots u) = false := by
        by_cases e : u = t
        · simp [e]
        · have : valid s.slots u = false := by
            cases hvu : valid s.slots u with
            | false => rfl
            | true => exact absurd (valid_idx hvu hv hut) e
          simp [this]
      rw [h1, h2]
    · have hne : u ≠ t := fun e => hut (by rw [e])
      have : valid (s.slots.set t.idx
          { sl with live := false, gen := (sl.gen + 1) % GENS, waker := none, queued := false }) u =
          valid s.slots u := by
        unfold valid
        rw [slotAt_set_ne _ _ _ u hut]
      rw [this]
      simp [hne]

theorem run_order (op : Op) (s : S) (o : List Ticket) (h : Inv s) (hq : QInv s)
    (ho : s.queue.filter (valid s.slots) = o) (hn : ¬op.revives s) :
    (op.run s).queue.filter (valid (op.run s).slots) = op.order s o := by
  cases op with
  | alloc => exact (alloc_live s h hn).trans ho
  | arm t w => exact arm_order t w s o h hq ho
  | notify t =>
    obtain ⟨hsh, _, hqe⟩ := notify_shape t s
    show (notify t s).2.queue.filter (valid (notify t s).2.slots) = o
    rw [hqe, List.filter_congr (fun u _ => valid_lg (shape_lg hsh) u)]
    exact ho
  | baton =>
    show (baton s).2.queue.filter (valid (baton s).2.slots) = orderAfter s.slots o
    rw [← ho]; exact (baton_order s).1
  | notifyAll =>
    obtain ⟨hsh, _, hqe⟩ := notifyAll_shape s
    show (notifyAll s).2.queue.filter (valid (notifyAll s).2.slots) = o
    rw [hqe, List.filter_congr (fun u _ => valid_lg (shape_lg hsh) u)]
    exact ho
  | release t => exact release_order t s o ho

/-- Over any run that revives no stale entry, the live entries of an exact queue in the documented order stay that
order. -/
theorem exec_order : ∀ (os : List Op) (s : S) (o : List Ticket), Inv s → QInv s →
    s.queue.filter (valid s.slots) = o → NoRevive os s →
    (execO os s o).1.queue.filter (valid (execO os s o).1.slots) = (execO os s o).2
  | [], _, _, _, _, ho, _ => ho
  | op :: os, s, o, h, hq, ho, hn =>
    exec_order os (op.run s) (op.order s o) (run_inv op s h) (run_qinv op s h hq hn.1)
      (run_order op s o h hq ho hn.1) hn.2

theorem execO_fst : ∀ (os : List Op) (s : S) (o : List Ticket), (execO os s o).1 = exec os s
  | [], _, _ => rfl
  | op :: os, s, o => execO_fst os (op.run s) (op.order s o)

/-- From the empty slab, over any run that revives no stale entry, the baton wakes the oldest armed ticket of the
documented order. -/
theorem exec_oldest (os : List Op) (hn : NoRevive os {}) :
    (baton (execO os {} []).1).1 = orderWoken (execO os {} []).1.slots (execO os {} []).2 :=
  baton_oldest _ _ (exec_order os {} [] init_inv init_qinv rfl hn)

/-! ## The order of issue #311 -/

/-- `release` before the fix: the slot stays queued and the entry of its ticket stays in the queue. -/
def releaseOld (t : Ticket) (s : S) : S :=
  match slotOf s t with
  | none => s
  | some sl =>
    { s with slots := s.slots.set t.idx { sl with live := false, gen := (sl.gen + 1) % GENS, waker := none },
             free := t.idx :: s.free }

/-- `arm` before the fix: a ticket is queued only when its slot is not, and nothing is compacted. -/
def armOld (t : Ticket) (w : Nat) (s : S) : S :=
  match slotOf s t with
  | none => s
  | some sl =>
    if sl.queued then { s with slots := s.slots.set t.idx { sl with waker := some w } }
    else { s with slots := s.slots.set t.idx { sl with waker := some w, queued := true }, queue := s.queue ++ [t] }

/-- The baton's loop before the fix: an entry is taken by its slot, whatever the generation. -/
def batonOldGo (slots : List Slot) : List Ticket → List Nat × List Slot × List Ticket
  | [] => ([], slots, [])
  | t :: rest =>
    match slots[t.idx]? with
    | none => batonOldGo slots rest
    | some sl =>
      match sl.live, sl.waker with
      | true, some w => ([w], slots.set t.idx { sl with queued := false, waker := none }, rest)
      | _, _ => batonOldGo (slots.set t.idx { sl with queued := false }) rest

def batonOld (s : S) : List Nat × S :=
  match batonOldGo s.slots s.queue with
  | (w, slots, q) => (w, { s with slots := slots, queue := q })

def Op.runOld : Op → S → S
  | .alloc, s => (FacadeStandby.alloc s).2
  | .arm t w, s => armOld t w s
  | .notify t, s => (FacadeStandby.notify t s).2
  | .baton, s => (batonOld s).2
  | .notifyAll, s => (FacadeStandby.notifyAll s).2
  | .release t, s => releaseOld t s

def execOld : List Op → S → S
  | [], s => s
  | o :: os, s => execOld os (o.runOld s)

/-- Three futures wait (tickets `⟨0,0⟩`, `⟨1,0⟩`, `⟨2,0⟩`, wakers 1, 2, 3, armed in that order); the second ends,
and a fourth takes its slot (ticket `⟨1,1⟩`) and arms waker 4 after the third armed waker 3; the first, the driver,
ends. -/
def run311 : List Op :=
  [.alloc, .alloc, .alloc, .arm ⟨0, 0⟩ 1, .arm ⟨1, 0⟩ 2, .arm ⟨2, 0⟩ 3, .release ⟨1, 0⟩, .alloc, .arm ⟨1, 1⟩ 4,
   .release ⟨0, 0⟩]

/-- Under the rule before the fix the documented order does not hold: in `run311` the reused slot kept the place of
the ticket that ended, and the baton woke waker 4, though the documented order (ticket `⟨2,0⟩`, then `⟨1,1⟩`) says
waker 3, which still waits. -/
theorem oldest_bad :
    (alloc (execOld (run311.take 7) {})).1 = ⟨1, 1⟩ ∧
    (execO run311 {} []).2 = [⟨2, 0⟩, ⟨1, 1⟩] ∧
    orderWoken (execOld run311 {}).slots (execO run311 {} []).2 = [3] ∧
    (batonOld (execOld run311 {})).1 = [4] := by
  decide

/-- The fixed rule on the same run: the ticket that reused the slot queued behind the one that waited, and the baton
wakes waker 3, as the documented order says. -/
theorem oldest_ok :
    (alloc (exec (run311.take 7) {})).1 = ⟨1, 1⟩ ∧
    (execO run311 {} []).2 = [⟨2, 0⟩, ⟨1, 1⟩] ∧
    (baton (exec run311 {})).1 = [3] ∧
    (baton (exec run311 {})).1 = orderWoken (exec run311 {}).slots (execO run311 {} []).2 := by
  decide

#audit_axioms Vinc.FacadeStandby.baton_first
#audit_axioms Vinc.FacadeStandby.baton_one
#audit_axioms Vinc.FacadeStandby.init_qinv
#audit_axioms Vinc.FacadeStandby.exec_qinv
#audit_axioms Vinc.FacadeStandby.live_le
#audit_axioms Vinc.FacadeStandby.exec_order
#audit_axioms Vinc.FacadeStandby.baton_order
#audit_axioms Vinc.FacadeStandby.baton_oldest
#audit_axioms Vinc.FacadeStandby.exec_oldest
#audit_axioms Vinc.FacadeStandby.oldest_bad
#audit_axioms Vinc.FacadeStandby.oldest_ok

end Vinc.FacadeStandby
