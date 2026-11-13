import Vinc.Axioms
import Vinc.CoreQueue

/-!
# The event queue: events leave in order, the ring never grows, an eviction takes the oldest recoverable event

What the model proves about `EventRing`, for any number of places and any run of calls (the statements about a
run are in `Vinc.CoreQueueRun`):

- the ring is a queue: a list `q` stands for what is queued, and `Rep` ties the cells, head and length to it. A push
  of `ev` onto a ring that is not full appends it; onto a full ring it drops `ev` when `ev` is recoverable, and
  else gives up the oldest recoverable queued event, or, when the queue holds none, its oldest event, then appends
  (`push_rep`, with `pushSpec`); a pop gives the oldest (`pop_rep`); a purge keeps the others in their order
  (`purge_rep`). The shift of the eviction and the compaction of the purge are the code's loops
  (`shift_spec`, `shiftC_eq_shift`, `purgeGo_spec`);
- the counters: a push onto a full ring counts one drop, and one loss exactly when the queue holds no recoverable
  event and the new one is not recoverable (`push_dropped`, `push_lost`); nothing else changes them;
- the places a table of `K` sessions uses are the places `0 .. CAP - 1` once each (`place_inj`).
-/

namespace Vinc.CoreQueue

/-! ## Places -/

theorem mod_inj_aux {c x y : Nat} (e : x % c = y % c) (hxy : x ≤ y) (hy : y < x + c) : x = y := by
  have h1 := Nat.div_add_mod x c
  have h2 := Nat.div_add_mod y c
  rw [← e] at h2
  rcases Nat.lt_trichotomy (x / c) (y / c) with h | h | h
  · have h3 : c * (x / c + 1) ≤ c * (y / c) := Nat.mul_le_mul_left c h
    have h4 : c * (x / c + 1) = c * (x / c) + c := Nat.mul_succ c (x / c)
    omega
  · rw [h] at h1
    omega
  · have h3 : c * (y / c + 1) ≤ c * (x / c) := Nat.mul_le_mul_left c h
    have h4 : c * (y / c + 1) = c * (y / c) + c := Nat.mul_succ c (y / c)
    omega

theorem at_inj {cap h i j : Nat} (hi : i < cap) (hj : j < cap) (e : (h + i) % cap = (h + j) % cap) : i = j := by
  rcases Nat.le_total i j with hij | hij
  · have := mod_inj_aux e (by omega) (by omega)
    omega
  · have := mod_inj_aux e.symm (by omega) (by omega)
    omega

theorem at_ne {cap h i j : Nat} (hi : i < cap) (hj : j < cap) (hne : i ≠ j) : (h + i) % cap ≠ (h + j) % cap :=
  fun e => hne (at_inj hi hj e)

/-- The code's address of place `p`: the base, or a row of `k` places. -/
def loc (k p : Nat) : Nat × Nat := if p < 1024 then (0, p) else (1 + (p - 1024) / k, (p - 1024) % k)

/-- The addressing is total on `0 .. CAP - 1`, lands in the base or in one of the four rows, and no two places
share a cell. -/
theorem place_inj {k p p' : Nat} (hk : 0 < k) (hp : p < eventQueue k) (hp' : p' < eventQueue k)
    (e : loc k p = loc k p') : p = p' := by
  unfold loc at e
  unfold eventQueue at hp hp'
  have d1 := Nat.div_add_mod (p - 1024) k
  have d2 := Nat.div_add_mod (p' - 1024) k
  by_cases a : p < 1024 <;> by_cases b : p' < 1024
  · simp [a, b] at e; exact e
  · simp [a, b] at e
    exact absurd e.1 (Nat.ne_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right _ _)))
  · simp [a, b] at e
  · simp [a, b] at e
    obtain ⟨e1, e2⟩ := e
    rw [e1, e2] at d1
    omega

theorem place_range {k p : Nat} (hk : 0 < k) (hp : p < eventQueue k) :
    (loc k p).1 < 5 ∧ ((loc k p).1 = 0 → (loc k p).2 < 1024) ∧ ((loc k p).1 ≠ 0 → (loc k p).2 < k) := by
  unfold loc
  unfold eventQueue at hp
  by_cases a : p < 1024
  · simp [a]
  · have : (p - 1024) / k < 4 := (Nat.div_lt_iff_lt_mul hk).2 (by omega)
    have h2 : (p - 1024) % k < k := Nat.mod_lt _ hk
    simp only [a, ite_false]
    exact ⟨by omega, fun hh => by simp at hh, fun _ => h2⟩

/-! ## The queue a ring stands for -/

/-- The cells, head and length of `r` hold the queue `q`, and the recoverable count is the queue's. -/
structure Rep (cap : Nat) (r : R) (q : List E) : Prop where
  cap_pos : 0 < cap
  head_lt : r.head < cap
  len_eq : r.len = q.length
  len_le : q.length ≤ cap
  cell : ∀ (i : Nat) (h : i < q.length), r.cells ((r.head + i) % cap) = some q[i]
  ll_eq : r.ll = q.countP (·.lossy)

theorem rep_init (cap : Nat) (hc : 0 < cap) : Rep cap ({} : R) [] :=
  ⟨hc, hc, rfl, Nat.zero_le _, fun _ h => by simp at h, rfl⟩

theorem setC_same (c : Cells) (p : Nat) (v : Option E) : setC c p v p = v := by simp [setC]

theorem setC_ne (c : Cells) (p q : Nat) (v : Option E) (h : q ≠ p) : setC c p v q = c q := by simp [setC, h]

theorem isLossy_some (e : E) : isLossy (some e) = e.lossy := rfl

theorem get_eq {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) (i : Nat) (hi : i < q.length) :
    get r cap i = some q[i] := h.cell i hi

/-! ## The scan for the oldest recoverable event -/

/-- The first position of a recoverable event, and the queue without it. -/
def evictFirstLossy : List E → Option (List E)
  | [] => none
  | e :: t => if e.lossy then some t else (evictFirstLossy t).map (e :: ·)

/-- What a push does to the queue: the specification of `push`. -/
def pushSpec (cap : Nat) (ev : E) (q : List E) : List E :=
  if q.length = cap then
    if ev.lossy then q else (evictFirstLossy q).getD (q.eraseIdx 0) ++ [ev]
  else q ++ [ev]

theorem evictFirstLossy_none : ∀ q : List E, evictFirstLossy q = none ↔ ∀ x ∈ q, x.lossy = false
  | [] => by simp [evictFirstLossy]
  | e :: t => by
    unfold evictFirstLossy
    by_cases h : e.lossy = true
    · simp [h]
    · have := evictFirstLossy_none t
      simp [h, this]

theorem evictFirstLossy_some : ∀ (q : List E) (v : Nat) (hv : v < q.length),
    q[v].lossy = true → (∀ (i : Nat) (hi : i < v), q[i].lossy = false) → evictFirstLossy q = some (q.eraseIdx v)
  | [], v, hv, _, _ => by simp at hv
  | e :: t, 0, _, h, _ => by
    have h' : e.lossy = true := h
    simp [evictFirstLossy, h']
  | e :: t, v + 1, hv, h, hb => by
    have he : e.lossy = false := by simpa using hb 0 (by omega)
    have ih := evictFirstLossy_some t v (by simpa using hv) (by simpa using h)
      (fun i hi => by simpa using hb (i + 1) (by omega))
    simp [evictFirstLossy, he, ih]

theorem evictFirstLossy_length : ∀ (q : List E) (t : List E), evictFirstLossy q = some t → t.length + 1 = q.length
  | [], t, h => by simp [evictFirstLossy] at h
  | e :: u, t, h => by
    unfold evictFirstLossy at h
    by_cases hl : e.lossy = true
    · simp [hl] at h; subst h; simp
    · simp [hl] at h
      obtain ⟨w, hw, rfl⟩ := h
      have := evictFirstLossy_length u w hw
      simp; omega

theorem evictFirstLossy_count : ∀ (q : List E) (t : List E), evictFirstLossy q = some t →
    q.countP (·.lossy) = t.countP (·.lossy) + 1
  | [], t, h => by simp [evictFirstLossy] at h
  | e :: u, t, h => by
    unfold evictFirstLossy at h
    by_cases hl : e.lossy = true
    · simp [hl] at h; subst h; simp [List.countP_cons, hl]
    · simp [hl] at h
      obtain ⟨w, hw, rfl⟩ := h
      have := evictFirstLossy_count u w hw
      simp [List.countP_cons, hl, this]

/-- The oldest recoverable event is gone, and the others are in their order (the eviction keeps a subsequence). -/
theorem evictFirstLossy_sublist : ∀ (q : List E) (t : List E), evictFirstLossy q = some t → t.Sublist q
  | [], t, h => by simp [evictFirstLossy] at h
  | e :: u, t, h => by
    unfold evictFirstLossy at h
    by_cases hl : e.lossy = true
    · simp [hl] at h; subst h; exact List.sublist_cons_self _ _
    · simp [hl] at h
      obtain ⟨w, hw, rfl⟩ := h
      exact (evictFirstLossy_sublist u w hw).cons_cons e

/-- What leaves is recoverable: every unrecoverable event of the queue stays. -/
theorem evictFirstLossy_keeps : ∀ (q : List E) (t : List E), evictFirstLossy q = some t →
    ∀ x ∈ q, x.lossy = false → x ∈ t
  | [], t, h => by simp [evictFirstLossy] at h
  | e :: u, t, h => by
    intro x hx hxl
    unfold evictFirstLossy at h
    by_cases hl : e.lossy = true
    · simp [hl] at h; subst h
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [hl] at hxl
      · exact hx
    · simp [hl] at h
      obtain ⟨w, hw, rfl⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (evictFirstLossy_keeps u w hw x hx hxl)

/-! ## The scans of the ring -/

theorem find_range_some (p : Nat → Bool) : ∀ (n v : Nat), (List.range n).find? p = some v →
    v < n ∧ p v = true ∧ ∀ i, i < v → p i = false
  | 0, v, h => by simp at h
  | n + 1, v, h => by
    rw [List.range_succ, List.find?_append] at h
    cases hf : (List.range n).find? p with
    | some w =>
      rw [hf] at h
      simp at h
      subst h
      obtain ⟨a, b, c⟩ := find_range_some p n w hf
      exact ⟨by omega, b, c⟩
    | none =>
      rw [hf] at h
      simp at h
      obtain ⟨hp, rfl⟩ := h
      refine ⟨by omega, hp, fun i hi => ?_⟩
      have := (List.find?_eq_none.mp hf) i (List.mem_range.mpr hi)
      simpa using this

theorem find_range_none (p : Nat → Bool) (n : Nat) (h : (List.range n).find? p = none) :
    ∀ i, i < n → p i = false := by
  intro i hi
  have := (List.find?_eq_none.mp h) i (List.mem_range.mpr hi)
  simpa using this

/-- The scan of the ring finds what `evictFirstLossy` removes. -/
theorem victim_evict {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) :
    (victim r cap = none ∧ evictFirstLossy q = none) ∨
    (∃ v, ∃ hv : v < q.length, victim r cap = some v ∧ q[v].lossy = true ∧ evictFirstLossy q = some (q.eraseIdx v)) := by
  cases hv : victim r cap with
  | none =>
    left
    refine ⟨rfl, (evictFirstLossy_none q).2 fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := find_range_none _ _ hv i (by rw [h.len_eq]; exact hi)
    rw [get_eq h i hi] at this
    simpa [isLossy] using this
  | some v =>
    right
    obtain ⟨a, b, c⟩ := find_range_some _ _ _ hv
    have hlt : v < q.length := by rw [← h.len_eq]; exact a
    refine ⟨v, hlt, rfl, ?_, ?_⟩
    · rw [get_eq h v hlt] at b; simpa [isLossy] using b
    · apply evictFirstLossy_some q v hlt
      · rw [get_eq h v hlt] at b; simpa [isLossy] using b
      · intro i hi
        have := c i hi
        rw [get_eq h i (by omega)] at this
        simpa [isLossy] using this

/-! ## The shift of an eviction -/

theorem shift_spec (head cap : Nat) : ∀ (v : Nat) (c : Cells), v < cap → ∀ j, j < cap →
    shift c head cap v ((head + j) % cap) =
      if 1 ≤ j ∧ j ≤ v then c ((head + (j - 1)) % cap) else c ((head + j) % cap)
  | 0, c, _, j, _ => by simp [shift]; omega
  | k + 1, c, hv, j, hj => by
    have ih := shift_spec head cap k (setC c ((head + k + 1) % cap) (c ((head + k) % cap))) (by omega) j hj
    simp only [shift]
    rw [ih]
    by_cases h1 : 1 ≤ j ∧ j ≤ k
    · have hne : (head + (j - 1)) % cap ≠ (head + k + 1) % cap := by
        have hi : j - 1 < cap := by omega
        have hj' : k + 1 < cap := hv
        have hn : j - 1 ≠ k + 1 := by omega
        have := at_ne (h := head) hi hj' hn
        rwa [← Nat.add_assoc] at this
      rw [if_pos h1, if_pos (by omega), setC_ne _ _ _ _ hne]
    · by_cases h2 : j = k + 1
      · subst h2
        have e : (head + (k + 1)) % cap = (head + k + 1) % cap := by rw [Nat.add_assoc]
        rw [if_neg h1, if_pos (by omega), e, setC_same]
        simp
      · have hne : (head + j) % cap ≠ (head + k + 1) % cap := by
          have hj' : k + 1 < cap := hv
          have := at_ne (h := head) hj hj' h2
          rwa [← Nat.add_assoc] at this
        rw [if_neg h1, if_neg (by omega), setC_ne _ _ _ _ hne]

theorem append_rep {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) (hl : r.len < cap) (ev : E) :
    Rep cap (append cap ev r) (q ++ [ev]) := by
  have hlen := h.len_eq
  refine ⟨h.cap_pos, h.head_lt, ?_, ?_, ?_, ?_⟩
  · simp [append, hlen]
  · have := h.len_le; simp; omega
  · intro i hi
    simp only [append]
    by_cases hi' : i < q.length
    · rw [List.getElem_append_left hi']
      rw [setC_ne _ _ _ _ (at_ne (by have := h.len_le; omega) (by omega) (by omega))]
      exact h.cell i hi'
    · have : i = q.length := by simp at hi; omega
      subst this
      simp [setC_same, hlen]
  · simp [append, h.ll_eq, List.countP_append]

theorem append_counts (cap : Nat) (ev : E) (r : R) :
    (append cap ev r).dropped = r.dropped ∧ (append cap ev r).lost = r.lost := ⟨rfl, rfl⟩

theorem pop_rep {cap : Nat} {r : R} {e : E} {t : List E} (h : Rep cap r (e :: t)) :
    (pop cap r).1 = some e ∧ Rep cap (pop cap r).2 t ∧ (pop cap r).2.dropped = r.dropped ∧
      (pop cap r).2.lost = r.lost := by
  have hlen := h.len_eq
  have hne : r.len ≠ 0 := by simp at hlen; omega
  have hc := h.cell 0 (by simp)
  have hhead : r.cells r.head = some e := by
    simpa [Nat.mod_eq_of_lt h.head_lt] using hc
  simp only [pop, hne, if_false, hhead]
  refine ⟨by simp, ⟨h.cap_pos, Nat.mod_lt _ h.cap_pos, ?_, ?_, ?_, ?_⟩, by simp, by simp⟩
  · simp at hlen ⊢; omega
  · have := h.len_le; simp at this ⊢; omega
  · intro i hi
    have hi1 : i + 1 < (e :: t).length := by simp; simpa using hi
    have hcell := h.cell (i + 1) hi1
    have e1 : ((r.head + 1) % cap + i) % cap = (r.head + (i + 1)) % cap := by
      rw [Nat.mod_add_mod]; congr 1; omega
    have hlt : i + 1 < cap := by have := h.len_le; omega
    have hne2 : (r.head + (i + 1)) % cap ≠ r.head := by
      have := at_ne (h := r.head) hlt h.cap_pos (by omega : i + 1 ≠ 0)
      simpa [Nat.mod_eq_of_lt h.head_lt] using this
    simp only [e1]
    rw [setC_ne _ _ _ _ hne2]
    simpa using hcell
  · have := h.ll_eq
    simp only [List.countP_cons] at this
    by_cases hl : e.lossy = true <;> simp [hl, isLossy_some] at this ⊢ <;> omega

theorem pop_empty {cap : Nat} {r : R} (h : Rep cap r []) : pop cap r = (none, r) := by
  have := h.len_eq
  simp [pop, this]

/-! ## The eviction -/

theorem shiftC_spec (head cap v : Nat) (c : Cells) (hc : 0 < cap) (j : Nat) (hj : j < cap) :
    shiftC c head cap v ((head + j) % cap) =
      if 1 ≤ j ∧ j ≤ v then c ((head + (j - 1)) % cap) else c ((head + j) % cap) := by
  have h1 : head % cap < cap := Nat.mod_lt _ hc
  have h2 : (head + j) % cap = (head % cap + j) % cap := by
    rw [Nat.add_mod head j cap, Nat.mod_eq_of_lt hj]
  have key : ((head + j) % cap + cap - head % cap) % cap = j := by
    rw [h2]
    by_cases h3 : head % cap + j < cap
    · rw [Nat.mod_eq_of_lt h3]
      have e : head % cap + j + cap - head % cap = j + cap := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    · have e1 : (head % cap + j) % cap = (head % cap + j - cap) % cap := Nat.mod_eq_sub_mod (by omega)
      rw [e1, Nat.mod_eq_of_lt (by omega : head % cap + j - cap < cap)]
      have e : head % cap + j - cap + cap - head % cap = j := by omega
      rw [e, Nat.mod_eq_of_lt hj]
  unfold shiftC
  simp only [key]

/-- The closed form is the code's loop (the loop of `shift`, which `shift_spec` describes). -/
theorem shiftC_eq_shift (head cap v : Nat) (c : Cells) (hc : 0 < cap) (hhead : head < cap) (hv : v < cap)
    (p : Nat) (hp : p < cap) : shiftC c head cap v p = shift c head cap v p := by
  have hj : (p + cap - head % cap) % cap < cap := Nat.mod_lt _ hc
  have hpj : (head + (p + cap - head % cap) % cap) % cap = p := by
    rw [Nat.mod_eq_of_lt hhead, Nat.add_mod_mod]
    have e : head + (p + cap - head) = p + cap := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hp]
  have h1 := shift_spec head cap v c hv _ hj
  rw [hpj] at h1
  rw [h1]
  unfold shiftC
  simp only [Nat.mod_eq_of_lt hhead]

theorem evict_cells {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) (hfull : r.len = cap) (v : Nat)
    (hv : v < q.length) :
    ∀ (i : Nat) (hi : i < (q.eraseIdx v).length),
      shiftC r.cells r.head cap v (((r.head + 1) % cap + i) % cap) = some (q.eraseIdx v)[i] := by
  intro i hi
  have hlen := h.len_eq
  have hle := h.len_le
  have hel : (q.eraseIdx v).length = q.length - 1 := by simp [List.length_eraseIdx, hv]
  have e1 : ((r.head + 1) % cap + i) % cap = (r.head + (i + 1)) % cap := by
    rw [Nat.mod_add_mod]; congr 1; omega
  rw [e1, shiftC_spec r.head cap v r.cells h.cap_pos (i + 1) (by omega)]
  rw [List.getElem_eraseIdx]
  by_cases hiv : i < v
  · simp only [hiv, dif_pos]
    rw [if_pos (by omega)]
    simpa using h.cell i (by omega)
  · simp only [hiv, dif_neg, not_false_eq_true]
    rw [if_neg (by omega)]
    exact h.cell (i + 1) (by omega)

theorem evict_rep {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) (hfull : r.len = cap) :
    (∀ t, evictFirstLossy q = some t → Rep cap (evict cap r) t ∧ (evict cap r).lost = r.lost ∧
        (evict cap r).dropped = r.dropped) ∧
    (evictFirstLossy q = none → Rep cap (evict cap r) (q.eraseIdx 0) ∧ (evict cap r).lost = r.lost + 1 ∧
        (evict cap r).dropped = r.dropped) := by
  have hlen := h.len_eq
  have hle := h.len_le
  have hpos : 0 < q.length := by have := h.cap_pos; omega
  rcases victim_evict h with ⟨hv, hq⟩ | ⟨v, hv, hvic, hl, hq⟩
  · refine ⟨fun t ht => by rw [hq] at ht; simp at ht, fun _ => ?_⟩
    have hall := (evictFirstLossy_none q).1 hq
    have hv0 : victim r cap = none := hv
    refine ⟨⟨h.cap_pos, Nat.mod_lt _ h.cap_pos, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [evict, List.length_eraseIdx, hpos]; omega
    · simp [List.length_eraseIdx, hpos]; omega
    · intro i hi
      have := evict_cells h hfull 0 hpos i hi
      simp only [evict, hv0, Option.getD_none]
      exact this
    · have hq1 : ∀ x ∈ q, x.lossy = false := hall
      have c0 : q.countP (·.lossy) = 0 := by
        rw [List.countP_eq_zero]; intro a ha; simp [hq1 a ha]
      have c1 : (q.eraseIdx 0).countP (·.lossy) = 0 := by
        rw [List.countP_eq_zero]; intro a ha
        have : a ∈ q := (List.eraseIdx_sublist q 0).subset ha
        simp [hq1 a this]
      have g0 : isLossy (get r cap 0) = false := by
        rw [get_eq h 0 hpos]
        simp [isLossy, hq1 _ (List.getElem_mem hpos)]
      have : (evict cap r).ll = r.ll := by simp [evict, hv0, g0]
      rw [this, h.ll_eq, c0, c1]
    · simp [evict, hv0]
    · rfl
  · refine ⟨fun t ht => ?_, fun hn => by rw [hq] at hn; simp at hn⟩
    rw [hq] at ht
    cases ht
    refine ⟨⟨h.cap_pos, Nat.mod_lt _ h.cap_pos, ?_, ?_, ?_, ?_⟩, ?_, rfl⟩
    · simp [evict, hvic, List.length_eraseIdx, hv]; omega
    · simp [List.length_eraseIdx, hv]; omega
    · intro i hi
      have := evict_cells h hfull v hv i hi
      simp only [evict, hvic]
      simpa using this
    · have hc := evictFirstLossy_count q _ hq
      have g : isLossy (get r cap v) = true := by rw [get_eq h v hv]; exact hl
      have hll := h.ll_eq
      simp [evict, hvic, g]
      omega
    · simp [evict, hvic]

/-! ## A push -/

theorem push_rep {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) (ev : E) :
    Rep cap (push cap ev r) (pushSpec cap ev q) := by
  have hlen := h.len_eq
  by_cases hfull : r.len = cap
  · have hfq : q.length = cap := by omega
    have hr : Rep cap { r with dropped := r.dropped + 1 } q :=
      ⟨h.cap_pos, h.head_lt, h.len_eq, h.len_le, h.cell, h.ll_eq⟩
    have hf1 : ({ r with dropped := r.dropped + 1 } : R).len = cap := hfull
    obtain ⟨e1, e2⟩ := evict_rep hr hf1
    unfold push pushSpec
    rw [if_pos hfull, if_pos hfq]
    by_cases hl : ev.lossy = true
    · simp only [hl, if_true]
      exact hr
    · simp only [hl, if_false]
      cases hq : evictFirstLossy q with
      | some t =>
        have hh := (e1 t hq).1
        have h1 := hh.len_eq
        have h2 := hh.len_le
        have h3 := evictFirstLossy_length q t hq
        have hlt : (evict cap { r with dropped := r.dropped + 1 }).len < cap := by omega
        exact append_rep hh hlt ev
      | none =>
        have hh := (e2 hq).1
        have h1 := hh.len_eq
        have h2 := hh.len_le
        have h3 : (q.eraseIdx 0).length = q.length - 1 := by simp [List.length_eraseIdx, hfq]
        have hlt : (evict cap { r with dropped := r.dropped + 1 }).len < cap := by have := h.cap_pos; omega
        exact append_rep hh hlt ev
  · have hfq : q.length ≠ cap := by omega
    unfold push pushSpec
    rw [if_neg hfull, if_neg hfq]
    exact append_rep h (by have := h.len_le; omega) ev

theorem push_dropped {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) (ev : E) :
    (push cap ev r).dropped = r.dropped + (if q.length = cap then 1 else 0) := by
  have hlen := h.len_eq
  by_cases hfull : r.len = cap
  · have hfq : q.length = cap := by omega
    unfold push
    rw [if_pos hfull, if_pos hfq]
    by_cases hl : ev.lossy = true <;> simp [hl, append, evict]
  · have hfq : q.length ≠ cap := by omega
    unfold push
    rw [if_neg hfull, if_neg hfq]
    simp [append]

theorem push_lost {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) (ev : E) :
    (push cap ev r).lost = r.lost +
      (if q.length = cap ∧ ev.lossy = false ∧ (∀ x ∈ q, x.lossy = false) then 1 else 0) := by
  have hlen := h.len_eq
  by_cases hfull : r.len = cap
  · have hfq : q.length = cap := by omega
    by_cases hl : ev.lossy = true
    · unfold push
      rw [if_pos hfull]
      simp [hl]
    · have hl' : ev.lossy = false := by simpa using hl
      have hr : Rep cap { r with dropped := r.dropped + 1 } q :=
        ⟨h.cap_pos, h.head_lt, h.len_eq, h.len_le, h.cell, h.ll_eq⟩
      have hf1 : ({ r with dropped := r.dropped + 1 } : R).len = cap := hfull
      obtain ⟨e1, e2⟩ := evict_rep hr hf1
      unfold push
      rw [if_pos hfull]
      cases hq : evictFirstLossy q with
      | some t =>
        have hn : ¬ (∀ x ∈ q, x.lossy = false) := fun hall =>
          absurd ((evictFirstLossy_none q).2 hall) (by simp [hq])
        simp only [hl, Bool.false_eq_true, ite_false, append, true_and]
        rw [if_neg (show ¬ (q.length = cap ∧ ∀ x ∈ q, x.lossy = false) from fun hh => hn hh.2)]
        simpa using (e1 t hq).2.1
      | none =>
        have hall := (evictFirstLossy_none q).1 hq
        simp only [hl, Bool.false_eq_true, ite_false, append, true_and]
        rw [if_pos (show q.length = cap ∧ ∀ x ∈ q, x.lossy = false from ⟨hfq, hall⟩)]
        simpa using (e2 hq).2.1
  · have hfq : q.length ≠ cap := by omega
    unfold push
    rw [if_neg hfull]
    simp [append, hfq]

/-! ## A purge -/

/-- What a purge keeps. -/
def keep (s : Nat) (e : E) : Bool := !stale s e

theorem purgeGo_spec (cap head s : Nat) (hc : 0 < cap) :
    ∀ (R F : List E) (c : Cells) (i ll : Nat), i + R.length ≤ cap → F.length ≤ i →
      (∀ (j : Nat) (hj : j < F.length), c ((head + j) % cap) = some F[j]) →
      (∀ (j : Nat) (hj : j < R.length), c ((head + (i + j)) % cap) = some R[j]) →
      ll = (F ++ R).countP (·.lossy) →
      (purgeGo cap head s R.length i c F.length ll).2.1 = (F ++ R.filter (keep s)).length ∧
      (∀ (j : Nat) (hj : j < (F ++ R.filter (keep s)).length),
        (purgeGo cap head s R.length i c F.length ll).1 ((head + j) % cap) = some (F ++ R.filter (keep s))[j]) ∧
      (purgeGo cap head s R.length i c F.length ll).2.2 = (F ++ R.filter (keep s)).countP (·.lossy)
  | [], F, c, i, ll, _, _, hA, _, hll => by
    refine ⟨by simp [purgeGo], fun j hj => ?_, by simp [purgeGo, hll]⟩
    simpa [purgeGo] using hA j (by simpa using hj)
  | ev :: R', F, c, i, ll, hi, hk, hA, hB, hll => by
    have hev := hB 0 (by simp)
    have hic : i < cap := by simp at hi; omega
    simp only [Nat.add_zero, List.getElem_cons_zero] at hev
    have hle : (purgeGo cap head s (ev :: R').length i c F.length ll) =
        (match c ((head + i) % cap) with
        | none => purgeGo cap head s R'.length (i + 1) c F.length ll
        | some ev =>
          if stale s ev then
            purgeGo cap head s R'.length (i + 1) (setC c ((head + i) % cap) none) F.length
              (ll - (if ev.lossy then 1 else 0))
          else purgeGo cap head s R'.length (i + 1)
            (setC (setC c ((head + i) % cap) none) ((head + F.length) % cap) (some ev)) (F.length + 1) ll) := by
      simp only [List.length_cons]
      rfl
    rw [hle, hev]
    simp only []
    by_cases hst : stale s ev = true
    · rw [if_pos hst]
      have hf : (ev :: R').filter (keep s) = R'.filter (keep s) := by simp [List.filter_cons, keep, hst]
      rw [hf]
      have ih := purgeGo_spec cap head s hc R' F (setC c ((head + i) % cap) none) (i + 1)
        (ll - (if ev.lossy then 1 else 0)) (by simp at hi; omega) (by omega)
        (fun j hj => by
          rw [setC_ne _ _ _ _ (at_ne (by omega) hic (by omega))]
          exact hA j hj)
        (fun j hj => by
          have e : i + 1 + j = i + (j + 1) := by omega
          rw [e, setC_ne _ _ _ _ (at_ne (by simp at hi; omega) hic (by omega))]
          have := hB (j + 1) (by simpa using hj)
          rw [List.getElem_cons_succ] at this
          exact this)
        (by
          rw [hll]
          simp only [List.countP_append, List.countP_cons]
          by_cases hl : ev.lossy = true <;> simp [hl])
      exact ih
    · rw [if_neg hst]
      have hf : (ev :: R').filter (keep s) = ev :: R'.filter (keep s) := by
        have : keep s ev = true := by simpa [keep] using hst
        simp [List.filter_cons, this]
      rw [hf]
      have ih := purgeGo_spec cap head s hc R' (F ++ [ev])
        (setC (setC c ((head + i) % cap) none) ((head + F.length) % cap) (some ev)) (i + 1) ll
        (by simp at hi; omega) (by simp; omega)
        (fun j hj => by
          by_cases hjF : j < F.length
          · rw [List.getElem_append_left hjF]
            rw [setC_ne _ _ _ _ (at_ne (by omega) (by omega) (by omega)),
              setC_ne _ _ _ _ (at_ne (by omega) hic (by omega))]
            exact hA j hjF
          · have : j = F.length := by simp at hj; omega
            subst this
            simp [setC_same])
        (fun j hj => by
          have e : i + 1 + j = i + (j + 1) := by omega
          rw [e, setC_ne _ _ _ _ (at_ne (by simp at hi; omega) (by omega) (by omega)),
            setC_ne _ _ _ _ (at_ne (by simp at hi; omega) hic (by omega))]
          have := hB (j + 1) (by simpa using hj)
          rw [List.getElem_cons_succ] at this
          exact this)
        (by simpa [List.countP_append, List.countP_cons] using hll)
      have e : (F ++ [ev]).length = F.length + 1 := by simp
      rw [e] at ih
      simp only [List.append_assoc, List.singleton_append] at ih
      exact ih

theorem purge_rep {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) (s : Nat) :
    Rep cap (purge cap s r) (q.filter (keep s)) := by
  have hlen := h.len_eq
  have key := purgeGo_spec cap r.head s h.cap_pos q [] r.cells 0 r.ll (by have := h.len_le; omega) (by simp)
    (fun j hj => by simp at hj) (fun j hj => by simpa using h.cell j hj) (by simpa using h.ll_eq)
  rw [← hlen] at key
  simp only [List.length_nil, List.nil_append] at key
  obtain ⟨c1, c2, c3⟩ := key
  unfold purge
  rcases hres : purgeGo cap r.head s r.len 0 r.cells 0 r.ll with ⟨c', k', l'⟩
  rw [hres] at c1 c2 c3
  refine ⟨h.cap_pos, h.head_lt, ?_, ?_, ?_, ?_⟩
  · exact c1
  · exact Nat.le_trans (List.length_filter_le _ _) h.len_le
  · intro j hj
    exact c2 j hj
  · exact c3

theorem purge_counts {r : R} (cap s : Nat) :
    (purge cap s r).dropped = r.dropped ∧ (purge cap s r).lost = r.lost := by
  unfold purge
  rcases purgeGo cap r.head s r.len 0 r.cells 0 r.ll with ⟨c', k', l'⟩
  exact ⟨rfl, rfl⟩

#audit_axioms Vinc.CoreQueue.place_inj
#audit_axioms Vinc.CoreQueue.place_range
#audit_axioms Vinc.CoreQueue.shift_spec
#audit_axioms Vinc.CoreQueue.shiftC_spec
#audit_axioms Vinc.CoreQueue.shiftC_eq_shift
#audit_axioms Vinc.CoreQueue.append_rep
#audit_axioms Vinc.CoreQueue.pop_rep
#audit_axioms Vinc.CoreQueue.evict_rep
#audit_axioms Vinc.CoreQueue.push_rep
#audit_axioms Vinc.CoreQueue.push_dropped
#audit_axioms Vinc.CoreQueue.push_lost
#audit_axioms Vinc.CoreQueue.purgeGo_spec
#audit_axioms Vinc.CoreQueue.purge_rep

end Vinc.CoreQueue
