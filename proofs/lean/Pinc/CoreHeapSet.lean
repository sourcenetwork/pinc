import Pinc.CoreHeapSift

/-!
# The deadline heap, part 3: `set` (push, update, remove)

- `set_new` (a new id goes at the end and up), `set_upd` (a held id moves up, down or nowhere) and `set_rem` (the last
  element takes the removed id's place and goes up, or down), with what each did (`Facts`).
- `set_inv`: `set` keeps `Inv` for every id (one outside `0..n` is ignored: `set_out`) and every deadline, and so does
  every run of calls (`run_inv`).
- `set_exact`: `set` changes exactly the entry it names: every other id keeps its presence and its deadline, the id
  asked about has the deadline given (or none), and the size changes by one only when an id comes or goes
  (`set_len_new`, `set_len_upd`, `set_len_rem`).
- `set_len_le`, `full_all_held`: the heap never holds more than `n` items, and at `n` every id is held, so a deadline
  given then moves its id in place; `view_run`: the entries are a map from ids to deadlines that each call updates,
  whatever the run.
-/

namespace Pinc.CoreHeap

/-! ## `set` -/

/-- What a call of `set` did, apart from keeping the invariant: `d` is the deadlines after it, `L` the size and `b`
whether the id asked about is present. -/
structure Facts (s : S) (id : Nat) (d : Nat → Nat) (L : Nat) (b : Bool) (r : S) : Prop where
  inv : Inv r
  n : r.n = s.n
  others : ∀ a, a ≠ id → (r.pos a).isSome = (s.pos a).isSome
  dl : r.dl = d
  len : r.len = L
  here : (r.pos id).isSome = b

theorem inj_id (s : S) (h : PosInv s) (id p j : Nat) (hp : s.pos id = some p) (hj : j < s.len) (hjp : j ≠ p) :
    s.heap j ≠ id := by
  intro he
  have := h.pa j hj
  rw [he, hp] at this
  exact hjp (Option.some.inj this).symm

theorem set_new (s : S) (h : Inv s) (id v : Nat) (hid : id < s.n) (hpos : s.pos id = none) :
    Facts s id (upd s.dl id v) (s.len + 1) true (set s id (some v)) := by
  have hp := h.pos
  have hne : ∀ j, j < s.len → s.heap j ≠ id := by
    intro j hj he
    have := hp.pa j hj
    rw [he, hpos] at this
    cases this
  simp only [set, hid, hpos, ite_true]
  generalize hs1 : ({ s with dl := upd s.dl id v, len := s.len + 1 } : S) = s1
  have hs1len : s1.len = s.len + 1 := by rw [← hs1]
  have hs1n : s1.n = s.n := by rw [← hs1]
  have hs1dl : s1.dl = upd s.dl id v := by rw [← hs1]
  have hs1h : s1.heap = s.heap := by rw [← hs1]
  have hs1p : s1.pos = s.pos := by rw [← hs1]
  have key1 : ∀ j, j < s.len → key (put s1 s.len id) j = key s j := by
    intro j hj
    rw [key_put_ne _ _ _ _ (by omega)]
    simp [key, hs1dl, hs1h, upd, hne j hj]
  have hHS : HS (put s1 s.len id) s.len id := by
    refine ⟨by simp [hs1len], by simp [hs1n, hid], ?_, ?_, ?_, ?_, ⟨s.len, by simp [pos_put]⟩, ?_, ?_⟩
    · intro j hj hjl
      simp only [len_put, hs1len] at hj
      simp only [heap_put, hjl, ite_false, hs1h, n_put, hs1n]
      exact hp.hlt j (by omega)
    · intro j hj hjl
      simp only [len_put, hs1len] at hj
      have hj' : j < s.len := by omega
      simp only [heap_put, hjl, ite_false, hs1h, pos_put, hne j hj', hs1p]
      exact hp.pa j hj'
    · intro a q hq hax
      rw [pos_put, if_neg hax, hs1p] at hq
      obtain ⟨h1, h2⟩ := hp.pb a q hq
      refine ⟨by simp [hs1len]; omega, by omega, ?_⟩
      simp [heap_put, hs1h, show q ≠ s.len by omega, h2]
    · intro j hj hjl
      simp only [len_put, hs1len] at hj
      simp only [heap_put, hjl, ite_false, hs1h]
      exact hne j (by omega)
    · intro j hj0 hj hjl hpj
      simp only [len_put, hs1len] at hj
      rw [key1 j (by omega), key1 _ (by omega)]
      exact h.ord j hj0 (by omega)
    · intro _ c hc0 hc hcp
      simp only [len_put, hs1len] at hc
      omega
  have hk : key (put s1 s.len id) s.len = ((put s1 s.len id).dl id, id) := key_put_eq _ _ _
  have hF := upLoop_spec id ((put s1 s.len id).dl id, id) s.len (put s1 s.len id) hHS rfl
    (fun c hc0 hc hcp => by simp only [len_put, hs1len] at hc; omega)
  have hup : up (put s1 s.len id) s.len = upLoop (put s1 s.len id) s.len id ((put s1 s.len id).dl id, id) := by
    unfold up; rw [← hk]; congr 1; simp [heap_put]
  rw [hup]
  refine ⟨⟨hF.pos, hF.ord⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF.n]; simp [hs1n]
  · intro a ha
    rw [hF.some]; simp [pos_put, ha, hs1p]
  · rw [hF.dl]; simp [hs1dl]
  · rw [hF.len]; simp [hs1len]
  · rw [hF.some]; simp [pos_put]


theorem set_upd (s : S) (h : Inv s) (id v p : Nat) (hid : id < s.n) (hpos : s.pos id = some p) :
    Facts s id (upd s.dl id v) s.len true (set s id (some v)) := by
  have hp := h.pos
  obtain ⟨hpl, hph⟩ := hp.pb id p hpos
  have hne : ∀ j, j < s.len → j ≠ p → s.heap j ≠ id := fun j hj hjp => inj_id s hp id p j hpos hj hjp
  simp only [set, hid, hpos, ite_true]
  generalize hs1 : ({ s with dl := upd s.dl id v } : S) = s1
  have hs1len : s1.len = s.len := by rw [← hs1]
  have hs1n : s1.n = s.n := by rw [← hs1]
  have hs1dl : s1.dl = upd s.dl id v := by rw [← hs1]
  have hs1h : s1.heap = s.heap := by rw [← hs1]
  have hs1p : s1.pos = s.pos := by rw [← hs1]
  have key1 : ∀ j, j < s.len → j ≠ p → key s1 j = key s j := by
    intro j hj hjp
    simp [key, hs1dl, hs1h, upd, hne j hj hjp]
  have kp : key s p = (s.dl id, id) := by simp [key, hph]
  have kp1 : key s1 p = (v, id) := by simp [key, hs1dl, hs1h, hph, upd]
  have hHS : HS s1 p id := by
    refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ⟨p, by rw [hs1p]; exact hpos⟩, ?_, ?_⟩
    · intro j hj _; rw [hs1h, hs1n]; exact hp.hlt j (by omega)
    · intro j hj _; rw [hs1h, hs1p]; exact hp.pa j (by omega)
    · intro a q hq hax
      rw [hs1p] at hq
      obtain ⟨h1, h2⟩ := hp.pb a q hq
      refine ⟨by omega, ?_, by rw [hs1h]; exact h2⟩
      rintro rfl
      rw [hph] at h2
      exact hax h2.symm
    · intro j hj hjp; rw [hs1h]; exact hne j (by omega) hjp
    · intro j hj0 hj hjp hpj
      rw [key1 j (by omega) hjp, key1 _ (by omega) hpj]
      exact h.ord j hj0 (by omega)
    · intro hp0 c hc0 hc hcp
      have hcp' : c ≠ p := by omega
      rw [key1 _ (by omega) (by omega), key1 c (by omega) hcp']
      have h1 := h.ord p hp0 hpl
      have h2 := h.ord c hc0 (by omega)
      rw [hcp] at h2
      exact Le_trans h1 h2
  have hup : up s1 p = upLoop s1 p id (v, id) := by
    unfold up; rw [kp1, hs1h, hph]
  have hdn : down s1 p = downLoop s1 p id (v, id) := by
    unfold down; rw [kp1, hs1h, hph]
  have hF : ∀ r, Fin' r s1 → Facts s id (upd s.dl id v) s.len true r := by
    intro r hr
    refine ⟨⟨hr.pos, hr.ord⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hr.n, hs1n]
    · intro a ha; rw [hr.some, hs1p]
    · rw [hr.dl, hs1dl]
    · rw [hr.len, hs1len]
    · rw [hr.some, hs1p, hpos]; rfl
  by_cases hlt : v < s.dl id
  · rw [if_pos hlt, hup]
    refine hF _ (upLoop_spec id (v, id) p s1 hHS (by simp [hs1dl, upd]) ?_)
    intro c hc0 hc hcp
    have hcp' : c ≠ p := by omega
    rw [key1 c (by omega) hcp']
    have h2 := h.ord c hc0 (by omega)
    rw [hcp, kp] at h2
    refine Le_trans ?_ h2
    unfold Le; simp; omega
  · rw [if_neg hlt]
    by_cases hgt : s.dl id < v
    · rw [if_pos hgt, hdn]
      refine hF _ (downLoop_spec id (v, id) (s1.len - p) p s1 rfl hHS (by simp [hs1dl, upd]) ?_)
      intro hp0
      rw [key1 _ (by omega) (by omega)]
      have h2 := h.ord p hp0 hpl
      rw [kp] at h2
      refine Le_trans h2 ?_
      unfold Le; simp; omega
    · rw [if_neg hgt]
      have hv : v = s.dl id := by omega
      have e : upd s.dl id v = s.dl := funext fun j => by
        simp only [upd]; split
        · rename_i hj; subst hj; exact hv
        · rfl
      have hs1s : s1 = s := by rw [← hs1, e]
      rw [hs1s]
      refine ⟨h, rfl, fun _ _ => rfl, ?_, rfl, ?_⟩
      · simp [e]
      · rw [hpos]; rfl

theorem set_rem (s : S) (h : Inv s) (id p : Nat) (hid : id < s.n) (hpos : s.pos id = some p) :
    Facts s id s.dl (if s.pos id = none then s.len else s.len - 1) false (set s id none) := by
  have hp := h.pos
  obtain ⟨hpl, hph⟩ := hp.pb id p hpos
  simp only [set, hid, hpos, ite_true]
  generalize hs1 : ({ s with len := s.len - 1, pos := upd s.pos id none } : S) = s1
  have hs1len : s1.len = s.len - 1 := by rw [← hs1]
  have hs1n : s1.n = s.n := by rw [← hs1]
  have hs1dl : s1.dl = s.dl := by rw [← hs1]
  have hs1h : s1.heap = s.heap := by rw [← hs1]
  have hs1p : s1.pos = upd s.pos id none := by rw [← hs1]
  have hLl : s.len - 1 < s.len := by omega
  generalize hlast : s.heap (s.len - 1) = last
  have hplast : s.pos last = some (s.len - 1) := by rw [← hlast]; exact hp.pa _ hLl
  have hlastn : last < s.n := by rw [← hlast]; exact hp.hlt _ hLl
  by_cases hli : last ≠ id
  · rw [if_pos hli]
    have hpL : p ≠ s.len - 1 := by
      rintro rfl
      rw [hlast] at hph
      exact hli hph
    have hpL' : p < s.len - 1 := by omega
    have hjinj : ∀ j, j < s.len → j ≠ p → s.heap j ≠ id := fun j hj hjp => inj_id s hp id p j hpos hj hjp
    have hjl : ∀ j, j < s.len - 1 → s.heap j ≠ last := by
      intro j hj he
      have := hp.pa j (by omega)
      rw [he, hplast] at this
      have := Option.some.inj this
      omega
    generalize hs2 : put s1 p last = s2
    have hs2len : s2.len = s.len - 1 := by rw [← hs2]; exact hs1len
    have hs2n : s2.n = s.n := by rw [← hs2]; exact hs1n
    have hs2dl : s2.dl = s.dl := by rw [← hs2]; exact hs1dl
    have hs2h : ∀ j, s2.heap j = if j = p then last else s.heap j := by
      intro j; rw [← hs2, heap_put, hs1h]
    have hs2p : ∀ a, s2.pos a = if a = last then some p else if a = id then none else s.pos a := by
      intro a; rw [← hs2, pos_put, hs1p]; simp [upd]
    have key2 : ∀ j, j ≠ p → key s2 j = key s j := by
      intro j hjp; simp [key, hs2h, hs2dl, hjp]
    have hHS : HS s2 p last := by
      refine ⟨by omega, by rw [hs2n]; exact hlastn, ?_, ?_, ?_, ?_, ⟨p, by simp [hs2p]⟩, ?_, ?_⟩
      · intro j hj hjp; rw [hs2h, if_neg hjp, hs2n]; exact hp.hlt j (by omega)
      · intro j hj hjp
        rw [hs2h, if_neg hjp, hs2p, if_neg (hjl j (by omega)), if_neg (hjinj j (by omega) hjp)]
        exact hp.pa j (by omega)
      · intro a q hq hal
        rw [hs2p, if_neg hal] at hq
        by_cases hai : a = id
        · rw [if_pos hai] at hq; cases hq
        · rw [if_neg hai] at hq
          obtain ⟨h1, h2⟩ := hp.pb a q hq
          have hqL : q ≠ s.len - 1 := by
            rintro rfl; rw [hlast] at h2; exact hal h2.symm
          have hqp : q ≠ p := by
            rintro rfl; rw [hph] at h2; exact hai h2.symm
          refine ⟨by omega, hqp, ?_⟩
          rw [hs2h, if_neg hqp]; exact h2
      · intro j hj hjp; rw [hs2h, if_neg hjp]; exact hjl j (by omega)
      · intro j hj0 hj hjp hpj
        rw [key2 j hjp, key2 _ hpj]
        exact h.ord j hj0 (by omega)
      · intro hp0 c hc0 hc hcp
        have hcp' : c ≠ p := by omega
        rw [key2 _ (by omega), key2 c hcp']
        have h1 := h.ord p hp0 hpl
        have h2 := h.ord c hc0 (by omega)
        rw [hcp] at h2
        exact Le_trans h1 h2
    have hT := rem_tail s2 p last hHS (by rw [hs2h, if_pos rfl]) (by rw [hs2p, if_pos rfl])
    refine ⟨⟨hT.pos, hT.ord⟩, hT.n.trans hs2n, ?_, hT.dl.trans hs2dl, ?_, ?_⟩
    · intro a ha
      rw [hT.some, hs2p]
      by_cases hal : a = last
      · subst hal; rw [hplast]; simp
      · simp [hal, ha]
    · rw [hT.len, hs2len]; simp
    · rw [hT.some, hs2p, if_neg (Ne.symm hli), if_pos rfl]; rfl
  · have hli' : last = id := by simpa using hli
    rw [if_neg hli]
    have hpL : p = s.len - 1 := by
      have := hp.pa p hpl
      rw [hph] at this
      have h2 : s.pos id = some (s.len - 1) := by rw [← hli']; exact hplast
      rw [hpos] at h2
      exact Option.some.inj h2
    have hjinj : ∀ j, j < s.len - 1 → s.heap j ≠ id := fun j hj => inj_id s hp id p j hpos (by omega) (by omega)
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, by rw [hs1n], ?_, by rw [hs1dl], ?_, ?_⟩
    · intro j hj
      rw [hs1len] at hj
      rw [hs1h, hs1p]
      have := hp.pa j (by omega)
      simp only [upd, hjinj j hj, ite_false]
      exact this
    · intro a q hq
      rw [hs1p] at hq
      simp only [upd] at hq
      split at hq
      · cases hq
      · rename_i hai
        obtain ⟨h1, h2⟩ := hp.pb a q hq
        have hqL : q ≠ s.len - 1 := by
          rintro rfl; rw [hlast, hli'] at h2; exact hai h2.symm
        rw [hs1len, hs1h]
        exact ⟨by omega, h2⟩
    · intro j hj
      rw [hs1len] at hj
      rw [hs1h, hs1n]; exact hp.hlt j (by omega)
    · intro j hj0 hj
      rw [hs1len] at hj
      have := h.ord j hj0 (by omega)
      simp only [key, hs1h, hs1dl]
      exact this
    · intro a ha; rw [hs1p]; simp [upd, ha]
    · rw [hs1len]; simp
    · rw [hs1p]; simp [upd]


theorem set_out (s : S) (id : Nat) (t : Option Nat) (h : ¬ id < s.n) : set s id t = s := by
  simp [set, h]

theorem set_nop (s : S) (id : Nat) (hpos : s.pos id = none) : set s id none = s := by
  by_cases hid : id < s.n <;> simp [set, hid, hpos]

/-- `set` keeps the invariant, for every id and every deadline. -/
theorem set_inv (s : S) (h : Inv s) (id : Nat) (t : Option Nat) : Inv (set s id t) := by
  by_cases hid : id < s.n
  · cases hpos : s.pos id with
    | none =>
      cases t with
      | none => rw [set_nop s id hpos]; exact h
      | some v => exact (set_new s h id v hid hpos).inv
    | some p =>
      cases t with
      | none => exact (set_rem s h id p hid hpos).inv
      | some v => exact (set_upd s h id v p hid hpos).inv
  · rw [set_out s id t hid]; exact h

/-- `set` changes exactly the entry it names: every other id keeps whether it is present and its deadline; the id
asked about has the deadline given, or none; the capacity is the same. -/
theorem set_exact (s : S) (h : Inv s) (id : Nat) (t : Option Nat) (hid : id < s.n) :
    (set s id t).n = s.n ∧
    (∀ a, a ≠ id → ((set s id t).pos a).isSome = (s.pos a).isSome ∧ (set s id t).dl a = s.dl a) ∧
    (∀ v, t = some v → ((set s id t).pos id).isSome = true ∧ (set s id t).dl id = v) ∧
    (t = none → (set s id t).pos id = none) := by
  cases hpos : s.pos id with
  | none =>
    cases t with
    | none => rw [set_nop s id hpos]; simp [hpos]
    | some v =>
      have F := set_new s h id v hid hpos
      refine ⟨F.n, fun a ha => ⟨F.others a ha, ?_⟩, fun w hw => ?_, fun hw => (by cases hw)⟩
      · rw [F.dl]; simp [upd, ha]
      · cases hw; exact ⟨F.here, by rw [F.dl]; simp [upd]⟩
  | some p =>
    cases t with
    | none =>
      have F := set_rem s h id p hid hpos
      refine ⟨F.n, fun a ha => ⟨F.others a ha, by rw [F.dl]⟩, fun w hw => (by cases hw), fun _ => ?_⟩
      have := F.here
      simpa using this
    | some v =>
      have F := set_upd s h id v p hid hpos
      refine ⟨F.n, fun a ha => ⟨F.others a ha, ?_⟩, fun w hw => ?_, fun hw => (by cases hw)⟩
      · rw [F.dl]; simp [upd, ha]
      · cases hw; exact ⟨F.here, by rw [F.dl]; simp [upd]⟩

/-- The size changes by one when an id comes or goes, and not otherwise. -/
theorem set_len_new (s : S) (h : Inv s) (id v : Nat) (hid : id < s.n) (hpos : s.pos id = none) :
    (set s id (some v)).len = s.len + 1 := (set_new s h id v hid hpos).len
theorem set_len_upd (s : S) (h : Inv s) (id v p : Nat) (hid : id < s.n) (hpos : s.pos id = some p) :
    (set s id (some v)).len = s.len := (set_upd s h id v p hid hpos).len
theorem set_len_rem (s : S) (h : Inv s) (id p : Nat) (hid : id < s.n) (hpos : s.pos id = some p) :
    (set s id none).len = s.len - 1 := by
  have := (set_rem s h id p hid hpos).len
  simpa [hpos] using this

theorem set_n (s : S) (h : Inv s) (id : Nat) (t : Option Nat) : (set s id t).n = s.n := by
  by_cases hid : id < s.n
  · exact (set_exact s h id t hid).1
  · rw [set_out s id t hid]

/-- A run of calls keeps the invariant. -/
theorem run_inv (s : S) (h : Inv s) : ∀ ops, Inv (run s ops)
  | [] => h
  | (id, t) :: l => run_inv (set s id t) (set_inv s h id t) l

theorem run_n (s : S) (h : Inv s) : ∀ ops, (run s ops).n = s.n
  | [] => rfl
  | (id, t) :: l => by
    rw [show run s ((id, t) :: l) = run (set s id t) l from rfl, run_n (set s id t) (set_inv s h id t) l]
    exact set_n s h id t

/-! ## The capacity -/

/-- After any call the heap holds at most `n` items. -/
theorem set_len_le (s : S) (h : Inv s) (id : Nat) (t : Option Nat) : (set s id t).len ≤ s.n := by
  have := len_le _ (set_inv s h id t).pos
  rwa [set_n s h id t] at this

/-- At capacity every id below `n` is held, so a call that gives an id a deadline moves it in place and the heap
does not grow. -/
theorem full_all_held (s : S) (h : Inv s) (hfull : s.len = s.n) (id : Nat) (hid : id < s.n) :
    (s.pos id).isSome = true := by
  cases hpos : s.pos id with
  | some _ => rfl
  | none =>
    have h1 := set_len_new s h id 0 hid hpos
    have h2 := set_len_le s h id (some 0)
    omega

/-! ## The entries as a map -/

/-- The deadline of each id, if it has one. -/
def view (s : S) (a : Nat) : Option Nat := if (s.pos a).isSome then some (s.dl a) else none

theorem view_set (s : S) (h : Inv s) (id : Nat) (t : Option Nat) (a : Nat) :
    view (set s id t) a = if id < s.n ∧ a = id then t else view s a := by
  by_cases hid : id < s.n
  · by_cases ha : a = id
    · subst ha
      obtain ⟨_, _, h3, h4⟩ := set_exact s h a t hid
      cases t with
      | some v =>
        obtain ⟨h5, h6⟩ := h3 v rfl
        simp [view, h5, h6, hid]
      | none => simp [view, h4 rfl, hid]
    · obtain ⟨_, h2, _, _⟩ := set_exact s h id t hid
      obtain ⟨h5, h6⟩ := h2 a ha
      simp [view, h5, h6, ha]
  · simp [set_out s id t hid, hid]

/-- The naive heap: a map from ids to deadlines. -/
def naive (n : Nat) (m : Nat → Option Nat) : List (Nat × Option Nat) → Nat → Option Nat
  | [] => m
  | (id, t) :: l => naive n (if id < n then upd m id t else m) l

theorem view_run (s : S) (h : Inv s) : ∀ ops, view (run s ops) = naive s.n (view s) ops
  | [] => rfl
  | (id, t) :: l => by
    show view (run (set s id t) l) = naive s.n (if id < s.n then upd (view s) id t else view s) l
    rw [view_run (set s id t) (set_inv s h id t) l, set_n s h id t]
    congr 1
    funext a
    rw [view_set s h id t a]
    by_cases hid : id < s.n
    · by_cases ha : a = id <;> simp [upd, hid, ha]
    · simp [hid]

#audit_axioms Pinc.CoreHeap.set_inv
#audit_axioms Pinc.CoreHeap.set_exact
#audit_axioms Pinc.CoreHeap.set_len_new
#audit_axioms Pinc.CoreHeap.set_len_upd
#audit_axioms Pinc.CoreHeap.set_len_rem
#audit_axioms Pinc.CoreHeap.run_inv
#audit_axioms Pinc.CoreHeap.set_len_le
#audit_axioms Pinc.CoreHeap.full_all_held
#audit_axioms Pinc.CoreHeap.view_run

end Pinc.CoreHeap
